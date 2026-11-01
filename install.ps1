param (
    [switch]$Clean
)

$ErrorActionPreference = "Stop"

$InstallDir = Get-Location
$CompilerDir = Join-Path $InstallDir "compiler_win"
$LibffiDir   = Join-Path $InstallDir "libffi_win"
$DotnetDir   = Join-Path $InstallDir "dotnet_win"

# --- DEPENDENCY DOWNLOAD AND CHECK --- #

Write-Host "[1/6] Verifying system dependencies..." -ForegroundColor Cyan

$GccZipUrl  = "https://github.com/brechtsanders/winlibs_mingw/releases/download/14.2.0posix-19.1.1-12.0.0-ucrt-r2/winlibs-x86_64-posix-seh-gcc-14.2.0-mingw-w64ucrt-12.0.0-r2.zip"
$GccZipPath = Join-Path $InstallDir "gcc_mingw.zip"

$LibffiPkgUrl  = "https://repo.msys2.org/mingw/mingw64/mingw-w64-x86_64-libffi-3.5.2-1-any.pkg.tar.zst"
$LibffiPkgPath = Join-Path $InstallDir "libffi.pkg.tar.zst"

$ZstdZipUrl  = "https://github.com/facebook/zstd/releases/download/v1.5.6/zstd-v1.5.6-win64.zip"
$ZstdZipPath = Join-Path $InstallDir "zstd.zip"
$ZstdTmpDir  = Join-Path $InstallDir "zstd_tmp"

function Test-CommandExists { param($cmd) return [bool](Get-Command $cmd -ErrorAction SilentlyContinue) }

if (!(Test-Path $CompilerDir)) { New-Item -ItemType Directory -Path $CompilerDir | Out-Null }
if (!(Test-Path $LibffiDir)) { New-Item -ItemType Directory -Path $LibffiDir | Out-Null }

if (!(Test-CommandExists tar.exe)) { throw "tar.exe is missing on the host environment." }

# GCC Compiler
$GccExe = Join-Path $CompilerDir "mingw64\bin\gcc.exe"
$GccBinFolder = Join-Path $CompilerDir "mingw64\bin"
if (!(Test-Path $GccExe)) {
    if (!(Test-Path $GccZipPath)) {
        Write-Host "Downloading GCC/MinGW..." -ForegroundColor Gray
        Invoke-WebRequest -Uri $GccZipUrl -OutFile $GccZipPath -UseBasicParsing
    }
    Write-Host "Extracting GCC/MinGW..." -ForegroundColor Gray
    Expand-Archive -Path $GccZipPath -DestinationPath $CompilerDir -Force
    if (Test-Path $GccZipPath) { Remove-Item $GccZipPath -Force }
}

# Libffi
$FfiIncludeDir = Join-Path $LibffiDir "mingw64\include"
$FfiLibDir     = Join-Path $LibffiDir "mingw64\lib"
$FfiBinDir     = Join-Path $LibffiDir "mingw64\bin"
$FfiHeader     = Join-Path $FfiIncludeDir "ffi.h"

if (!(Test-Path $FfiHeader)) {
    if (!(Test-CommandExists "zstd")) {
        if (!(Test-Path $ZstdZipPath)) {
            Invoke-WebRequest -Uri $ZstdZipUrl -OutFile $ZstdZipPath -UseBasicParsing
        }
        Expand-Archive -Path $ZstdZipPath -DestinationPath $ZstdTmpDir -Force
        $ZstdExe = Get-ChildItem -Path $ZstdTmpDir -Filter "zstd.exe" -Recurse | Select-Object -First 1
        if ($ZstdExe) { Copy-Item -Path $ZstdExe.FullName -Destination $InstallDir -Force }
        if (Test-Path $ZstdZipPath) { Remove-Item $ZstdZipPath -Force }
        if (Test-Path $ZstdTmpDir) { Remove-Item $ZstdTmpDir -Recurse -Force }
    }

    $OldPath = $env:PATH
    $env:PATH = "$InstallDir;" + $env:PATH
    if (!(Test-Path $LibffiPkgPath)) {
        Write-Host "Downloading Libffi..." -ForegroundColor Gray
        Invoke-WebRequest -Uri $LibffiPkgUrl -OutFile $LibffiPkgPath -UseBasicParsing
    }
    Write-Host "Extracting Libffi..." -ForegroundColor Gray
    & tar.exe -xf $LibffiPkgPath -C $LibffiDir
    $TarExitCode = $LASTEXITCODE
    $env:PATH = $OldPath
    if (Test-Path $LibffiPkgPath) { Remove-Item $LibffiPkgPath -Force }
    if (Test-Path (Join-Path $InstallDir "zstd.exe")) { Remove-Item (Join-Path $InstallDir "zstd.exe") -Force }
    if ($TarExitCode -ne 0) { throw "Libffi extraction failed." }
}

# .NET 10 SDK
$DotnetExe = Join-Path $DotnetDir "dotnet.exe"
if (!(Test-Path $DotnetExe)) {
    Write-Host "Installing local .NET 10 SDK..." -ForegroundColor Gray
    if (!(Test-Path $DotnetDir)) { New-Item -ItemType Directory -Path $DotnetDir | Out-Null }
    $InstallScript = Join-Path $InstallDir "dotnet-install.ps1"
    Invoke-WebRequest -Uri "https://dot.net/v1/dotnet-install.ps1" -OutFile $InstallScript -UseBasicParsing
    & $InstallScript -Channel "10.0" -InstallDir $DotnetDir -NoPath
    if (Test-Path $InstallScript) { Remove-Item $InstallScript -Force }
}

# --- NATIVE C LIBRARY COMPILATION --- #

Write-Host "`n[2/6] Compiling native C library (librcl.dll)..." -ForegroundColor Cyan

$CSourceFile = Join-Path $InstallDir "liyh\C\rcl.c"
$CLibOutput  = Join-Path $InstallDir "librcl.dll"

if (!(Test-Path $CSourceFile)) {
    throw "C source file not found: $CSourceFile"
}

& $GccExe -shared -o $CLibOutput $CSourceFile -I"$FfiIncludeDir" -L"$FfiLibDir" -lffi -O3
if ($LASTEXITCODE -ne 0 -or !(Test-Path $CLibOutput)) {
    throw "Failed to compile librcl.dll with GCC."
}

# --- .NET APPLICATION PUBLICATION ---

Write-Host "`n[3/6] Publishing .NET project for Windows (Self-Contained)..." -ForegroundColor Cyan

$Rid = "win-x64"
$BuildOutput = Join-Path $InstallDir "bin\Release\net10.0\$Rid\publish"

& $DotnetExe publish liyh -c Release -r $Rid --self-contained true -p:PublishReadyToRun=true -o $BuildOutput
if ($LASTEXITCODE -ne 0) {
    throw ".NET publication failed."
}

# --- DEPENDENCY ASSEMBLING AND LOCAL CONFIGURATION ---

Write-Host "`n[4/6] Assembling local dynamic dependencies..." -ForegroundColor Cyan

Copy-Item -Path $CLibOutput -Destination $BuildOutput -Force
Get-ChildItem -Path $FfiBinDir -Filter "libffi*.dll" | Copy-Item -Destination $BuildOutput -Force

$ConfigPath = Join-Path $BuildOutput ".compiler_config"
@"
CC_PATH=$GccBinFolder\gcc.exe
GCC_BIN_DIR=$GccBinFolder
FFI_INCLUDE_DIR=$FfiIncludeDir
FFI_LIB_DIR=$FfiLibDir
"@ | Out-File -FilePath $ConfigPath -Encoding ascii

$RootConfigPath = Join-Path $InstallDir ".compiler_config"
Copy-Item $ConfigPath -Destination $RootConfigPath -Force

# --- GLOBAL PERMANENT INSTALLATION --- #

Write-Host "`n[5/6] Installing globally into user profile..." -ForegroundColor Cyan

$TargetInstallDir = Join-Path $env:USERPROFILE ".liyh"
$TargetBinDir     = Join-Path $TargetInstallDir "bin"
$TargetCompilerDir= Join-Path $TargetInstallDir "compiler"
$TargetLibffiDir  = Join-Path $TargetInstallDir "libffi"

Write-Host "Preparing permanent directories in: $TargetInstallDir"
if (Test-Path $TargetBinDir) { Remove-Item "$TargetBinDir\*" -Recurse -Force } else { New-Item -ItemType Directory -Path $TargetBinDir | Out-Null }
if (Test-Path $TargetCompilerDir) { Remove-Item "$TargetCompilerDir\*" -Recurse -Force } else { New-Item -ItemType Directory -Path $TargetCompilerDir | Out-Null }
if (Test-Path $TargetLibffiDir) { Remove-Item "$TargetLibffiDir\*" -Recurse -Force } else { New-Item -ItemType Directory -Path $TargetLibffiDir | Out-Null }

Write-Host "Copying liyh application..."
Copy-Item -Path "$BuildOutput\*" -Destination $TargetBinDir -Recurse -Force

Write-Host "Copying embedded GCC compiler..."
Copy-Item -Path "$CompilerDir\mingw64\*" -Destination $TargetCompilerDir -Recurse -Force

Write-Host "Copying LibFFI development files..."
Copy-Item -Path "$LibffiDir\mingw64\*" -Destination $TargetLibffiDir -Recurse -Force

# Global permanent configuration
$FinalConfigPath = Join-Path $TargetBinDir ".compiler_config"
@"
CC_PATH=$TargetCompilerDir\bin\gcc.exe
GCC_BIN_DIR=$TargetCompilerDir\bin
FFI_INCLUDE_DIR=$TargetLibffiDir\include
FFI_LIB_DIR=$TargetLibffiDir\lib
"@ | Out-File -FilePath $FinalConfigPath -Encoding ascii

# Robust user PATH update
Write-Host "Adding application to user PATH..." -ForegroundColor Yellow
$UserPath = [Environment]::GetEnvironmentVariable("PATH", "User")
$UserPathPaths = $UserPath -split ';'
if ($UserPathPaths -notcontains $TargetBinDir) {
    [Environment]::SetEnvironmentVariable("PATH", "$UserPath;$TargetBinDir", "User")
    $env:PATH = "$env:PATH;$TargetBinDir"
    Write-Host "-> PATH successfully updated." -ForegroundColor Green
} else {
    Write-Host "-> Directory already present in PATH." -ForegroundColor Gray
}

# --- PARTIE 6: OPTIONAL SECURE CLEANUP OF TEMPORARY BUILD DIRECTORIES --- #

if ($Clean) {
    Write-Host "`n[6/6] Cleaning up temporary build folders (-Clean flag detected)..." -ForegroundColor Cyan

    $ItemsToClean = @(
        $CompilerDir,
        $LibffiDir,
        $DotnetDir,
        $CLibOutput,
        (Join-Path $InstallDir "bin"),
        (Join-Path $InstallDir "obj")
    )

    foreach ($Item in $ItemsToClean) {
        if (Test-Path $Item) {
            Write-Host "Removing: $Item" -ForegroundColor Gray
            Remove-Item $Item -Recurse -Force
        }
    }
    Write-Host "-> Cleanup completed successfully." -ForegroundColor Green
} else {
    Write-Host "`n[6/6] Skipping build folders cleanup (Run with -Clean to remove temporary artifacts)." -ForegroundColor Gray
}

Write-Host " Installation and compilation completed successfully." -ForegroundColor Green
Write-Host " You can now use 'liyh' from anywhere."
Write-Host " You may clean the building files by running this script using '-Clean'."

