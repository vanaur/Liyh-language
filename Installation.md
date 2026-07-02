# Installation

Follow these instructions carefully if you wish to install Liyh.

> [!NOTE]
> The project is written in [F#](https://fsharp.org/) and in C. It requires .NET as well as a C compiler (for the build _and_ the runtime). The installation scripts handle dependencies automatically.
> 
> If .NET is missing, it installs a local, isolated version just for this project. Don't worry, this local version won't touch your global configuration and can be completely removed from your system. The same goes for the needed C compiler.

Liyh is being developed on Manjaro Linux, so development efforts are primarily focused on Linux, but efforts have been made to make the project as cross-platform as possible. It has been tested on Linux and Windows.

No dependencies or prior setup on your part are required; the installation scripts are designed to be self-contained and non-intrusive, so as to respect your environment.

Please feel free to report any build errors for the handled plateforms in the [issues](https://github.com/vanaur/Liyh-language/issues) if necessary.

## Linux and MacOS

 1. Go to the root of the project (`Liyh-language`).
 2. Open a terminal, and type `chmod +x ./install.sh` to make the installation script executable.
 3. Execute the installer with `./install.sh`. If asked, enter your password and validate the dependencies.
 4. If everything went well, type `make` and install globally with `sudo make install`.
 5. You can uninstall at any time with `sudo make uninstall`.

You can clean up build files with `make clean` and `make distclean`.

If everything went well, then you should be able to use `liyh` in a terminal!

## Windows

 1. Go the root of the project (`Liyh-language`).
 2. Open a PowerShell terminal (you may need to open it as administrator).
 3. Type `Set-ExecutionPolicy Bypass -Scope Process` to allow the script to run.
 4. Execute the installer with `& .\install.ps1`. This will install the dependencies locally and build the compiler for your PATH.
 5. You can uninstall at any time by deleting the folder that was created (the PowerShell script message will tell you which folder).

You can clean up build files with `& ./install.ps1 -Clean`.

If everything went well, then you should be able to use `liyh` in a terminal!

---

**Note:** Gemini 3.5 Flash was used to help building those installation scripts, in particular for Windows and MacOS.

