#!/bin/bash
set -e

# Prevent running as root
if [ "$EUID" -eq 0 ]; then
    echo "Error: Do not run this script as root. Run as a normal user."
    echo "The script will request sudo privileges only when needed."
    exit 1
fi

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

info() { echo -e "${GREEN}[INFO]${NC} $1"; }
warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }
error() { echo -e "${RED}[ERROR]${NC} $1"; exit 1; }

command_exists() { command -v "$1" >/dev/null 2>&1; }

# Global variables for config generation
EXTRA_CFLAGS=""
EXTRA_LDFLAGS=""

detect_os() {
    local kernel=$(uname -s)
    if [ "$kernel" = "Darwin" ]; then
        OS="macos"
        DISTRO="macos"
        info "Detected OS: macOS"
    elif [ -f /etc/os-release ]; then
        OS="linux"
        . /etc/os-release
        DISTRO=$ID
        DISTRO_LIKE=$ID_LIKE
        info "Detected OS: Linux ($DISTRO)"
    else
        error "Unsupported operating system: $kernel"
    fi
}

install_dependencies() {
    info "Checking system dependencies..."
    local needs_install=false
    local packages=""
    
    # Check for C compiler
    if ! command_exists cc; then
        warn "No C compiler found."
        needs_install=true
    fi

    if [ "$OS" = "macos" ]; then
        # macOS (Homebrew)
        if ! command_exists brew; then
            error "Homebrew is required for macOS installation. See https://brew.sh/"
        fi
        
        if ! brew list libgc >/dev/null 2>&1; then
            packages="$packages libgc"
            needs_install=true
        fi
        
        if $needs_install; then
            info "Installing dependencies via Homebrew..."
            brew install $packages
        fi
        
        # Set flags for Homebrew libraries
        EXTRA_CFLAGS="-I$(brew --prefix libgc)/include"
        EXTRA_LDFLAGS="-L$(brew --prefix libgc)/lib"

    elif [ "$OS" = "linux" ]; then
        # Linux Logic
        if [[ "$DISTRO" == "ubuntu" || "$DISTRO" == "debian" || "$DISTRO_LIKE" == *"debian"* ]]; then
            if ! dpkg -l | grep -q libgc-dev; then
                packages="$packages libgc-dev"
                needs_install=true
            fi
            if ! command_exists cc; then packages="$packages build-essential"; fi
            
            if $needs_install; then
                info "Installing dependencies via apt..."
                sudo apt-get update && sudo apt-get install -y $packages
            fi

        elif [[ "$DISTRO" == "fedora" || "$DISTRO" == "rhel" || "$DISTRO" == "centos" || "$DISTRO_LIKE" == *"fedora"* ]]; then
            if ! rpm -q gc-devel >/dev/null 2>&1; then
                packages="$packages gc-devel"
                needs_install=true
            fi
            if ! command_exists cc; then packages="$packages gcc gcc-c++ make"; fi

            if $needs_install; then
                info "Installing dependencies via dnf/yum..."
                if command_exists dnf; then sudo dnf install -y $packages; else sudo yum install -y $packages; fi
            fi

        elif [[ "$DISTRO" == "arch" || "$DISTRO" == "manjaro" ]]; then
            if ! pacman -Q gc >/dev/null 2>&1; then
                packages="$packages gc"
                needs_install=true
            fi
            if ! command_exists cc; then packages="$packages base-devel"; fi

            if $needs_install; then
                info "Installing dependencies via pacman..."
                sudo pacman -S --noconfirm $packages
            fi
        else
            warn "Unknown Linux distribution. Please manually install: Boehm GC (libgc) and a C compiler."
        fi
    fi
}

setup_environment() {
    local dotnet_cmd="dotnet"
    local use_local_dotnet=false
    local project_root="$(pwd)"

    # Check for global .NET SDK
    if command_exists dotnet; then
        info "Global .NET SDK found ($(dotnet --version))."
    else
        info ".NET SDK not found. Installing a local copy..."
        local install_dir="$project_root/.dotnet_internal"
        
        if [ ! -d "$install_dir" ]; then
            if ! command_exists wget; then error "wget is required to download .NET SDK."; fi
            wget -q https://dot.net/v1/dotnet-install.sh -O /tmp/dotnet-install.sh
            chmod +x /tmp/dotnet-install.sh
            /tmp/dotnet-install.sh --channel 9.0 --install-dir "$install_dir" --no-path
            rm /tmp/dotnet-install.sh
        fi
        
        dotnet_cmd="$install_dir/dotnet"
        use_local_dotnet=true
        info "Local .NET SDK installed in .dotnet_internal."
    fi

    # Generate configuration for Makefile
    local cc_path=$(command -v cc)
    
    cat > .compiler_config << EOF
CC=cc
CC_PATH=$cc_path
DOTNET_PATH=$dotnet_cmd
IS_LOCAL_DOTNET=$use_local_dotnet
EXTRA_CFLAGS=$EXTRA_CFLAGS
EXTRA_LDFLAGS=$EXTRA_LDFLAGS
EOF
    
    info "Configuration saved to .compiler_config."
}

main() {
    detect_os
    install_dependencies
    setup_environment
    
    echo ""
    echo -e "${GREEN}Setup complete.${NC}"
    echo "Run 'make' to build and 'sudo make install' to install."
}

main "$@"
