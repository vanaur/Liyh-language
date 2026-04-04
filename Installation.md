# Installation

Follow these instructions carefully if you wish to install Liyh.

> [!NOTE]
> The project is written in F# and requires .NET and a C compiler (for the build _and_ the runtime). The installation script handles dependencies automatically.
> 
> If .NET is missing, it installs a local, isolated version just for this project. Don't worry, this local version won't touch your global configuration and can be completely removed from your system with `make distclean`.

## Linux and MacOS

 1. Go to the root of the project (`Liyh-language`).
 2. Open a terminal, and type `chmod +x ./install.sh` to make the installation script executable.
 3. Execute the installer with `./install.sh`. If asked, enter your password and validate the dependencies.
 4. If everything went well, type `make` and install globally with `sudo make install`.
 5. You can uninstall at any time with `sudo make uninstall`.

You can clean up build files with `make clean` and `make distclean`.

If everything went well, then you should be able to use `liyh` in a terminal!

## Windows

Windows is not yet supported. 😕
