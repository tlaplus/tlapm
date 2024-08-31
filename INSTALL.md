<!-- cSpell:words tlapm caml ocaml opam zenon sandboxing -->
# Installing the TLA+ Proof Manager (tlapm)

Copyright (C) 2008-2010  INRIA and Microsoft Corporation

## 0. Dependencies

  - A UNIX-like system. The following are known to work:

     * Any modern UNIX
     * WSL under Windows
     * OS X

  - Objective Caml (OCaml) version 4.08.1 or later.

    Typically installed using `opam` (<https://opam.ocaml.org/>).

  - The Dune build system.

  - Zenon.

    Built during the TLAPM build procedure.

  - Isabelle/TLA+.

    Downloaded and built during the TLAPM build procedure.

## 1. Installation

### 1.1. Setup the environment

Setup required OS packages; Debian/Ubuntu:
```{bash}
sudo apt install opam zlib1g-dev gawk time
```
Arch Linux:
```{bash}
sudo pacman -Sy time git make gcc patch diffutils ocaml opam dune zlib wget fontconfig gnu-free-fonts
```

macOS:
```{bash}
# No additional packages needed.
```

Initialize the OPAM. Add `--disable-sandboxing` option if running this on the docker or sandboxing is not supported for other reasons.

```{bash}
opam init
```

Install the desired OCAML version. The second command is required to setup the ocaml for the current shell session.

```{bash}
opam switch create 5.1.0
eval $(opam env --switch=5.1.0)
```

### 1.2. Build and install TLAPM

Clone the TLAPM source code

```{bash}
git clone https://github.com/tlaplus/tlapm
cd tlapm
```

Install the dependencies via OPAM. A helper `make` target is present for that:

```{bash}
make opam-update
make opam-deps
```

Compile the embedded dependencies and TLAPM:

```{bash}
make
```

Install it under the `~/.opam/` folder:

```{bash}
make install
```

Now you can invoke `tlapm` in either way:

  - `opam exec -- tlapm --help` (locates it using the current selected opam switch);
  - `~/.opam/5.1.0/bin/tlapm --help`.


### 1.3. Running the tests
To run the test suite, invoke:
```{bash}
make test
```

### 1.4. Development environment

To setup the development environment, run the following in addition to the above steps:

```{bash}
make opam-deps-dev
```

Then view/edit the code e.g. using VSCode with the `OCaml Platform` extension installed.


## Appendix: Testing the build/install procedures

The above instructions were tested for Debian as follows:

```{bash}
docker run -it --rm debian bash
apt install sudo
adduser u1
usermod -aG sudo u1
su - u1
# Then run the commands above.
```
