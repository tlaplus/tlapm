Overview
--------
This file contains basic installation instructions as well as development knowledge & practices for this project.
You will learn the repository structure, how to build & test the software it contains from your command line interface (CLI), how to set up your interactive development environment (IDE), and several other tidbits.
This project is mostly written in [OCaml](https://ocaml.org/) with some [Isabelle](https://isabelle.in.tum.de/) code.
It uses the [Dune](https://dune.build/) build system for OCaml, with [Make](https://www.gnu.org/software/make/) used to compile the backend theorem provers.

Release Channels
----------------
Past versioned releases can be downloaded from the [GitHub Releases page](https://github.com/tlaplus/tlapm/releases).
For the latest development version, download the builds attached to the [1.6.0 rolling pre-release](https://github.com/tlaplus/tlapm/releases/tag/1.6.0-pre) or follow the instructions below to build TLAPS from source.

Dependencies
------------
TLAPS development & use is only supported on Unix-like systems, such as:
* Any modern Linux
* macOS
* Windows Subsystem for Linux

For building TLAPS, some Linux distros require additional packages beyond the base install; on Debian/Ubuntu:
```sh
apt install zlib1g-dev gawk time
```
On Arch Linux:
```sh
pacman -Sy wget time zlib patch diffutils fontconfig gnu-free-fonts
```
Install the following dependencies to your path:
* [OCaml](https://ocaml.org/install) 4.08.1 or later (usually installed using [opam](https://opam.ocaml.org/))
* [Dune](https://dune.build/install)
* [Make](https://www.gnu.org/software/make/)

OCaml requires that you initialize an environment within your shell.
For example, you can create & initialize an OCaml 5.1.0 environment with:
```sh
opam switch create 5.1.0
eval $(opam env --switch=5.1.0)
```
You can put the `eval` statement in your shell init file (`~/.bashrc` or similar) to ensure your shell always has an active OCaml environment.

Build & Install TLAPS
---------------------
Clone this repo & open a shell in its root.
Install OCaml package dependencies with:
```sh
make opam-update
make opam-deps
make opam-deps-opt
```
Package dependencies are unfortunately not yet declarative, but [will be in the future](https://github.com/tlaplus/tlapm/issues/158#issuecomment-2455455589).

Compile the embedded dependencies and TLAPS with:
```sh
make
```
Install TLAPS to your local OCaml environment with:
```sh
make install
```
This should put `tlapm` on your path from your local OCaml environment, but if not you can run:
```sh
opam exec -- tlapm --help
```
Compile a TLAPS release distributable with:
```sh
make release
```
This will output a file to `_build/tlaps-$GIT_COMMMIT_HASH-$ARCH-$OS.tar.gz`; for example, running `make release` on Linux produced the file `_build/tlaps-a7a3a0a-x86_64-linux-gnu.tar.gz`.
This file can be used the same as any downloaded TLAPS release.

Test TLAPS
----------
You can run all tests with:
```sh
make test
```
You can run specific tests or groups of tests with (for example):
```sh
dune runtest test/parser --force --always-show-command-line
```

IDE Setup
---------
You are free to use your own editor, but most people develop this project using VS Code with the [OCaml Platform](https://github.com/ocamllabs/vscode-ocaml-platform) extension.

If you are new to OCaml coming from other programming languages, you might expect the debugger to be an important tool.
This is not so!
The OCaml debugger is not often used, and [you will encounter many problems](https://github.com/tlaplus/tlapm/discussions/143#discussioncomment-10277989) when trying to use it.
Instead (as befits a functional language), people use a REPL when analyzing parts of the codebase.
The [UTop](https://opam.ocaml.org/blog/about-utop/) REPL (aka toplevel) works well; you can enter a UTop instance with TLAPM libraries available by running:
```sh
dune utop
```

Repository Layout
-----------------
Here is a diagram of the repository layout.
There are other files and directories beyond these, but these are the most important:
```
/
├── LICENSE                     # The project license
├── README.md                   # Basic info about the project
├── DEVELOPING.md               # This document
├── CONTRIBUTING.md             # How to contribute to the project
├── hints.txt                   # Some tips on effectively writing TLAPS proofs
├── todo.txt                    # Feature wishlist
├── dune-project                # Top-level Dune project file (generates tlapm.opam)
├── Makefile                    # Makefile for installing dependencies & launching Dune builds
├── index.html                  # proofs.tlapl.us root page; currently redirects to docs
├── deps/                       # Makefiles for dependencies (LS4, Isabelle, Z3, etc.)
├── doc/                        # Sources for TLAPS documentation on proofs.tlapl.us
├── examples/                   # Some example proofs that can be used as tests
├── isabelle/                   # Embedding of non-temporal parts of TLA⁺ in Isabelle
├── library/                    # The TLAPS standard modules for TLA⁺
├── translate/                  # External library for translating temporal logic formulas to LS4
├── zenon/                      # The vendored source code of the Zenon theorem prover
├── misc/
│   └── tla_mode/               # A TLAPS mode for Emacs
├── lsp/                        # A language server for checking TLA⁺ proofs with TLAPS
├── src/                        # Main TLAPM source code directory
│   ├── dune                    # Dune build file
│   ├── tlapm.ml                # The main entrypoint to the TLAPM CLI
│   └── tlapm_lib.mli           # Main interface for TLAPM when used as a library
├── test/                       # Tests for TLAPS
└── .github/
    ├── CODE_OF_CONDUCT.md      # The code of conduct
    └── workflows/              # GitHub CI workflow definition files
        ├── ci.yml              # The CI workflow that validates PRs
        └── release.yml         # CI workflow to publish a release
```

Using Git
---------

Git was designed to shine in a federated open source development model.
You are likely to require use of more of its features here than you would in a corporate development environment.
Here is a brief primer on using git to develop this project.
It assumes a basic familiarity with common git operations like clone, commit, push, and pull.
There are countless free and paid git guides available online; [here](https://www.git-scm.com/doc) are the docs from the git project itself, and [here](https://wizardzines.com/git-cheat-sheet.pdf) is a useful cheat-sheet from Julia Evans.

### PR Conventions

Reshape your PR commits to publishable shape: unless you want all your commits to be squashed into a single commit when the PR is merged, craft each commit with care into a logical series of changes with descriptive messages.
Modify each commit in place in response to PR feedback.

Unfortunately GitHub does not really support patch series, so if you have multiple PRs that stack on top of each other the only real way to handle it is to wait until each one is accepted before opening the next, or put them into a single PR where each PR is mapped to a single commit with a descriptive message.

### Developer Certificate of Origin (DCO) sign-off

Due to legal disputes in the mid-2000s, all commits to projects under the Linux Foundation are required to contain a [Developer Certificate of Origin (DCO)](https://en.wikipedia.org/wiki/Developer_Certificate_of_Origin) sign-off (note this is different from signing commits with a GPG key).
This basically says that you (the developer) were entirely responsible for writing the code in the commit and that you are legally permitted to contribute it under a permissive license (it isn't copied from proprietary code, for example).
In git this is easily done by adding an extra `-s` flag as you commit:
```bash
git commit -s -am "Commit message here"
```
Don't worry too much about forgetting this; the CI will catch it and GitHub provides a page with simple instructions to retroactively add DCO sign-off to past commits.
Eventually adding the `-s` flag will become muscle memory.

