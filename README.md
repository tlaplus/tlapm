The TLA⁺ Proof Manager (`tlapm`)
================================
[![Build & Test](https://github.com/tlaplus/tlapm/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/tlaplus/tlapm/actions/workflows/ci.yml)

This repository hosts the TLA⁺ Proof Manager TLAPM, formerly known as TLAPS.
TLAPM translates TLA⁺ proof constructs into forms understood by an array of backend solvers & theorem provers, enabling machine-checked proofs of correctness for TLA⁺ specifications.
TLAPM's development is managed by the [TLA⁺ Foundation](https://foundation.tlapl.us/).
For documentation, see http://proofs.tlapl.us.
For information on TLA⁺ generally, see http://tlapl.us.

Installation & Use
------------------
Versioned releases can be downloaded from the [GitHub Releases page](https://github.com/tlaplus/tlapm/releases).
If you instead prefer to use the latest development version, follow the instructions in [`DEVELOPING.md`](DEVELOPING.md) to build & install TLAPM.

Once TLAPM is installed, run `tlapm --help` to see documentation of the various command-line parameters.
Check the proofs in a simple example spec in this repo by running:
```sh
tlapm examples/Euclid.tla
```
Documentation is hosted at http://proofs.tlapl.us, or can be viewed locally from this repository starting at [`doc/web/index.html`](doc/web/index.html).

Developing & Contributing
-------------------------
For instructions on building & testing TLAPM as well as setting up a development environment, see [DEVELOPING.md](DEVELOPING.md).

We welcome your contributions to this open source project!
TLAPM is used in safety-critical systems, so we have a contribution process in place to ensure quality is maintained; read [CONTRIBUTING.md](CONTRIBUTING.md) before beginning work.

Authors
-------
The following people were instrumental in creating TLAPM:
- [Kaustuv Chaudhuri](https://chaudhuri.info/) (@[chaudhuri](https://github.com/chaudhuri))
- Denis Cousineau
- [Damien Doligez](http://cambium.inria.fr/~doligez/) (@[damiendoligez](https://github.com/damiendoligez))
- [Leslie Lamport](https://lamport.azurewebsites.net/) (@[xxyzzn](https://github.com/xxyzzn))
- [Tomer Libal](https://tomer.libal.info/) (@[shaolintl](https://github.com/shaolintl))
- [Stephan Merz](https://members.loria.fr/Stephan.Merz/) (@[muenchnerkindl](https://github.com/muenchnerkindl))
- [Jean-Baptiste Tristan](https://jtristan.github.io/) (@[jtristan](https://github.com/jtristan))
- [Hernán Vanzetto](https://www.cs.yale.edu/homes/vanzetto/) (@[hvanz](https://github.com/hvanz))

License & Copyright
-------------------
Copyright © 2008 INRIA & Microsoft Corporation  
Copyright © 2023 Linux Foundation

Licenses:
- Main codebase licensed under [2-Clause BSD](LICENSE)
- Contents of [`translate`](translate) directory licensed under LGPL2.1+LE

