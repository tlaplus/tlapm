The TLA⁺ Proof System
=====================
[![Build & Test](https://github.com/tlaplus/tlapm/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/tlaplus/tlapm/actions/workflows/ci.yml)

This repository hosts what is collectively called the TLA⁺ Proof System, or TLAPS.
It consists of the TLA⁺ Proof Manager `tlapm` that interprets TLA⁺ proofs & manages their state, as well as interfaces to automatic backend provers such as [SMT](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) solvers like [Z3](https://github.com/Z3Prover/z3), the [tableau](https://en.wikipedia.org/wiki/Method_of_analytic_tableaux) prover [Zenon](https://github.com/zenon-prover/zenon), the [Isabelle](https://isabelle.in.tum.de/)/TLA⁺ object logic, and the LS4 decision procedure for [propositional temporal logic](https://plato.stanford.edu/entries/logic-temporal/).

TLAPS development is managed by the [TLA⁺ Foundation](https://foundation.tlapl.us/).
For documentation, see http://proofs.tlapl.us.
For information on TLA⁺ generally, see http://tlapl.us.

Installation & Use
------------------
Past versioned releases can be downloaded from the [GitHub Releases page](https://github.com/tlaplus/tlapm/releases).
For the latest development version, download the builds attached to the [1.6.0 rolling pre-release](https://github.com/tlaplus/tlapm/releases/tag/1.6.0-pre) or follow the instructions in [`DEVELOPING.md`](DEVELOPING.md) to build TLAPS from source.

Once TLAPS is installed, run `tlapm --help` to see documentation of the various command-line parameters.
Check the proofs in a simple example spec in this repo by running:
```sh
tlapm examples/Euclid.tla
```
Documentation is hosted at http://proofs.tlapl.us, or can be viewed locally from this repository starting at [`doc/web/index.html`](doc/web/index.html).

Developing & Contributing
-------------------------
For instructions on building & testing TLAPS as well as setting up a development environment, see [DEVELOPING.md](DEVELOPING.md).

We welcome your contributions to this open source project!
TLAPS is used in safety-critical systems, so we have a contribution process in place to ensure quality is maintained; read [CONTRIBUTING.md](CONTRIBUTING.md) before beginning work.

Authors
-------
The following people were instrumental in creating TLAPS:
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

