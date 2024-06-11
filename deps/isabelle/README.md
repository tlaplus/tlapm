## Debugging Isabelle prover

Run the `tlapm` with the `--debug=tempfiles` option, e.g.:

    (cd ../tlaplus-examples/specifications/MisraReachability/ \
        && rm -rf .tlacache/ && tlapm --toolbox 228 228 --debug=tempfiles ReachabilityProofs.tla)

Then look for the corresponding `*.thy` files and open them with Isabelle, e.g.

    ./_build/default/deps/isabelle/Isabelle/bin/isabelle jedit \
        -d ./_build/default/deps/isabelle/Isabelle/src/TLA+/ \
        ../tlaplus-examples/specifications/MisraReachability/.tlacache/ReachabilityProofs.tlaps/tlapm_624cb2.thy

