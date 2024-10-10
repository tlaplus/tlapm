---- MODULE nonexistent_test ----
(* Run `tlapm` with a filename that does not
end with `.tla`, to ensure that proof obligations
are indeed generated.

The TLA+ module's filename in the `command`
below intentionally has no extension `.tla`,
in order to test the behavior of `tlapm` when
it automatically appends the extension `.tla`
to the filename (filepath).
*)
THEOREM FALSE
OBVIOUS
=================================
command: ${TLAPM} --toolbox 0,0 nonexistent_test
stderr: obligation failed.

