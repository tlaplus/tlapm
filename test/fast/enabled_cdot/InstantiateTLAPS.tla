--------------------------- MODULE InstantiateTLAPS ----------------------------
(* Tests that no warnings or other issues arise when writing `INSTANCE TLAPS`.

The motivation is that earlier versions of the TLA+ module `TLAPS` contained
theorems that applied `ENABLED` to `ACTION` operators. If the current version
of `tlapm` encounters `INSTANCE TLAPS` when using those older versions of the
module `TLAPS`, then `tlapm` raises warnings.

The warnings are raised to inform that certain theorems from the module being
instantiated (in this case the module `TLAPS`) will be absent in the
instantiated module, and so proofs that invoke them will not work.

This warning is not raised when instantiating versions of the module `TLAPS`
contained in this repository after support for `ENABLED` was added to `tlapm`.

When this warning is raised due to instantiating modules other than `TLAPS`,
then one possibility would be to change those modules, to not instantiate
theorems that contain `ENABLED` applied to `ACTION` operators
(reasoning about instantiations of such theorems is currently unsupported by
`tlapm`).

(`tlapm` will raise such warnings even when no proof directive related to
`ENABLED` is used in user modules, because the `INSTANCE` statement will lead
`tlapm` to attempt instantiating all the theorems in the module that is being
instantiated.)

There was a change to the module `TLAPS`, earlier than support for reasoning
about `ENABLED`, that commented certain theorems that contained `ENABLED` and
operator declarations (with the intention of using `BY PTL` instead).
After that change, `tlapm` will not raise warnings about `ENABLED` when
instantiating the module `TLAPS`.
*)
INSTANCE TLAPS

THEOREM
    ASSUME VARIABLE x
    PROVE ([]x) => <>x
BY PTL


--------------------------------------------------------------------------------
M == INSTANCE TLAPS


THEOREM
    ASSUME VARIABLE x
    PROVE ([]x) => <>x
BY M!PTL
================================================================================
