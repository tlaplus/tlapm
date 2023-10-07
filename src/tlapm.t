Test the --stdin option
  $ cat <<EOF | (tlapm --toolbox 0 0 --stdin A.tla 2>&1 | grep -e '^@!!' | grep -v 'time-used')
  > ---- MODULE A ----
  > THEOREM
  >   ASSUME
  >      NEW A,
  >      NEW B,
  >      A,
  >      A => B
  >   PROVE B
  >   OBVIOUS
  > ====
  > EOF
  @!!BEGIN
  @!!type:obligation
  @!!id:1
  @!!loc:9:3:9:10
  @!!status:to be proved
  @!!END
  @!!BEGIN
  @!!type:obligationsnumber
  @!!count:1
  @!!END
  @!!BEGIN
  @!!type:obligation
  @!!id:1
  @!!loc:9:3:9:10
  @!!status:proved
  @!!prover:smt
  @!!already:false
  @!!END
