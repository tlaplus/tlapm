------------------------ MODULE prime_commuter_test ------------------------

\* Valid prime and modal identities. Each one must be proved.
\* H is defined at the top level, so the lambda theorems still contain a
\* LAMBDA when the action frontend distributes the prime. A LET would be
\* inlined first.

EXTENDS Naturals, TLAPS

VARIABLES x, y
CONSTANT c

H(F(_)) == F(x)

\* Constant-level, so a prime pushed into an application is not attached
\* to G or N. Their definitions are not expanded. N is the one-argument
\* operator used for nested LAMBDAs; H above is expanded by DEF H.
G(F(_,_)) == F(0, 1)
N(F(_)) == F(0)

\* Prime all occurrences in a compound tuple.
THEOREM (<<x, y, x>>)' = <<x', y', x'>>
BY Isa

\* Prime both sides of equality.
THEOREM (x = y)' <=> (x' = y')
BY Isa

\* Constant symbols stay unchanged when primes commute.
THEOREM (c * (x + 1))' = c * (x' + 1)
BY Isa

\* Prime free state variables but not the quantified binder z.
THEOREM (\A z \in {x} : z = y)'
        <=> (\A z \in {x'} : z = y')
BY Isa

\* Prime outside an application of a lambda-valued argument.
\* After substitution, this is (<<x, y>>)' = <<x', y'>>.
THEOREM H(LAMBDA a : <<a, y>>)' = <<x', y'>>
BY Isa DEF H

\* Prime inside the lambda body on a compound tuple.
\* The bound a is instantiated with x, so its explicit prime must survive.
THEOREM H(LAMBDA a : <<a, y>>') = <<x', y'>>
BY Isa DEF H

\* Two-parameter and nested LAMBDAs. G and N stay unexpanded, so the
\* action frontend distributes the prime while the binders are present.
\* A parameter bound while the prime is pushed under its LAMBDA stays
\* unprimed. A parameter already in scope keeps the prime.

\* The prime is inside the body, so both parameters are already in scope.
THEOREM G(LAMBDA a, b : <<a, b>>')
      = G(LAMBDA a, b : <<a', b'>>)
BY Isa

\* The prime is on the innermost expression, so both parameters are in scope.
THEOREM N(LAMBDA a : N(LAMBDA b : <<a, b>>'))
      = N(LAMBDA a : N(LAMBDA b : <<a', b'>>))
BY Isa

\* In (c + x)', the constant c is left unchanged and x is primed.
THEOREM (c + x)' = c + x'
BY Isa

\* ENABLED is not entered.
THEOREM (ENABLED (x = x))' = (ENABLED (x = x))'
BY Isa

\* A LET is not entered.
THEOREM LET E(e) == e' IN E(x) = E(x)
BY Isa

=============================================================================
