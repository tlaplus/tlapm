------ MODULE userops_test ------

EXTENDS TLAPS

x + y           == TRUE
x - y           == TRUE
x * y           == TRUE
x / y           == TRUE
x \circ y       == TRUE
x \div y        == TRUE
x % y           == TRUE
x ^ y           == TRUE

x .. y          == TRUE
x ... y         == TRUE

x (+) y         == TRUE
x (-) y         == TRUE
x (\X) y        == TRUE
x (/) y         == TRUE
x (.) y         == TRUE

x < y           == TRUE
x > y           == TRUE
x <= y          == TRUE
x >= y          == TRUE

x \sqcap y      == TRUE
x \sqcup y      == TRUE
x \sqsubset y   == TRUE
x \sqsubseteq y == TRUE
x \sqsupset y   == TRUE
x \sqsupseteq y == TRUE

x \prec y       == TRUE
x \succ y       == TRUE
x \preceq y     == TRUE
x \succeq y     == TRUE

x \ll y         == TRUE
x \gg y         == TRUE
x <: y          == TRUE
x :> y          == TRUE

x ++ y          == TRUE
x -- y          == TRUE
x ** y          == TRUE
x // y          == TRUE
x ^^ y          == TRUE
x && y          == TRUE
x %% y          == TRUE
x @@ y          == TRUE
x ## y          == TRUE
x $$ y          == TRUE
x ?? y          == TRUE
x !! y          == TRUE

x \subset y     == TRUE
x \supset y     == TRUE
x \supseteq y   == TRUE
x \uplus y      == TRUE

x \sim y        == TRUE
x \simeq y      == TRUE
x \asymp y      == TRUE
x \approx y     == TRUE
x \cong y       == TRUE
x \doteq y      == TRUE
x \wr y         == TRUE
x \propto y     == TRUE
x ::= y         == TRUE

x |- y          == TRUE
x -| y          == TRUE
x |= y          == TRUE
x =| y          == TRUE

x \star y       == TRUE
x \bullet y     == TRUE
x \bigcirc y    == TRUE
x & y           == TRUE
x $ y           == TRUE
x | y           == TRUE

x^+             == TRUE
x^*             == TRUE
x^#             == TRUE

THEOREM ASSUME NEW x, NEW y,
               x + y,
               x - y,
               x * y,
               x / y,
               x \circ y,
               x \div y,
               x % y,
               x ^ y,
               x .. y,
               x ... y,
               x (+) y,
               x (-) y,
               x (\X) y,
               x (/) y,
               x (.) y,
               x < y,
               x > y,
               x <= y,
               x >= y,
               x \sqcap y,
               x \sqcup y,
               x \sqsubset y,
               x \sqsubseteq y,
               x \sqsupset y,
               x \sqsupseteq y,
               x \prec y,
               x \succ y,
               x \preceq y,
               x \succeq y,
               x \ll y,
               x \gg y,
               x <: y,
               x :> y,
               x ++ y,
               x -- y,
               x ** y,
               x // y,
               x ^^ y,
               x && y,
               x %% y,
               x @@ y,
               x ## y,
               x $$ y,
               x ?? y,
               x !! y,
               x \subset y,
               x \supset y,
               x \supseteq y,
               x \uplus y,
               x \sim y,
               x \simeq y,
               x \asymp y,
               x \approx y,
               x \cong y,
               x \doteq y,
               x \wr y,
               x \propto y,
               x ::= y,
               x |- y,
               x -| y,
               x |= y,
               x =| y,
               x \star y,
               x \bullet y,
               x \bigcirc y,
               x & y,
               x $ y,
               x | y,
               x^+,
               x^*,
               x^#
        PROVE TRUE
    OBVIOUS

====

