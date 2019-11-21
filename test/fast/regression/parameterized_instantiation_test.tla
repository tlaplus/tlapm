----------- MODULE parameterized_instantiation_test -----------------
EXTENDS Integers, FiniteSets

VARIABLE x, z
F(y) == INSTANCE parameterized_instantiation_aux

THEOREM (x = z) => (F(x)!Foo = F(z)!Foo)
BY DEF F!Foo
==========================================
