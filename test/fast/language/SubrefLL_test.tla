(* Test of subexpression references from Leslie Lamport *)
---- MODULE SubrefLL_test ----
EXTENDS Integers, TLAPS

CONSTANT C
ASSUME c4 == C = 4
USE c4

Salt(s) == s = s
USE DEF Salt

Op(Arg(_), p) ==
   \A x \in {1,2}, y, z \in {<<3, 4>>} :
                      lab(x,y,z) ::  LET a ++ b ==
                                          Arg(a) + b + x + 2*y + 3*z
                                     IN  (Arg(1) + Arg(p) + C +
                                            2*x  + 4*y + 6*z) =
                                         1 ++ ( label2 :: p ++ C)

Foo(u) == 2*u

ASSUME Foo(5) = Foo(5)!:

THEOREM Thm == ASSUME FALSE
               PROVE  lab:: C > 0

THEOREM Thm2 == lab3 :: TRUE

THEOREM Foo(25) = 50
BY SMT DEF Foo

THEOREM Op(Foo, 9)!lab(1,2,3)!label2 = Op(Foo, 9)!lab(1,2,3)!:!++(9, 4)
        /\ Salt("5e4b7")
OBVIOUS

Op3(A(_,_,_), a1, a2, a3) == A(a1, a2, a3)

Op1(a) == \A x \in {} : lab(x) :: IF TRUE
                             THEN LET Op1a(c) == 4 * c + a*x
                                  IN  a + Op1a(x)
                             ELSE 1

SOp1(a) == a
OOp1(A(_), a) == A(a)
THEOREM OOp1(SOp1, 2) = 2 /\ Salt("f30a2")
BY DEF SOp1, OOp1

OOp4(A(_,_,_,_), a, b, c, d) == A(a, b, c, d)

THEOREM Op1(2)!(3)!2!1 = 2 + 4*3 + 6
BY SMT

THEOREM Op1(2)!(3)!2!Op1a(4) = 16 + 6
BY SMT

COp(q, p) ==
   CHOOSE x : lab(x) ::  LET a ++ b ==  {a, b, q, p, x}
                         IN  <<q, 99 ++ p >>

THEOREM COp(1, 2)!(3)!++(4, 5) = {2,1, 3, 4, 5} /\ Salt("9b120")
OBVIOUS

THEOREM COp(1, 2)!(3) = <<1, {99, 1, 2, 3} >> /\ Salt("3e57a")
OBVIOUS

THEOREM COp(1, 2)!(3)!1 = <<1, {99, 1, 2, 3} >> /\ Salt("e83f2")
OBVIOUS

THEOREM COp(1, 2)!(3)!1!>> = {99, 1, 2, 3} /\ Salt("f6df2")
OBVIOUS


THEOREM COp(1, 2)!lab(3)!:!++(4, 5) = {2,1, 3, 4, 5} /\ Salt("5d1d5")
OBVIOUS

COp2(q, p) ==
   CHOOSE x : lab(x) ::  LET a ++ b ==  {lab(y):: y + a + b : y \in {1}}
                         IN  <<q, 99 ++ p >>

THEOREM COp2(1,2)!lab(3)!:!++(9,10)!lab(11) = 30
BY SMT

THEOREM COp2(1,2)!(3)!++(9,10)!lab(11) = 30
BY SMT

THEOREM COp2(1,2)!lab(3)!:!++(9,10)!(11) = 30
BY SMT

Def1 == {1, 2, 3, 4}
THEOREM Def1!2 = 2 /\ Salt("1999b")
OBVIOUS

Def2 == {x \in {1, 2, 3} : x > 17}
THEOREM Def2!1 = {1, 2, 3} /\ Salt("427cf")
OBVIOUS

THEOREM Def2!(14)!<< = 14 /\ Salt("441e8")
OBVIOUS


Def3 == {<<x, y>> : x \in {1}, y \in {2}}
THEOREM Def3!2!1 = 2 /\ Salt("1b17c")
OBVIOUS

THEOREM Def3!(1, 2)!<< = 1 /\ Salt("d266a")
OBVIOUS

Def4 == SUBSET UNION {{1}, {2}}
THEOREM Def4!<<!<<!2 = {2} /\ Salt("09b61")
OBVIOUS

Def5 == [i \in 1..10 |-> i+1][3]
THEOREM Def5!>> = 3 /\ Salt("424b4")
OBVIOUS

THEOREM Def5!<<[4] = [i \in 1 .. 10 |-> i + 1][4] /\ Salt("564c2")
OBVIOUS

THEOREM Def5!<<!1!>> = 10 /\ Salt("db493")
OBVIOUS

Def6 == [[i \in 1..10 |-> i+1] EXCEPT ![2] = 1, ![3] = 2]
THEOREM Def6!1[3] = [i \in 1..10 |-> i+1][3] /\ Salt("254bd")
OBVIOUS

Def7 == 3.a
THEOREM Def7!1 = 3 /\ Salt("a1f95")
OBVIOUS

THEOREM Def7!2 = "a" /\ Salt("00d13")
OBVIOUS


Def8 == [a |-> 1, b |-> 2]
THEOREM Def8!2 = 2 /\ Salt("1caa0")
OBVIOUS


Def9 == [a : 1, b : 2]
THEOREM Def9!2 = 2 /\ Salt("a0120")
OBVIOUS


Def10 == <<1, 2, 3>>
THEOREM Def10!2 = 2 /\ Salt("2f44a")
OBVIOUS


Def11 == {1} \X {2} \X {3}
THEOREM Def11!3!1 = 3 /\ Salt("5cb2b")
OBVIOUS


Def12 == IF 2=3 THEN 2 ELSE 3
THEOREM /\ Def12!1!<< = 2
        /\ Def12!2 = 2
        /\ Def12!3 = 3 /\ Salt("1fc6d")
OBVIOUS


Def13 == \A x : CASE x=1 -> 1
                  [] x=2 -> 2
                  [] OTHER -> 3
THEOREM /\ Def13!(42)!1!<<!<< = 42
        /\ Def13!(42)!1!>> = 1
        /\ Def13!(42)!2!>> = 2
        /\ Def13!(42)!3!>> = 3 /\ Salt("ed4e7")
OBVIOUS


Def14 == \A x \in {1} : x = 1
THEOREM /\ Def14!(2)!<< = 2
        /\ Def14!1!1 = 1 /\ Salt("a7601")
OBVIOUS


Def15 == \A x \in {1}, y \in {2} : (x = 1) /\ (y = 2)
THEOREM /\ Def15!(2,3)!<<!<< = 2
        /\ Def15!(2,3)!>>!<< = 3
        /\ Def15!2!<< = 2 /\ Salt("ed1ec")
OBVIOUS


Def16 == \E x \in {1}, y, z \in {<<2,3>>} :     /\ ((x = 1))
                                                /\ y = 2
                                                /\ (z=3)
THEOREM /\ Def16!(2,3,4)!1!1 = 2
        /\ Def16!(2,3,4)!2!1 = 3
        /\ Def16!2!1!<< = 2 /\ Salt("ee67b")
OBVIOUS


Def17 == \E x , y, z : /\ ((x = 1))
                       /\ y = 2
                       /\ (z=3)
THEOREM /\ Def17!(2,3,4)!1!1 = 2
        /\ Def17!(2,3,4)!2!1 = 3 /\ Salt("25402")
OBVIOUS

Def18 == CHOOSE x : (x=1)
THEOREM Def18!(2)!<< = 2 /\ Salt("45e32")
OBVIOUS


Def19 == CHOOSE x \in {42}: (x=1)
THEOREM /\ Def19!(2)!<< = 2
        /\ Def19!1!1 = 42 /\ Salt("aa8ec")
OBVIOUS


Def20 == [12]_(23)
THEOREM /\ Def20!1 = 12
        /\ Def20!>> = 23 /\ Salt("2c4e2")
OBVIOUS


Def21 == <<12>>_(23)
THEOREM /\ Def21!1 = 12
        /\ Def21!>> = 23 /\ Salt("9a716")
OBVIOUS

Def22 == WF_(12)(23)
THEOREM /\ Def22!1 = 12
        /\ Def22!>> = 23 /\ Salt("42319")
OBVIOUS

Def23 == \EE x , y, z : /\ ((x = 1))
                        /\ y = 2
                        /\ (z=3)
THEOREM /\ Def23!(2,3,4)!1!1 = 2
        /\ Def23!(2,3,4)!2!1 = 3 /\ Salt("92077")
OBVIOUS

=============================================================================
