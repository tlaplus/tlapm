-------------------------------- MODULE Sets --------------------------------
EXTENDS Integers, NaturalsInduction, TLAPS
  \** NB: Module NaturalsInduction comes from the TLAPS library, usually
  \** installed in /usr/local/lib/tlaps. Make sure this is in your Toolbox
  \** search path, see Preferences/TLA+ Preferences.

IsBijection(f, S, T) == /\ f \in [S -> T]
                        /\ \A x, y \in S : (x # y) => (f[x] # f[y])
                        /\ \A y \in T : \E x \in S : f[x] = y


IsFiniteSet(S) == \E n \in Nat : \E f : IsBijection(f, 1..n, S)

(****************************************************************************)
(* Finite sets and cardinality are defined in the TLA+ standard module      *)
(* FiniteSets, but this is not yet natively supported by TLAPS. For the     *)
(* time being, we use the following axiom for defining set cardinality.     *)
(****************************************************************************)
\* Cardinality(S) == CHOOSE n : (n \in Nat) /\ \E f : IsBijection(f, 1..n, S)

CONSTANT Cardinality(_)
AXIOM CardinalityAxiom ==
         \A S : IsFiniteSet(S) =>
           \A n : (n = Cardinality(S)) <=>
                    (n \in Nat) /\ \E f : IsBijection(f, 1..n, S)
-----------------------------------------------------------------------------

THEOREM CardinalityInNat == \A S : IsFiniteSet(S) => Cardinality(S) \in Nat
BY CardinalityAxiom 
  
------------------------------------------------------------------

THEOREM CardinalityZero ==
           /\ IsFiniteSet({})
           /\ Cardinality({}) = 0
           /\ \A S : IsFiniteSet(S) /\ (Cardinality(S)=0) => (S = {})
<1>1. /\ IsFiniteSet({})
      /\ Cardinality({}) = 0
  <2>1. IsBijection([x \in 1..0 |-> {}], 1..0, {})
    BY Z3 DEF IsBijection
  <2>2. QED
    BY <2>1, CardinalityAxiom DEF IsFiniteSet
<1>2. ASSUME NEW S,
             IsFiniteSet(S),
             Cardinality(S) = 0
      PROVE  S = {}
  BY <1>2, CardinalityAxiom, SMT DEF IsBijection
<1>3. QED
  BY <1>1, <1>2

THEOREM CardinalityPlusOne ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW x, x \notin S
    PROVE  /\ IsFiniteSet(S \cup {x})
           /\ Cardinality(S \cup {x}) = Cardinality(S) + 1
<1> DEFINE N == Cardinality(S)
<1>1. PICK f : IsBijection(f, 1..N, S)
  BY CardinalityAxiom
<1> DEFINE g == [i \in 1..(N+1) |-> IF i = N+1 THEN x ELSE f[i]]
<1>2. IsBijection(g, 1..(N+1), S \cup {x})
  BY <1>1, CardinalityInNat, Z3 DEF IsBijection
<1>3. QED
  BY <1>2, CardinalityInNat, CardinalityAxiom, SMT DEF IsFiniteSet

------------------------------------------------------------------

THEOREM CardinalityOne == \A m : /\ IsFiniteSet({m})
                                 /\ Cardinality({m}) = 1
BY CardinalityZero, CardinalityPlusOne, IsaM("auto")

THEOREM CardinalityTwo == \A m, p : m # p => 
                              /\ IsFiniteSet({m,p})
                              /\ Cardinality({m,p}) = 2
BY CardinalityOne, CardinalityPlusOne, IsaM("auto")

THEOREM IntervalCardinality ==  
  ASSUME NEW a \in Nat, NEW b \in Nat 
  PROVE  /\ IsFiniteSet(a..b)
         /\ Cardinality(a..b) = IF a > b THEN 0 ELSE b-a+1
<1>1. CASE a > b
  BY <1>1, CardinalityZero, SetExtensionality, SMT
<1>2. CASE a <= b
  <2> DEFINE n == b - a + 1
  <2> DEFINE F == [x \in 1..n |-> x + a - 1]
  <2>1. \A y \in a .. b:  \E x \in 1 .. n : y + 1 - a = x
    (** This equation cannot be proved by SMTs if the variables 
        are in a different order. *)
    BY <1>2, SMT
  <2>2. IsBijection(F, 1..n, a..b)
    BY <2>1, Z3 DEF IsBijection
  <2> QED
    BY <2>2, <1>2, CardinalityAxiom, SMT DEF IsFiniteSet
<1>q. QED
  BY <1>1, <1>2, SMT

------------------------------------------------------------------

THEOREM CardinalityOneConverse ==
   ASSUME NEW S, IsFiniteSet(S), Cardinality(S) = 1
   PROVE  \E m : S = {m}
<1>1. PICK f : IsBijection(f, 1..1, S)
  BY CardinalityAxiom
<1>2. S = {f[1]}
  BY <1>1, SMT DEF IsBijection
<1>q. QED
  BY <1>2

-----------------------------------------------------------------------------

THEOREM IsBijectionInverse ==
  ASSUME NEW f, NEW S, NEW T, 
         IsBijection(f, S, T) 
  PROVE  \E g : IsBijection(g, T, S)
<1> WITNESS [y \in T |-> CHOOSE x \in S : f[x] = y]
<1> QED
  BY DEF IsBijection

THEOREM IsBijectionTransitive ==
  ASSUME NEW f1, NEW f2, NEW S, NEW T, NEW U, 
           IsBijection(f1, S, U),
           IsBijection(f2, U, T) 
  PROVE  \E g : IsBijection(g, S, T)
<1> WITNESS [x \in S |-> f2[f1[x]]]
<1> QED
  BY SMT DEF IsBijection

THEOREM 
    ASSUME NEW n \in Nat, NEW m \in Nat,
           IsBijection([x \in 1..n |-> x], 1..n, 1..m)
    PROVE  n = m

THEOREM IsBijectionCardinality ==
  \A f, S, T : /\ IsFiniteSet(S)
               /\ IsFiniteSet(T)
               => (IsBijection(f, S, T) <=> Cardinality(S) = Cardinality(T))

LEMMA CardinalitySetMinus ==
      ASSUME NEW S, IsFiniteSet(S),
             NEW x \in S
      PROVE /\ IsFiniteSet(S \ {x})
            /\ Cardinality(S \ {x}) = Cardinality(S) - 1
<1> DEFINE N == Cardinality(S)
<1>1. IsFiniteSet(S \ {x})
  <2>g. PICK g : IsBijection(g, 1..N, S)
    BY CardinalityAxiom
  <2>k. PICK k \in 1..N : g[k] = x
    BY <2>g DEF IsBijection
  <2> /\ N \in Nat
      /\ N - 1 \in Nat
    BY CardinalityInNat, CardinalityZero, SMT
  <2> DEFINE f == [i \in 1..N-1 |-> g[IF i < k THEN i ELSE i+1]]
  <2> HIDE DEF f
  <2> SUFFICES IsBijection(f, 1 .. N-1, S  \  {x})
    BY DEF IsFiniteSet
  <2>1. f \in [1..N-1 -> S \ {x}]
    BY <2>g, <2>k, SMT DEF IsBijection, f
  <2>2. ASSUME NEW i \in 1..N-1,
               NEW j \in 1..N-1,
               i # j
        PROVE  f[i] # f[j]
    BY <2>g, <2>2, SMT DEF IsBijection, f
  <2>3. ASSUME NEW y \in S \ {x}
        PROVE  \E i \in 1..N-1 : f[i] = y
    <3>j. PICK j \in 1..N : g[j] = y
      BY <2>g DEF IsBijection
    <3>1. CASE j < k
      BY <3>j, <3>1, Z3 DEF f
    <3>2. CASE ~(j < k)
      <4> /\ ~(j-1 < k)
          /\ (j-1)+1 = j
          /\ j-1 \in 1..N-1
        BY <3>j, <3>2, <2>k, SMT
      <4> QED
        BY <3>j DEF f
    <3>4. QED
      BY <3>1, <3>2
  <2>q. QED
    BY <2>1, <2>2, <2>3 DEF IsBijection
<1>2. Cardinality(S \ {x}) = Cardinality(S) - 1
  PROOF OMITTED
<1>q. QED
  BY <1>1, <1>2

THEOREM FiniteSubset ==
  ASSUME NEW S, NEW TT, IsFiniteSet(TT), S \subseteq TT
  PROVE  /\ IsFiniteSet(S)
         /\ Cardinality(S) \leq Cardinality(TT)
<1>2. PICK N \in Nat : N = Cardinality(TT)
  BY CardinalityAxiom
<1>3.  IsFiniteSet(S)
  <2> DEFINE P(n) == \A T : S \subseteq T /\ IsFiniteSet(T) /\ Cardinality(T) = n
                            => IsFiniteSet(S)
  <2>2. P(0)
    BY CardinalityZero
  <2>3. ASSUME NEW n \in Nat, P(n)
        PROVE  P(n+1)
    <3>1. SUFFICES ASSUME \A R : /\ S \subseteq R
                                 /\ IsFiniteSet(R)
                                 /\ Cardinality(R) = n
                                 => IsFiniteSet(S),
                          NEW T,
                          S \subseteq T,
                          IsFiniteSet(T),
                          Cardinality(T) = n+1,
                          NEW x \in T, x \notin S
                   PROVE  IsFiniteSet(S)
     BY <2>3, SetExtensionality, SMT
   <3>2. IsFiniteSet(T \ {x})
     BY <3>1, CardinalitySetMinus
   <3>q. QED
     BY <3>1, <3>2, CardinalityPlusOne, CardinalityInNat, SMT
  <2>. HIDE DEF P
  <2>4. \A n \in Nat : P(n)
    BY <1>2, <2>2, <2>3, NatInduction
  <2>q. QED
    BY <1>2, <2>4 DEF P
<1>4. Cardinality(S) \leq Cardinality(TT)
  <2> DEFINE P(n) == \A T : /\ S \subseteq T
                            /\ IsFiniteSet(T)
                            /\ IsFiniteSet(S)
                            /\ Cardinality(T) = n
                            => Cardinality(S) <= Cardinality(T)
  <2>1. P(0)
    BY CardinalityZero, SetExtensionality, SMT
  <2>2. ASSUME NEW n \in Nat, P(n)
        PROVE  P(n+1)
    <3> SUFFICES ASSUME \A R :
                           /\ S  \subseteq  R
                           /\ IsFiniteSet(R)
                           /\ IsFiniteSet(S)
                           /\ Cardinality(R)  =  n
                           =>  Cardinality(S)  \leq  Cardinality(R),
                        NEW T,
                        S  \subseteq  T,
                        IsFiniteSet(T),
                        IsFiniteSet(S),
                        Cardinality(T)  =  n + 1,
                        NEW x \in T, x \notin S
                PROVE Cardinality(S)  \leq  Cardinality(T)
      BY <2>2, SetExtensionality, SMT
    <3> /\ IsFiniteSet(T \ {x})
        /\ Cardinality(T \ {x}) = Cardinality(T) - 1
      BY CardinalitySetMinus
    <3> QED
      BY CardinalityPlusOne, CardinalityInNat, Z3
  <2> HIDE DEF P
  <2>3. \A n \in Nat : P(n)
    BY <1>2, <2>1, <2>2, NatInduction
  <2>q. QED
    BY <1>2, <1>3, <2>3, CardinalityInNat DEF P
<1>q. QED
  BY <1>3, <1>4
-------------------------------------------------------

THEOREM CardinalityUnion ==
          \A S, T : IsFiniteSet(S) /\ IsFiniteSet(T) =>
                      /\ IsFiniteSet(S \cup T)
                      /\ IsFiniteSet(S \cap T)
                      /\ Cardinality(S \cup T) =
                              Cardinality(S) + Cardinality(T)
                              - Cardinality(S \cap T)  

-----------------------------------------------------------------------------

THEOREM PigeonHole ==
            \A S, T : /\ IsFiniteSet(S)
                      /\ IsFiniteSet(T)
                      /\ Cardinality(T) < Cardinality(S)
                      => \A f \in [S -> T] :
                           \E x, y \in S : x # y /\ f[x] = f[y]
<1> DEFINE P(n) == \A S : IsFiniteSet(S) /\ (Cardinality(S) = n) =>
                      \A T : /\ IsFiniteSet(T)
                             /\ Cardinality(T) < Cardinality(S)
                             => \A f \in [S -> T] :
                                  \E x, y \in S : x # y /\ f[x] = f[y]

<1>2. SUFFICES \A n \in Nat : P(n)
  BY CardinalityInNat
<1>3. P(0)
  BY CardinalityInNat, SMT
<1>4. ASSUME NEW n \in Nat, P(n)
      PROVE  P(n+1)
  <2> SUFFICES ASSUME NEW S, IsFiniteSet(S), Cardinality(S) = n+1,
                      NEW T, IsFiniteSet(T), Cardinality(T) < Cardinality(S),
                      NEW f \in [S -> T]
                 PROVE  \E x, y \in S : x # y /\ f[x] = f[y]
    OBVIOUS
  <2>2. PICK z : z \in S
    <3>1. S # {}
      BY CardinalityZero, IsaM("force")
    <3>2. QED
      BY <3>1
  <2>3. CASE \E w \in S : w # z /\ f[w] = f[z]
    BY <2>2, <2>3
  <2>4. CASE \A w  \in S : w # z => f[w] # f[z]
    <3>1. DEFINE g == [w \in (S \ {z}) |-> f[w]]
    <3>2. \E x, y \in S \ {z} : x # y /\ g[x] = g[y]
      <4>1. /\ IsFiniteSet(S \ {z}) 
            /\ Cardinality(S \ {z}) = (n+1) - 1
            /\ IsFiniteSet(T \ {f[z]})
            /\ Cardinality(T \ {f[z]}) = Cardinality(T) - 1
        BY (*<2>1,*) <2>2, CardinalitySetMinus
      <4>2. Cardinality(T \ {f[z]}) < Cardinality(S \ {z})
        BY (*<2>1,*) CardinalityInNat, <4>1, SMT
      <4>3. \A ff \in [S \ {z} -> T \ {f[z]}] :
                 \E x, y \in S \ {z} : x # y /\ ff[x] = ff[y]
        BY <1>4, <4>1, <4>2, IsaM("auto")
      <4>4. g \in [S \ {z} -> T \ {f[z]}]
        BY <2>4
      <4> HIDE DEF g
      <4>5. QED
        BY <4>4, <4>3
    <3>3.  QED
      BY <3>2
  <2>5. QED
    BY <2>3, <2>4
<1> HIDE DEF P
<1>5. QED
  BY <1>3, <1>4, NatInduction
-------------------------------------------------------

THEOREM \A S, T , f :  /\ IsFiniteSet(S)
                       /\ f \in [S -> T]
                       /\ \A y \in T : \E x \in S : y = f[x]
                       => /\ IsFiniteSet(T)
                          /\ Cardinality(T) \leq Cardinality(S)
PROOF OMITTED

THEOREM ProductFinite ==
     \A S, T : IsFiniteSet(S) /\ IsFiniteSet(T) => IsFiniteSet(S \X T)
PROOF OMITTED

THEOREM SubsetsFinite == \A S : IsFiniteSet(S) => IsFiniteSet(SUBSET S)
PROOF OMITTED
=============================================================================
