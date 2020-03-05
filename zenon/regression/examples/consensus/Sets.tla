-------------------------------- MODULE Sets --------------------------------
EXTENDS Integers

\* CONSTANTS S, T
\* THEOREM \A x \in S : (\E y \in T : x = y)  => (S \cap T # {})
\*  <1>1. SUFFICES ASSUME NEW x \in S,
\*                        \E y \in T : x = y
\*                 PROVE  (S \cap T # {})
\*     OBVIOUS
\*  <1>2. QED


THEOREM SetDiff ==  \A S, T, x : x \in S \ T => x \in S /\ x \notin T
OBVIOUS

THEOREM SetEquality == TRUE (*{ by (isabelle "(auto intro: setEqualI)") }*)
OBVIOUS

THEOREM S4 == ASSUME NEW S, NEW T
              PROVE (S = T) <=> (S \subseteq T) /\ (T \subseteq S)
BY SetEquality

THEOREM ASSUME NEW S, NEW T
        PROVE (S = T) <=> (\A x \in S : x \in T) /\ (\A x \in T : x \in S)
BY SetEquality

THEOREM ASSUME NEW S, NEW T
        PROVE  (S \ T) \cup (T \ S) = (S \cup T) \ (S \cap T)
<1>1. SUFFICES ASSUME NEW x
               PROVE  \/ x \in S /\ x \notin T
                      \/ x \in T /\ x \notin S
                     <=>
                      /\ x \in S \/ x \in T
                      /\ ~ (x \in S /\ x \in T)
    OBVIOUS
<1>2. QED
  BY <1>1

THEOREM ASSUME NEW S, NEW T
        PROVE  (S \ T) \cup (T \ S) \subseteq (S \cup T) \ (S \cap T)
<1>1. SUFFICES ASSUME NEW x
               PROVE  \/ x \in S /\ x \notin T
                      \/ x \in T /\ x \notin S
                     =>
                      /\ x \in S \/ x \in T
                      /\ ~ (x \in S /\ x \in T)
  BY SetEquality
<1>2. QED
  BY <1>1

ASSUME Arithmetic == TRUE
   (*{by (cooper) }*)

ASSUME DotDotDef == \A a, b : a..b = {x \in Int : a \leq x /\ x \leq b}

ASSUME Induction == \A f : /\ f[0]
                           /\ \A n \in Nat : f[n] => f[n+1]
                           => \A n \in Nat : f[n]
-----------------------------------------------------------------------------
(***************************************************************************)
(* Some simple tests.                                                      *)
(***************************************************************************)
THEOREM \A S : \A x \in S : S = (S \ {x}) \cup {x}
OBVIOUS

THEOREM \A S, x : (x \notin S) <=> (S = S \ {x})
OBVIOUS

-----------------------------------------------------------------------------
IsBijection(f, S, T) == /\ f \in [S -> T]
                        /\ \A x, y \in S : (x # y) => (f[x] # f[y])
                        /\ \A y \in T : \E x \in S : f[x] = y


IsFiniteSet(S) == \E n \in Nat : \E f : IsBijection(f, 1..n, S)

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
\* THEOREM \A S : IsFiniteSet(S) => Cardinality(S) \in Nat
\* <1>1. SUFFICES ASSUME NEW S,
\*                       IsFiniteSet(S)
\*                PROVE  Cardinality(S) \in Nat
\*   OBVIOUS
\* <1>2. DEFINE F(n) == n \in Nat /\ \E f : IsBijection(f, 1..n, S)
\* <1>2a. HIDE DEF F
\* <1>3. \E n : F(n)
\*   BY DEF IsFiniteSet, F
\* <1>4. Cardinality(S) = CHOOSE n : F(n)
\*   BY DEF Cardinality, F, IsBijection
\* <1>5. F(Cardinality(S))
\*   BY <1>3, <1>4
\* <1>6. QED
\*   BY DEF F

THEOREM IntervalCardinality == \A m, n \in Int :
                                 /\ IsFiniteSet(m..n)
                                 /\ m \leq n+1 => Cardinality(m..n) = n-m+1
PROOF OMITTED


THEOREM CardinalityZero ==
           /\ IsFiniteSet({})
           /\ Cardinality({}) = 0
           /\ \A S : IsFiniteSet(S) /\ (Cardinality(S)=0) => (S = {})
<1>0. 1..0 = {}
  <2>1. \A i \in Int : i \notin 1..0
    BY Arithmetic
  <2>2. QED
    BY <2>1, DotDotDef
<1>1. /\ IsFiniteSet({})
      /\ Cardinality({}) = 0
  <2> DEFINE F == [x \in 1..0 |-> TRUE]
  <2>1. \A x \in 1..0 : F[x] \in {}
    BY <1>0
  <2>2. IsBijection(F, 1..0, {})
    BY <1>0, <2>1 DEF IsBijection
  <2>3. IsFiniteSet({})
    BY <2>2 DEF IsFiniteSet
  <2>4. QED
     <3>1. 0 \in Nat
       BY Arithmetic
     <3>2. QED
        BY <3>1, <2>2, <2>3, CardinalityAxiom
<1>2. ASSUME NEW S,
             IsFiniteSet(S),
             Cardinality(S) = 0
      PROVE  S = {}

  <2>1. PICK F : IsBijection(F, 1..0, S)
     BY <1>2, CardinalityAxiom
  <2>2. \A x \in S : \E y \in {} : F[x] = y
      BY <1>0, <2>1 DEF IsBijection
  <2>3. QED
    BY <2>2
<1>3. QED
  BY <1>1, <1>2

------------------------------------------------------------------

THEOREM CardinalityPlusOne ==
           ASSUME NEW S ,
                  IsFiniteSet(S),
                  NEW x ,
                  x \notin S
           PROVE  /\ IsFiniteSet(S \cup {x})
                  /\ Cardinality(S \cup {x}) = Cardinality(S) + 1
<1> DEFINE N == Cardinality(S)
<1>1. N \in Nat
  BY CardinalityAxiom
<1>2. N+1 \in Nat
  <2>1. \A n \in Nat : n+1 \in Nat
    BY Arithmetic
  <2>2. QED
    BY <2>1, <1>1
<1>3. PICK f : IsBijection(f, 1..N, S)
  BY CardinalityAxiom
<1> DEFINE g == [i \in 1..(N+1) |-> IF i = N+1 THEN x ELSE f[i]]
<1>4. IsBijection(g, 1..(N+1), S \cup {x})
  <2>1. 1..(N+1) = 1..N \cup {N+1}
    <3>1. \A n \in Nat : \A i : (i \in 1..(n+1)) <=> (i \in 1..n \/ i = n + 1)
      BY Arithmetic
    <3>2. QED
      BY <3>1, <1>1
  <2>2. g \in [1..(N+1) -> S \cup {x}]
    <3>1. \A i \in 1..(N+1) : g[i] \in S \cup {x}
      <4>1. \A n \in Nat : \A i \in 1..(n+1) : i # n+1 => i \in 1..n
        BY Arithmetic
      <4>2. \A i \in 1..(N+1) : i # N+1 => g[i] \in S
        BY <1>1, <1>3, <4>1 DEF IsBijection
      <4>3. g[N+1] = x
        <5>1. \A n \in Nat : n+1 \in 1..(n+1)
          BY Arithmetic
        <5>2. QED
          BY <1>1, <5>1
      <4>4. QED
        BY <4>2, <4>3
    <3>2. QED
      BY <3>1
  <2>3. \A a, b \in 1..(N+1) : (a # b) => (g[a] # g[b])
    <3>1. SUFFICES ASSUME NEW a \in 1..(N+1),
                          NEW b \in 1..(N+1),
                          a # b
                   PROVE  g[a] # g[b]
      BY <3>1
    <3>2. CASE a # N+1
      <5>1. g[a] = f[a]
        BY <2>1, <3>2
      <5>2. CASE b # N+1
        <6>1. g[b] = f[b]
          BY <2>1, <5>2
        <6>2. a \in 1..N /\ b \in 1..N
          BY <2>1, <3>2, <5>2
        <6>3. f[a] # f[b]
          BY <6>2, a # b, <1>3 DEF IsBijection
        <6>4. QED
          BY <5>1, <6>1, <6>3
      <5>3. CASE b = N+1
        <6>1. g[b] = x
          BY <2>1, <5>3
        <6>2. f[a] \in S
          BY <2>1, <1>3, <3>2 DEF IsBijection
        <6>3. QED
          BY <5>1, <6>1, <6>2
      <5>4. QED
        BY <5>3, <5>2
    <3>3. CASE a = N+1
      <4>1. g[a] = x
        BY <2>1, <3>3
      <4>2. g[b] \in S
        BY <2>1, <3>1, <3>3, <1>3 DEF IsBijection
      <4>3. QED
        BY <4>1, <4>2
    <3>4. QED
      BY <3>3, <3>2
  <2>4. \A b \in S \cup {x} : \E a \in 1..(N+1) : g[a] = b
    <3>1. TAKE b \in S \cup {x}
    <3>2. CASE b \in S
      <4>1. PICK a \in 1..N : f[a] = b
        BY <1>3, <3>2 DEF IsBijection
      <4>2. a # N+1
        <5>1. \A n \in Nat : n+1 \notin 1..n
          BY Arithmetic
        <5>2. N+1 \notin 1..N
          BY <1>1, <5>1
        <5>3. QED
          BY <4>1, <5>2
      <4>3. g[a] = f[a]
         BY <4>1, <4>2, <2>1
      <4>4. a \in 1..(N+1)
        BY <2>1, <4>1
      <4>5. QED
        BY <4>1, <4>3, <4>4
    <3>3. CASE b = x
      <4> N+1 \in 1..(N+1)
        BY <2>1
      <4>1. WITNESS N+1 \in 1..(N+1)
      <4>2. QED
        BY <3>3, <4>1
    <3>4. QED
      BY <3>2, <3>3
  <2>5. QED
    BY <2>2, <2>3, <2>4 DEF IsBijection
<1>5. IsFiniteSet(S \cup {x})
  BY <1>2, <1>4 DEF IsFiniteSet
<1>6. QED
  BY CardinalityAxiom, <1>2, <1>4, <1>5
------------------------------------------------------------------
THEOREM CardinalityOne == \A m :  /\ IsFiniteSet({m})
                                  /\ Cardinality({m}) = 1
<1>1. SUFFICES ASSUME NEW m
               PROVE  /\ IsFiniteSet({m})
                      /\ Cardinality({m}) = 1
  BY <1>1
<1>2. /\ {m} = {} \cup {m}
      /\ m \notin {}
  OBVIOUS
<1>3. IsFiniteSet({}) /\ Cardinality({}) = 0
  BY CardinalityZero
<1>4. /\ IsFiniteSet({} \cup {m})
      /\ Cardinality({} \cup {m}) = Cardinality({}) + 1
  BY <1>2, <1>3, CardinalityPlusOne
<1>5. (0+1 = 1)
  BY Arithmetic
<1>6. QED
  BY  <1>2, <1>3, <1>4, <1>5
------------------------------------------------------------------
THEOREM CardinalityOneConverse ==
            \A S : IsFiniteSet(S) /\ Cardinality(S) = 1 =>
                     \E m : S = {m}

<1> SUFFICES ASSUME NEW S, IsFiniteSet(S), Cardinality(S) = 1
             PROVE  \E m : S = {m}
  OBVIOUS
<1>1. \E f : IsBijection(f, 1..1, S)
  BY CardinalityAxiom
<1>2. 1..1 = {1}
  <3>1. /\ \A x \in 1..1 : x = 1
        /\ 1 \in 1..1
    BY Arithmetic
  <3>2. QED
    BY <3>1
<1>3. PICK f : IsBijection(f, 1..1, S)
  BY <1>1
<1>4. /\ \A y \in S : \E x \in {1} : f[x] = y
      /\ f \in [{1} -> S]
  BY <1>2, <1>3 DEF IsBijection
<1>5. /\ \A y \in S : f[1] = y
      /\ f[1] \in S
  BY <1>4
<1>6. S = {f[1]}
  BY <1>5
<1>7. QED
  BY <1>6
-----------------------------------------------------------------------------
THEOREM FiniteSubset ==
  \A S, T : /\ IsFiniteSet(T)
            /\ S \subseteq T
            => /\ IsFiniteSet(S)
               /\ Cardinality(S) \leq Cardinality(T)
<1>1 SUFFICES ASSUME NEW S, NEW TT,
                     S \subseteq TT,
                     IsFiniteSet(TT)
              PROVE  /\ IsFiniteSet(S)
                     /\ Cardinality(S) \leq Cardinality(TT)

  BY <1>1
<1>2. PICK N \in Nat : N = Cardinality(TT)
  BY <1>1, CardinalityAxiom
<1>3. DEFINE F == [n \in Nat |-> \A T : /\ S \subseteq T
                                        /\ IsFiniteSet(T)
                                        /\ Cardinality(T) = n
                                        => IsFiniteSet(S)]
<1>4. F[0]
  <2>1. 0 \in Nat
    BY Arithmetic
  <2>2. SUFFICES ASSUME NEW T,
                        IsFiniteSet(T),
                        S \subseteq T,
                        Cardinality(T) = 0
                 PROVE  IsFiniteSet(S)
    BY <2>1, <2>2
  <2>3. T = {}
    BY <2>2, CardinalityZero
  <2>4. S = {}
    BY <2>2, <2>3
  <2>5 QED
    BY <2>4, CardinalityZero
<1>5. ASSUME NEW n \in Nat,
             F[n]
      PROVE  F[n+1]
  <2>1. n+1 \in Nat
    BY Arithmetic
  <2>2. SUFFICES ASSUME \A R : /\ S \subseteq R
                               /\ IsFiniteSet(R)
                               /\ Cardinality(R) = n
                               => IsFiniteSet(S),
                        NEW T,
                        S \subseteq T,
                        IsFiniteSet(T),
                        Cardinality(T) = n+1
                 PROVE  IsFiniteSet(S)
     BY <1>5, <2>1, <2>2
  <2>3. CASE S = T
    BY <2>2, <2>3
  <2>4. CASE S # T
    <3>1. PICK x \in T : x \notin S
      BY <2>2, <2>4, SetEquality
    <3>2. S \subseteq T \ {x}
      BY <3>1, <2>2
\*    <3>3. SUFFICES ASSUME Cardinality(T) = n+1
\*                   PROVE  IsFiniteSet(S)
\*      BY <2>1
    <3>4. IsFiniteSet(T \ {x})
      <4>1. PICK g : IsBijection(g, 1..(n+1), T)
        <5>1. \A S1 : IsFiniteSet(S1) =>
                  \A n1 : n1 = Cardinality(S1) =>
                       /\ n1 \in Nat
                       /\ \E f : IsBijection(f, 1..n1, S1)
          BY <2>1, CardinalityAxiom
          \* The need to introduce this step is an example of
          \* leading the prover to use a fact that it has but
          \* isn't making proper use of.
        <5>2. QED
          BY <5>1, <2>2
      <4>2. PICK k \in 1..(n+1) : g[k] = x
        BY <4>1 DEF IsBijection
      <4>3. \A i \in 1..(n+1) : i # k => g[i] # g[k]
        BY <4>1 DEF IsBijection
      <4>4. \A y \in T : y # x
                => \E i \in 1..(n+1) : i # k /\ g[i] = y
        BY <4>3, <4>2, <4>1 DEF IsBijection
      <4>5. DEFINE f == [i \in 1..n |-> g[IF i < k THEN i ELSE i+1]]
      <4>6. f \in [1..n -> T\{x}]
        <5>1. \A i \in 1..n : f[i] \in T /\ f[i] # g[k]
          <6>1. SUFFICES ASSUME NEW i \in 1..n
                         PROVE  f[i] \in T /\ f[i] # g[k]
            BY <6>1
          <6>2. CASE i < k
             <7>1. (i # k) /\ (i \in 1..(n+1))
               BY <6>2, Arithmetic
             <7>2. QED
               BY <7>1, <4>1, <6>2 DEF IsBijection
          <6>3. CASE ~(i < k)
            <7>1. i+1 \in 1..(n+1) /\ i+1 # k
              BY <6>3, Arithmetic
            <7>2. QED
              BY <7>1, <4>1, <6>3 DEF IsBijection
          <6>4. QED
            BY <6>2, <6>3
        <5>2. QED
          BY <5>1, <4>2
      <4>7. ASSUME NEW i \in 1..n ,
                   NEW j \in 1..n,
                   i # j
            PROVE  f[i] # f[j]
        <5> DEFINE H(a) == IF a < k THEN a ELSE a+1
        <5>1. /\ H(i) # H(j)
              /\ H(i) \in 1..n+1
              /\ H(j) \in 1..n+1
          <6>1. ASSUME NEW a \in 1..n
                PROVE  H(a) \in 1..(n+1)
            <7>1. \A b : b = a \/ b = a+1 => b \in 1..(n+1)
              BY Arithmetic
            <7>2. H(a) = a \/ H(a) = a+1
              OBVIOUS
            <7>3. QED
              BY <7>1, <7>2
          <6>2. H(i) # H(j)
            <7>1. ASSUME NEW a \in 1..n, NEW b \in 1..n, a # b, a < k
                  PROVE  H(a) # H(b)
              <8>1. H(a) = a
                BY <7>1
              <8>2 CASE b < k
                BY <7>1, <8>2
              <8>3 CASE ~(b < k)
               <9> H(b) = b+1
                 BY <8>3
               <9> b+1 # a
                 BY <7>1, <8>3, Arithmetic
               <9> QED
                 BY <8>1
              <8>4. QED
                BY <8>2, <8>3
            <7>2. ASSUME NEW a \in 1..n, NEW b \in 1..n, a # b,
                         ~(a < k) /\ ~(b < k)
                  PROVE  H(a) # H(b)
              <8>1. H(a) = a+1 /\ H(b) = b+1
                BY <7>2
              <8>2. a+1 # b+1
                BY <7>2, Arithmetic
              <8>3. QED
                BY <8>1, <8>2
            <7>3. QED
              BY <7>1, <7>2, <4>7
          <6>3. QED
            BY <6>1, <6>2
        <5>2. i+1 \in 1..(n+1) /\ j+1 \in 1..(n+1)
          BY Arithmetic
        <5> HIDE DEF H \* Here's the first case I've found where hiding
                       \* is necessary for a proof
        <5>3. g[H(i)] # g[H(j)]
           BY <5>1, <4>1 DEF IsBijection
        <5> USE DEF H
        <5>4. QED
          BY <5>3
      <4>8. ASSUME NEW y \in T \ {x}
            PROVE  \E i \in 1..n : f[i] = y
        <5>1. PICK j \in 1..(n+1) : g[j] = y
          BY <2>1, <4>1 DEF IsBijection
        <5>2. j # k
          BY <5>1, <4>2
        <5>3. CASE j < k
          <6>1. j \in 1..n
            BY <5>3, Arithmetic
          <6>2. f[j] = g[j]
            BY <6>1, <5>3
          <6>3. QED
            BY <6>1, <6>2, <5>1
        <5>4. CASE ~(j < k)
          <6>1. j # k
            OBVIOUS
          <6>2. /\ ~(j-1 < k)
                /\ (j-1)+1 = j
                /\ (j-1) \in 1..n
            BY <5>4, <6>1, Arithmetic
          <6>3. f[j-1] = g[j]
            BY <6>2
          <6>4. QED
            BY <6>2, <6>3, <5>1
        <5>5. QED
          BY <5>3, <5>4
      <4>9. QED
        OMITTED \*** BY <4>6, <4>7, <4>8 DEF IsBijection, IsFiniteSet
    <3>5. Cardinality(T \ {x}) = n
      <4>1. T = (T \ {x}) \cup {x}
        BY SetEquality
      <4>2. Cardinality(T) = Cardinality(T \ {x}) + 1
        <5>1. Cardinality((T \ {x}) \cup {x}) = Cardinality(T \ {x}) + 1
          BY <3>4, CardinalityPlusOne
        <5>2. QED
          BY <4>1, <5>1
      <4>3. Cardinality(T \ {x}) \in Nat
        BY <3>4, CardinalityInNat
      <4>4. \A m \in Nat : (n+1 = m+1) => (n = m)
        BY Arithmetic
      <4>5. QED
        BY <4>2, <4>3, <4>4, <2>2
    <3>6. QED
      BY <3>2, <3>4, <3>5, <2>2
  <2>5. QED
    BY <2>3, <2>4
<1>6.  IsFiniteSet(S)
  OMITTED \*** BY <1>2, <1>4, <1>5, Induction
<1>7. Cardinality(S) \leq Cardinality(TT)
  PROOF OMITTED
<1>8. QED
  BY <1>6, <1>7
-------------------------------------------------------

THEOREM CardinalityMinusOne ==
         \A S : IsFiniteSet(S) =>
                   \A x \in S : /\ IsFiniteSet(S \ {x})
                                /\ Cardinality(S \ {x}) = Cardinality(S)-1
<1>1. SUFFICES ASSUME NEW S,
                      IsFiniteSet(S),
                      NEW x \in S
               PROVE  /\ IsFiniteSet(S \ {x})
                      /\ Cardinality(S \ {x}) = Cardinality(S)-1
  BY <1>1
<1>2. IsFiniteSet(S \ {x})
  <2>1. (S \ {x}) \subseteq S
    OBVIOUS
  <2>2. QED
    BY <2>1, <1>1, FiniteSubset
<1>3. Cardinality(S \ {x}) = Cardinality(S)-1
  <2>1. /\ S = (S \ {x}) \cup {x}
        /\ x \notin (S \ {x})
     BY SetEquality
  <2>2. IsFiniteSet((S \ {x}) \cup {x})
    BY <2>1, <1>1
  <2>3. Cardinality((S \ {x}) \cup {x}) = Cardinality(S \ {x}) + 1
    BY <1>2, <2>1, <2>2, CardinalityPlusOne
  <2>4. Cardinality(S) = Cardinality(S \ {x}) + 1
    BY <2>3, <2>1
  <2>5. \A m : \A n \in Nat: m = n + 1 => n = m - 1
    BY Arithmetic
  <2>6. Cardinality(S \ {x}) \in Nat
    BY <1>2, CardinalityInNat
  <2>7. QED
    BY <2>4, <2>5, <2>6
<1>4. QED
  BY <1>2, <1>3

THEOREM CardinalityUnion ==
          \A S, T : IsFiniteSet(S) /\ IsFiniteSet(T) =>
                      /\ IsFiniteSet(S \cup T)
                      /\ IsFiniteSet(S \cap T)
                      /\ Cardinality(S \cup T) =
                              Cardinality(S) + Cardinality(T)
                              - Cardinality(S \cap T)
PROOF OMITTED


-----------------------------------------------------------------------------

THEOREM PigeonHole ==
            \A S, T : /\ IsFiniteSet(S)
                      /\ IsFiniteSet(T)
                      /\ Cardinality(T) < Cardinality(S)
                      => \A f \in [S -> T] :
                           \E x, y \in S : x # y /\ f[x] = f[y]

<1>1. DEFINE F == [n \in Nat |->
                    \A S : IsFiniteSet(S) /\ (Cardinality(S) = n) =>
                      \A T : /\ IsFiniteSet(T)
                             /\ Cardinality(T) < Cardinality(S)
                             => \A f \in [S -> T] :
                                  \E x, y \in S : x # y /\ f[x] = f[y]]

<1>2. SUFFICES \A n \in Nat : F[n]
  <2>1. SUFFICES ASSUME \A n \in Nat : F[n],
                        NEW S, NEW T,
                        IsFiniteSet(S),
                        IsFiniteSet(T),
                        Cardinality(T) < Cardinality(S)
                 PROVE  \A f \in [S -> T] :
                           \E x, y \in S : x # y /\ f[x] = f[y]
    BY <1>2, <2>1
  <2>2. PICK n \in Nat : Cardinality(S) = n
    BY CardinalityInNat, <2>1
  <2>3. F[n]
    BY <1>2
  <2>4. QED
    BY <2>3, <2>1, <2>2
<1>3. F[0]
  <2>1. 0 \in Nat
    BY Arithmetic
  <2>2. SUFFICES ASSUME NEW S,
                        IsFiniteSet(S) /\ (Cardinality(S) = 0),
                        NEW T,
                        IsFiniteSet(T),
                        Cardinality(T) < Cardinality(S)
                 PROVE  FALSE
    BY <2>2
  <2>3. Cardinality(T) \in Nat
    BY <2>2, CardinalityInNat
  <2>4. \A n \in Nat : ~(n < 0)
    BY Arithmetic
  <2>5. QED
    BY <2>3, <2>4, <2>2

<1>4. ASSUME NEW n \in Nat,
             F[n]
      PROVE  F[n+1]
  <2>1. n+1 \in Nat /\ n+1 # 0
    BY Arithmetic
  <2>2. SUFFICES ASSUME NEW S,
                        IsFiniteSet(S),
                        Cardinality(S) = n+1,
                        NEW T,
                        IsFiniteSet(T),
                        Cardinality(T) < Cardinality(S),
                        NEW f \in [S -> T]
                 PROVE  \E x, y \in S : x # y /\ f[x] = f[y]
    BY <2>1, <2>2
  <2>3. S # {}
    <3>1. Cardinality({}) = 0
      BY CardinalityZero
    <3>2. Cardinality(S) # 0
      BY <2>1, <2>2
    <3>3. QED
      BY <3>1, <3>2
  <2>4. PICK z : z \in S
    BY <2>3
  <2>5. f[z] \in T
    BY <2>4
  <2>6. CASE \E w \in S : w # z /\ f[w] = f[z]
    BY <2>4, <2>6
  <2>7. CASE \A w  \in S : w # z => f[w] # f[z]
    <3>1a. IsFiniteSet(S \ {z}) /\ Cardinality(S \ {z}) = (n+1) - 1
      BY CardinalityMinusOne, <2>2, <2>4
    <3>1b. /\ IsFiniteSet(T \ {f[z]})
           /\ Cardinality(T \ {f[z]}) = Cardinality(T) - 1
        BY <2>5, CardinalityMinusOne, <2>2
    <3>2. Cardinality(S \ {z}) = n
      <4>1. \A i \in Nat : (i+1) -1 = i
        BY Arithmetic
      <4>2. QED
        BY <3>1a, <4>1
    <3>2a. Cardinality(T \ {f[z]}) < Cardinality(S \ {z})
      <4>1. \A m  \in Nat : m < n+1 => m-1 < n
        BY Arithmetic
      <4>2. Cardinality(T) \in Nat
         BY CardinalityInNat, <2>2
      <4>3. Cardinality(T) < n+1
        BY <2>2
      <4>4. Cardinality(T)-1 < n
        BY <4>1, <4>2, <4>3
      <4>5. QED
        BY <3>1b, <4>4, <3>2
    <3>3. DEFINE g == [w \in (S \ {z}) |-> f[w]]
    <3>4. \A w \in (S \ {z}) : w \in S /\ w # z
      OBVIOUS
    <3>5. \A w \in (S \ {z}) : f[w] # f[z]
      BY <3>5, <2>7
    <3>6. \A w \in (S \ {z}) : f[w] \in T \ {f[z]}
      BY <3>4, <3>5
    <3>7. g \in [S \ {z} -> T \ {f[z]}]
      BY <3>6
    <3>8. \E x, y \in S \ {z} : x # y /\ g[x] = g[y]
      <4>1. \A SS :
              \A TT : /\ IsFiniteSet(SS)
                      /\ Cardinality(SS) = n
                      /\ IsFiniteSet(TT)
                      /\ Cardinality(TT) < Cardinality(SS)
                    => \A ff \in [SS -> TT] :
                          \E x, y \in SS : x # y /\ ff[x] = ff[y]
         BY ONLY <1>4
      <4>2. \A TT : /\ IsFiniteSet(TT)
                    /\ Cardinality(TT) < Cardinality(S \ {z})
                    => \A ff \in [S \ {z} -> TT] :
                          \E x, y \in S \ {z} : x # y /\ ff[x] = ff[y]
        BY ONLY <4>1, <3>1a, <3>2
      <4>3. \A ff \in [S \ {z} -> T \ {f[z]}] :
                 \E x, y \in S \ {z} : x # y /\ ff[x] = ff[y]
        BY <4>2, <3>1b, <3>2a
      <4> HIDE DEF g  \* The QED step doesn't work without hiding g
      <4>4. QED
        BY <3>7, <4>3
    <3>9. PICK x, y : /\ x \in S \ {z}
                      /\ y \in S \ {z}
                      /\ x # y
                      /\ g[x] = g[y]
      BY <3>8
    <3>10. x \in S /\ y \in S /\ f[x] = f[y]
      <4>1. x \in S /\ y \in S
        <5>1. S \ {z} \subseteq S
          OBVIOUS
        <5>2 QED
         BY <5>1, <3>9
      <4>2. f[x] = g[x] /\ f[y] = g[y]
        BY <4>1, <3>9
      <4>3. QED
        BY <4>2, <3>9
    <3>11.  QED
      BY <3>10, <3>9
  <2>8. QED
    BY <2>6, <2>7
<1>5. QED
  BY <1>3, <1>4, Induction
-------------------------------------------------------

THEOREM \A S, T , f :  /\ IsFiniteSet(S)
                       /\ f \in [S -> T]
                       /\ \A y \in T : \E x \in S : y = f[x]
                       => /\ IsFiniteSet(T)
                          /\ Cardinality(T) \leq Cardinality(S)
PROOF OMITTED
\* I started trying to prove this but gave up because it required
\* proving a other lemmas.

\* <1> DEFINE F == [n \in Nat |->
\*                   \A S : /\ Cardinality(S) = n
\*                          /\ IsFiniteSet(S)
\*                          =>
\*                           \A T, f :
\*                             /\ f \in [S -> T]
\*                             /\ \A y \in T : \E x \in S : y = f[x]
\*                             => /\ IsFiniteSet(T)
\*                                /\ Cardinality(T) \leq Cardinality(S)]
\*
\* <1>1. F[0]
\*   <2>1. 0 \in Nat
\*     BY Arithmetic
\*   <2>2. SUFFICES ASSUME NEW S,
\*                         Cardinality(S) = 0,
\*                         IsFiniteSet(S)
\*                  PROVE  \A T, f :
\*                             /\ f \in [S -> T]
\*                             /\ \A y \in T : \E x \in S : y = f[x]
\*                             => /\ IsFiniteSet(T)
\*                                /\ Cardinality(T) \leq Cardinality(S)
\*      BY <2>1
\*
\*   <2>3. SUFFICES ASSUME NEW T, NEW f \in [S -> T],
\*                         \A y \in T : \E x \in S : y = f[x]
\*                  PROVE  /\ IsFiniteSet(T)
\*                         /\ Cardinality(T) \leq Cardinality(S)
\*     OBVIOUS
\*
\*   <2>4. S = {}
\*     BY CardinalityZero
\*   <2>6. CASE T = {}
\*     <3>1. IsFiniteSet(T) /\ Cardinality(T) = 0
\*       BY CardinalityZero
\*     <3>2. (0 \leq 0)
\*       BY Arithmetic
\*     <3>3. QED
\*       BY <3>1, <3>2
\*   <2>7. CASE T # {}
\*     <3>1. PICK y : y \in T
\*       OBVIOUS
\*     <3>2. \E x \in S : y = f[x]
\*       OBVIOUS
\*     <3>3. QED
\*       BY <3>2, <2>4
\*   <2>8. QED
\*     BY <2>6, <2>7
\* <1>2. ASSUME NEW n \in Nat,
\*              F[n]
\*       PROVE  F[n+1]
\* <1>3. QED
\*   <2>1. \A n \in Nat : F[n]
\*     BY <1>1, <1>2, Induction
\*   <2>2. SUFFICES ASSUME NEW S,
\*                         IsFiniteSet(S)
\*                  PROVE \A T, f :
\*                           /\ f \in [S -> T]
\*                           /\ \A y \in T : \E x \in S : y = f[x]
\*                           => /\ IsFiniteSet(T)
\*                              /\ Cardinality(T) \leq Cardinality(S)
\*        OBVIOUS
\*   <2>3. Cardinality(S) \in Nat
\*     BY CardinalityInNat
\*   <2>4. PICK n \in Nat : Cardinality(S) = n
\*     BY <2>3
\*   <2>5. QED
\*     BY <2>1, <2>4

THEOREM ProductFinite ==
     \A S, T : IsFiniteSet(S) /\ IsFiniteSet(T) => IsFiniteSet(S \X T)
PROOF OMITTED

THEOREM SubsetsFinite == \A S : IsFiniteSet(S) => IsFiniteSet(SUBSET S)
PROOF OMITTED
=============================================================================
