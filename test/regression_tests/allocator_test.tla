-------------------------- MODULE allocator_test -----------------------------

(***********************************************************************)
(* Specification of an allocator managing a set of resources:          *)
(* - Clients can request sets of resources whenever all their previous *)
(*   requests have been satisfied.                                     *)
(* - Requests can be partly fulfilled, and resources can be returned   *)
(*   even before the full request has been satisfied. However, clients *)
(*   only have an obligation to return resources after they have       *)
(*   obtained all resources they requested.                            *)
(***********************************************************************)

\* EXTENDS FiniteSets, TLC

CONSTANTS
  Client,     \* set of all clients
  Resource    \* set of all resources

\* ASSUME
\*  IsFiniteSet(Resource)

VARIABLES
  unsat,       \* set of all outstanding requests per process
  alloc        \* set of resources allocated to given process

TypeInvariant ==
  /\ unsat \in [Client -> SUBSET Resource]
  /\ alloc \in [Client -> SUBSET Resource]

-------------------------------------------------------------------------

(* Resource are available iff they have not been allocated. *)
available == Resource \ (UNION {alloc[c] : c \in Client})

(* Initially, no resources have been requested or allocated. *)
Init ==
  /\ unsat = [c \in Client |-> {}]
  /\ alloc = [c \in Client |-> {}]

(**********************************************************************)
(* A client c may request a set of resources provided that all of its *)
(* previous requests have been satisfied and that it doesn't hold any *)
(* resources.                                                         *)
(**********************************************************************)
Request(c,S) ==
  /\ unsat[c] = {} /\ alloc[c] = {}
  /\ S # {} /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED alloc
  /\ alloc' = alloc

(*******************************************************************)
(* Allocation of a set of available resources to a client that     *)
(* requested them (the entire request does not have to be filled). *)
(*******************************************************************)
Allocate(c,S) ==
  /\ S # {} /\ S \subseteq available \cap unsat[c]
  /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]

(*******************************************************************)
(* Client c returns a set of resources that it holds. It may do so *)
(* even before its full request has been honored.                  *)
(*******************************************************************)
Return(c,S) ==
  /\ S # {} /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
  /\ UNCHANGED unsat
  /\ unsat' = unsat

(* The next-state relation. *)
Next ==
  \E c \in Client, S \in SUBSET Resource :
     Request(c,S) \/ Allocate(c,S) \/ Return(c,S)

vars == <<unsat,alloc>>

-------------------------------------------------------------------------

(*

(* The complete high-level specification. *)
SimpleAllocator ==
  /\ Init /\ [][Next]_vars
  /\ \A c \in Client: WF_vars(Return(c, alloc[c]))
  /\ \A c \in Client: SF_vars(\E S \in SUBSET Resource: Allocate(c,S))

*)

-------------------------------------------------------------------------

Mutex ==
  \A c1,c2 \in Client : \A r \in Resource :
     r \in alloc[c1] \cap alloc[c2] => c1 = c2

ClientsWillReturn ==
  \A c \in Client : unsat[c]={} ~> alloc[c]={}

ClientsWillObtain ==
  \A c \in Client, r \in Resource : r \in unsat[c] ~> r \in alloc[c]

InfOftenSatisfied ==
  \A c \in Client : []<>(unsat[c] = {})

-------------------------------------------------------------------------

(* Used for symmetry reduction with TLC *)
\* Symmetry == Permutations(Client) \cup Permutations(Resource)

-------------------------------------------------------------------------

(**********************************************************************)
(* The following version states a weaker fairness requirement for the *)
(* clients: resources need be returned only if the entire request has *)
(* been satisfied.                                                    *)
(**********************************************************************)

(*

SimpleAllocator2 ==
  /\ Init /\ [][Next]_vars
  /\ \A c \in Client: WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Client: SF_vars(\E S \in SUBSET Resource: Allocate(c,S))

*)

-------------------------------------------------------------------------

THEOREM InitTypeInvariant == Init => TypeInvariant
BY DEFS Init, TypeInvariant

THEOREM RequestTypeInvariant ==
  ASSUME NEW c \in Client,
         NEW S \in SUBSET Resource
  PROVE  TypeInvariant /\ Request(c,S) => TypeInvariant'
BY DEFS TypeInvariant, Request

THEOREM AllocateTypeInvariant ==
  ASSUME NEW c \in Client,
         NEW S \in SUBSET Resource
  PROVE  TypeInvariant /\ Allocate(c,S) => TypeInvariant'
BY DEFS TypeInvariant, Allocate

THEOREM ReturnTypeInvariant ==
  ASSUME NEW c \in Client,
         NEW S \in SUBSET Resource
  PROVE  TypeInvariant /\ Return(c,S) => TypeInvariant'
BY DEFS TypeInvariant, Return

THEOREM NextTypeInvariant == TypeInvariant /\ Next => TypeInvariant'
<1>1. ASSUME TypeInvariant, Next
      PROVE TypeInvariant'
  <2>. PICK c \in Client,
            S \in SUBSET Resource :
              \/ Request(c, S)
              \/ Allocate(c, S)
              \/ Return(c, S)
    BY <1>1!2 DEF Next         \** TypeInvariant assumption not needed
  <2>. QED
    BY <1>1,
       RequestTypeInvariant,
       AllocateTypeInvariant,
       ReturnTypeInvariant
<1>2. QED
  BY <1>1

-------------------------------------------------------------------------

THEOREM InitMutex == Init => Mutex
BY DEFS Init, Mutex

THEOREM RequestMutexBis ==
  ASSUME NEW clt \in Client,
         NEW S \in SUBSET Resource
  PROVE  Mutex /\ Request(clt,S) => Mutex'
BY DEFS Mutex, Request

THEOREM ReturnMutex ==
  ASSUME NEW clt \in Client,
         NEW S \in SUBSET Resource
  PROVE  TypeInvariant /\ Mutex /\ Return(clt,S) => Mutex'
<1>1. SUFFICES
        ASSUME TypeInvariant,
               Mutex,
               Return(clt,S)
        PROVE  Mutex'
  OBVIOUS
<1>2. SUFFICES
        ASSUME NEW c1 \in Client,
               NEW c2 \in Client,
               NEW r \in Resource,
               r \in alloc'[c1] \cap alloc'[c2]
        PROVE  c1 = c2
  BY DEF Mutex
<1>3. alloc'[c1] \subseteq alloc[c1]
  BY <1>1
  DEF Return, TypeInvariant
<1>4. alloc'[c2] \subseteq alloc[c2]
  BY <1>1
  DEF Return, TypeInvariant
<1>5. QED
  BY <1>1, <1>2, <1>3, <1>4
  DEF Mutex, TypeInvariant

THEOREM AllocateMutex ==
  ASSUME NEW clt \in Client,
         NEW S \in SUBSET Resource
  PROVE  TypeInvariant /\ Mutex /\ Allocate(clt, S) => Mutex'
<1>1. SUFFICES
        ASSUME TypeInvariant,
               Mutex,
               Allocate(clt,S)
        PROVE  Mutex'
  OBVIOUS
<1>2. SUFFICES
        ASSUME NEW c1 \in Client,
               NEW c2 \in Client,
               NEW r \in Resource,
               r \in alloc'[c1] \cap alloc'[c2]
        PROVE  c1 = c2
  BY DEF Mutex
<1>3. CASE ~(c1 = clt \/ c2 = clt)
  <2>1. alloc'[c1] = alloc[c1] /\ alloc'[c2] = alloc[c2]
    BY <1>1, <1>2, <1>3
    DEF Allocate, TypeInvariant
  <2>2. QED
    BY <1>1, <1>2, <2>1
    DEF Mutex, TypeInvariant
    (* mutex in pre-state, typing *)
<1>4. CASE c1 = clt
  <2>1. SUFFICES ASSUME c1 # c2
                 PROVE FALSE
    OBVIOUS
  <2>2. alloc'[c2] = alloc[c2]
    BY <1>1, <1>4, <2>1
    DEFS Allocate, TypeInvariant
  <2>3. r \notin alloc[c1]
    BY <1>1, <1>2, <2>1, <2>2
    DEFS Mutex, TypeInvariant
  <2>4. r \notin available
    BY <1>1, <1>2, <2>2, <2>1
    DEFS available, TypeInvariant
  <2>5. r \notin S
    BY <1>1, <1>2, <2>4
    DEF Allocate
  <2>6. r \notin alloc'[c1]
    BY <1>1, <2>3, <2>5
    DEFS Allocate, TypeInvariant
  <2>7. QED
    BY <1>1, <1>2, <2>1,
       <2>2, <2>3, <2>4, <2>5, <2>6
    DEFS Allocate, TypeInvariant
<1>5. CASE c2 = clt
  <2>1. SUFFICES ASSUME c1 # c2
                 PROVE FALSE
    OBVIOUS
  <2>2. alloc'[c1] = alloc[c1]
    BY <1>1, <1>4, <2>1
    DEFS Allocate, TypeInvariant
  <2>3. r \notin alloc[c2]
    BY <1>1, <1>2, <2>1, <2>2
    DEFS Mutex, TypeInvariant
  <2>4. r \notin available
    BY <1>1, <1>2, <2>2, <2>1
    DEF available, TypeInvariant
  <2>5. r \notin S
    BY <1>1, <1>2, <2>4
    DEF Allocate
  <2>6. r \notin alloc'[c2]
    BY <1>1, <2>3, <2>5
    DEFS Allocate, TypeInvariant
  <2>7. QED
    BY <1>1, <1>2, <2>1,
       <2>2, <2>3, <2>4, <2>5, <2>6
    DEFS Allocate, TypeInvariant
<1>6. 1=1
    OBVIOUS
 <1>7. QED
  BY <1>3, <1>4, <1>5

THEOREM NextMutex == TypeInvariant /\ Mutex /\ Next => Mutex'
BY RequestMutexBis, AllocateMutex, ReturnMutex DEF Next


(*Allocator.tla
THEOREM SimpleAllocator => InfOftenSatisfied
(** The following do not hold:                          **)
(** THEOREM SimpleAllocator2 => ClientsWillObtain       **)
(** THEOREM SimpleAllocator2 => InfOftenSatisfied       **)

*)

=========================================================================
