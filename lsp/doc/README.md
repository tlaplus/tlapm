# Proof Decomposition

The general idea is to keep the decision on making new proof levels for the user.
Thus, if possible, the decomposition commands will try to refine the goal at the current level.

Commands for introducing/reducing levels:

- Convert the leaf proof to steps.
  This introduces a new level into the proof.
- Convert QED-only steps to a leaf proof.
  This simplifies proof. If only a single step (QED) is left,
  then there is no point in keeping the proof with the additional level introduced.

Decomposition by the goal works by invoking code actions at the QED step of the current level.
This is because during the steps at that level, the goal is refined, thus the ultimate goal
is known at the QED step, and not at the upped-level step which is decomposed.
Decompose goal is a single command for the user, but it works dependent on the structure of the goal:

# Goal is implication

The step with a goal `G == P => Q` and proof

```tla
<l>q. QED Proof
```

is transformed to

```tla
<l>x. SUFFICES ASSUME P PROVE Q BY DEF G
<l>q. QED Proof
```

or if no operator expansion is needed:

```tla
<l>x. HAVE P
<l>q. QED Proof
```

# Goal is conjunction

If the goal is `P == P1 /\ P2 /\ ... Pn` with the proof

```tla
<l>q. QED ProofP
```

then it is transformed to steps (inserted before the QED):

```tla
<l>1. P1 ProofP
<l>2. P2 ProofP
...
<l>n. Pn ProofP
<l>q. QED BY <l>1, <l>2, ... <l>n DEF P
```

Here `DEF P` is only added, of the goal was an operator, which should be expanded.
All the proof labels are introduced to be unused at that level.
