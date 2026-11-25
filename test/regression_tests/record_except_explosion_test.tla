---- MODULE record_except_explosion_test ----

\* Regression guard for the EXCEPT-normalization fold in Expr.Elab
\* (src/expr/e_elab.ml): a `[ recordLiteral EXCEPT ... ]` is folded back into a
\* record literal instead of re-embedding the wide base once per path
\* component.
\*
\* `Chain(z)` is a chain of nested, multi-component EXCEPT updates over a wide
\* (20-field) record literal.  It is normalized during obligation generation,
\* BEFORE any backend runs.  Without the fold the normalized term grows
\* geometrically in the number of chain layers; the goal is deliberately
\* trivial (`fa` is written once in `Step` and never touched again, so
\* `Chain(z).fa = z` holds by inspection), leaving term SIZE as the only thing
\* at stake.
\*
\* Measured with `--noproving --verbose | wc -l` at the 4 layers below:
\*   fold present (Expr.Elab):   ~5000 lines
\*   fold removed:              >=39000 lines  (>=9,000,000 lines at 6 layers)
\* The size is monotone in the layer count, so the (500, 25000) window in the
\* command below sits safely between the two: a regression that drops the fold
\* makes this test fail.  `head` caps the captured output so the failing case
\* stays cheap.
\*
\* This is a term-SIZE guard only; the semantic correctness of the fold (that
\* the reduced value is right, and that no reduction is unsound) is covered by
\* the inline tests in src/expr/e_elab.ml.

EXTENDS Naturals, TLAPS

VARIABLES p, dir, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, q, r, s
CONSTANT X, Y

\* A wide (20-field) record literal.  `fp` is accessed as a function (indexed
\* `[X]`) and `fdir` as a record (sub-field `.local`), so the EXCEPT paths
\* through them are multi-component.
Rec ==
  [ fp |-> p, fdir |-> dir,
    fa |-> a, fb |-> b, fc |-> c, fd |-> d, fe |-> e, ff |-> f, fg |-> g, fh |-> h,
    fi |-> i, fj |-> j, fk |-> k, fl |-> l, fm |-> m, fn |-> n, fo |-> o, fq |-> q,
    fr |-> r, fs |-> s ]

\* One update layer: multi-component paths and IF-valued sub-updates over the
\* wide literal.
Step(z) ==
  [ Rec EXCEPT
      !.fp   = IF z THEN [Rec.fp   EXCEPT ![X].c1 = TRUE, ![Y].c1 = FALSE]
                    ELSE  Rec.fp,
      !.fdir = IF z THEN [Rec.fdir EXCEPT !.local = TRUE, !.pending = FALSE]
                    ELSE  Rec.fdir,
      !.fa = z, !.fb = z, !.fc = z, !.fd = z, !.fe = z ]

\* Four update layers over a common base bound by LET; each layer is a nested
\* EXCEPT with multi-component paths, so the duplication compounds
\* multiplicatively without the fold.
Chain(z) ==
  LET s1 == Step(z)
      s2 == [ s1 EXCEPT !.fp[X].c1 = FALSE, !.fdir.local   = FALSE, !.ff = z, !.fg = z ]
      s3 == [ s2 EXCEPT !.fp[Y].c1 = TRUE,  !.fdir.pending = TRUE,  !.fh = z, !.fi = z ]
      s4 == [ s3 EXCEPT !.fp[X].c1 = TRUE,  !.fdir.local   = TRUE,  !.fj = z, !.fk = z ]
  IN  s4

LEMMA Explode ==
  ASSUME NEW z \in BOOLEAN
  PROVE  Chain(z).fa = z
BY DEF Chain, Step, Rec

====
\* Bound the size of the normalized obligation (see header).  With the
\* record-literal EXCEPT fold it is ~5000 lines; without it >=39000 and growing
\* geometrically, so the (500, 25000) window fails on regression.  `head` caps
\* the captured output so a regression cannot grow it unboundedly here.
command: L=$( ${TLAPM} --noproving --verbose --nofp ${FILE} 2>&1 | head -n 60000 | wc -l | tr -d ' ' ); echo "normalized-obligation lines (cap 60000): $L"; test "$L" -gt 500 && test "$L" -lt 25000
result: 0
