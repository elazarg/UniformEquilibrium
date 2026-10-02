# Independent review of `REPAIRED_ATOM_MISSING_FACE_SIGN_SEPARATION`

**Reviewer:** CODEX_EULER  
**Date:** 2026-08-25  
**Verdict:** **PASS at the stated interface-separation scope.**

I checked the incidence split, signs, residual-average estimate, and the
explicit Fin4 table against Miner's reviewed affine repaired-law theorem and
the pair-base missing-face decomposition.  I found no repair requiring a
change to the mathematics.  The note should remain internal: it proves that a
specific proposed connector is unavailable, not a terminal compiler,
contradiction, or maintained-rank decrease.

## 1. Incidence and sign split: PASS

Let the singleton repaired atom be a nonempty (A\subseteq\{c,a,f\}), with
singleton owner (o).  The pair-base missing-face law is on
(D\subseteq\{a,f\}).

If (c\in A), write (A=D\cup\{c\}).  The repaired leave comparison is

\[
r_o(D\cup\{c\})-r_o(D\cup\{c,o\}),
\]

which is exactly a term in the positive conditional-(c)-Quit average
(L_o).  It is not a term of `H_missing`.

If (c\notin A), then (A\subseteq\{a,f\}), and the same comparison is
literally the corresponding nonempty term

\[
r_o(A)-r_o(A\cup\{o\})
\]

of `H_missing`.  The repaired-atom theorem makes it at least (\Gamma/2),
whereas interior exact softening requires the complete weighted average to
be at most

\[
-{z\Gamma\over1-z}<0.
\]

Thus the atom has the opposite sign.  The solo alternative compares
(r_o(A)) with (r_o(\{o\})) and gives no relation between (r_o(A)) and
(r_o(A\cup\{o\})).  These statements cover both incidences and both
inclusive atom alternatives.  The note correctly retains the additional
debtor-label and law-weight nonidentifications.

## 2. Quantitative residual burden: PASS

Under the deliberately extra alignment assumptions, write

\[
H_{\rm missing}=w h_A+(1-w)H_{\rm rest},
\qquad h_A\ge\Gamma/2.
\]

Combining this with
(H_{\rm missing}\le-z\Gamma/(1-z)) gives, for (w<1),

\[
H_{\rm rest}\le
 { -z\Gamma/(1-z)-w\Gamma/2\over1-w}.
\]

The inequality orientation and denominator are correct.  At (w=1), the
positive atom alone makes the required negative average impossible whenever
(z>0).  This is a burden on a different atom, not a payment supplied by the
affine bridge.

## 3. Exact Fin4 realization: PASS

All unlisted coordinates are zero and the five displayed coordinates have
absolute value at most (M=1).

### Singleton source and repair

At singleton base (o), with (a) sure Quit and (c,f) Continue, every
free-player comparison on rows containing (o) is zero.  In particular the
exceptional coordinate (r_f(\{a,f\})=1) is not reached when (o) is in the
terminal coalition.  Hence the selected free point is an induced Nash point.

The source and repair laws are respectively

\[
\delta_{\{o,a\}},\qquad\delta_{\{a\}},
\]

so the affine law formula holds with absorption (a_{\rm abs}=1).  The owner
repair gain is

\[
r_o(\{a\})-r_o(\{o,a\})=1.
\]

The repaired free restriction is not Nash because player (f) can join
({a}) and gain (1).

### Pair-base source

At base ({o,c}), with (a) sure and (f) Continue, all free-player
comparisons again vanish.  Owner (o)'s Continue-minus-Quit difference is

\[
r_o(\{c,a\})-r_o(\{o,c,a\})=1,
\]

so its unrestricted debt is exactly one because the other base player makes
absorption certain at date zero.  Player (f)'s prescribed payoff and cap
are both zero, and either sure base player gives unit opponent incidence.

Both the repaired law and pair-base free law are the point mass on ({a}).
Nevertheless

\[
L_o=1,\qquad H_{\rm missing}=1.
\]

For every softening rate (z\in[0,1]), the Continue-over-Quit difference of
(o) is therefore (zL_o+(1-z)H_{\rm missing}=1).  Any exact root retaining
this free law must prescribe (o) pure Continue.  The claimed interior
cancellation fails even after owner, debtor, atom, and law have all been
aligned.

## 4. Scope and novelty

The example does not supply a terminal exploitability witness, positive
global minimum, checked double-inert port, or full hard residual.  It is not a
quitting-game counterexample and does not exclude another root or a nonlocal
block.  Its valid conclusion is narrower and useful: the reviewed affine
repaired-law atom cannot be used as the negative missing-base term required
by the literal pair-base softening converter.

This is a genuine same-table/interface separation beyond a labels-only
objection, but it does not close a named residual chamber or enter a checked
consumer.  I therefore recommend retaining it as an internal obstruction,
not an export packet.

