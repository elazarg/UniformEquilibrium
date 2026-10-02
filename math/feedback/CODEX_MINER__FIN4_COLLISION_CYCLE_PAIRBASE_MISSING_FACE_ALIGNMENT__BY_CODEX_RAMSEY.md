# Independent review of `FIN4_COLLISION_CYCLE_PAIRBASE_MISSING_FACE_ALIGNMENT`

**Reviewer:** CODEX_RAMSEY  
**Date:** 2026-08-25  
**Verdict:** **PASS mathematically, with one wording qualification; keep internal.**

I checked the four-cycle label selection, the pair-base source declarations,
the `H_missing` sign conversion and mass bounds, and every displayed value in
the rational separation table.  I found no mathematical defect.  The positive
result is a genuine same-table alignment, but it currently has no downstream
consumer: it identifies a useful payoff-table entry without putting positive
source-law mass on that entry.  The forced cycle cancellation is not a remedy,
because its sign is opposite to the one required by the exact softening
identity.

One sentence should be read narrowly.  Proposition 5.1's construction is
*uniformly guaranteed* by a genuine four-cycle; it is not literally exclusive
to four-cycles.  For example, if the functional graph consists of two
disjoint two-cycles, choosing one vertex from each cycle as the base also puts
both possible debtors' predecessors in the free set.  What fails for a
general two- or three-cycle is a guarantee from that cycle's labels and the
current unprescribed-debtor target.  The explanatory paragraph already gives
the correct weaker conclusion, so replacing “It is special to the
four-cycle” by “This uniform alternating-cycle guarantee is special to the
four-cycle” would remove the only ambiguity.

## 1. Source and quantifier check

The edge convention is correct.  The checked map supplied by
`FinFourQuantitativeFullSupportHardResidual.
exists_fixedPointFree_terminalGap_collisionMap` sends an owner `x` to a
distinct collider `d` and gives

\[
r_d(\{x,d\})-r_d(\{x\})\geq\Gamma.
\]

The pair-base producer has the exact weaker selection used in the note.
`nonempty_finFourPairBasePaidResetTarget` permits either prescribed reset
owner outside a chosen two-element base, while
`FinFourPairBasePaidResetTarget.debtor_mem_base` returns an emergent debtor in
that base.  It does **not** prescribe which base member is the debtor.

For the four-cycle

\[
e_0\to e_1\to e_2\to e_3\to e_0,
\]

the base `B={e0,e2}` and free set `F={e1,e3}` solve exactly that selection
problem: if the returned debtor is `e0`, its predecessor is `e3`; if it is
`e2`, its predecessor is `e1`.  In both cases the predecessor is free, so the
incoming singleton collision is a literal entry of the debtor's missing-base
table.  This uses the same reward table and the same terminal witness.  It
does not identify the marked cancelling edge from the cycle theorem with the
incoming edge of the returned debtor, and the note explicitly retains that
distinction.

Invoking the target once with either chosen free reset owner is legitimate,
but it should not be read as saying the two owner choices return the same
noncomputably selected induced-Nash point.  No such simultaneous claim is
needed.

## 2. Sign and face-incidence audit

With debtor `d`, other base player `e`, free law `nu`, and `x` the incoming
collider, the note uses

\[
h_A=r_d(A)-r_d(A\cup\{d\}),
\]

so `h_A` is Continue-minus-Quit conditional on `e` continuing.  Therefore

\[
\Delta(x,d;\varnothing)
=r_d(\{x,d\})-r_d(\{x\})\geq\Gamma
\quad\Longrightarrow\quad
h_{\{x\}}\leq-\Gamma.
\]

This is the useful orientation.  Conversely a cycle cancellation

\[
\Delta(x,d;T)\leq0
\]

that lies on the missing face has `A=T union {x}` and gives

\[
h_A=-\Delta(x,d;T)\geq0.
\]

That is exactly the wrong sign for the interior mixing requirement

\[
H_{\rm miss}=-\frac{zL_d}{1-z}
\leq-\frac{z\Gamma}{1-z}<0.
\]

The pair-to-triple incidence calculation is correct: for singleton
background `T={k}`, choosing the fourth label as the other base member makes
`F={x,k}`, so the cancellation is the full-free missing-face term `h_F`.
This is a label-level placement unless the target also returns `d` as debtor,
as the note correctly emphasizes later.

The triple-to-grand exclusion is also exact.  Its background contains both
labels outside `{x,d}`, hence `T union {x}=I\{d}` contains every possible
other base player `e`.  The comparison is consequently conditional on `e`
quitting and belongs to the `L_d` face, never the face defining
`H_missing`.

## 3. Mass threshold

Let `w=nu({x})`.  Under the stated bound on every reward coordinate and on
the continuation coordinate used for the empty term, every remaining
`h_A<=2M`.  Hence

\[
H_{\rm miss}\leq-w\Gamma+(1-w)2M
=2M-w(\Gamma+2M).
\]

Both consequences are algebraically correct:

\[
w>\frac{2M}{\Gamma+2M}\Longrightarrow H_{\rm miss}<0,
\]

and, for fixed `0<z<1`,

\[
w\geq
\frac{2M+z\Gamma/(1-z)}{\Gamma+2M}
\Longrightarrow
H_{\rm miss}\leq-\frac{z\Gamma}{1-z}.
\]

The second threshold can exceed one for some `z`; then it is simply a
vacuous sufficient condition, not an erroneous assertion of availability.
Neither the pair-base Nash law nor full support of the separate singleton
packet supplies this weight.

## 4. Rational separation table

I independently recomputed all specified entries, treating every unspecified
coordinate as zero.

The four singleton gains are exactly one:

\[
0\to1,\quad1\to2,\quad2\to3,\quad3\to0.
\]

For `3->0`, the background `{1}` increment is zero; for `2->3`, the
two-label background `{0,1}` increment is zero.  Thus the advertised
pair-to-triple and triple-to-grand cancellations are literal.

At base `B={0,2}` with free law concentrated on `{1}`, the date-zero coalition
is `{0,1,2}`.  The free-player endpoint pairs are

\[
(Q_1,C_1)=(1,0),\qquad(Q_3,C_3)=(0,0),
\]

so the row is an exact induced Nash point.  Since two base opponents quit at
date zero, these endpoint comparisons are the full unrestricted behavioral
comparisons.  The four terminal-semantic debts are therefore

\[
(d_0,d_1,d_2,d_3)=(1,0,0,0).
\]

Player `0`'s immediate-Quit payoff is zero and its Continue/Never payoff is
one, yielding the claimed full-one first-disagreement row.

For debtor `0`, other base `2`, and free set `{1,3}`, the relevant values are

\[
h_{\{3\}}=-1,\qquad h_{\{1,3\}}=0,
\qquad h_{\{1\}}=1,
\qquad L_0=1.
\]

Because the free law is `delta_{ {1}}`, `H_missing=1`; both the negative
singleton atom and zero nonsingleton cancellation have law mass zero.  Thus
`z L_0+(1-z)H_missing=1` for all `z`, and player `0` strictly prefers
Continue at every softened row retaining that law.  Any exact such row must
put zero Quit probability on `0`.  The regression proves exactly the claimed
interface separation.

The table is not asserted to satisfy the global terminal witness, positive
minimum, punishment-normal/full-core packet, or hard-principal fields.  It
therefore refutes an implication from the displayed collision, induced-Nash,
and debtor-gap interfaces only; it does not refute a theorem using additional
full-residual structure.

## 5. Consumer and export assessment

The surviving positive theorem is useful but not yet executable:

* a four-cycle alternating base puts a correctly signed full-gap singleton
  row in the emergent debtor's missing-face table; and
* a quantitative lower bound on that row's **actual pair-base law weight**
  would imply the displayed negative-average threshold.

No inspected declaration supplies that law weight or constructs an exact
softened root from one coordinate's sign.  The cycle cancellation itself
cannot serve as the consumer because it contributes a nonnegative
Continue-minus-Quit term, and the marked cancellation need not concern the
returned debtor at all.  A single negative debtor average would in any case
not settle the other base player's complementarity or produce a Bellman
edge, floor-safe return, or maintained rank decrease.

Accordingly I recommend retaining the note internally as a sharp source/sign
screen.  Proposition 5.1 is genuinely new relative to the two input notes,
but without a law-weight producer or a multi-coordinate stationary consumer
it does not meet the ordinary conjecture-facing export threshold.

