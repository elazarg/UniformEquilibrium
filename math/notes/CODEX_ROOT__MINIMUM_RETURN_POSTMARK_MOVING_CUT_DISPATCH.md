# Minimum-return tails have a uniformly charged moving cut

**Status:** ordinary-mathematics proof draft; not Lean-checked; awaiting
independent review.

## Question

Does the literal post-mark tail in the Fin4 minimum-return packet already
produce the finite two-cut input of
`POSITIVE_MINIMUM_TWO_CUT_COERCIVITY_AND_PAID_SPLICE`, without assuming a
renewed downstream row or a common fixed cutoff?

## Result

Let `s_n` be the literal behavioral continuation after the retained marked
row of a `FinFourMinimumReturnPacket`.  Thus

\[
 D(s_n)\longrightarrow D_*>0.
\]

After one strict subsequence there are a constant `chi>0` and finite moving
cutoffs `L_n>0` such that

\[
 \sum_{t<L_n}\sum_{i\in\operatorname{Fin}4}q_{n,t,i}\ge\chi.
\]

The block is literal in the same `s_n`, its entry cut is zero, and its reach
from the standalone parent `s_n` is exactly one.  Consequently the reviewed
two-cut theorem gives, after further finite-label subsequences, one of:

1. a fixed off-minimum exit-suffix family;
2. a fixed off-minimum paid-target family; or
3. a minimum-fibre paid-target cluster with one fixed payer's debt annihilated
   and an actual same-table paid behavioral edge from `s_n`.

In arm 3 the target profiles themselves admit joint-law compactification,
selection of a positive finite atom at that same target joint point, and
source-faithful causalization.  Thus they reconstruct a complete minimum
source.  This statement does not by itself prove no support entry, a renewable
rank decrease, or a terminal consumer.

The result is weaker than the previously requested two-cut field because it
does not assert that the exit suffix returns to the minimum fibre.  Its point
is that the absence of such return becomes an explicit off-minimum branch;
positive hazard and positive entry reach are not themselves missing.

## Proof

### 1. Joint compactification of the actual post-mark tails

The terminal-semantic carrier is compact.  Pass to a subsequence on which

\[
 z(s_n)\longrightarrow z_*.
\]

Continuity of total debt and `D(s_n)->D_*` give `D(z_*)=D_*`, so `z_*` is a
global minimum.  Apply
`exists_retainedProfile_terminalSemanticLawCluster` to this same subsequence.
After a further strict subsequence,

\[
 \bigl(z(s_n),\mu(s_n)\bigr)\longrightarrow(z_*,\mu_*),
\]

where the joint point belongs to the terminal semantic/law carrier.

The hard-residual theorem
`exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` supplies one
nonempty coalition `S` and a number

\[
 a:=\mu_*(S)>0.
\]

Coordinate convergence gives, eventually,

\[
 \mu(s_n)(S)>a/2.
\]

### 2. Select a finite moving cutoff

For each such `n`, the finite partial masses of the event with terminal
coalition `S` increase to `mu(s_n)(S)`.  Choose a finite `L_n>0` such that

\[
 \Pr_{s_n}(\text{terminal coalition }S\text{ before }L_n)>a/4.
\]

Therefore the probability of some absorption before `L_n` is greater than
`a/4`.  By the elementary union bound for the displayed independent root
hazards,

\[
 \Pr_{s_n}(\text{absorption before }L_n)
 \le \sum_{t<L_n}\sum_iq_{n,t,i}.
\]

Thus the required two-cut hazard floor holds with

\[
 \chi=a/4.
\]

Take `entryCut_n=0` and `exitCut_n=L_n`.  The parent profile for the finite
consumer is the standalone executable profile `s_n`, so its reach at the
entry cut is exactly one.  Every root in the block and the exit suffix are
literal parts of the same post-mark continuation.  The equality identifying
`s_n` as the complete continuation behind the retained marked row remains as
external ancestry.

### 3. Apply the two-cut dichotomy

Put

\[
 K_\chi=(1-e^{-\chi})D_*,
 \qquad
 \delta_\chi=\frac{e^\chi-1}{2}D_*.
\]

For every selected `n`, the two-cut theorem yields either

\[
 D(\operatorname{suffix}_{L_n}s_n)\ge D_*+\delta_\chi,
\]

or a player `p_n` and an actual unilateral behavioral replacement `y_n` of
`s_n` with, after choosing an approximation error `eta_n->0`,

\[
 U_{p_n}(y_n)-U_{p_n}(s_n)
 >K_\chi/8-\eta_n,
 \qquad
 d_{p_n}(y_n)\le\eta_n.
\]

There are only four payer labels.  Pass to a subsequence fixing `p` in the
paid arm.

If the exit arm occurs cofinally, it is the fixed off-minimum exit-suffix
family in Output 1.  Otherwise use the paid arm cofinally.  Compactness gives
a further subsequence on which the paid target semantic pairs converge to a
point `y`.  Global minimality gives `D(y)>=D_*`.  Split again:

- if `D(y)>D_*`, continuity gives a fixed off-minimum paid-target floor;
- if `D(y)=D_*`, then `d_p(y)=0`, while the limiting paid gain is at least
  `K_chi/8>0`.

Since changing only player `p`'s strategy leaves that player's behavioral
best-response cap unchanged, the last statement is exact mover-debt
annihilation at the limiting minimum endpoint, not merely a signed local
defect.

### 4. Same-target source reconstruction in the minimum arm

Jointly compactify the same paid target profiles `y_n`.  Their first
coordinate is the minimum point `y`.  The Fin4 hard-residual minimum-law
theorem selects a positive finite atom at that exact joint point.  The
source-faithful minimum causalization theorem can then be applied to the same
literal target family and its selected marked dates.  This reconstructs a
complete minimum source whose behavioral provenance is the paid family,
rather than an unrelated realization of `y`.

The actual replacements `s_n -> y_n` are retained as the backward paid-edge
compiler.  What is not supplied is a strict renewable support rank: another
coordinate can enter positive debt when `p` is killed.

## Relation to the stronger post-mark renewed-row target

The stronger field proposed in
`CODEX_ADVERSARY__FIN4_POSTMARK_TWO_CUT_SOURCE_ADAPTER.md` asks additionally
for

\[
 D(\operatorname{suffix}_{L_n}s_n)\longrightarrow D_*.
\]

That condition is still not derivable here.  It is exactly what suppresses
Output 1 and forces the paid branch.  The present observation is that a
positive finite atom at the joint cluster already supplies the reach-one,
positive-hazard block; no downstream renewed row is needed for the exhaustive
off-minimum-or-paid dispatch.

## Limitations

1. The marked row preceding `s_n` is a pure absorbing pair, so a replacement
   made inside `s_n` has zero on-path gain when naively reattached behind that
   row.  The paid edge is actual for the standalone parent `s_n`; external
   ancestry alone does not turn it into gain in the earlier forced-pair
   profile.
2. An off-minimum exit suffix is not automatically a complete
   `FinFourUniformEscapePacket`; its retained atom and source fields must be
   reconstructed or a source-independent consumer must be supplied.
3. A minimum paid target kills one debtor but may create a new debtor, so
   support cardinality need not decrease.
4. This result is therefore a genuine finite source dispatch only if its
   three outputs are attached to the maintained off-minimum and renewable
   child consumers.  It does not itself prove a uniform payoff.

## Declarations inspected

- `FinFourMinimumReturnPacket.tailDebt_tendsto_minimum` and
  `FinFourStabilizedForcedPairStream.tail_eq_framePostDateTail` in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`;
- `exists_retainedProfile_terminalSemanticLawCluster` in
  `Research/Quitting/MinimumFiberDebtTransfer.lean`;
- `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- the source-faithful minimum causalization declarations under
  `Research/Quitting/SourceFaithfulMinimumLawCausalization.lean`; and
- `exports/POSITIVE_MINIMUM_TWO_CUT_COERCIVITY_AND_PAID_SPLICE.md`.

## Next question

Can the off-minimum exit and paid-target arms be converted into complete
source nodes while retaining the finite block as an executable backward
compiler, so that the resulting transition enters the existing uniform-
escape or renewable-support consumers without resetting their rank?
