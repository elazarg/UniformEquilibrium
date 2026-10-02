# Persistent-spine quantifiers and the bounded-capacity waist

**Identity:** `SOCIAL_WEIGHT_REVIEW`  
**Status:** proved ordinary reduction from checked declarations; no new
Fin4 consumer.  The current persistent-spine question is a legitimate
contradiction target, but it is not a branch that can coexist with the
hypothetical counterexample.

## 1. Question audited

Let (r) be a four-player quitting reward table.  Suppose that bounded
vectors (v_t) and product roots (x_t) satisfy

\[
 v_t=F_{x_t}(v_{t+1})
\]

and (x_t) is an exact root Nash equilibrium against (v_{t+1}).  The
question asks whether absence of a uniform-equilibrium payoff forces the
existence of such a spine with

\[
 \sum_t q_{t,p}=+\infty
\]

for some fixed player (p), where (q_{t,p}) is (p)'s marginal Quit
probability.

The checked counterexample-side theorem is superficially narrower: it is
stated for `IsCanonicalExactQuittingNashBellmanSpine`, which includes

\[
 |v_t(i)|\le R:=\operatorname{quittingRewardBound}(r).
\]

The first point of this note is that persistence removes this apparent
quantifier difference.

## 2. A persistent bounded exact spine is automatically canonical

Assume only that there is some finite (K) with

\[
 |v_t(i)|\le K
\]

for every (t,i), and that one fixed marginal is nonsummable:

\[
 \sum_t q_{t,p}=+\infty.                                      \tag{1}
\]

Let

\[
 a_t=1-\prod_i(1-q_{t,i})
\]

be the one-row absorption probability.  Since (q_{t,p}\le a_t), (1)
implies that (sum_t a_t=+infty).  Therefore the joint survival product
vanishes from every suffix:

\[
 \prod_{s=t}^{t+n-1}(1-a_s)\longrightarrow0.                 \tag{2}
\]

Use one common bound (B=\max\{K,R\}) in the bounded Bellman
transversality theorem.  Equations (2) and the exact Bellman recursion imply

\[
 v_t(i)=U_i(x_t,x_{t+1},\ldots)                              \tag{3}
\]

for every (t,i), where the right side is the literal terminal payoff of
the root schedule beginning at (t).  That payoff is a subprobability
mixture of the finite terminal rewards, with the remaining Never mass paid
zero.  Hence

\[
 |v_t(i)|\le R.                                               \tag{4}
\]

Thus the supplied bounded exact spine satisfies the canonical reward-cube
bound after all.  Together with its already assumed exact Bellman and exact
root-Nash identities, it is an
`IsCanonicalExactQuittingNashBellmanSpine`.

The checked ingredients are:

- `tendsto_zero_quittingJointSurvivalWeight_of_not_summable_absorption`;
- `eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_`
  `jointSurvival_tendsto_zero` in
  `UniformEquilibrium/Quitting/Paths/JointSurvivalSelection.lean`; and
- `abs_quittingRootSequenceTerminalValue_le` in
  `UniformEquilibrium/Quitting/Cycles/PhaseSwitchDeviationCap.lean`.

No source, minimum, law, or punishment-normality hypothesis enters this
bootstrap.

## 3. Exact counterexample-side negation

The declaration

`all_marginalQuitHazards_summable_of_no_uniformPayoff`

in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/`
`FullSupportHardNashBellmanSpine.lean` states:

> for a bounded Fin4 reward table with no uniform-equilibrium payoff, every
> marginal Quit-hazard stream of every supplied canonical exact
> Nash--Bellman spine is summable.

It has no source-selection or ancestry hypothesis.  Combining it with
Section 2 gives the stronger ordinary statement:

\[
\boxed{
 \text{no Fin4 uniform payoff}
 \Longrightarrow
 \text{every bounded exact Nash--Bellman spine has no persistent marginal}.}
                                                               \tag{5}
\]

Here "bounded" may use an arbitrary spine-dependent finite bound; it need
not be the canonical reward bound in advance.

The same conclusion follows from the checked bounded-capacity theorem.  If
a bounded exact spine had a persistent marginal, (3)--(4) would put every
finite prefix in the canonical exact-block carrier, while its prefix hazard
charges would be unbounded.  This contradicts

`finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`

in
`UniformEquilibrium/Diagnostics/Quitting/`
`FinFourUnboundedExactBlockHazardCapacity.lean`.

## 4. Logical status of the selection question

Equation (5) does **not** refute the desired positive theorem in the usual
unconditional sense.  Rather, under the premise "no uniform payoff," the
repository already proves the negation of the requested output.  Therefore
a proof that the same premise produces a persistent spine would immediately
contradict (5), and hence prove Fin4 uniform-payoff existence.

The correct interpretation is consequently:

> A persistent-spine producer is itself a contradiction certificate for the
> entire bounded-capacity residual.  It is not an additional atlas branch
> which can be selected inside a hypothetical counterexample.

In particular, compactness or graph-directed choice **inside the ordinary
exact Nash--Bellman relation** cannot by itself supply the desired spine.
Under the premise being attacked, every infinite path in that relation has
finite total marginal hazard.

## 5. Why reversing an all-summable spine does not evade (5)

A finite segment

\[
 v_a\xleftarrow{x_a}v_{a+1}\xleftarrow{x_{a+1}}\cdots
 \xleftarrow{x_{b-1}}v_b
\]

can be read in the opposite order as an exact finite forward Bellman block:

\[
 v_b\longrightarrow v_{b-1}\longrightarrow\cdots
 \longrightarrow v_a.
\]

The root at each forward phase is exact Nash against its displayed entering
value.  The only obstruction to periodic repetition is the closing seam

\[
 \Delta[a,b]=\lVert v_b-v_a\rVert_\infty.
\]

If positive-hazard late blocks satisfied

\[
 \frac{\Delta[a,b]}{H[a,b]}\longrightarrow0,
\]

where (H[a,b]=\sum_{t=a}^{b-1}\sum_iq_{t,i}), repetition and a fast
subsequence would give a summable-residual persistent chronology.  This is
the genuine approximate-forward-packet route.

But the checked Fin4 ambient returned-block gap rules it out under no UE.
Closing a finite exact segment into a returned block costs only a fixed
multiple of its endpoint seam.  Therefore
`hasAmbientReturnedBlockRelativeErrorGap_of_fourPlayer_counterexample`
implies one table-dependent (kappa>0) such that every sufficiently late
positive-hazard segment of every canonical exact spine satisfies

\[
 \Delta[a,b]\ge\kappa H[a,b].                               \tag{6}
\]

This deduction, including the cyclic-closing constant, is already recorded
in
`CODEX_STRENGTHEN__FIN4_EXACT_SPINES_ARE_BALLISTIC_TO_PHANTOMS.md`.
Thus finite-segment reversal is exact but its seam is necessarily first
order in its charge.  Ordinary compact recurrence only makes both quantities
small; it does not improve their ratio.

## 6. Correct surviving question

The meaningful source-facing obligation is not to choose a better path in
the same exact graph.  It is to prove that the positive-minimum source
supplies one of the following:

1. exact source-compatible blocks of unbounded total hazard, contradicting
   the checked bounded-capacity conclusion;
2. a restart or regeneration **outside** the ordinary exact-spine graph whose
   total seam is sublinear in the renewed charge;
3. terminal approximate Nash profiles directly from the source-attached
   all-summable tail; or
4. a contradiction between the positive-minimum source passport and its
   necessarily ballistic all-Continue phantom limit.

The hard part is the source-to-restart edge.  A minimum point, terminal law,
marked atom, or response endpoint is not automatically an exact
Nash--Bellman successor of the phantom limit.  Without that literal edge,
bounded capacity is reset rather than spent.

## 7. Nonclaims

- This note does not consume the bounded-capacity branch.
- It does not produce a source restart, a terminal approximation, or a
  persistent approximate spine.
- It does not strengthen the already checked all-summability theorem on its
  canonical domain; it closes the harmless arbitrary-bound wording gap.
- It does not claim that source decorations are useless.  They are exactly
  what a successful construction must use to leave the ordinary exact-spine
  graph.

## 8. The common-prefix response compiler is not a summable restart

The later common-prefix compiler does preserve a literal complete response,
but it cannot by itself supply item 2 of Section 6.  Write

\[
 A_n=W_n\star H_n,
 \qquad
 P_n=W_n\star Y_n,
\]

where (H_n\to Y_n) is a one-player response of suffix gain (g_n), and
the joint survival (c_n) of the copied word satisfies (c_n\to1).  The
exact common-word identity is

\[
 U_q(P_n)-U_q(A_n)=c_ng_n.                                \tag{7}
\]

Consequently, if (g_n\ge g>0) eventually, then

\[
 \lVert U(P_n)-U(A_n)\rVert_\infty\ge {g\over2}            \tag{8}
\]

eventually.  Thus the literal response edge (A_n\to P_n) is a
macroscopic payoff seam.  It is neither summable nor (o(a_n)) for any
charge scale (a_n\le1).

There is also a type distinction.  If (W_n) is exact cap--Nash over
(H_n), it gives an exact admissible predecessor path

\[
 H_n\longrightarrow A_n.
\]

Copying the word onto (Y_n) preserves the behavioral response
(A_n\to P_n), but does not make (W_n) exact over (Y_n).  Hence it does
not give an admissible path to (P_n), and the payoff-near-return consumer
cannot prepend or append this horizontal response as a Nash--Bellman edge.

This does not weaken the common-prefix theorem's intended use.  A finite-rank
minimum-fibre contraction only needs the incoming behavioral edge and a
separately regenerated child source.  It does show that the same compiler
does not secretly solve the persistent-spine restart problem.  To do so one
must either cancel several macroscopic response seams inside one admissible
macro, or construct a different source transition whose executable error is
sublinear in renewed charge.

## 9. Exact cap prefixing cannot damp the response seam

The positive-minimum cap lift gives a stronger obstruction than (8) when the
copied word is the canonical exact cap-prefix word.  Let \(A\) be an actual
profile with total debt \(D(A)\), let \(B\) differ only in player \(i\)'s
complete continuation strategy, and suppose

\[
 U_i(B)-U_i(A)=g>0.
\]

Let \(W_N\) be the first \(N\) exact cap--Nash prefixes constructed outward
from \(A\), and let \(c_N\) be their joint survival.  Exact debt scaling and
global minimality give

\[
 c_ND(A)=D(W_N\star A)\ge D_* ,
 \qquad
 c_N\ge {D_*\over D(A)}.                              \tag{9}
\]

Copy the same prescribed word onto \(B\).  Early terminal outcomes are
identical at the two profiles, while the suffix is reached with probability
\(c_N\).  Hence

\[
 U_i(W_N\star B)-U_i(W_N\star A)=c_Ng
 \ge {D_*\over D(A)}g.                                \tag{10}
\]

In particular, \(W_N\star B\) is still a legal complete response to
\(W_N\star A\), so

\[
 d_i(W_N\star A)\ge {D_*\over D(A)}g.                 \tag{11}
\]

The same conclusion for the two shifted pure-time witnesses uses the
observer-deleted prefix survival, which is at least the joint survival.
Thus neither the inert all-Continue lift nor an infinite summable-absorption
maximal lift makes the response seam tend to zero.  In the inert case the
factor is exactly one; in the nontrivial case it is uniformly bounded below
by the debt ratio in (9).

Applied to the uniformly off-minimum arm of the signed source-retraction
theorem, \(g\) and the source debt ratio both have fixed positive lower
bounds after compactness and reward boundedness.  Therefore that new source
orientation enters the paid-port waist, but cannot by itself enter the
summable-restart waist.  Any successful restart must cancel several response
increments before prefixing, or use a transition not obtained by copying a
single response through the cap word.

This is an ordinary-mathematics corollary of the checked cap-prefix debt
scaling and payoff-shift identities.  It is not a new terminal consumer.
