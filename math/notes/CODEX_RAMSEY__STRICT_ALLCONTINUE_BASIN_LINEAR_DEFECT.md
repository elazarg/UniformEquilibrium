# A linear Nash-defect price in a strict all-Continue basin

## Status

Ordinary mathematics.  Proposition 1 and Corollary 2 passed independent
falsification and the whole-packet gate; Proposition 3 is a later exact-
successor strengthening awaiting an addendum review.  The result extends the
reviewed exact-path rigidity and is not a uniform-equilibrium construction or
a checked Lean theorem.

## Question

Let `I` be a nonempty finite player set and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow \mathbb R^I
\]

be a quitting reward table with `|r_i(S)| <= M`, where `M >= 0`.  Write

\[
 s_i=r_i(\{i\}),\qquad
 A(q)=1-\prod_i(1-q_i)
\]

for the singleton payoff and total absorption of a product root `q`.  Let
`Def(V,q)` be `quittingRootTotalNashDefect r V q`.

Suppose `K` is a nonempty compact set of tail payoff vectors such that:

1. there is `delta > 0` with `V_i-s_i >= delta` for every `V in K` and every
   player `i`; and
2. at every `V in K`, all-Continue is the only exact product-root Nash root.

Does exact isolation have a quantitative approximate version uniform over
`K`?

## Proposition 1 (linear absorption price)

Under the hypotheses above, there are an open set `N` containing `K` and a
constant `c>0` such that, for every `V in N` and every product root `q`,

\[
                 c A(q)\ \le\ \operatorname{Def}(V,q).             \tag{1.1}
\]

Consequently, if `q` is an `epsilon`-Nash root at `V in N`, then

\[
                 A(q)\ \le\ {|I|\over c}\,\epsilon.                \tag{1.2}
\]

Here (1.2) is intended for `epsilon >= 0`; existence of such a root already
rules out a genuinely negative error.

### Proof

Represent a root by its marginal quit probabilities `q_i in [0,1]`.  For a
player `i`, let

\[
 O_i(q)=1-\prod_{j\ne i}(1-q_j)
\]

be opponent absorption, and let `Delta_i(V,q)` be the pure Quit-minus-Continue
endpoint difference.  The outsider-Never decomposition is

\[
 \Delta_i(V,q)
   =(1-O_i(q))(s_i-V_i)+J_i(q),\qquad
 |J_i(q)|\le 2M O_i(q).                                             \tag{1.3}
\]

The exact action-probability identity is

\[
 \operatorname{Def}_i(V,q)
 =(1-q_i)\max(\Delta_i,0)+q_i\max(-\Delta_i,0).                      \tag{1.4}
\]

Shrink to an open neighborhood `G` of `K` on which

\[
                         V_i-s_i\ge \delta/2                         \tag{1.5}
\]

for every player.  Put

\[
                 a_0={\delta\over 2(\delta+4M)}>0.                   \tag{1.6}
\]

If `V in G` and `A(q) <= a_0`, then `O_i(q) <= A(q) <= a_0`.  From
(1.3)--(1.6),

\[
\begin{aligned}
 \Delta_i(V,q)
 &\le -(1-O_i)\delta/2+2MO_i\\
 &=-\delta/2+O_i(\delta/2+2M)\\
 &\le -\delta/4.
\end{aligned}                                                        \tag{1.7}
\]

Thus (1.4) gives

\[
 \operatorname{Def}(V,q)
 \ge {\delta\over4}\sum_i q_i
 \ge {\delta\over4}A(q).                                           \tag{1.8}
\]

It remains to charge roots with `A(q) >= a_0`.  Let `X=[0,1]^I`, the compact
product-root simplex.  On the compact set

\[
                 H=K\times\{q\in X:A(q)\ge a_0\},                   \tag{1.9}
\]

the continuous function `Def` is strictly positive.  Indeed, a zero would be
an exact root at a point of `K`; uniqueness would make it all-Continue, whose
absorption is zero, contrary to (1.9).  Hence

\[
                 m:=\min_H\operatorname{Def}>0.                     \tag{1.10}
\]

This lower bound persists on an open neighborhood `G_1` of `K`.  One precise
closed-projection proof is to set

\[
 B=\{(V,q):A(q)\ge a_0,\ \operatorname{Def}(V,q)\le m/2\}.
\]

The set `B` is closed, and its projection to the payoff coordinate is closed
because `X` is compact.  That projection misses `K`, so its complement is the
required `G_1`.  Therefore, for `V in G_1` and `A(q) >= a_0`,

\[
                 \operatorname{Def}(V,q)>m/2\ge (m/2)A(q),           \tag{1.11}
\]

where `A(q) <= 1` was used.

Take

\[
       N=G\cap G_1,\qquad c=\min\{\delta/4,m/2\}>0.
\]

Equations (1.8) and (1.11) prove (1.1).  Finally the checked root-defect
estimate

\[
 \operatorname{Def}(V,q)\le |I|\epsilon
\]

for an `epsilon`-Nash root proves (1.2).  QED.

## Corollary 2 (arbitrary-length approximate stacks)

Consider any finite family of rows indexed by `t`, with every displayed tail
`V_t in N` and every root `q_t` an `epsilon_t`-Nash root at `V_t`, where
`epsilon_t >= 0`.  Then

\[
        \sum_t A(q_t)\le {|I|\over c}\sum_t\epsilon_t.               \tag{2.1}
\]

In particular, the number of rows is irrelevant: a family of stacks whose
*total declared root error* tends to zero has total absorption tending to
zero.  If all tails and rewards are bounded in absolute value by `C`, the
one-edge Bellman motion estimate gives, coordinatewise,

\[
 \sum_t |\operatorname{Succ}(V_t,q_t)_i-V_{t,i}|
 \le {2C|I|\over c}\sum_t\epsilon_t.                                \tag{2.2}
\]

For exact roots, (2.1) gives zero absorption at every row, hence every root is
literally all-Continue.  This recovers the finite part of the open-basin exact
path rigidity theorem, but (2.1) is stronger because it allows arbitrary
stack length and approximate roots provided their *aggregate* defect budget
is controlled.

## Proposition 3 (terminal-near approximate paths cannot exit the basin)

The hypothesis in Corollary 2 that every displayed tail already lies in `N`
can be removed for an actual successor-linked path.

Shrink `N`, without changing Proposition 1, so that it is bounded.  Choose
`C>0` which bounds every reward coordinate and every payoff coordinate on
`N`.  Since `K` is compact and `N` is open, there is `rho>0` such that

\[
 \operatorname{dist}_\infty(V,K)<\rho\quad\Longrightarrow\quad V\in N.
                                                                    \tag{3.1}
\]

Let `V_0,...,V_L` be payoff vectors and, for `0<=t<L`, let `q_t` be an
`epsilon_t`-Nash root against the continuation tail `V_{t+1}`, with
`epsilon_t>=0`, satisfying the exact Bellman successor identity

\[
 V_t=\operatorname{Succ}(V_{t+1},q_t).                              \tag{3.2}
\]

If

\[
 \operatorname{dist}_\infty(V_L,K)<\rho/2,
 \qquad
 E:=\sum_{t<L}\epsilon_t<{c\rho\over4C|I|},                         \tag{3.3}
\]

then every `V_t` lies in `N`, and

\[
 \sum_{t<L}A(q_t)\le {|I|\over c}E,\qquad
 \max_{t\le L}\|V_t-V_L\|_\infty
   \le {2C|I|\over c}E<\rho/2.                                     \tag{3.4}
\]

### Proof

Proceed backward from `V_L`.  Suppose `V_{t+1},...,V_L` have already been
shown to lie in `N`.  Proposition 1 and the checked one-edge motion bound give
for every `k=t,...,L-1` whose tail has been admitted,

\[
 A(q_k)\le {|I|\over c}\epsilon_k,
 \qquad
 \|V_k-V_{k+1}\|_\infty\le {2C|I|\over c}\epsilon_k.                \tag{3.5}
\]

For the current edge `t`, its tail `V_{t+1}` is in `N`, so (3.5) applies.
Together with the already admitted later edges,

\[
 \|V_t-V_L\|_\infty
 \le {2C|I|\over c}\sum_{k=t}^{L-1}\epsilon_k
 \le {2C|I|\over c}E<\rho/2.                                      \tag{3.6}
\]

By (3.3), the triangle inequality gives
`dist_infinity(V_t,K)<rho`; hence (3.1) admits `V_t` to `N` and completes the
induction.  Summing the now-valid one-row absorption bounds proves (3.4).
QED.

Consequently, for any sequence of such paths of arbitrary lengths, if the
terminal distance to `K` and the aggregate root-error budget both tend to
zero, then the whole path diameter and the aggregate absorption both tend to
zero.  In particular there is no fixed-size nonlocal excursion hidden inside
an arbitrarily long, aggregate-error-vanishing exact-successor stack.

Equivalently, every exact-successor path with
`dist_infinity(V_L,K)<rho/2` that reaches even one node outside `N` must pay
the fixed aggregate-error toll

\[
             \sum_{t<L}\epsilon_t\ge {c\rho\over4C|I|}.             \tag{3.7}
\]

For a common per-row error `epsilon`, this says `L*epsilon` is bounded below;
it deliberately gives no length-independent lower bound on `epsilon` when
the row count is unbounded.

The aggregate-error hypothesis is essential.  A per-row bound
`max_t epsilon_t -> 0` with unbounded length does not imply (3.3).

## Finite-four minimum-plateau application

In the reviewed no-uniform Finite-four branch of
`notes/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md`, Proposition 4 gives:

- a compact set of global-minimum carrier pairs;
- a compact prescribed-payoff projection `K`;
- one uniform strict singleton separation on all of `K`; and
- all-Continue as the unique exact root at every point of `K`.

Thus Proposition 1 applies to that whole projection, not merely to one
selected minimum pair.  It upgrades the reviewed exact all-Continue tube to a
linear local price on every approximate absorption row.

The same argument actually covers the whole minimum debt-segment bundle.  If
`M_*` is the compact set of minimum carrier pairs, define

\[
 \mathcal H_*=
 \{\,X.2-t(X.2-X.1):X\in M_*,\ 0\le t\le1\,\}.                     \tag{4.1}
\]

The set `H_*` is compact as the continuous image of
`M_* x [0,1]`.  Proposition 4 supplies one `delta_*>0` with
`X.1_i-s_i>=delta_*` on every minimum pair.  Debt nonnegativity gives

\[
 X.2_i-t(X.2_i-X.1_i)\ge X.1_i,
\]

so the same singleton gap holds throughout every segment.  Finally the
checked declaration
`minimumTerminalSemantic_debtHomotopy_closed_eq_allContinue` applies to each
minimum pair and every `t in [0,1]`.  Therefore Proposition 1 may take
`K=H_*`: one linear-defect neighborhood and one constant control the
prescribed endpoints, envelope endpoints, and every interpolating tail of
every global minimum carrier.

This enlargement matters for cap-Nash iteration because an actual suffix cap
is an envelope endpoint.  It still does not show that a nonminimum cap vector
or an incoming nonlocal tail lies in the resulting neighborhood.

This does **not** close the conjecture.  It says that any local approximate
chronology must pay root error in direct proportion to its absorption.  An
isolated incoming nonlocal edge is not excluded by Proposition 1 alone.
Proposition 3 does exclude a successor-linked nonlocal excursion whose
terminal node approaches `K` and whose *aggregate* error tends to zero.  A
construction with a nonvanishing or nonsummable total error budget remains
open.

## Why the fixed-table diffuse regressions do not refute Proposition 1

`TerminalSemanticFixedTableDiffuseIncidenceRegression.lean` and
`TerminalSemanticFixedTableCapDefectRegression.lean` exhibit fixed-table roots
with order-one carried incidence and vanishing local defect.  In those roots,
however, the smallest singleton-to-tail gap is `q_n=1/(n+2)` and therefore
vanishes at exactly the defect scale.  There is no common `delta>0` as required
in Proposition 1.  The low-absorption estimate (1.7) identifies precisely the
missing hypothesis.

## Exact checked ingredients inspected

- `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart` and
  `quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`;
- `continuous_quittingRootEndpointDifference_simplex` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`;
- `continuous_quittingRootTotalNashDefect_simplex` and the compact
  fixed-incidence moat pattern in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauNashMoat.lean`;
- `abs_quittingOutsiderJoiningContribution_le_two_mul_absorptionMass` in
  `UniformEquilibrium/Quitting/Boundary/Repair/FixedTailUniformAbsorption.lean`;
- `abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass` in
  `UniformEquilibrium/Quitting/Debt/Marked/TimeAdvance.lean`;
- the strict Finite-four minimum plateau and exact tube in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`.

## Nonclaims

- No root or chronological path is produced.
- No approximate incoming edge from outside `N` is excluded.
- No bound follows from uniqueness without the uniform strict singleton gap.
- The theorem controls total absorption, not any chosen player-deleted clock,
  atom, orientation, or conditioned-posterior availability.
- This is ordinary mathematics awaiting independent review, not a checked
  Lean theorem or an export candidate yet.

## Requested check

Please falsify the low-absorption constant in (1.6)--(1.8), the compact
closed-projection step (1.9)--(1.11), and the exact probability/error modes in
Corollary 2.  For Proposition 3, check the backward first-exit induction,
exact head/tail orientation in (3.2), and the factor `4C|I|` in (3.3).  In
particular, check that no fixed-table diffuse regression has a genuinely
uniform strict singleton separation on the compact cap set used by the
proposition.
