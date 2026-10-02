# Quantitative capacity of support-approximate exact-Bellman packets

**Identity:** CODEX_ADVERSARY  
**Status:** central theorem independently reviewed and approved after the
Section 4 correction below; not yet Lean-checked as one declaration  
**Scope:** arbitrary finite nonempty player set; unrestricted behavioral
deviations  
**Export status:** candidate only after independent falsification review

Independent review:
[`CODEX_ADVERSARY__QUANTITATIVE_SUPPORT_PACKET_CAPACITY__BY_CODEX_STRENGTHEN.md`](../feedback/CODEX_ADVERSARY__QUANTITATIVE_SUPPORT_PACKET_CAPACITY__BY_CODEX_STRENGTHEN.md).

## 1. Result

Let `I` be a finite nonempty player set, let `r` be a finite quitting reward
table, and suppose

$$
\gamma>0,
\qquad \operatorname{HasTerminalExploitabilityGap}(r,\gamma).   \tag{1.1}
$$

Write

$$
B=\operatorname{quittingRewardBound}(r),
\qquad C=2+7B,                                                \tag{1.2}
$$

and define

$$
\delta_*=
\frac{(\sqrt{C^2+12\gamma}-C)^2}{144}.                        \tag{1.3}
$$

Then `delta_*>0`.

Fix a compact set `K` of payoff vectors and a tolerance

$$
0<\delta<\delta_*.                                            \tag{1.4}
$$

Choose any finite set `F` of centres whose closed `delta/3` balls cover `K`,
and put `m=|F|`.

### Theorem 1 (explicit compact-cover charge cap)

Every finite sequence of payoff vectors `U_0,...,U_H` and product roots
`p_0,...,p_{H-1}` satisfying

$$
U_t\in K                                                       \tag{1.5}
$$

for `0<=t<=H`, the literal Bellman recursion

$$
U_{t+1}=F_r(p_t,U_t)                                          \tag{1.6}
$$

for `t<H`, support-local approximate Nash

$$
\operatorname{IsQuittingRootSupportApproxNash}
  (r,U_t,\delta,p_t),                                         \tag{1.7}
$$

and the behavioral punishment-floor inequality

$$
P_i-\delta\le U_{t,i}qquad(i\in I,\ 0\le t\le H)             \tag{1.8}
$$

has total raw absorption bounded by

$$
\boxed{
\sum_{t<H}\bigl(1-\prod_{i\in I}(1-p_{t,i})\bigr)<2m.}
\tag{1.9}
$$

Equivalently, there is no
`QuittingFiniteForwardPacket r K delta (2*m)`.

The cap is explicit relative to a chosen finite cover.  Compactness guarantees
that at least one such finite cover exists.  Optimizing over covers replaces
`m` by the corresponding covering number; no optimal-cover existence is
needed for the theorem.

### A coordinate-bound-only threshold

If `n=|I|` and every terminal reward coordinate satisfies

$$
|r(S)_i|\le M,                                               \tag{1.10}
$$

then

$$
B\le n(2^n-1)M.                                             \tag{1.11}
$$

Thus Theorem 1 remains valid with

$$
C_M=2+7n(2^n-1)M,
\qquad
\delta_{*,M}=
\frac{(\sqrt{C_M^2+12\gamma}-C_M)^2}{144}                  \tag{1.12}
$$

in place of `C,delta_*`.  A simpler, slightly weaker sufficient condition is

$$
0<\delta<
\min\left\{\frac\gamma{24},
            \frac{\gamma^2}{16C_M^2}\right\}.              \tag{1.13}
$$

## 2. Proof of Theorem 1

Assume contrary to (1.9) that the total absorption is at least `2m`.  Label
each `U_t` by a centre of a closed `delta/3` ball containing it.  The finite
charged-return lemma, with each stage absorption in `[0,1]`, gives indices

$$
0\le s<t\le H                                               \tag{2.1}
$$

such that

$$
\operatorname{dist}(U_s,U_t)<\delta                         \tag{2.2}
$$

and the intervening raw absorption is at least one:

$$
1\le\sum_{u=s}^{t-1}
 \bigl(1-\prod_i(1-p_{u,i})\bigr).                          \tag{2.3}
$$

For clarity, the factor `2m` comes directly from
`exists_close_pair_with_large_charge_gap_of_finite_labels`, applied to the
labels given by the supplied cover.  The more general checked theorem
`exists_charge_threshold_for_close_pair_of_compact` chooses a cover
internally and does not expose the cardinality of an arbitrarily prescribed
cover.

Reverse the literal forward block from `s` to `t`.  The product estimate used
by the checked forward-block compiler gives whole-block weighted absorption

$$
1-\prod_{u=s}^{t-1}(1-q_u)\ge\frac12,                       \tag{2.4}
$$

where `q_u` is the stage absorption.  Indeed, (2.3) and

$$
\prod_u(1-q_u)\le\frac1{1+\sum_u q_u}
$$

give (2.4).

The reversed block is a finite single-seam projective lasso with error

$$
e=2\delta.                                                  \tag{2.5}
$$

The fields are exact:

- (1.6) makes every nonclosing policy equation exact;
- (1.7) supplies support error `delta`;
- (2.2) supplies seam error at most `delta` coordinatewise;
- (2.4) gives
  `delta <= (2*delta) * weightedAbsorption`; and
- (1.8) is stronger than the lasso rationality requirement
  `P_i-2*delta <= U_{u,i}`.

The checked theorem
`QuittingFiniteSingleSeamProjectiveLasso.exists_supportRationalDivergentPath`
then supplies a divergent root path with support error `2e=4delta` and
rationality error `2e=4delta`.  Apply the checked quantitative path compiler
`exists_isεAsymptoticNash_of_divergentAbsorption_supportRationalPath` with

$$
\text{support error}=4\delta,
\qquad
\text{rationality error}=4\delta.                          \tag{2.6}
$$

It produces an actual terminal behavior profile satisfying the Nash
inequality against **every unrestricted behavioral unilateral deviation** at
error

$$
2(4\delta)+4\delta+
 \sqrt{4\delta}\,(2+7B)
=12\delta+2C\sqrt\delta.                                  \tag{2.7}
$$

On the other hand, (1.1) supplies, against that same behavioral profile, a
player and an unrestricted behavioral deviation gaining at least `gamma`.
Therefore

$$
\gamma\le12\delta+2C\sqrt\delta.                           \tag{2.8}
$$

If `x=sqrt(delta)`, the positive solution of

$$
12x^2+2Cx=\gamma
$$

is

$$
x_* = \frac{\sqrt{C^2+12\gamma}-C}{12}.
$$

Condition (1.4) says `x<x_*`, so (2.8) is impossible.  This proves (1.9).
QED.

For (1.11), there are `2^n-1` nonempty quitting coalitions and `n`
coordinates in the sum defining `quittingRewardBound`.  For (1.13), the two
strict bounds give respectively

$$
12\delta<\gamma/2,
\qquad 2C_M\sqrt\delta<\gamma/2,
$$

and `C<=C_M`.

## 3. Equivalent orbit and packet formulations

### Corollary 2 (no divergent fixed-carrier orbit below the gap scale)

Under (1.1)--(1.4), no infinite sequence `(U_t,p_t)` can satisfy
(1.5)--(1.8) at every date and have

$$
\sum_{t=0}^{\infty}
 \bigl(1-\prod_i(1-p_{t,i})\bigr)=+\infty.                \tag{3.1}
$$

Otherwise one finite prefix reaches the cap `2m`.

### Corollary 3 (null-error arbitrary-charge packets are terminal)

Suppose one fixed compact carrier `K` has the following property.  There are
`delta_j>0` tending to zero, and for every `j` and every charge target `R>=0`
there is a `QuittingFiniteForwardPacket r K delta_j R`.  Then the game has a
uniform-equilibrium payoff.

For any requested positive support tolerance, choose a smaller `delta_j`.
Support-local Nash is monotone in the tolerance, and
`P-delta_j >= P-requestedTolerance`, so the same packet satisfies the weaker
rationality requirement.  This supplies exactly the quantifiers of the
checked theorem
`quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets`.

Theorem 1 is stronger inside a terminal-gap branch: it says that one fixed
sufficiently small error already has a finite charge cap.  It does not need
packets at all errors.

## 4. Fin4 switch-row application

Now assume `I=Fin 4`, rewards are coordinatewise bounded by `M`, and the
hard source selects distinct `a,k` with

$$
r_k(\{a,k\})-r_k(\{a\})\ge\gamma.                         \tag{4.1}
$$

Assume also that the common carrier is contained in `[-M,M]^(Fin 4)`.  For
the two-active row

$$
p_a=1-\varepsilon,qquad p_k=t,qquad 0<t<1,               \tag{4.2}
$$

support-`delta` Nash at `k` forces

$$
\varepsilon\ge
\frac{\gamma-\delta}{\gamma+2M}                           \tag{4.3}
$$

when `delta<gamma`.  Inequality (4.3) is a lower bound on the owner's
**Continue** probability; by itself it gives no positive absorption floor.
If a construction separately chooses equality in (4.3), then the owner's
Quit probability is

$$
1-\varepsilon=
\frac{2M+\delta}{\gamma+2M}\ge\frac12,                    \tag{4.4}
$$

using the checked inequality `gamma<=2M`, and that specially chosen row has
stage absorption at least one half.  More generally, an independent bound
`epsilon<=barEpsilon<1` gives absorption at least `1-barEpsilon`.

### Corollary 4 (finite number of switch rows with supplied charge floor)

Fix `0<delta<delta_{*,M}` and a finite `delta/3` cover of the common compact
carrier with `m` centres.  In any exact-Bellman support-`delta` prefix above
`P-delta`, fewer than `4m` dates can carry a switch row for which equality is
chosen in (4.3).

Indeed `N` such dates contribute raw absorption at least `N/2`, while
Theorem 1 gives total absorption `<2m`.

More generally, if the selected switch rows satisfy the independent bound
`epsilon<=barEpsilon<1`, then their
number is strictly less than

$$
\frac{2m}{1-\bar\varepsilon}.                             \tag{4.5}
$$

This is the exact obstruction to an indefinitely iterable two-root switch
orbit once a fixed positive charge floor is supplied.  Support optimality
alone does not supply that floor: `epsilon` may approach one and the second
mover's Quit probability may approach zero while (4.3) still holds.

The canonical source-faithful descreening does not reach the small-error
regime.  It has `epsilon=gamma/(8M)`, `t=1/2`, and endpoint difference at
`k` at least `gamma/2`.  Since both actions of `k` are supported, its
`QuittingFiniteForwardPacket` support error is at least `gamma/2`, not merely
the probability-weighted root defect `gamma/4`.  Also
`delta_*<gamma/12`, so this row lies far outside Theorem 1's usable range.

Corollary 4 is a consumer, not a producer.  To turn it into a contradiction
proof, the Fin4 source must place arbitrarily many small-support-error switch
rows on one literal exact-Bellman forward orbit in one compact carrier while
retaining (1.8).  The current packet mass, collision row, and independently
indexed minimum-return profiles do not supply those successor equalities.

## 5. Novelty and checked dependencies

No current declaration located in the named subtree states Theorem 1
directly.

- `exists_singleSeamProjectiveLasso_of_finiteForwardPackets` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets`
  require a producer for every positive support error and every nonnegative
  charge target.  They do not expose the fixed-error charge cap forced by a
  terminal gap.
- `QuittingTerminalExploitabilityWitness.false_of_uniform_reachable_packet_producer`
  concerns exact paths in the punishment-floor reachable charged relation.
  It does not cover support-approximate forward packets.

The smallest genuinely new **strategic** lemma is the following quantitative
one-lasso exclusion:

> If a terminal-gap witness has gap `gamma` and there is a
> `QuittingFiniteSingleSeamProjectiveLasso r H e` with `e>0`, then
> $$
> \gamma\le 6e+(2+7B)\sqrt{2e}.                            \tag{5.1}
> $$

Its proof is only the named lasso-to-path theorem followed by the named
support-rational path compiler and one application of the witness's
unrestricted deviation.  No new game construction is involved.

The smallest genuinely new **packet/topology** wrapper says that one
support-`delta` forward packet whose charge reaches `2m`, for an `m`-centre
`delta/3` cover of its carrier, produces a single-seam lasso at error
`2delta`.  This is the single-packet specialization of the proof already
inside `exists_singleSeamProjectiveLasso_of_finiteForwardPackets`; its current
public statement exposes only the all-errors/all-targets producer quantifier.

Composing those two lemmas gives Theorem 1.  For formalization, separating
them is preferable: (5.1) is the reusable terminal-gap interface, while the
cover-cardinality wrapper contains all finite-return bookkeeping.

Theorem 1 is the quantitative single-packet composition of the following
checked declarations:

- `Math.exists_close_pair_with_large_charge_gap_of_finite_labels`,
  `MathUE/FiniteChargedReturn.lean` (and the compact wrapper in
  `MathUE/CompactFiniteChargedReturn.lean`);
- `QuittingFiniteForwardPacket` and the proof ingredients of
  `exists_singleSeamProjectiveLasso_of_finiteForwardPackets`,
  `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`;
- `quittingFiniteSingleSeamProjectiveLasso_of_reversedForwardBlock`,
  `UniformEquilibrium/Quitting/Projective/ForwardBlockSingleSeam.lean`;
- `QuittingFiniteSingleSeamProjectiveLasso.exists_supportRationalDivergentPath`,
  `UniformEquilibrium/Quitting/Projective/SingleSeamProjectiveLasso.lean`;
- `exists_isεAsymptoticNash_of_divergentAbsorption_supportRationalPath`,
  `UniformEquilibrium/Quitting/Paths/SupportWitnessPathCompiler.lean`; and
- `QuittingTerminalExploitabilityWitness.terminalExploitability`,
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityWitness.lean`.

The Fin4 application additionally uses:

- `FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`,
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`; and
- `terminalExploitabilityGap_le_two_mul_bound`,
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalTerminalGapConstrainedStationary.lean`.

No Lean source or export was modified.
