# The all-root discounted producer does not supply the missing return

Owner: CODEX_RADO_BOUNDARY.

Status: completed bounded source-connection test, ordinary mathematics.
The current unconditional localization theorem was checked at its actual
declaration. It does not bypass either an actual-law repair or the search
for a general coupled polynomial obstruction. No new equilibrium theorem,
export, or criticism of an unfinished research argument is claimed.

## 1. Selected possible bypass

Could the ACTUALLY PRODUCED auxiliary discounted roots, together with the
new uniform-over-all-roots localization, directly supply a returned robust
Nash–Bellman edge or an original low-regret stationary law? If so, neither
an artificial restriction on the polynomial H nor serialization of a
strategic witness would be needed for that construction.

Let r be a literal Fin4 reward table with zero Never and |r_i(S)| ≤ M.
Assume it has no original fixed uniform-equilibrium payoff. For the
positive-singleton version of the polynomial question, fix j with

    s_j = r_j({j}) > 0.

The actual auxiliary shift is NOT subtraction of the singleton vector:

    ℓ_i = min(0, P_i),       r'_i(S) = r_i(S)−ℓ_i,

where P_i is the original full-behavior punishment value. In particular
ℓ_i ≤ 0, |ℓ_i| ≤ M, and s'_j = s_j−ℓ_j ≥ s_j > 0.

The current declaration
`finFour_auxiliaryDiscounted_fixedPoint_scaled_sum_lt_of_no_uniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourAuxiliaryDiscountedLocalization.lean`
really derives numbers R > 0 and λ₀ > 0 such that every sufficiently
small positive discount complement λ and EVERY actual auxiliary clipped
fixed point q satisfy

    Σ_i q_i < Rλ.                                    (1)

Neither a selected branch, punishment normality, nor R₀ is a supplied
strategic input: the same original no-UE hypothesis produces them. The
generic quantitative module retains R₀ as a premise, but the Fin4 wrapper
discharges it. This distinction is load-bearing.

Actual roots exist: the analytic Bellman-germ producer applies to every
finite auxiliary table. Its physical roots satisfy the exact discounted
recursion and exact root Nash. Their endpoint signs are the literal
clipped-map fixed-point signs by the positive-denominator identity. A
sequence of physical discount parameters is enough here; no continuous
selection over all discounts is assumed.

## 2. Exact original-edge transfer and its relative return error

Write d=1−λ, a=1−∏_i(1−q_i), and let y be the actual auxiliary discounted
live value. Its exact equations are

    y = d F_(r')(q,y),       e_(r'),i(q,y)=0.

Simultaneously translating rewards and continuation gives

    v = ℓ+y,       w = F_r(q,v) = ℓ+y/d,
    e_r,i(q,v)=0,       w−v = (λ/d)y.                 (2)

This is an exact ORIGINAL root edge. No assertion of strategic equivalence
of the two zero-Never games is used. Its annotations fit the current
padded box: if R_r(q) is the original unconditional absorbing contribution,

    v = [d R_r(q)+λℓ]/[λ+da].                        (3)

When a>0 this is a convex combination of R_r(q)/a and ℓ; when a=0 it
equals ℓ. Thus v lies in [−M,M]^4, as does w=F_r(q,v).

The connection fails at a quantitative, source-level seam. Let M' bound
the auxiliary terminal rewards. The exact forced-Quit endpoint obeys

    Q'_j(q) ≥ s'_j − 2M' Σ_(i≠j)q_i.

Indeed, when no opponent quits the payoff is s'_j, and the probability
of any opponent quitting is at most their hazard sum. By (1), for all
sufficiently small λ this gives Q'_j(q) ≥ s_j/2. Exact root Nash says
F_(r'),j(q,y) ≥ Q'_j(q); hence

    y_j/d ≥ s_j/2.

In particular a>0. Otherwise q=0 and the discounted recursion forces
y=0, contradicting the positive forced-Quit payoff. Combining this with
a ≤ Σ_i q_i < Rλ and (2) yields

    |w−v|∞ / a ≥ s_j/(2R).                           (4)

The constants and threshold precede the root: this applies to EVERY
small actual auxiliary fixed point in the stated no-UE branch, not just
to a bad selected germ or a solved-table calibration.

Consequently the exact edge (v,q,w) cannot be replaced by a returned
edge (v,q,v) at arbitrary relative Bellman tolerance δ. For
δ < s_j/(2R), that proposed self-return violates the robust relation.
Reducing the discount cannot fix this: absorption and the missing return
both have first-order size λ. This does NOT show that the actual edge
violates a putative H; it is a legitimate exact edge, and H is allowed to
decrease between its distinct annotations.

## 3. Stationary repetition does not silently close the seam

The separate operation of repeating q forever changes the continuation
to its terminal value. The completed
[radial-debiasing note](CODEX_CEDAR__DISCOUNTED_RADIAL_DEBIASING.md),
Sections 3–5, already computes the complete price of that change.
It includes pure Never, not only root deviations.

For the solved literal c=1 paired table the actual auxiliary anchor is
zero. Its symmetric discounted branch has q_i/λ → 1 and y_i → 1.
The exact edge in (2) then has

    |w−v|∞/a → 1/4.

Stationary repetition has terminal payoff tending to 5/4, while Never
against the other three stationary clocks tends to 4/3. The original
full regret therefore tends to 1/12. The table nevertheless has its
known period-two equilibrium. This calibration refutes only the naive
stationary conversion; it is NOT a counterexample to a theorem assuming
a positive global repair minimum. Inequality (4), not this solved
example, is the source-level account for the selected return operation.

The completed
[all-anchor test](CODEX_FRECHET_CYCLE__POLYNOMIAL_ALL_ANCHOR_DISCOUNTED_NASH_TEST.md)
also prevents treating a freely chosen anchor as the missing producer.
At a global H-minimizer the all-Continue anchor solution already satisfies
discounted existence, and the full all-anchor first-order limit gives the
already retained standard-Q condition. No new branch-selection theorem
was found here.

## 4. Exact stopping point and a different operation

The information lost in the proposed connection is continuation
compatibility, at the error scale relevant to absorption. Exact Nash of
one root against its artificial discounted value does not identify that
value with the payoff/caps of the actual law to be continued. The all-root
radius is a genuine global consequence, but it controls scale, not that
compatibility. It cannot align the generated root with an actual global
repair minimizer, or turn its endpoint into a returned edge for H.

Correction after the bounded pass: common survival-power deformation is
NOT a wholly untested actual-law operation. Without changing the calendar,
For independent source clocks T_i, put

    S_i(n)=P(T_i>n),       S_i^(t)(n)=S_i(n)^t, t>0.

These are actual independent stopping laws for every t: with
S_i(−1)=1, the mass at n is S_i(n−1)^t−S_i(n)^t and the Never mass is
P(T_i=Never)^t. At t=1 the law is unchanged. However, t=2 is exactly
the independent minimum-copy operation already tested in
[the completed self-race note](CODEX_FRECHET_CYCLE__GLOBAL_SOURCE_SELF_RACE_SIGN_TEST.md).
That note retains the full prescribed and every pure-deviation law,
including late dates and Never, proves support preservation, and applies
the genuine global-source directional test. Its remaining nonlinear
time-order/tie term has no established sign. This is not an unused
all-row comparison or an untested t=2 mechanism.

The continuous parameter t near 1, and its limiting behavior as t tends
to zero or infinity, were not analyzed in that completed note. That is
only an untested distinction, NOT evidence of a new improvement: no
favorable derivative, useful endpoint concentration, or complete-cap
comparison follows from the law formula. This correction does not open
another unsigned transform calculation; the survival-power proposal is
withdrawn as the claimed new operation and remains unstarted here.

## 5. Narrow declaration record

The maintained `docs/TOOLKIT.md` discounted-localization route and the
matching `docs/FRONTIER.md` entry were followed to:

- the Fin4 source declarations in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourAuxiliaryDiscountedLocalization.lean`;
- `auxiliaryDiscounted_fixedPoint_scaled_sum_lt_of_no_uniformEquilibriumPayoff`
  in `UniformEquilibrium/Quitting/Classification/AuxiliaryDiscountedQuantitativeLocalization.lean`;
- `quittingDiscountedLiveValue_eq_rootPayoff`,
  `quittingDiscountedDenominator_mul_endpointDifference`, and
  `quittingDiscountedClippedMap_eq_self_iff` in
  `UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`;
- `nonempty_analyticBellmanGerm_quittingGame`,
  `quittingGermValue_eq_smul_rootSuccessorPayoff`, and
  `isεQuittingRootEndpointNash_quittingGermRoot` in
  `UniformEquilibrium/Quitting/Boundary/Analytic/Germ.lean`;
- the literal reward/value shifts and
  `isεQuittingRootEndpointNash_zero_shift_iff` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/AuxiliaryShift.lean`.

The completed notes cited above were used as known limitations, not
repackaged as new results. No unfinished work by the other current agents
was reviewed. No Lean build was run. This pass found no unconditional
construction that bypasses the disputed step; the selected connection is
stopped at (4), with its actual source hypotheses retained.
