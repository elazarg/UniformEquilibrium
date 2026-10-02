# An explicit reward-uniform finite portfolio approximation rate

Author: CODEX_SKEPTIC.

## Status and significance

This is an immediate ordinary-mathematical corollary of the existing checked
quantile-clock approximation rate and rational simplex rounding. It corrects
a possible overreading of the earlier statement that a compactness proof
gives no effective rate for a raw enumeration. The repository already has
a stronger structured hierarchy; no new strategic approximation theorem is
claimed here. This corollary has not been independently reviewed or newly
checked in Lean.

There is an explicit, reward-independent finite portfolio P whose minimum
unrestricted regret approximates the true unrestricted regret infimum η(r)
uniformly over all normalized Fin4 reward tables, with a displayed error.
This does not imply that η(r)=0, refine a supplied equilibrium cover to a
smaller accuracy, or prove the conjecture.

## Exact finite portfolio and bound

Fix integers m,D≥1 and put L=8m+1. Let P_{m,D} consist of every independent
four-player product of timing laws on {0,…,L−1,Never}, each marginal having
all probabilities in {0,1/D,…,1}. No public randomization chooses among
profiles: P is a finite list from which a profile may be selected for the
known reward table.

Each marginal is a weak composition of D into L+1 integer counts, so

    |P_{m,D}| = binomial(D+L,L)^4.

For any reward table r∈[−1,1]^60, let E_r(p) be maximum regret against
every complete unilateral behavioral deviation and let

    η(r)=inf_p E_r(p),
    G_{m,D}(r)=min_{p∈P_{m,D}} E_r(p).

Then, simultaneously for every such r,

    0 ≤ G_{m,D}(r)−η(r) ≤ 24/m + 16L/D.              (1)

In particular, for any δ>0 choose

    m≥max(1,ceil(48/δ)),
    L=8m+1,
    D≥max(1,ceil(32L/δ)).

The explicitly enumerable portfolio then has uniform approximation error
at most δ. These parameters are not optimized.

## Proof

The inspected declarations in
`Research/Quitting/EscapeAwareQuantileClockHierarchy.lean` are:

- `quantileClockSupport_fin4`, giving literal support bound 8m+1;
- `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket`, giving
  lower≤η≤upper and upper−lower≤24/m;
- `escapeAwareQuantileClockUpper_sub_exploitabilityInf`, giving the
  corresponding upper approximation estimate directly; and
- `exists_finiteClockSemanticPair_exploitability_eq_upper`, attaining the
  upper value at one actual independent finite-clock law on the very
  support `quantileClockSupport (Fin 4) m`, without an index shift.

The normalized compression input is supplied by
`hasEscapeAwareQuantileClockCompression_of_normalized` in
`Research/Quitting/EscapeAwareQuantileClockTransport.lean`. Its semantic
coordinates include the unrestricted behavioral cap, and its Never atom is
retained literally. Thus, for each r, there is a finite-clock profile p on
{0,…,L−1,Never} with

    E_r(p)≤η(r)+24/m.                                (2)

For each player's marginal probabilities x_t at finite dates t<L, replace
x_t by floor(Dx_t)/D. Assign the residual probability to Never. This is a
valid probability law with the same finite clock. Every finite coordinate
only decreases; the Never coordinate increases by exactly their total
loss. Therefore its marginal total variation distance is

    TV(x,x')=Σ_{t<L} (x_t−floor(Dx_t)/D) ≤ L/D.       (3)

The four marginal TV distances sum to at most 4L/D. Independent product
coupling changes each prescribed payoff by at most twice that sum because
rewards lie in [−1,1]. Against any fixed unilateral deviation, couple only
the opponents. The same bound is uniform over all complete deviating laws,
so it also bounds the change in the full behavioral cap. Each regret and
their maximum consequently change by at most four times the sum:

    |E_r(p')−E_r(p)|≤16L/D.                          (4)

The rounded p' belongs to P_{m,D}. Equations (2)–(4) prove the upper bound
in (1), while η≤G is immediate because every portfolio member is an
actual profile. All choices of p are existential only inside the proof of
coverage: the entire portfolio itself is explicitly determined by m,D and
does not depend on r.

The finite-product estimate was inspected as
`Math.PMFProduct.pmfTV_pmfPi_le_sum` and
`Math.PMFProduct.abs_expect_pmfPi_sub_le_two_mul_sum_pmfTV` in
`MathUE/PMFProduct/TotalVariation.lean`. General stopping-law replacement
contracts to finite outcome-law TV by
`pmfTV_quittingCounterfactualOutcomeLaw_update_le` in
`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`.
The same-clock residual-floor rationalization is already implemented in
`FinFourRationalFiniteClockProfileCompleteness.rationalMass` and the
surrounding completeness declarations in
`Research/Quitting/FinFourRationalFiniteClockProfileCompleteness.lean`.
The elementary one-sided TV bound (3) is enough here; no continuity-only
argument is needed to hide the denominator dependence.

## What the rate does and does not certify

Let Ω=max_{r∈[−1,1]^60}η(r) and C_{m,D}=max_r G_{m,D}(r). The maxima exist:
η and each fixed-profile regret are 2-Lipschitz in reward sup norm, and a
finite minimum remains continuous. Equation (1) gives

    0≤C_{m,D}−Ω≤24/m+16L/D.                          (5)

For a fixed finite rational portfolio, C_{m,D} is an exactly computable
rational finite optimization value. Each E_r(p) is the maximum of finitely
many rational reward-linear forms; the full deviation menu includes the
after-support date L as well as Never. Choosing one active row for each
profile reduces maximum-of-minimum evaluation to finitely many rational
linear programs over the reward cube. The explicit verifier argument is
already recorded in
[the earlier portfolio audit](CODEX_SKEPTIC__FIN4_BLINDSPOT_RESTART.md).

Thus the structured hierarchy and simplex net give a finite, explicit
approximation scheme for the worst-table infimum as well. Running it can be
enormously expensive. No such global run is made here. Most importantly,
(5) does not prove Ω=0: an effective approximation to a nonnegative number
does not decide whether that number is exactly zero. A portfolio would
certify an ε-cover only after its actual computed maximum is below ε.

For a raw exhaustive enumeration, the compactness argument still supplies
no enumeration-index rate by itself. The explicit family above can be
inserted into that enumeration or searched for there, and its known finite
membership supplies a different effective schedule. The absence of a rate
from that particular compactness proof must not be reported as absence of
an effective finite-clock approximation rate in the repository.

No new optimization project, Lean edit, export, or shared-file change was
made. This owned gitignored note and a qualification in the earlier owned
portfolio note are the only mathematical record edits for this check.
