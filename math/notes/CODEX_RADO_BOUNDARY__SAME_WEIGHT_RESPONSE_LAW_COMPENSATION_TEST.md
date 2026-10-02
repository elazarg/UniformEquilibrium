# Same-weight response laws: exact compensation and the unconsumed outer input

Identity: CODEX_RADO_BOUNDARY. Date: 2026-09-08.

## Status

Bounded test stopped. Ordinary mathematics, not independently reviewed or
Lean-checked. No new UE producer, counterexample, or strict reduction of the
actual worst-table source is obtained. The generic joint-response ledger
below is prior machinery, not a new result. The extra check isolates a
specific nonsingleton reward coordinate which can increase its compensation
while leaving the singleton-pressure account and all source caps unchanged.
It does NOT preserve global worst-table ancestry, so it is not a falsifier
to a theorem using the ENTIRE produced source.

## 1. Exact question and genuine source

Use the actual finite silent sources at ONE fixed table supplied by
[the singleton-fiber reduction](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md),
SHA-256 `1fdefe4acb70e12b789e045885bc8711cea707daa059a70daab197623afbaa70`.
There are four players, rewards in [−1,1], zero Never reward, and independent
complete stopping laws. Every behavioral deviation is allowed.

Write U_i(p) for payoff, B_i(p) for the full response cap, E for maximum
debt, and g_(i,t)=U_i(p[i←t])−U_i(p). The SAME retained probability λ on
the complete enlarged response pool plus a zero tester satisfies

    W:=Σ_(i,t) λ_(i,t) g_(i,t)=E−a,
    a→0, E→m>0,
    θ_i:=Σ_t λ_(i,t)≥m/4,
    Σ_a λ_a Dg_a(p)[ν−p]≥−R for every allowed product-law endpoint ν,
    R→0,
    S:=Σ_(i,t) λ_(i,t)[μ_(p[i←t])({i})−μ_p({i})]≤o(1).

The source also has its exact global near-minimality, original/final
worst-table ancestry, and strict pure sure-coalition regret gap. None of
those fields may be replaced by a local KKT point. In particular, the
calibration in §4 below does not furnish a new source with that ancestry.

The selected operation normalizes the SAME owner weights:

    ρ_i(t)=λ_(i,t)/θ_i,
    p_i(x)=(1−x)p_i+xρ_i,  0≤x≤1.

Each player independently mixes two complete laws. No common λ label is
played publicly. Never remains a genuine atom. All original tester labels
are retained separately; equal source payoffs do not identify labels on
the enlarged competitor domain. The zero tester is not allocated to any
ρ_i and contributes zero to the formulas.

Question: do the additional outer-fiber fields force a uniformly negative
SAME-λ derivative along this actual joint-law move?

## 2. Exact double-replacement cancellation

For A⊆I, let p^A replace exactly the marginals in A by their ρ_i, using
independent draws. Define

    h_i=U_i(p^{i})−U_i(p),
    H_ij=U_i(p^{i,j})−U_i(p^i)−U_i(p^j)+U_i(p),  i≠j.

All four terms use literal actual product profiles at the same reward
table. Affinity in one complete law gives W=Σ_i θ_i h_i. Holding λ
fixed while differentiating, one obtains exactly

    J:=Σ_a λ_a Dg_a(p)[ρ−p]
      =−W+Σ_(i≠j) θ_i H_ij.                         (1)

The diagonal term is −θ_i h_i: changing a player's own prescribed law
does not change any of its response values. The off-diagonal term is
the displayed double-replacement difference; the response value itself
changes when another prescribed marginal changes.

Thus the ACTUALLY produced enlarged-domain derivative inequality gives

    Σ_(i≠j) θ_i H_ij≥E−a−R.                         (2)

For separate nonnegative speeds c_j, with x c_j≤1, the exact expression is

    J(c)=Σ_j c_j[−θ_j h_j+Σ_(i≠j) θ_i H_ij].        (3)

Every individual bracket is at least −R, by applying the same source
inequality to the endpoint replacing just j. Near-activity gives
0≤E−h_i≤a/θ_i. These conclusions are the old simultaneous KKT/cross-
amplification mechanism, now with the already-produced enlarged source;
they are not a new restriction.

Even a negative weighted derivative is not by itself a full-regret upper
bound. For the intended contradiction it would suffice to contradict the
source's uniform first-order inequality. To instead claim an actual finite-
amplitude improvement one must control ALL enlarged response gains,
including source-active labels with zero λ weight and new late tests.

## 3. What the singleton normal actually adds to this operation

For the own-singleton payoff coordinate, the source difference is

    S=Σ_i θ_i[μ_(p^i)({i})−μ_p({i})].                (4)

Equation (4) contains no double-replacement law μ_(p^{i,j}). In general
the singleton part of H_ij is its rectangle difference

    μ_(p^{i,j})({i})−μ_(p^i)({i})−μ_(p^j)({i})+μ_p({i}),

which is not the difference in (4). The remaining fourteen reward
coordinates of owner i contribute their own rectangle differences. The
56 frozen coordinates have no retained normality. A sign on (4) therefore
cannot simply be substituted for an upper bound on the compensation in
(1). A new argument from actual global ancestry would be needed.

The already-known A−L identity and the lower bound on delayed singleton
loss/tie alteration mass are not repeated as new consequences here. Nor
does the non-pair finite-event mass floor bound any H_ij from above.

## 4. An exact coordinate check: compensation invisible to source pressure

This is a calibration of the proposed algebraic bound, NOT an asserted
actual worst-table source. Prescribe players 0,1,2 to Quit surely at date
1; player 3 quits at date 1 with probability q∈(0,1), and otherwise Never.
Let the selected response law of every owner be Never, with arbitrary
positive owner weights θ_i. Assume λ is concentrated on those four labelled
Never responses. No global-minimality premise is made in this check.

The prescribed terminal coalitions are {0,1,2} and I. Each of the four
SELECTED Never responses still leaves at least two sure players at date 1.
Hence the prescribed law and these selected responses have no own-singleton
outcome: S=0 exactly, independently of rewards and of q. An unselected
Quit0 response does have its own-singleton outcome and remains in the full
cap; it is not discarded.

Now change ONLY r_0({2,3}) by δ>0, staying within the reward bound.
This changes none of the four prescribed payoffs or complete source caps.
For owner 0, original opponents 1 and 2 remain sure, so none of its pure
responses, including date 0, any tie, any later date, or Never, can produce
{2,3}. Other owners' reward coordinates were not changed. All source gains,
their inactivity, owner weights, and singleton pressure are unchanged.

Nevertheless p^{0,1} has terminal coalition {2,3} with probability q,
whereas p, p^0, and p^1 never have that coalition. Consequently

    H_01(new)−H_01(old)=qδ,
    J(new)−J(old)=θ_0 qδ>0.                          (5)

This increment does not merely preserve the tested joint inequality. For
ANY simultaneous endpoint ν in the retained finite domain, the increment
of its SAME-λ derivative is exactly

    θ_0 qδ · Pr_(ν_1)(T_1>1),                       (6)

where T_1>1 includes Never. The original marginal of player 1 is Quit1.
To first order, only changing that marginal together with the fixed owner-0
Never response can expose {2,3}; changing either of the other prescribed
marginals does not. Thus (6) is nonnegative. If a profile in this shape
already satisfied a given uniform derivative lower bound, increasing this
coordinate could not violate that lower bound.

Strict finite pure-coalition inequalities, when present with slack, survive
sufficiently small reward perturbations by the full-regret Lipschitz bound.
This observation does NOT preserve the exact original/final global maxima,
near-minimizing provenance, or the retained stretch relations as a package.
No such preservation is asserted, and no actual table with positive global
minimum is constructed. Equations (5)–(6) isolate why the scalar pressure
and pointwise first-order fields alone do not remove the compensation.

An exact Fraction check used q=2/5, δ=1/7 and
θ=(1/10,2/10,3/10,4/10). It verified (6) on all 256 independent pure
endpoints with dates 0,1,2,Never, together with all sixteen complete source
response payoffs. Later finite dates equal date 2 in this check. This
checks the coefficient calculation only, not positive global minimality.

## 5. Sources, known/new boundary, and stopping decision

Read completely for this test:

- FRECHET's `STRICT_FIBER_NONPAIR_MASS_AND_NEVER_SINGLETON_TRANSFER`,
  including its stopped two-sided support-promotion test;
- NOETHER's `POSITIVE_SINGLETON_NORMAL_AND_CONTESTED_WINS`, including
  the distinction between tuple normality and one retained scalar source;
- NOETHER's `SINGLETON_PRESSURE_DELAY_OR_TIE_RESIDUAL` and
  `GLOBAL_KKT_TWO_LAW_COMPETITOR_CHECKPOINT`;
- RENY's `SIMULTANEOUS_ACTIVE_RESPONSE_RECOMBINATION_BOUNDARY`;
- TARSKI's `SAME_POTENTIAL_OUTSIDE_FIBER_JOINT_LAW_TEST`.

Narrow comparisons also read HILBERT's two-response rectangle and local
regression sections in `EXTREMAL_REWARD_TABLE_VARIATIONAL_TEST`, and
FRECHET's source/copy/full-compensation sections in
`NORMAL_OWNER_CLOCK_RESAMPLING_AND_FULL_CAP_ACCOUNT`.

Named declarations inspected at their actual sources:
`quittingTerminalPayoff_update_stoppingLawMixture_observer_eq` in
`UniformEquilibrium/Quitting/Paths/FiniteStoppingLawMixture.lean`, and
`quittingTerminalPayoff_twoStoppingLawMixtures_rectangle` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawResetCube.lean`.
Their observer-affine and literal independent-square meanings are precisely
the algebra used in (1); no Lean implementation of this checkpoint is claimed.

Outcome: the normalized same-response competitor is legitimate but does
not currently consume the outer-table source. Equations (1)–(3) duplicate
the known cross ledger, while (5)–(6) identify a concrete nonsingleton
compensation direction invisible to the source singleton normal. The
remaining unproved step is a bound on those double-replacement coefficients
from the GLOBAL original/final worst-table relations, not from a freshly
chosen multiplier or an assumed normality of the selected profile. No new
conditional compiler, mass-floor note, or export is warranted; this first
operation stops here.
