# Independent check of the canonical finite-repair contraction

Reviewer: CODEX_HILBERT. Ordinary mathematics, not Lean-checked here.

Verdict on the stated conditional inequality: **PASS in the canonical
four-player class**. The argument below was derived independently from the
table and the proposed inequality before reading the author's written proof.
The finite-calendar realization uses zero nonpivot own singletons. It does
not assert convergence of the global repair minima for arbitrary tables.

## Claim and actual domains

Let I={0,1,2,3}, Never pay zero, and |r_i(S)|≤M, with M>0. Assume
s_0=r_0({0})=1 and s_j=r_j({j})=0 for j≠0. All other entries may have
either sign. For N≥1, let F_N={0,…,N−1,Never}. Fixing the three independent
nonpivot laws on F_N, the geometric-repair LP minimizes the full error over
all pivot laws in the infimum sense. Minimize this LP jointly over all three
nonpivot laws, and denote its attained relaxed minimum by m_N.

The finite joint domain has head masses, late pivot mass λ, Never mass ν,
and first late atom α with 0≤α≤λ. Its payoff and cap constraints are finite
continuous polynomial inequalities, with z bounded in [0,2M]. Thus the joint
relaxed minimum is attained, without asserting continuity of a parametric
LP value or behavioral realization at α=0<λ.

If one such minimizing point has m=m_N>0 and prescribed payoff

    U_i≤s_i−η,       η>0,

then the claimed conclusion is

    m_(N+2) ≤ m_N − η m_N²/(128M²).                 (1)

The quantifier is over any global minimizing relaxed point that has the
displayed shortfall. Other minimizers need not have it. No global minimum
over unrestricted profiles, total-debt minimum, periodic source, or common
chronology across N is assumed.

## 1. Root prefix against prescribed U, not against a cap

First let p be a literal geometric source, with E(p)=d and payoff U.
Choose an exact independent mixed Nash root q in the finite one-stage game
with continuation U. Write

    a=1−∏_j(1−q_j),       c_j=∏_(ℓ≠j)(1−q_ℓ).

For player j, Q_j is the root Quit payoff and A_j the payoff contribution
from nonempty opponent root coalitions while j Continues. Let B_j be the
full tail response cap. The literal prefixed profile has

    U'_j=max(Q_j,A_j+c_jU_j),
    B'_j=max(Q_j,A_j+c_jB_j).

The second identity covers every behavioral response: Quit at the first row,
or Continue and use an arbitrary complete tail response. It remains valid
when prescribed joint or own survival is zero; no conditional payoff on a
null event is invoked. Since d_j=B_j−U_j≥0,

    0≤d'_j≤c_jd_j.                                  (2)

If U_i≤s_i−η, then Q_i≥s_i−2Ma. Indeed the event of at least one opponent
root Quit has probability at most a. Also |U'_i−U_i|≤2Ma, since only root
absorption replaces U by a bounded terminal reward. Nash gives U'_i≥Q_i,
and hence

    a≥η/(4M).                                       (3)

Choose k maximizing q_k. The union bound gives q_k≥a/4. For j≠k,
c_j≤1−q_k≤1−a/4, so

    d'_k≤d,       d'_j≤(1−a/4)d  (j≠k).             (4)

These are upper bounds relative to the maximum d, not an assertion that
every other coordinate loses a d/4 from its own old debt.

## 2. Complete-law best-response mixture

Replace only k's complete prescribed stopping law by its mixture with a
full pure best response, with weight θ=a d/(32M). The existence and finite
location of that response are checked in Section 3. Since d≤2M, 0≤θ≤1/16.
One private coin followed by a sampled stopping time realizes this law; it
is not a correlated mixture of whole profiles or a datewise hazard average.

The moved player's cap depends only on its opponents, so its new debt is
exactly (1−θ)d'_k. For each j≠k and each fixed complete response of j,
changing k's law by this mixture changes expected reward by at most 2Mθ.
Taking the supremum preserves the same bound on B_j, while U_j changes by
at most 2Mθ. No differentiability or stability of the maximizing response
is needed. Thus

    d''_k≤d−a d²/(32M),
    d''_j≤d−a d/4+4Mθ=d−a d/8  (j≠k).

Since d≤2M, a d²/(32M)≤a d/8. Consequently

    E(p'')≤d−a d²/(32M)
           ≤d−η d²/(128M²).                        (5)

This calculation works for any literal geometric source with a shortfall;
global minimality enters only when comparing its competitor to m_(N+2).

## 3. Exact response attainment and the two-date bound

After the root prefix, all nonpivot finite atoms are before L=N+1 and the
pivot has a geometric tail starting at L. A pivot response is maximized at
one of {0,…,L,Never}: after L every finite response has payoff W_0+D_0,
while Never has W_0.

For j≠0, write α' for the pivot's first tail atom, λ' for its late mass,
and h=α'/λ' when λ'>0. Let A be j's payoff contribution from opponent
absorption before L, b=r_j({0,j}), v=r_j({0}), and D the probability that
the other two nonpivot players are Never. For ℓ≥0 the exact response value is

    A + D[vλ'(1−(1−h)^ℓ)+bα'(1−h)^ℓ].             (6)

This is a convex combination of its first-tail value A+Dbα' and its Never
value A+Dvλ'. The own singleton is zero, so there is no additional endpoint
from finite stopping after a positive residual all-Never event. Therefore a
full best response is attained in {0,…,L,Never}. If λ'=0, every late finite
response has the same payoff as Never and the conclusion remains true.

After the one-player mixture, every nonpivot law is supported on
F_(N+2)={0,…,L,Never}. The pivot's atoms after L still form a geometric tail;
any changed atom at L is now part of its head. Thus the result is already a
literal admissible source for the repair problem at N+2. A second compression
is permissible but unnecessary. No truncation of a positive geometric tail,
extra response deadline, or approximate best-response limit is hidden here.

## 4. The nonattained LP boundary

At an optimizer with α=0<λ, choose α_n>0 tending to zero with λ, ν, all
head atoms, and all nonpivot laws unchanged. These are literal geometric
sources with exactly the optimizer's prescribed U and errors d_n satisfying

    m_N≤d_n≤m_N+o(1).

The upper bound is the geometric LP's endpoint implementation estimate;
the lower bound follows because each source competes in the same global
repair infimum. Select the exact root against this common U once. It has
the same a≥η/(4M) for every n. Apply the actual construction separately,
with θ_n=a d_n/(32M). Section 3 places each output in the N+2 repair domain.
Thus

    m_(N+2)≤d_n−a d_n²/(32M).

Pass to the real limit d_n→m_N to obtain (1). This is an inequality of
infimum values, not a claim that the boundary optimizer itself is an actual
profile. Cases α>0 or λ=0 are literal and need no approximation.

## 5. Exact overlap and remaining obstruction

The checked source results inspected for this calculation are:

- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`.
- `quittingTerminalDeviationDebt_rootThenContinuation_le` in
  `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
- `quittingTerminalSemanticDebt_stoppingLawMixture_eq_self` and
  `quittingTerminalSemanticDebt_stoppingLawMixture_le_boundChord` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`.
- `exists_exactRoot_terminalExploitability_le_and_debtSum_descent` in
  `UniformEquilibrium/Quitting/Terminal/TerminalDebtPrefixDescent.lean`:
  its direct descent is for SUM debt while preserving the MAX sublevel.
- `minimumTerminalSemantic_exploitabilitySingletonMargin` and
  `minimumTerminalSemantic_exploitabilityIs_allContinuePlateau` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.
  These already imply U≥s at every positive unrestricted MAX-minimizing
  semantic pair. They are not finite-N approximation-rate statements.

The geometric implementation and endpoint formulas are the reviewed ordinary
mathematics of `GEOMETRIC_PIVOT_TAIL_COMPRESSION_AND_EXACT_REPAIR_LP.md`.
The added content of (1) is a concrete two-date MAX-debt decrease at a
finite global repair minimizer with a singleton shortfall. The limiting
plateau U≥s is not new, and no mechanism here rules out that plateau.
Therefore (1) is not a proof that m_N tends to zero.

## 6. Frozen author-draft correspondence

The entire 415-line author draft
`notes/CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_PAYOFF_FLOOR_ESCAPE.md` was then
read and its SHA-256 verified as

    5a719508f3970be8e5e33721c29d44e049e83ad32d069cafba4afe743e762335

**Exact-surface verdict: PASS.** Its complete joint LP, stronger every-root
inequality (R), shortfall consequence (T), literal calendar realization,
and relaxed-boundary argument agree with the independent calculation above.

The following additions in the author surface were also checked:

- N=0 is valid: all three opponent laws are Never, the finite head is
  empty, and each cap maximum still has its displayed late endpoint. The
  prefix/repair has L=1 and lands in the N+2=2 family exactly as stated.
- The arbitrary exact-root form (R) holds even if the singleton deficit is
  zero. If its absorption is zero, it reduces to domain monotonicity; no
  positive θ or positive absorption is silently assumed in that case.
- In the nonattained boundary proof, the author keeps θ=a m_N/(32M)
  fixed rather than using the actual approximant error d_n. The stated
  additive-ε inequalities are correct and still give the same limit.
- The convergence of η_N and of maximal root absorption is uniform over
  all global optimizer choices, since the bounds use only m_N and m_(N+2).
  These conclusions are conditional on a positive limit m_∞.
- Maximal root absorption exists because the exact finite-root set is
  nonempty and closed in a compact product simplex, and absorption is
  continuous. Its vanishing along U_N alone does not justify root
  uniqueness at U_∞ by lower hemicontinuity.

The phrase “increases any cap ... by at most Mα” in Section 1 is read as
the upper estimate B_j(α)−B_j(0)≤Mα, not a claim of monotonicity. With
negative collision rewards an individual cap can decrease. The required
upper estimate, and the objective estimate used in the proof, are valid.
This is only a wording clarification, not a mathematical repair.

No unresolved mathematical objection remains to the frozen statement.

## 7. Approximate-root addendum

The entire 200-line
`notes/CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_APPROXIMATE_ROOT_CLUSTER_ADDENDUM.md`
was independently checked at SHA-256

    10cd17c43b8d2620efae3faa80e11516e7afc045849964ab97c243df595dd9b7

**PASS.** For an arbitrary root, subtracting its prescribed payoff instead
of its larger action endpoint adds exactly its coordinate one-stage Nash
defect e_i to the prefix debt identity. Thus d'_i≤c_i d_i+e_i. The same
private best-response mixture gives

    m_(N+2)≤m_N−a(q)m_N²/(32M)+max_i e_i.

For the moved player, multiplication by 1−θ cannot increase the additive
defect bound; for the others it is unchanged. There is no multiplicative
calendar loss in that error. Pure response attainment and the N+2 shape
depend only on the geometric/finite support structure, not on exact Nash.
At α=0<λ the literal approximants keep U and hence every e_i fixed, so
the same vanishing additive approximation argument remains valid.

For fixed q the Quit endpoint is independent of continuation and both the
Continue endpoint and prescribed root payoff are 1-Lipschitz. The claimed
2‖U−W‖∞ bound on the change in defect is therefore valid. Holding an exact
root at W fixed while letting optimizer payoffs converge to W yields zero
absorption if m_∞>0. This proves uniqueness of the all-Continue root at W
without any lower-hemicontinuity assumption. It is the same qualitative
conclusion as the separately reviewed carrier proof, reached through the
new finite approximate-root inequality; no additional positive-minimum
consumer follows.
