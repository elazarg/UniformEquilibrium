# Single-pivot own continuity does not supply marginal continuity

Identity: CODEX_NOETHER_SUPPORT.

Status: this bounded method is closed with an exact obstruction. The
Reny–Prokopovych approximate-equilibrium theorem requires continuity of
opponent-dependent best-response values. For quitting games with nonnegative
own singletons, that global property holds exactly when every player's
reward at every terminal coalition is at most their own singleton reward.
Thus this application adds no coverage beyond the already capped class.
The proof below is ordinary mathematics, not independently reviewed or
Lean-checked. No export or change to the open question is proposed.

## Question and exact strategy spaces

Let I be finite and nonempty, with rewards r_i(S) for every nonempty S ⊆ I.
All coordinates are bounded real numbers. Write s_i = r_i({i}); the raw
canonical question has I = {0,1,2,3}, s_0 = 1, and s_i = 0 otherwise.
All passive and collision rewards remain arbitrary. Never pays zero;
preabsorption payoffs are zero and terminal rewards repeat after absorption.

Let K = ℕ ∪ {∞}, with finite dates isolated and n → ∞. Each player's
space X_i = P(K) has the weak topology. It is compact, metrizable, and convex.
A point μ in ∏_i X_i means independent private draws of complete stopping
times. Before absorption there is one all-Continue history at each date, so
conditional hazards realize precisely these laws as behavioral strategies.
Any complete unilateral behavioral deviation replaces one marginal law.
No convex hull of the joint product-law image is taken.

Let U_i(μ) be the expected terminal payoff, a_i = μ_i({∞}), and
A = ∏_i a_i. Against fixed opponents define F_i(t;μ_−i) as the payoff from
the pure finite date t, V_i(μ_−i) as the payoff from Never, and

B_i(μ_−i) = sup_{ν_i∈X_i} U_i(ν_i,μ_−i).

The proposed use of one exceptional player would need to turn the
nonpivots' own-strategy continuity into hypotheses yielding, for every
ε > 0, one actual product μ with B_i(μ_−i)−U_i(μ) ≤ ε for every i.
An exact Nash theorem and an approximate-equilibrium theorem are different
possible consumers; this note tests a theorem for the latter conclusion.

## Which continuity and security properties really hold

For every fixed finite t, F_i(t;·) is continuous in the opponents' laws:
it is a finite polynomial in their atoms through date t. Independence and
bounded convergence give

lim_{t→∞} F_i(t;μ_−i) = V_i(μ_−i) + s_i ∏_{j≠i} a_j.       (1)

The event where some opponent has a finite clock eventually agrees with
Never; when every opponent chooses Never, a late finite Quit pays s_i.
The unrestricted mixture identity gives
B_i = max(sup_t F_i(t), V_i). If s_i ≥ 0, (1) therefore gives

B_i = sup_t F_i(t).                                       (2)

In particular B_i is lower semicontinuous. Every α < B_i is secured by one
fixed finite date throughout some neighborhood of the opponents: choose
t with F_i(t)>α and use its continuity. Thus the supremum of secure values
equals B_i. The game is payoff secure when all s_i ≥ 0.

The distinctions between kinds of continuity are exact:

- Fix all laws except coordinate j. The resulting function of the pure
  clock T_j has its sole possible discontinuity at ∞, with finite-date
  limit minus its Never value equal to
  r_i({j})∏_{k≠j}a_k. Consequently the entire map
  ν_j ↦ U_i(ν_j,μ_−j) is continuous on X_j if and only if this coefficient
  is zero. At a particular full profile μ, continuity in coordinate j
  holds if and only if r_i({j})A = 0. If μ_j has no Never atom, bounded
  finite-head approximation proves continuity there even when the
  coefficient is nonzero.
- Taking j=i proves that every nonpivot's payoff is continuous in its
  own law against fixed opponents. The pivot's own payoff can have a
  downward jump at a law with a positive Never atom. With s_i ≥ 0 the
  own-law payoff is lower semicontinuous, including that jump.
- U_i is jointly continuous at μ if A=0. A finite cutoff controls the
  remaining reward by its vanishing joint survival probability. If A>0,
  joint continuity holds only when r_i(S)=0 for every nonempty S: otherwise
  replace the Never atoms of players in one such S by atoms at date n.
  The laws converge weakly to μ, while payoffs converge to
  U_i(μ)+A r_i(S), not U_i(μ). These remain independent product profiles.

The single-pivot observation is therefore an own-coordinate statement.
It is neither joint payoff continuity nor continuity of B_i in opponents.

## Exact cap-continuity characterization

Fix a player i and assume only s_i ≥ 0; no sign assumption on other
players' singleton rewards is needed for this player's statement. The
following are equivalent:

1. B_i is continuous at the opponent profile where everybody chooses Never.
2. r_i(S) ≤ s_i for every nonempty S ⊆ I, including coalitions excluding i.
3. B_i is continuous everywhere on ∏_{j≠i} X_j.

Proof of 1 ⇒ 2. At all-Never opponents, B_i=s_i. For any S containing i
with S≠{i}, let precisely its other members choose the pure date n and all
remaining opponents choose Never. These opponents converge to all-Never,
and player i can obtain r_i(S) by choosing n. For S excluding i, let its
members choose n; choosing Never obtains r_i(S). In either case continuity
forces r_i(S)≤s_i. The singleton S={i} is equality by definition.

Proof of 2 ⇒ 3. An elementary finite-head argument makes the upper bound
explicit. For H≥1, let P_i^H be the payoff contribution from opponents'
first stopping coalition strictly before H, with i at Never. Let R_i^H
be the probability that all opponents survive to H. Both depend
continuously on finitely many opponent atoms. Put

C_i^H = max(max_{0≤t<H} F_i(t), P_i^H + s_i R_i^H).        (3)

For every finite own date t≥H, the early contribution is P_i^H. On the
remaining event, every possible payoff is at most s_i, by hypothesis;
Never's zero is also at most s_i. Thus C_i^H bounds every complete reply
and B_i≤C_i^H. At fixed opponents,

P_i^H → V_i,       R_i^H → ∏_{j≠i}a_j,

and (1)–(2) show C_i^H→B_i. Each C_i^H is continuous, so
B_i = inf_{H≥1} C_i^H is upper semicontinuous. Equation (2) already gives
lower semicontinuity, proving continuity. The implication 3 ⇒ 1 is immediate.

The alternative kernel proof agrees: assign s_i at the pure all-Never
tuple while retaining r_i(S) elsewhere. Under condition 2 this kernel is
bounded upper semicontinuous. Its best-response value equals the original
B_i because its altered Never response is precisely the limit (1) of
allowed finite responses. Compact maximization therefore gives upper
semicontinuity. Formula (3) avoids changing even this auxiliary payoff.

For all players with s_i≥0, the game's global marginal-continuity condition
is therefore equivalent to r_i(S)≤s_i for all i and S. In the canonical
case it forces every nonpivot reward, including every passive reward, to
be nonpositive. It also caps every pivot reward by one. This is much
stronger than the own-singleton normalization.

## Exact small tests

A two-player canonical table is

| Terminal S | r_0(S) | r_1(S) |
|---|---:|---:|
| {0} | 1 | 1 |
| {1} | 2 | 0 |
| {0,1} | 0 | 0 |

Against opponent 0 at date n, nonpivot 1 has B_1=1 by waiting. Against
opponent 0 at Never, B_1=0. Against opponent 1 at date n, pivot 0 has
B_0=2 by waiting past n; against Never, B_0=1. Thus both best-response
values fail upper semicontinuity, although only one player has an
own-response jump in (1). The profile with player 0 quitting at date zero
and player 1 at Never is exact terminal Nash, so this is a failure of a
theorem hypothesis, not a failure of approximate equilibrium existence.
Two zero-payoff dummy players embed the same example in the canonical
four-player class: let core coalition membership determine the displayed
rewards and let dummy-only coalitions pay zero.

Even separate continuity in every coordinate of one nonpivot's payoff
does not suffice. On four players, set every reward to zero except
r_0({0})=1 and r_1({0,2})=1. All singleton rewards in coordinate 1 are
zero, so U_1 is separately continuous in every marginal everywhere.
Let players 0 and 2 both choose the pure date n and players 1 and 3 choose
Never. Then U_1=B_1=1, while the all-Never limit has U_1=B_1=0. The laws
are independent, with an exact simultaneous tie, and no correlated
convexification is involved. This table too has the exact equilibrium
where player 0 quits at zero and everyone else chooses Never.

## The primary theorem and why this route stops

I inspected Bich and Laraki, *On the existence of approximate equilibria
and sharing rule solutions in discontinuous games*, Theoretical Economics
12 (2017), Sections 2.2 and 3.3,
[original paper](https://onlinelibrary.wiley.com/doi/pdf/10.3982/TE2081).
Their Definition 2.8 concerns continuity of each best-response value in
opponents. Theorem 2.9 attributes to Reny and Prokopovych existence of
approximate equilibria for compact quasiconcave payoff-secure games with
that property. Definition 2.7 uses a limit of actual ε_n-Nash profiles,
with ε_n→0, so its conclusion is appropriate for all-error existence.

Compactness, own-law affinity/quasiconcavity, and payoff security hold here.
The exact missing hypothesis is marginal continuity. The characterization
above shows that imposing it globally yields only the all-coordinate
capped class, already covered by own-participant capping and hence by the
reviewed supportwise-premium theorem. It cannot extend coverage to raw
canonical reward tables.

The weaker approximately-better-reply-security theorem in their Section
3.3 is not falsified by the examples above. A subsequent, separately
requested bounded check gives an exact solved canonical counterexample
to that weaker condition in the
[approximate-security follow-up](CODEX_NOETHER_SUPPORT__CANONICAL_APPROXIMATE_SECURITY_COUNTEREXAMPLE.md).
Its failure uses a fixed finite supported-action loss that escaping
collision payoffs cannot remove. Neither condition is added as an open
premise to the canonical equilibrium question.

## Bounded repository correspondence

The source route was selected through `docs/TOOLKIT.md` and
`questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md`. Exact inspected
declarations are:

- `IsSinglePivotSingletonTable` and
  `singlePivot_fullExploitability_eq_max_menuExploitability_scalar`
  (`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`).
- `CompactStoppingLaw`, `compactStoppingLawEquivPMF`, and the finite
  clopen-atom continuity facts
  (`MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`).
- `quittingCompactStoppingLawProfile`
  (`UniformEquilibrium/Quitting/Terminal/CompactStoppingLawProfile.lean`).
- `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws` and
  `quittingBehaviorDeviationPayoffCap_eq_pureTime`
  (`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`).
- `quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton`
  and `quittingCompactStoppingLawProfile_cap_le_finiteBound_add_opponentNeverProduct_mul_negPart`
  (`UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`).
- `quittingTerminalPayoff_update_compactStoppingLawProfile_finiteTime_tendsto`,
  `quittingContinuationBestResponseValue_compactStoppingLawProfile_tendsto`,
  and `QuittingOpponentTightAtLawSequence.of_properOpponentLimit`
  (`UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`).

The last existing cap-continuity API requires opponent tightness. Escaping
pure clocks at the all-Never boundary fail exactly that condition. The
negative-singleton correction and fixed finite-response continuity are
already implemented; the global reward-cap equivalence was not found in
this narrow source check. Finite one-stage continuity in
`UniformEquilibrium/Quitting/Root/NashDefectContinuity.lean` is a different
topological statement and does not repair this boundary.

The existing CODEX_RENY finite-timing boundary-security note and CODEX_HILBERT
global better-reply-security note were read to avoid duplicating an exact
Nash claim or overlooking the secure-cap argument. Their notes were not
used as authority for a Lean or paper theorem. Only one primary paper was
consulted for this bounded route. No files outside `math/` were changed.

Next requested check: an independent reader can verify the necessity test
at all-Never and the continuous finite-head envelopes (3). This is a
method-boundary result; the raw canonical existence question remains open.
