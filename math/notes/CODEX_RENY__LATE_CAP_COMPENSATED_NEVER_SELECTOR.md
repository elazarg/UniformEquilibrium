# A late-cap-compensated Never selector with global pivot repair

Author: CODEX_RENY.

Ordinary mathematical proof draft, not newly checked in Lean. The theorem
below produces a compact coupled fixed-point set from EVERY canonical
four-player reward table and bounds the full repair value at EVERY point
of that set. It does not prove that its positive residual tends to zero.
The construction changes the outer response objective, not the original
game or the inner repair objective.

The proved residual is

    L ≤ max_j {β_j z_j + D[b_j α−a_j λ]₊}
      ≤ η + 2M λD.                                      (R)

Here λ is pivot LATE FINITE mass, ν is pivot Never mass, and D is the
product of the THREE nonpivot Never masses. In particular λD is NOT
all-player Never mass; that mass is νD. The added Never compensation
need not be small. Its contribution to original regret is small only
after weighting by the player's prescribed Never probability.

## 1. Game, full caps, and the actual finite repair data

Players are I={0,1,2,3}. For every nonempty S⊆I a reward vector r(S)
is given, with |r_i(S)|≤M and M≥1. The own singleton vector is

    r_0({0})=1,    r_j({j})=0 for j=1,2,3.

Every other singleton entry and every nonsingleton reward is arbitrary
and signed. Each player independently chooses a stopping law on
ℕ∪{Never}. The first finite stopping time pays the reward of ALL players
quitting at that time; all Never pays zero. Before absorption there is
only the all-Continue history. Consequently a complete unilateral
behavioral replacement has the payoff of a stopping law, and its cap is
the supremum of all pure finite-time and Never payoffs. Write U_i for
prescribed payoff, B_i for this full cap, d_i=B_i−U_i, and E=max_i d_i.

Fix N≥1 and let F_N={0,…,N−1,Never}. Nonpivots choose actual laws
p_j∈Δ(F_N). Set

    z_j=p_j(Never),    D=z_1 z_2 z_3,
    D_j=∏_{k∈{1,2,3}\{j}} z_k,
    a_j=r_j({0}),      b_j=r_j({0,j}).                    (1)

The pivot's compact convex closed repair domain K_N consists of

    m=(x_0,…,x_(N−1),λ,ν,α),
    x_t,λ,ν≥0,    Σ_t x_t+λ+ν=1,    0≤α≤λ.               (2)

If λ>0 and α>0, its literal law has the head x, Never mass ν, and

    μ_0(N+k)=α(1−α/λ)^k,    k≥0.                        (3)

Thus α/λ is the hazard of the conditional FINITE component, not the
actual hazard if ν>0. The actual tail hazard at N+k is its atom divided
by ν+λ(1−α/λ)^k. If λ=0, the head and Never law is literal. The face
α=0<λ is a compactification point, not a law with positive finite mass
and no finite atoms.

For every m, define the provisional ACTUAL law

    μ_0^prov=Σ_{t<N}x_tδ_t+λδ_N+νδ_Never.                (4)

Let Q_t be the pivot's pure response payoff at t<N against p, and W_0
its pure Never payoff. The exact pivot cap and its prescribed payoff are

    B_0=max({Q_t:t<N}∪{W_0,W_0+D}),
    U_0=Σ_{t<N}x_t Q_t+λ(W_0+D)+νW_0.                   (5)

For j≠0 let π_j,t be its pure payoff at t<N against (4) and p_−j.
Let A_j be the expected contribution from absorption strictly before N
when j chooses Never. This includes early pivot absorption and early
nonpivot absorption. Finite conditioning gives the endpoint values

    W_j=A_j+D_j a_jλ,         C_j=A_j+D_j b_jα,
    U_j=Σ_{t<N}p_j(t)π_j,t+z_j W_j.                     (6)

Here W_j is the actual pure Never payoff. C_j is the first late response
endpoint. The limiting late endpoint equals W_j because j's own
singleton is zero. For (3), every late finite response is between C_j
and W_j; explicitly its value at N+k is

    W_j+D_j(b_jα−a_jλ)(1−α/λ)^k.

The exact closed objective is

    L(m,p)=max(0, B_0−U_0,
               π_j,t−U_j, W_j−U_j, C_j−U_j : j≠0,t<N). (7)

For literal (3), or λ=0, this equals full behavioral E. The established
geometric repair theorem also identifies min_{m∈K_N}L(m,p) with the
infimum over ALL pivot stopping laws against these three laws. This
identification includes the potentially nonattained face α=0<λ.
It is used here as an existing exact repair theorem, not proved by
Kakutani or inferred from finite-menu equilibrium existence.

## 2. The adjusted rule and its own-law independence

Fix any η≥0 and any vector β∈[0,η]^3. Define

    Δ_j(m,p_−j)=[C_j−W_j]₊
                =D_j[b_jα−a_jλ]₊,
    γ_j=Δ_j+β_j.                                        (8)

The rule asks for a simultaneous fixed point of

    m∈argmin_{m'∈K_N} L(m',p),
    p_j∈argmax_{q_j∈Δ(F_N)}
       {U_j(m,q_j,p_−j)+γ_j(m,p_−j)q_j(Never)}, j≠0.    (9)

The pivot optimizes ORIGINAL full exploitability, without subsidies.
Each nonpivot optimizes its original finite-menu payoff with the
specified planned-Never subsidy. These are synthesis objectives; the
original quitting game has not acquired transfers, observation of hidden
plans, or detection of a deviation.

To check the apparently delicate own-law issue, A_j is computed with j
replaced by pure Never and π_j,t with j replaced by pure t. Neither uses
p_j. In the difference C_j−W_j, A_j cancels altogether. The remaining
factors a_j,b_j are fixed rewards, α,λ are pivot coordinates held fixed
in j's best response, and D_j contains only the OTHER TWO nonpivot laws.
Thus Δ_j is genuinely independent of q_j throughout (9), not merely
at a fixed point or on a selected support face. This is also true when
some z_k=0, λ=0, α=0, or α=λ; there is no division by any such value.

All expressions in (5)–(8) are jointly continuous in the finite
coordinates. The original prescribed payoff is affine in j's law,
and so is its subsidized objective. For fixed p, L is a finite maximum
of affine functions of m and therefore convex in m. Every argmin and
argmax in (9) is nonempty compact convex; their correspondences are
upper hemicontinuous by continuity on fixed compact domains. Their
product has a fixed point on K_N×Δ(F_N)^3 by Kakutani.

This proves existence for EVERY table above, EVERY N≥1, and EVERY
β∈[0,η]^3, not only a generic reward table or a specially chosen rate.
The entire fixed-point set has closed graph in β and is compact.
Consequently minimizing L, or λD, over all β∈[0,η]^3 and all fixed
points is well-defined and attained at each fixed N,η. No continuous
choice of LP optimizers is required. An exact minimization selector on
a compact set is not thereby an executable numerical algorithm for
arbitrary real reward data.

## 3. Full-regret bound at every fixed point

At a fixed point, the maximum subsidized pure menu value is exactly

    V_j^aux=U_j+z_jγ_j.

Every original finite menu value π_j,t is at most V_j^aux. Also

    max(W_j,C_j)=W_j+Δ_j≤W_j+γ_j≤V_j^aux,

because the subsidized Never action is one of the available actions.
Therefore EVERY endpoint in (7), including both late endpoints and
Never, is at most V_j^aux. Writing d_j for the corresponding closed
full cap minus U_j gives

    0≤d_j≤z_jγ_j
       =β_j z_j+D[b_jα−a_jλ]₊.                         (10)

Nonnegativity follows also directly because U_j averages the prescribed
finite and Never endpoints. No conditional-on-reach regret estimate is
used. The factor z_j is the probability of actually selecting the only
subsidized action, not an opponent survival mistakenly inserted later.
If z_j=0, (10) gives exact zero full debt for that player.

At ANY global pivot minimizer m, independent of the outer equations,

    L(m,p)≤max(0,d_1,d_2,d_3).                           (11)

Indeed suppose the right side is strictly smaller than L. Then the
pivot is the sole maximal debtor and d_0=L>0. Its cap B_0 is fixed by
p, and one of the finitely many candidates in (5) attains B_0. The
corresponding pure pivot law has a feasible point m* with d_0(m*,p)=0.
For m_θ=(1−θ)m+θm*, pivot debt is (1−θ)L. The finitely many nonpivot
gain functions in (7) are continuous (in fact affine) in θ, and at
θ=0 are ALL strictly below L. For sufficiently small θ>0 they remain
strictly below L, while pivot debt is strictly below L. This contradicts
global optimality of m. This argument works on every boundary face of
K_N and does not assume a behavioral realization of its initial point.

Combining (10) and (11) proves the first inequality of (R). Since

    [b_jα−a_jλ]₊≤|b_j|α+|a_j|λ≤2Mλ,

the second follows. There is no factor N, no predetermined support,
and no restriction to a selected LP minimizer or fixed-point branch.

The point of (10) is NOT that γ_j≤η: this is generally false.
Although β_j≤η, the endogenous Δ_j can be of order M. Its ORIGINAL
regret cost is z_jΔ_j=D[b_jα−a_jλ]₊. Treating (9) as η-Nash in the
original finite game without this weighted cost would be incorrect.

## 4. Closed-boundary realization and what is preserved

For a fixed m and p, every original prescribed payoff and every nonpivot
pure response in F_N is independent of the distribution of the pivot's
late finite mass, provided λ and ν are retained. If some nonpivot
chooses a finite time, the first such time precedes N and only the pivot
head and survival through that time matter. If all nonpivots choose
Never, only whether the pivot eventually quits matters. This proof
works for every replacement q_j on F_N, not just prescribed support.

Thus (4) gives common actual finite-menu payoffs even at α=0<λ. It
does NOT implement the closed full caps C_j at that boundary. To get
full behavioral control there, take 0<α'≤λ tending to zero and use
(3) with α'. Original U_i and EVERY old finite-menu response payoff
are unchanged; only the first late endpoint in (7) changes. Its change
has absolute value at most D_j Mα'≤Mα'. Consequently the resulting
ACTUAL product profile satisfies

    E≤L(m,p)+Mα'≤η+2MλD+Mα'.                            (12)

All three finite nonpivot laws and every Never mass are retained.
With the OLD numerical subsidies γ_j from (8), their exact old-menu
best-response equations are retained too. If compensation is instead
recomputed at the new first atom, then

    |Δ_j(α')−Δ_j(0)|≤M D_jα'.                           (13)

The original fixed law is then an M D_jα'-best response for that newly
compensated finite objective: for any replacement its change in bonus
gain is (q_j(Never)−z_j)(Δ_j(α')−Δ_j(0)). Exact fixed-point membership
and exact global pivot optimality at the changed point are NOT claimed.
They are unnecessary to retain the actual full bound (12).

In particular nonattainment has not supplied an imaginary profile, and
the provisional law is not silently used as a full-cap realization.
The actual tail can subsequently be finitely censored with arbitrarily
small full error using the existing finite-pivot-repair consumer.
That step provides no mechanism making the residual λD small.

## 5. Exact cyclic tests, including every old bad optimizer

Use the canonical VANISH table:

    r_0(S)=1 if 0∈S, and 2 otherwise.

For j=1,2,3 use cyclic predecessor and successor among these three.
Set r_j(S)=0 if j∈S; otherwise set it to −1 if 0∈S, and to
2·1_(pred(j)∈S)−1_(succ(j)∈S) if 0∉S. This defines every nonempty
coalition reward and has M=2. Here a_j=−1 and b_j=0 for all j.

### 5.1 The complete old last-date opponent family is excluded

Fix ANY N≥1, T=N−1, and p_j=(δ_T+δ_Never)/2 for all three j.
For any closed pivot point put y=Σ_{t<T}x_t, x=x_T, and retain λ,ν.
Set A=1/2−(3/2)(x+y). Direct full-cap calculations give

    d_0=1/8+(3/4)(x+y)−λ/8,
    U_j=A/2−y/2−λ/8,
    B_j=max(0,A),
    d_0+d_j=3/8+y/2+[−A]₊.                              (14)

These hold for every α∈[0,λ], since b_j=0. For the nonpivot cap,
early quitting gives at most zero, Quit0 gives zero, and the first late
endpoint is A; later endpoints decrease to A−λ/4. The closed LP
retains these endpoints at α=0 as well. The pivot cap is 15/8.

Equation (14) bounds every pivot repair below by 3/16. Equality is
attained at y=0, x=5/24, λ=3/4, ν=1/24 (with any feasible α).
At ANY global optimizer, (14) therefore forces

    y=0,   A≥0,   d_0=d_j=3/16,
    λ=6x−1/2,   1/12≤x≤3/14.

The last interval follows from λ≥0 and ν=3/2−7x≥0. In particular

    A≥5/28>0.                                          (15)

All finite actions in F_N now give a nonpivot zero, since y=0 and
joining at T pays zero. Its original Never value is W_j=A−λ/4,
whereas Δ_j=λ/4. Thus its SUBSIDIZED Never value is A+β_j>0.
Its prescribed half-mass at finite T cannot be a best response.

This excludes the WHOLE last-date half-law family from (9), for every
global optimizing pivot point, every α boundary choice, every β≥0,
and every deadline. It does not exclude all other bad fixed points on
this table, much less prove the general selector successful.

### 5.2 The known good branch remains in the adjusted correspondence

For K≥1 put N=3K, a=2^(−K), D=a³, and take pivot Never together with

    p_j(3k+j−1)=2^(−k−1),  0≤k<K;
    p_j(Never)=a,          j=1,2,3.                      (16)

Use β_2=a² and β_1=β_3=0, choosing η≥a². Here λ=α=0, so EVERY
endogenous compensation vanishes. The exact pure response values are

    f_1(3k)=f_1(3k+1)=0,      f_1(3k+2)=−4^(−k)/2;
    f_2(3k)=1−4^(−k),        f_2(3k+1)=f_2(3k+2)=1;
    f_3(3k)=f_3(3k+2)=0,      f_3(3k+1)=−4^(−k)/2.

Never values are (0,1−a²,0). Thus every used nonpivot action is an
exact subsidized best reply. The original values are

    U=(2−2D,0,1−D,0),   B=(2−D,0,1,0),
    d=(D,0,D,0).                                        (17)

The global pivot certificate is stronger than its own best-response
condition. Against (16), let g_2,1 be player 2's gain from pure time 1.
For every pivot law,

    d_0+g_2,1≥2D.                                      (18)

Both sides apart from the fixed constant are affine in the pivot law.
For pure pivot time 0 the two terms are 1−D and 0. For 1≤t<N,
d_0=2^(−t)−D≥D, the time-1 test pays one, and adding the pivot cannot
increase prescribed U_2, so g_2,1≥D. That monotonicity is pointwise:
preempting an outcome pays either zero when player 2 joins, as before,
or −1, the minimum possible reward on that realization. For t≥N,
d_0=0 and g_2,1=2D because only joint nonpivot Never changes the
prescribed payoff. At pivot Never both terms equal D. Integration
proves (18), including arbitrary unbounded pivot laws. The same affine
inequality holds on the closed mass domain because these two gains are
independent of α. Hence the global optimum is D, attained at pivot
Never. This is an actual point of (9), not just an auxiliary-game Nash
profile with an unverified inner optimum.

Consequently minimum-L selection over all β and fixed points at these
N,η has value at most 8^(−K). At (16), the sharper inequality (R) is
an equality: β_2 z_2=D and λD=0. This verifies the positive test without
assuming the cyclic response geometry for arbitrary tables.

## 6. Narrow correspondence and precise remaining source

The definitions and statements inspected are:

- `QuittingPivotRepairLPInput`, `prescribedPayoff`,
  `otherNeverProduct`, `responderNeverEndpoint`,
  `responderFirstEndpoint`, `objective`, and `exists_objective_minimizer`
  in `UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteLP.lean`;
- `constraintGain_affine`, `prescribedPayoff_withFirstAtom`,
  `responderLimitEndpoint_eq_neverEndpoint_of_later_zero`, and
  `abs_objective_withFirstAtom_sub_le_of_reward_bound_of_later_zero`
  in `PivotRepairFiniteLPBoundary.lean`;
- `exists_objective_minimizer_eq_behavioral_infimum` in
  `PivotRepairBehavioralInfimum.lean`, and
  `exists_law_boundary_approximation_of_reward_bound_of_later_zero`
  in `PivotRepairBehavioralApproximation.lean`;
- `singlePivot_exactMenuNash_pivot_debt_le_deletedNever` and
  `singlePivot_exactMenuNash_nonpivot_debt_eq_zero` in
  `SinglePivotFiniteMenuSource.lean`;
- `pivot_singleton_mul_jointNever_le_objective` in
  `PivotRepairNeverMassBound.lean`;
- the small-value source and consumer route named in `docs/TOOLKIT.md`:
  `HasQuittingSmallPivotRepairValue` in `PivotRepairSmallValueSource.lean`,
  `smallPivotRepairValue_iff_exists_uniformEquilibriumPayoff` in
  `PivotRepairUniformPayoffCharacterization.lean`, and the actual finite
  conversion in `PivotRepairFiniteMenuConsumer.lean`.

These source files were read, not rebuilt for this note. The exact LP and
its consumer are existing production mathematics. At an ordinary exact
finite-menu Nash profile the existing first pair of scalar results gives
E≤D already. Thus an upper bound by the three nonpivots' joint Never
mass is NOT new by itself. The new source structure is simultaneous
outer response with endogenous compensation and GLOBAL original pivot
repair, with the sharper event λD in its all-selector bound. The LP
Never theorem instead gives the opposite-direction budget νD≤L;
it neither is nor implies (R).

The exclusion of a sole maximal debtor in (11) is the elementary
one-coordinate repair argument already present in minimum-MAX geometry;
it is not a newly discovered simultaneous descent. The prior
[coupled-LP note](CODEX_RENY__PIVOT_LP_AND_FINITE_NONPIVOT_BEST_REPLY_COUPLING.md)
contains the old bad branch and the bonus good branch used in Section 5.
HILBERT's
[portfolio on H](CODEX_HILBERT__ADAPTIVE_NEVER_BONUS_PORTFOLIO_ON_H.md)
supplies a different successful ordinary auxiliary-Nash selector. Its
pivot is not proved globally optimal for the full repair objective;
therefore its success is NOT silently transferred to (9).

The exact unproved target for this new rule is:

    For every canonical table and every η,ε>0, there are N≥1,
    β∈[0,η]^3 and a fixed point of (9) with L<ε.           (S)

Equivalently the infimum over those complete finite fixed-point sets
vanishes at every permitted positive bonus ceiling. No nested source,
particular branch, or common relation between N and η is required.
An available sufficient but UNPROVED route is to make λD arbitrarily
small while taking η→0. Bound (R) produces no such decrease by itself.
The positive event λD retains all three nonpivot Never choices and a
finite pivot quit; replacing it by a three-player proper face without
controlling the original four-player caps would not be justified.

The next concrete issue is whether a late-tail expansion of the three
nonpivot laws can reduce this event while keeping a new compensated
fixed point or directly controlling every original full debt. The
current theorem supplies the source and the exact weighted error, not
that consumer, a uniform equilibrium, or an arbitrary-table algorithm.
