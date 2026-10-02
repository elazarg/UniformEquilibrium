# Weak odd interval blocker cores admit uniform payoffs

Author: CODEX_TARSKI_PREMIUM.

Status: valid ordinary-mathematical perturbation corollary, but RETIRED AS A
NEW EXISTENCE CLASS. Section 6 proves that the entire weak-band class already
lies in the existing normal-core/non-Q stationary consumer. The strictification
argument still records a more specified family of profiles: outsiders remain
exact best responders, core limiting payoffs stay in their passive bands, and
literal finite censoring gives a complete-response bound. These refinements
are not claimed novel or independently reviewed. The canonical Fin4 example
does separate two payoff criteria, but NOT the existing broader stationary
existence theorem. No export is proposed.

## 1. Finite data, strategies, and conclusion

Let I be a finite player set and let K=(k_0,...,k_{n-1}) be distinct members,
where n is odd and n≥3. Write b(k_j)=k_{j+1 mod n}. Players outside K are
unrestricted. Every nonempty S⊆I pays a finite real vector r(S); all-Continue
and Never pay zero. Each player independently chooses a complete stopping law
on ℕ∪{Never}; equivalently it uses a behavioral strategy on the unique live
history. Every unilateral deviation may replace the entire law, with arbitrary
private randomization and unbounded support. No public correlation is used.

For i∈K define the following four extrema of the ORIGINAL reward table:

    C_i^- = min {r_i(S): S≠∅, i∉S},
    C_i^+ = max {r_i(S): S≠∅, i∉S},
    H_i^- = min {r_i(S): i∈S, b(i)∉S},
    L_i^+ = max {r_i(S): i∈S, b(i)∈S}.

All four indexing families are nonempty because n≥3. Assume the weak band
condition, with no sign assumption on any singleton or passive reward:

    L_i^+ ≤ C_i^- ≤ C_i^+ ≤ H_i^-             for every i∈K.       (W)

The strict source theorem requires strictness in the first and last of these
comparisons. The middle comparison is automatic for these literal extrema.
No outside payoff coordinate occurs in (W), but the extrema include ALL
coalition backgrounds, including every combination of outside quitters.

Theorem. Every reward table satisfying (W) has the following properties.

1. For every ε>0 there is a stationary independent profile with unrestricted
   terminal exploitability at most ε. Every outside player is an exact best
   responder in that profile in the original game.
2. For every ε>0 there is a finite-calendar independent profile with
   unrestricted terminal exploitability at most ε.
3. There is one fixed uniform-equilibrium payoff v. It can be chosen with
   C_i^-≤v_i≤C_i^+ for every i∈K. Its accuracy-dependent profiles and horizon
   thresholds have the usual uniform finite-horizon quantifier order.

The stationary profile may depend on ε. An exact stationary equilibrium of
the original weak-band table, a nonvanishing absorption rate across errors,
and a quantitative calendar bound uniform over the class are not claimed.

## 2. Literal strictification and its compatibility

Fix δ>0. For every terminal coordinate set

    r_i^δ(S) = r_i(S)+δ     if i∈K∩S and b(i)∉S,
             = r_i(S)-δ     if i∈K∩S and b(i)∈S,
             = r_i(S)       otherwise.                         (1)

These clauses are disjoint. The blocker is unique for each core owner, so
there is no conflicting instruction for a coordinate. When a coalition
contains several core players, their reward coordinates are changed
independently according to their own blockers. No coalition is removed or
added. Never remains zero. Every outside reward and every core passive reward
is unchanged, including passive rewards on coalitions containing outsiders.

Consequently the two continuation extrema are unchanged and

    (L_i^+)^δ=L_i^+-δ < C_i^- ≤ C_i^+ < H_i^-+δ=(H_i^-)^δ.     (2)

Moreover |r_i^δ(S)-r_i(S)|≤δ uniformly over ALL players and coalitions.
Thus (1) constructs arbitrarily close strict-band tables directly from every
weak-band table. This is an explicit actual-table adapter, with no supplied
equilibrium or continuation as input. It does not preserve the original
singleton normalization, which is unnecessary: the strict theorem permits
arbitrary signed singletons.

Apply the strict odd interval-core theorem to r^δ, with the SAME embedded
odd core and all other players retained. It produces a stationary product
profile σ^δ that is exact terminal Nash against unrestricted behavioral
deviations. Every core hazard lies strictly between zero and one; every
player's opponents absorb almost surely. All outside coordinates and all
their deviations are included in this conclusion.

## 3. Original-game complete responses and the fixed payoff

The strategy spaces and first-stopping outcome map do not depend on rewards.
Use exactly the same independent profile σ^δ in the original table r. For
every profile p, including every complete unilateral replacement,

    |U_i^{r^δ}(p)-U_i^r(p)|≤δ.                                (3)

Indeed both expectations use the same terminal distribution, and each
nonempty outcome changes its reward by at most δ; Never changes by zero.
For every player i and EVERY behavioral deviation τ_i, exact Nash in r^δ
and (3) give

    U_i^r(σ^δ[i←τ_i])-U_i^r(σ^δ) ≤ 2δ.                        (4)

This remains valid when the cap supremum is not attained. Outside players
have no reward changes at all, so their bound in (4) is zero. In particular
choosing δ≤ε/2 proves conclusion 1. This controls complete deviations in the
original game, not root regret at an auxiliary continuation.

For core payoff localization, an interior core player in σ^δ is indifferent
between Quit and Continue at its literal stationary continuation. Opponent
absorption has probability one. Therefore its prescribed payoff equals its
Never payoff, an average of its passive rewards. Those passive rewards are
unchanged in (1) and lie in [C_i^-,C_i^+]. Hence

    C_i^-≤U_i^{r^δ}(σ^δ)≤C_i^+,
    C_i^-−δ≤U_i^r(σ^δ)≤C_i^++δ.                              (5)

Take δ_m→0 and a convergent subsequence of the bounded ORIGINAL payoff
vectors U^r(σ^{δ_m}). Call its limit v. Equation (4) gives terminal Nash
errors tending to zero, while (5) places v_i in the stated core intervals.
The terminal-Nash/fixed-target selection theorem gives one uniform payoff v.
No convergence of the stationary laws or of their absorption rates is used.
Alternatively, ordinary uniform-payoff existence without (5) follows directly
from reward-table closure and the strict equilibria of r^δ.

## 4. Finite-menu output on the same original table

Here is the finite construction, so conclusion 2 does not rely on a
payoff-only compression. Fix |r_i(S)|≤M with M>0 and one profile σ^δ from
Section 2. If its stationary Quit rate for i is q_i>0, its stopping law is
proper geometric. Move its finite mass at dates t≥N to Never. This changed
mass is e_i(N)=(1-q_i)^N. If q_i=0 the law is already pure Never, and define
e_i(N)=0. Let p^{δ,N} be the resulting independent product profile on
{0,...,N-1,Never}.

Couple each original marginal and its censored version independently. The
probability any prescribed clock changes is at most Σ_i e_i(N), so prescribed
payoffs change by at most 2MΣ_i e_i(N). For a fixed arbitrary deviating law
of player i only its opponents are censored; the deviation payoff changes by
at most 2MΣ_{j≠i}e_j(N). Taking the supremum over ALL deviating laws gives

    E_r(p^{δ,N}) ≤ 2δ + 4M Σ_i e_i(N).                        (6)

For each fixed δ all the nonzero-rate tails vanish as N→∞. Choose, for
example, δ=ε/4 and then N≥1 making the second term at most ε/2. This proves
conclusion 2 without assuming a calendar bound or uniform tightness as δ
changes. Censoring may lose exact outsider best responses; only (6) is claimed
for the finite laws.

In canonical Fin4 data s=(1,0,0,0), the verified identity
E_r(p)=max(E_N(p),L_0(p)) then yields BOTH inequalities in the current
finite-menu question at this same selected p. The theorem therefore supplies
an end-to-end producer on the raw weak-band class.

## 5. Exact canonical Fin4 separation

Take I={0,1,2,3}, K={1,2,3}, and b(1)=2, b(2)=3, b(3)=1. Define every
nonempty row by the following complete rules:

    r_0({0})=1,       r_0(S)=2 for S≠{0};

    for i∈K:
      r_i(S)=−1/2     if i∉S and 0∈S;
             =0       if i∉S and 0∉S;
             =−1      if i∈S and b(i)∈S;
             =0       if S={i};
             =8       otherwise (i∈S, b(i)∉S, |S|≥2).

Thus s=(1,0,0,0), |r_i(S)|≤8, and every core owner has

    (L_i^+,C_i^-,C_i^+,H_i^-)=(-1,-1/2,0,0).                  (7)

This satisfies (W), with a binding upper comparison.

Let every player Quit at date zero with probability 1/2 and choose Never
otherwise. Every subset, including Never, has probability 1/16. Direct exact
expectation gives

    U=(29/16,9/8,9/8,9/8) > (1,0,0,0) coordinatewise.         (8)

This is an actual independent finite profile, not a correlated coalition
lottery or a convex-hull relaxation. Therefore weak singleton payoff exclusion
fails for every nonempty subset of players. Any stronger exclusion which
requires a nonzero nonnegative weighted payoff deficit at every actual source also
fails at (8).

At its actual all-half product root the pure Quit endpoints are

    Q=(15/8,5/2,5/2,5/2).                                   (9)

For direct reproduction, U_0=2(7/8)+1/16 and Q_0=2(7/8)+1/8.
For a core owner, the high Quit outcome has probability (1/2)(3/4)=3/8
conditional on its Quit, and the blocked outcome has probability 1/2.
Thus Q_i=8(3/8)-1/2=5/2 and U_i=(1/2)Q_i-(1/2)(1/2)(1/2)=9/8.

Every player is active and every Quit endpoint is above its singleton. Thus
the product-low condition fails. Supportwise balance and ordered-premium
conditions, which imply product-low, fail as well. No core or full-game
participant-only theorem applies literally: core passive rewards can be
−1/2, and player 0's passive rewards are 2.

There is NO strict odd interval core under any labeling in this four-player
table. Such a core must have three members. A core containing player 0 has
H_0^-≤r_0({0})=1<2=C_0^+, regardless of its blocker. The only remaining
three-member set is {1,2,3}. For either cyclic orientation and any owner,
H_i^-≤r_i({i})=0=C_i^+, so the required strict upper comparison fails.
This argument covers every embedding, not only the displayed orientation.

Every pure terminal coalition is unstable. If S={0}, a core player joins
and improves from −1/2 to 8. If S contains exactly one core player i,
player b(i) joins; its own blocker is absent, so its payoff improves from
0 or −1/2 to 8. If S contains at least two core players, it contains an
edge i,b(i). Player i then leaves, improving from −1 to 0 or −1/2; the
remaining coalition is nonempty. These changes are feasible at the first
quitting date of ANY pure clock profile. All-Never is also unstable, since
player 0 can quit for 1. Thus the example has no pure exact terminal Nash
profile, even with unrestricted deterministic stopping dates.

For an additional exact positive check, this particular table has the
stationary profile q_0=0 and q_1=q_2=q_3=7/8 with payoff (2,0,0,0).
Writing x=7/8, each core Quit endpoint is

    8x(1-x)-x=7x-8x²=0,

and each core passive payoff is zero because player 0 Never quits. Every
core pure date and Never consequently pays zero. For player 0, Never pays
2 and quitting at finite date t pays

    2-(1-x)^{3(t+1)} < 2.

Arbitrary law mixtures cannot improve these values, so this is exact Nash
against the complete deviation class. It is an independent check on the
example, not a substituted proof for the arbitrary weak-band theorem.
This example and the entire class are contained in the existing non-Q
stationary existence theorem, as the next section proves.

## 6. Exact subsumption by the existing non-Q stationary consumer

Write s_i=r_i({i}) and M_ij=r_i({j})−s_i for the normalized singleton
matrix used by the source gate. Its diagonal is zero. For each core player i
and every j≠i, condition (W) gives

    r_i({j}) ≤ C_i^+ ≤ H_i^- ≤ r_i({i})=s_i.

The last inequality uses the singleton {i} in the high family, since b(i)≠i.
Thus the ENTIRE normalized row of each core owner is nonpositive.

The source's normal layer starts with all players and repeatedly keeps i
only if the preceding layer contains some distinct j with M_ij≤0. Induction
shows that every layer contains K: for i∈K use j=b(i)∈K as witness. Therefore
K is contained in the normal core N, regardless of every outsider's rewards.
In particular N is nonempty, and its restricted matrix retains a nonpositive
row, say that of a fixed i∈K.

That restricted matrix cannot be standard Q. Indeed choose a right-hand
side a on N with a_i=−1 and all other entries zero. For any nonnegative
candidate weights x, its i-th LCP residual is

    a_i + Σ_{j∈N} x_j M_ij ≤ −1 < 0.

So residual nonnegativity fails even before complementarity is checked.
This is an explicit infeasible standard-LCP right-hand side, not an inference
from a sign-pattern label. It directly contradicts the `normal_standardQ`
field of `StandardQMatrixSide`.

Apply `exists_stationaryUniformEquilibriumPayoff_or_standardQMatrixSide`:
its standard-Q alternative is impossible, so the game already has a fixed
uniform-equilibrium payoff approached by stationary approximate equilibria.
The proof uses neither oddness nor strictness of the bands; a persistent
nonempty collection of nonpositive singleton rows with distinct internal
witnesses would suffice. In particular neither this note's weak boundary nor
its strict-interior payoff example expands the source's raw existence class.

What survives from Sections 2–4 is the explicit strictification/censoring
construction and its additional outsider-best-response and payoff-localization
conclusions. These are narrower profile statements than bare existence, not
a new general consumer or a new proof mechanism. Exact stationary existence
throughout the weak class remains unproved here.

The same test retires an attempted disjoint five-player odd-core/pair
construction and an initial four-player overlapping-core/pair seed: both kept
at least two mutually witnessing rows with every passive singleton below the
owner's singleton. Their explicit periodic profiles cannot yield a new raw
existence class. No five-player packet will be developed from that seed.

## 7. Bounded source record and next check

The route was selected from docs/FRONTIER.md and docs/TOOLKIT.md. Exact
declarations inspected in their defining files:

- `IsLiteralStrictFiniteOddIntervalBlockerCore`, its literal extrema,
  `IsLiteralStrictFiniteOddIntervalBlockerCore.toStationaryFace`,
  `exists_stationaryCertificate_of_literalStrictFiniteOddIntervalBlockerCore`,
  and `isUniformEquilibriumPayoff_of_literalStrictFiniteOddIntervalBlockerCore`
  in `UniformEquilibrium/Quitting/Classification/Existence/FiniteOddIntervalBlockerCoreRowAdapter.lean`;
- `FiniteOddIntervalBlockerCoreStationaryCertificate` and
  `exists_stationaryCertificate_of_strictFiniteOddIntervalBlockerCore` in
  `UniformEquilibrium/Quitting/Classification/Existence/FiniteOddIntervalBlockerCore.lean`;
- `abs_quittingTerminalPayoff_sub_le_of_forall_abs_sub_le` and
  `IsεAsymptoticNash.of_reward_close` in
  `UniformEquilibrium/Quitting/PayoffProcess/TailStepSelector.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_of_uniform_reward_limit`
  and `quittingGame_exists_uniformEquilibriumPayoff_of_arbitrarily_close_rewards`
  in `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/UniformPayoffExistenceClosure.lean`;
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `singlePivot_fullExploitability_eq_max_menuExploitability_scalar` in
  `UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`; and
- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
- `normalizedSoloMatrix` and its normalization definitions in
  `UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean`;
- `normalLayer`, `mem_normalLayer_succ`, `normalCore`, `mem_normalCore`,
  `normalPlayerMatrix`, and `normalizedNormalPlayerMatrix` in
  `UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean`;
- `StandardLCPSolution` and `IsStandardQMatrix` in
  `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`;
- `StandardQMatrixSide` in
  `UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`; and
- `exists_stationaryUniformEquilibriumPayoff_or_standardQMatrixSide` in
  `UniformEquilibrium/Quitting/Classification/LCP/StationaryExistence.lean`.

The maintained frontier and the existing
[odd-core packet](../formalized/ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE.md)
explicitly exclude weak bands from their strict source predicates. A narrow
weak/closure search in the named existence subtree found no weak interval
adapter. Section 13 of
[GAUSS's note](CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md) already proves a
weak blocker switch for ALL players with zero passive rewards; it does not
cover this proper-core, variable-passive, arbitrary-outsider statement.
The reward closure principle itself is already integrated. The initial search
missed the broader normal-core/non-Q consumer; Section 6 corrects that mistake
and withdraws the claimed expanded raw existence application. Its authoritative
source is the named Lean theorem under its imports, whose file attributes its
stationary branches to Solan and Solan, *Quitting games and linear
complementarity problems*, Theorem 5.1(1). This note does not independently
reprove or audit that literature result. No worldwide novelty is claimed.

An exact standard-library Fraction enumeration independently checked (7)-(9)
and a profitable nonempty-coalition toggle for all fifteen rows. The formulas
and case proof above retain the complete exact mathematical evidence. No Lean
build was run; no Lean file, other author's record, shared index, or export
was changed. The initial strict-interior prefix and coordinate-repair ideas
were retired after detecting stronger existing obstructions, before creating
another example or claiming an additional result.

Next concrete research question: can a four-player construction overlapping a
three-player active block with a pair produce full-response profiles on a raw
class whose normal-core matrix is standard Q and has no homogeneous simplex
solution? Test this source-gate escape before further profile algebra. The
weak-band corollary itself is not an export candidate.
