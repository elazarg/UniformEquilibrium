# Repair duals, payoff exclusion, and reconstruction of deleted laws

Author: CODEX_LARCH_DUAL.

Status: theory sketch and ordinary mathematical deductions, not Lean-checked.
The two central deductions passed
[independent review](../feedback/CODEX_LARCH_DUAL__REPAIR_EXCLUSION_THEORY__BY_CODEX_LARCH_GEOMETRY.md)
by CODEX_LARCH_GEOMETRY. The direct proposed identification of repair dual
weights with payoff-exclusion weights fails on the existing exact repair
trap. A more plausible connecting theory concerns reconstruction of deleted
stopping laws from outcome data, with explicit singularities when individual
survival vanishes. This is a bounded audit, not a claim of a new UE producer.

## 1. Question and exact objects

Players independently sample complete stopping times in the nonnegative
integers together with Never. The first stopping time and its tied coalition
determine the reward; all-Never pays zero. All unilateral behavioral
deviations, including unbounded laws and Never, are allowed. For a profile p,
write U_i for prescribed reward, B_i for its full unilateral response cap,
d_i=B_i−U_i, E=max_i d_i, and D=Σ_i d_i. Put s_i=r_i({i}), with all reward
coordinates bounded in absolute value by M>0.

Fix finite opponent laws q for a pivot o. The existing exact repair LP has
value R(q)=inf_π E(π,q), where π ranges over every complete pivot law.
Its compact mass variables are head masses, late mass L, Never mass N, and
first late atom a with 0≤a≤L. Replacing (L,a) by (a,L−a) makes this polytope
a simplex. Thus its affine gain rows form a finite matrix game. Some simplex
vertices, such as L=1,a=0, represent limiting repair data rather than an
attained proper stopping law; the behavioral-infimum theorem handles this.

For row weights λ in the simplex, write w_i for the total weight on rows
belonging to player i. At positive value, an optimal dual places no mass on
the zero row. At a primal optimum m and an optimal dual λ, complementary
slackness gives

    R = Σ_a λ_a [b_a(m)−U_i(a)(m)]
      = Σ_a λ_a [b_a(m)−s_i(a)] − Σ_i w_i [U_i(m)−s_i].       (1)

Here b_a is the tested response value, not a singleton reward. Equation (1)
is the exact missing term in the informal proposed bridge. At an actual
attained optimum, every positive-weight row has gain R, hence its tested
response value equals the player's full cap. Without attainment, (1) is an
identity of the finite mass model and must first be transported through an
actual-law approximation before using a semantic consumer.

Payoff-exclusion instead requires a probability weight θ with

    max_i θ_i≤β<1,        Σ_i θ_i(U_i−s_i)≤0.                (2)

The exact prefix consumer in the source uses this to reduce TOTAL debt D.
The repair LP minimizes MAXIMUM debt E. These are two separate mismatches:
the response premiums in (1), and the objective used downstream.

## 2. An exact obstruction: every optimal repair dual fails exclusion

Use the VANISH table and the source profile from
[HILBERT's complete-coordinate trap](CODEX_HILBERT__FULL_EXPLOITABILITY_COORDINATE_REPAIR_TRAP.md).
The table has four players, pivot 0, and cyclic nonpivots 1,2,3:

    r_0(S)=1 if 0∈S, and 2 otherwise;
    r_j(S)=0 if j∈S;
           −1 if j∉S and 0∈S;
           2·1_(pred(j)∈S)−1_(succ(j)∈S) otherwise.

Take 1/3<t<3/8 satisfying x=(1−t)^3=t/(1+t), set z=1−t,
λ₀=1−x, and m=xλ₀. Fix each nonpivot law tδ_0+zδ_Never and use pivot law
xδ_0+λ₀δ_1. The known exact full debts all equal m, and

    s=(1,0,0,0),       B=(2−x,0,0,0),
    U=(2−2x+x²,−m,−m,−m).

For an arbitrary pivot law let X be mass at zero and L finite mass after
zero. Set C=t−(1+t)X. The three relevant distinct affine rows are

    g_0 = x + (1−2x)X − xL,
    g_Q = −zC + xL,
    g_C =  tC + xL.                                      (3)

The latter two are a nonpivot's date-zero and date-one deviation gains.
Every nonpivot has the same pair. The other endpoint rows are strictly
below m at the source, so no optimal dual can use them. First-atom mass has
zero coefficient in these active rows. The feasible region includes
X≥0, L≥0, X+L≤1.

Let w_0 be the pivot weight in ANY optimal dual. Its weighted gain has
L-coefficient x(1−2w_0). At the source X=x,L=λ₀, decreasing L while fixing
X is feasible, with the first-atom mass decreased along with L. The source
minimizes the dual's weighted affine function,
so that coefficient must be nonpositive. Consequently

    w_0≥1/2.                                             (4)

Every active nonpivot response pays its singleton reward zero; the pivot
response premium is (2−x)−1=λ₀. Applying (1) therefore gives

    Σ_i w_i(U_i−s_i) = w_0 λ₀−m
                    ≥ λ₀(1/2−x)>0.                      (5)

Thus NO optimal repair dual, after aggregating its rows to player weights,
is a payoff-exclusion weight for this same actual source profile.

An explicit small optimal dual makes the calculation independently testable.
Choose any one nonpivot j. Give pivot row weight 1/2, its g_C row weight
α/2, and its g_Q row weight (1−α)/2, where

    α=z+(1−2x)/(1+t).

This lies strictly between zero and one. Positivity is immediate, and
α<1 is equivalent to

    1−2x−t(1+t)<0,

whose exact factorization is
(2t−1)(t²−3t+1)<0 on the stated interval. The weighted expression in (3)
has both X and L coefficients zero. Since it equals m at the source, it is
identically m and certifies the exact repair optimum. Its induced player
weight is (1/2,1/2,0,0), up to the choice of j.

Nevertheless equal weights on the THREE nonpivots satisfy (2) with β=1/3:
their weighted surplus is −m. The exclusion prefix consumer is available at
the source independently of its repair dual. This is not a contradiction:
the allowed prefix changes multiple laws, and its advertised objective is D.

**Consequence for prioritization:** retire the direct universal implication
“positive repair LP dual ⇒ same-law payoff-exclusion weight.” The obstacle is
not nonuniqueness of the dual, selection of a poor optimizer, or omitted late
responses. Equation (5) rules out every optimal dual.

## 3. The surviving candidate: reconstructing deleted outcome laws

An outcome law records what happens when everybody follows the profile.
A response cap depends on what happens when one player's original stopping
law is deleted. The natural larger object is therefore the full dated
outcome law together with the individual survival functions, and the family
of deleted outcome laws reconstructed from them.

For one fixed profile p, let μ(t,S) be the probability that the first event
is at finite date t with nonempty tied coalition S; let μ(∞) be all-Never.
For player i let μ⁻ⁱ be the corresponding dated first-event law of all OTHER
players, and set

    a_i(t)=Pr(T_i>t),        a_i(∞)=Pr(T_i=Never).

Independence gives the exact uncensoring identities

    μ(t,S)=a_i(t) μ⁻ⁱ(t,S)       when i∉S,
    μ(∞)=a_i(∞) μ⁻ⁱ(∞).                              (6)

These use literal outcomes and literal stopping laws from the same profile.
They introduce no public lottery, correlated strategy, or counterfactual
resampling of the opponents.

Each complete pure response payoff is a bounded test of μ⁻ⁱ. For a response
at τ, an opponent event before τ pays its coalition reward, an event at τ
adds i to the coalition, and an event after τ pays the singleton reward s_i.
Never leaves the deleted event unchanged, with zero for deleted all-Never.
Consequently the entire full response cap is a supremum of tests bounded by
M in absolute value.

### A quantitative theorem draft on a nonsingular region

Let p,p' be two actual independent profiles. Assume both Never masses of
player i are at least ν>0. Let μ,μ' be their dated outcome laws and

    δ_i=sup_(t including ∞) |a_i(t)−a'_i(t)|.

Using TV=(1/2)Σ|mass difference|, equation (6) gives

    TV(μ⁻ⁱ,μ'⁻ⁱ) ≤ [TV(μ,μ')+δ_i/2]/ν,                (7)
    |B_i(p)−B_i(p')| ≤ [2M TV(μ,μ')+Mδ_i]/ν.           (8)

Proof sketch: for each deleted outcome y, write b_y=a_i(y)c_y and
b'_y=a'_i(y)c'_y, where b,b' are restrictions of the full outcome laws and
c,c' are the deleted probability laws. Then

    |c_y−c'_y| ≤ (|b_y−b'_y|+δ_i c'_y)/ν.

Sum over y; the restricted full-law absolute difference is bounded by the
full absolute difference and Σ_y c'_y=1. This proves (7). Bounded-test
expectation differences are at most 2M times TV; taking suprema preserves
that bound and proves (8). No response supremum needs to be attained.

If the individual law of i is unchanged, δ_i=0. If all players satisfy
the hypotheses, (8), together with |U_i(p)−U_i(p')|≤2M TV(μ,μ'), bounds
all debts and E. This is a concrete potential consumer: an outcome-law
construction with matching survival data and sufficiently small error now
transports every behavioral deviation cap.

### The inverse-survival loss is necessary

Two players suffice. Give player 0 reward 1 at {1}, and reward 0 at every
other outcome; all player-1 rewards are zero. Fix

    p_0=(1−ν)δ_0+νδ_Never.

Compare opponent laws p_1=δ_Never and p'_1=δ_1. The full dated outcome laws
differ in TV by exactly ν: both put mass 1−ν on date-zero coalition {0},
while their remaining mass is Never versus date-one coalition {1}.
The survival data for player 0 are identical. Yet B_0(p)=0 and B_0(p')=1.
Thus any reconstruction bound must lose at least order 1/ν. At ν=0 the full
dated outcome laws and player-0 survival functions agree exactly while the
response caps still differ. Unmarked coalition laws contain even less data.

This falsifies unconditional transport from payoff or outcome geometry to
strategic geometry. It also identifies the precise singularity: outcomes
hidden behind a player who has already stopped can remain decisive against
that player's deviation.

## 4. A bounded theorem ladder and stopping rule

1. **Elementary adapter:** prove (6)–(8) and inspect existing deleted-clock
   modules for an equivalent quantitative theorem. This is useful bounded
   mathematics even if it adds no new conjecture class.
2. **Table-specific consumer:** choose an existing payoff-fiber construction
   that preserves individual Never masses above ν and dated outcome law up
   to o(ν). Ask whether its entire response-cap vector is then controlled by
   (8). If its output retains only unmarked coalition masses, the adapter
   does not apply; do not silently replace that input.
3. **Singular-stratum question:** when one or more individual survivals tend
   to zero, determine which deleted outcome coordinates must be retained as
   independent limiting data. Seek an actual smaller carrier for these
   coordinates and a realizability theorem respecting common independent
   clocks. The two-player example gives the first mandatory coordinate.
4. **Only then revisit repair/exclusion:** expand the response-premium term
   in (1) using these deleted measures. A useful new theorem must bound that
   term or construct an improving actual law from its large-mass event.
   Merely stating its positivity is not progress.

The hardest gap is step 3. Small on-path mass need not make deleted mass or
cap small, and separately chosen deleted measures need not share one product
source. The existing payoff-only calendar compression is therefore not an
automatic source. A successful theorem needs a finite list of singular data
and compatibility conditions, with a named same-profile consumer.

The first falsifier is the two-player example above. The second is any
sequence with vanishing individual Never mass but a deleted late response
remaining of order one. If the proposed compactification merges such
sequences, it cannot control full caps. Stop this line if the only valid
repair is to retain the entire existing terminal-semantic carrier without
new structure or a more effective producer.

## 5. Existing overlap and sources inspected

The finite LP dual and its full optimal-set directional envelope already
appear in
[NOETHER's joint-repair note](CODEX_NOETHER_SUPPORT__JOINT_OPPONENT_MOVE_AND_COMPLETE_REPAIR_VALUE.md).
That note also supplies an infinitesimal joint escape from the coordinate
trap. Neither is a new candidate here. Generic strong duality is already in
`MathUE/LinearProgramming/StrongDuality.lean`.

The sparse social-weight dual already distinguishes correlated outcome
feasibility from product realization and incentive compatibility in
[the sparse Pareto-law note](CODEX_SOCIAL_DUAL__SPARSE_PARETO_LAW_AND_PRODUCT_BARRIER.md).
The proposed deleted-law adapter addresses a different missing datum: actual
outcome laws can coincide while unilateral caps differ.

General approximate cap-preserving calendar compression already exists in
[the quantile-clock packet](../formalized/ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md).
A new generic approximate compression theorem is not proposed here. The
question is whether specific outcome-geometric arguments can transport caps
through the nonsingular/singular decomposition above.

Exact declarations inspected, under their displayed imports, without a new
Lean build:

- `IsPivotRepairMassFeasible` and `pivotRepairMassFeasibleSet`
  (`MathUE/LinearProgramming/PivotRepairMassPolytope.lean`).
- `QuittingPivotRepairLPInput.constraintGain`, `.objective`, and
  `.exists_objective_minimizer`
  (`UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteLP.lean`).
- `QuittingPivotRepairLPInput.exists_objective_minimizer_eq_behavioral_infimum`
  (`UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`).
- `smallPivotRepairValue_iff_exists_uniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Terminal/PivotRepairUniformPayoffCharacterization.lean`),
  an equivalence, not a source of small repair values.
- `HasQuittingFiniteWordNonconcentratedGroupExclusion` and
  `quittingGroupExclusionExactWords_step`
  (`UniformEquilibrium/Quitting/Paths/GroupExclusionFiniteWords.lean`).
- `nonconcentratedWeight_exactAuxiliaryPrefix_debtDrop`
  (`UniformEquilibrium/Quitting/Terminal/GroupExclusionExactPrefixStep.lean`).

The independent review found no unresolved mathematical objection to the
all-duals obstruction or uncensoring estimates. It also identifies a
complementary singular regime: if deleting any one player leaves an almost
sure opponent quitter at a common root, direct counterfactual-tail coupling
controls caps without dividing by individual survival. The global residual
has neither control. The subsequent
[competing-risks identification sketch](CODEX_LARCH_DUAL__COMPETING_RISKS_CAP_FIBERS.md)
examines exact finite dated-law fibers in that direction.

No Lean files, exports, shared indexes, or commits were created. No literature
theorem is needed for the elementary deductions here. Independent review of
these elementary claims does not promote the open singular-stratum theory or
supply its actual-data consumer.
