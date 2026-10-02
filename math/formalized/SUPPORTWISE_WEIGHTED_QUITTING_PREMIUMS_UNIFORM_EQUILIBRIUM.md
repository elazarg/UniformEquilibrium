# Supportwise weighted quitting premiums imply uniform equilibrium

Authors: CODEX_FRECHET_CYCLE; support-dependent formulation proposed by ROOT.
Independent reviews:
[CODEX_TARSKI_PREMIUM](../feedback/SUPPORTWISE_WEIGHTED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM__BY_CODEX_TARSKI_PREMIUM.md),
[CODEX_NOETHER_SUPPORT](../feedback/SUPPORTWISE_WEIGHTED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM__BY_CODEX_NOETHER_SUPPORT.md).

## Conjecture-facing change

This is a complete sufficient reward-table criterion for every finite
nonempty player set with nonnegative own singleton rewards. It produces
actual periodic terminal approximate equilibria against unrestricted
behavioral deviations and then one fixed uniform-equilibrium payoff.
No equilibrium source, continuation family, or successful splice is supplied
as an input. For four players, the criterion consists of fifteen linear
feasibility tests on the actual table.

The new mathematical attachment is the supportwise participant-premium
identity and its finite-table hypothesis. The root, periodic construction,
and nonlocal full-response mechanism are due to Solan and Vieille and are
credited below. The criterion strictly includes ordered positive premiums
and globally balanced participant premiums, including tables satisfying
neither special condition. It is sufficient, not necessary; failure of a
test does not establish a counterexample. General four-player UE remains
open. The new adapter is ordinary mathematics, not a newly checked Lean
declaration or a claim of worldwide priority.

## 1. Finite input, agency, and exact conclusion

Let I be a finite nonempty player set. For every nonempty coalition S⊆I,
let r(S)∈ℝ^I be its quitting reward. Put s_i=r_i({i}) and assume s_i≥0
for every i. The payoff if nobody ever quits is zero. Before absorption,
all players independently choose Continue or Quit at each date using private
behavioral randomization, and preabsorption payoffs are zero. The first
nonempty quitting coalition absorbs;
its reward is repeated thereafter. A unilateral deviation may replace an
entire behavioral strategy, including Never and arbitrarily late finite
quitting plans. There is no public correlating device.

Define the own-quitting premium d_i(S)=r_i(S)−s_i for i∈S. Assume:

    For EVERY nonempty A⊆I there is a vector w^A∈ℝ^A such that
      w_i^A≥0                      for all i∈A,
      Σ_(i∈A) w_i^A=1,
      Σ_(i∈S) w_i^A d_i(S)≤0       for all nonempty S⊆A.       (SLP)

The vector may depend on A, but one vector must work simultaneously for
every S⊆A. It is chosen from the reward table before any root or accuracy.
Only members of S occur in its inequality. All passive rewards r_i(S),
i∉S, are arbitrary signed real numbers; own premiums may also have either
sign. No punishment vector, stationary equilibrium, or actual tail is input.

THEOREM. Under (SLP), for every ε>0 there is an actual periodic behavioral
profile whose every suffix is terminal ε-Nash against all unilateral
behavioral deviations. Consequently there is one fixed uniform-equilibrium
payoff for the original table.

The fixed payoff precedes accuracy. Periods, profiles, and horizon thresholds
may depend on accuracy. The uniform conclusion concerns all sufficiently
long finite-horizon expected average payoffs and all behavioral deviations,
not just deterministic clocks or stationary deviations. An exact stationary
or finitely supported equilibrium is not asserted.

## 2. Finite dimensions and the product identity

For n=|I|, (SLP) comprises 2^n−1 independent linear feasibility problems.
The problem for A has |A| variables, |A| nonnegativity inequalities, one
normalization equality, and 2^|A|−1 coalition inequalities. Its singleton
coalition inequalities are identically zero. The feasible set is a closed
subset of the probability simplex on A.

For Fin4 these are 15 LPs, with 32 variables in total, 15 normalization
equalities, 32 nonnegativity inequalities, and 65 coalition inequalities.
Of the latter, 32 singleton inequalities are tautologies, leaving 33
potentially nontrivial coalition inequalities. Every individual LP has at
most four variables. These counts describe the finite sufficient test, not
the complexity or completeness of equilibrium computation.

Let q∈[0,1]^I be a product root, with q_i the probability of Quit. Write

    p_q(S)=∏_(i∈S)q_i ∏_(i∉S)(1−q_i),
    a(q)=1−∏_i(1−q_i),
    Q_i(q)=Σ_(T⊆I\{i}) p_(q,−i)(T) r_i(T∪{i}).

For every i, including q_i=0 or 1,

    q_i[Q_i(q)−s_i]=Σ_(S∋i) p_q(S)d_i(S).                    (1)

This follows from q_i p_(q,−i)(S\{i})=p_q(S); no hazard is divided out.
Suppose a(q)>0 and take its EXACT active support A={i:q_i>0}. Then all
coalitions of positive p_q-mass are subsets of A. Multiply (1) by w_i^A
and sum to obtain

    Σ_(i∈A) w_i^A q_i[Q_i(q)−s_i]
      =Σ_(∅≠S⊆A) p_q(S) Σ_(i∈S)w_i^A d_i(S)≤0.             (2)

Since Σ_A w_i^A=1, some weight on A is positive. Every q_i is strictly
positive on A. Hence the coefficients w_i^A q_i are nonnegative and not
all zero. If all positive-weight coordinates had Q_i>s_i, the left side
would be positive. Therefore

    some i∈A has w_i^A>0 and Q_i(q)≤s_i.                     (3)

This holds for EVERY absorbing product root, without Nash or continuation
assumptions. It is not enough to use the weight for a larger set containing
the active support: that vector could vanish on the entire actual support.
Weights may jump when support changes. No continuity of them is needed.

The membership factor q_i in (2) is essential. With two players, pair
premiums (1,−1), equal weights, and q=(1/4,3/4), the endpoint premiums
are (3/4,−1/4). Their plain sum is positive, while the q-weighted sum is
zero. The argument makes no independence claim about an arbitrary mixture
of coalition vectors. LP infeasibility is not asserted to yield an absorbing
product root at which all active players have positive endpoint premium.

## 3. Exact root attachment in the unit-singleton game

First assume s_i=1 for all i. Fix R≥1 bounding every |r_i(S)|, and put

    W={v∈[−R,R]^I : some v_i≤1}.

This is a compact nonempty set. For a continuation v define

    F(q,v)=Σ_(S≠∅)p_q(S)r(S)+(1−a(q))v,
    C_i(q,v)=Σ_(∅≠T⊆I\{i})p_(q,−i)(T)r_i(T)
               +p_(q,−i)(∅)v_i.

Then F_i=q_i Q_i+(1−q_i)C_i. An exact root Nash profile satisfies
F_i=max(Q_i,C_i) for every player. Finite normal-form Nash existence
supplies an exact root at each v∈W.

If the root absorbs with positive probability, (3) supplies an active i
with Q_i≤1. Since Quit is supported at an exact root, F_i=Q_i≤1.
If instead q=0, exact Nash gives v_j≥1 for every j. Membership in W
then supplies i with v_i=1; that player is indifferent between both actions.
This is the low-payoff root condition of Solan--Vieille Proposition 2.2.

Choose 0<δ≤1 and raise only the selected player's hazard:

    q'_i=q_i+δ(1−q_i),          q'_j=q_j for j≠i.

If i was active and mixed, its endpoints were equal. If i was surely Quit,
the root is unchanged. In the all-Continue case its newly supported Quit
action was indifferent. Thus its payoff remains ≤1 in every case and both
of its supported actions are optimal. Also a(q')≥δ. All payoff coordinates
stay in [−R,R], so F(q',v)∈W.

For j≠i, the two pure endpoint payoffs change by at most 2Rδ and j's
support is unchanged. Every supported action is consequently within 4Rδ
of the best pure action. This is SUPPORT regret, not ordinary mixed regret.
The only use of (SLP) is (3) at the initial exact root. The perturbed root
need not be exact or share the same support, and no additional LP witness
is assumed for its continuation.

## 4. Actual periodic-tail producer and unrestricted consumer

For a desired row tolerance τ>0 choose

    δ=min(1/2,τ/(8R)),              ζ=δτ/4.

Take a finite ζ-net of W. At each representative v choose the preceding
root q', and map F(q',v) to a representative within ζ. This gives a
self-map of a finite nonempty set; hence it has a cycle. Reverse the
construction order around that cycle. The resulting periodic roots q_ℓ
and annotations v_ℓ satisfy

    |v_ℓ−F(q_ℓ,v_(ℓ+1))|∞≤ζ,
    a(q_ℓ)≥δ,
    support regret against v_(ℓ+1)≤4Rδ.                      (4)

No continuous root selector is needed: choices are made only at finitely
many representatives. The roots are implemented as independent private
product randomization at literal successive dates, not as a lottery over
whole profiles or correlated coalition outcomes.

Repeat the rows indefinitely. Every suffix absorbs almost surely, because
its survival for n more rows is at most (1−δ)^n. Its actual periodic
terminal suffix payoff U_ℓ satisfies U_ℓ=F(q_ℓ,U_(ℓ+1)). Taking the
maximum annotation error over a period in (4) gives

    max_ℓ |U_ℓ−v_ℓ|∞≤ζ/δ.

Both pure endpoints are 1-Lipschitz in the relevant continuation coordinate.
Thus every row has support regret at most

    4Rδ+2ζ/δ≤τ

against its ACTUAL next suffix value. Supported-endpoint inequalities also
control every mixed action whose support is contained in that row's support,
by taking convex combinations.

Use the existing unit-only extraction theorem
`quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
in `UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`:
for each requested full terminal error η>0 it supplies a positive row
tolerance τ; every positively absorbing periodic actual-tail-perfect
sequence at that tolerance yields a periodic profile whose EVERY suffix is
terminal η-Nash against unrestricted behavioral deviations. The result can
be a stationary repair rather than the original sequence. Its hypothesis
is unit own singletons, not capped joint rewards or weak support peeling.

Choose this τ before the finite-net construction. This proves the unit
theorem, including every suffix. We do not replace the full-response
extraction by summing per-row regret, nor assume that unilateral deviators
inherit the generated profile's absorption bound.

## 5. Positive coordinate scaling and zero singletons

For arbitrary s_i≥0 and t>0 put h_i=s_i+t and define

    hat r_i(S)=[r_i(S)+t]/h_i,
    Z_A=Σ_(j∈A)w_j^A h_j>0,
    hat w_i^A=w_i^A h_i/Z_A.

The new own singletons are 1; the new weights are nonnegative and sum to
1 on each A. Moreover, for every nonempty S⊆A,

    Σ_(i∈S)hat w_i^A[hat r_i(S)−1]
      =(1/Z_A)Σ_(i∈S)w_i^A[r_i(S)−s_i]≤0.                  (5)

Thus (SLP) survives unit normalization, including weights equal to zero.
Keeping the old weights after coordinate scaling would not in general
preserve (SLP). No uniform bound on the normalized rewards or their
construction parameters as t→0 is needed.

Given the desired original terminal error ε>0, set t=ε/4 and η=ε/2.
Apply the unit theorem to hat r with error η/max_i h_i. Undoing the positive
coordinate scales gives error at most η in the game with terminal rewards
r+t. All three games keep Never equal to zero. For every profile π,
including every unilateral deviation and every suffix,

    U_i(r+t,π)−U_i(r,π)=t Pr_π(absorption)∈[0,t].             (6)

Therefore the original regret is at most η+2t=ε. Periodicity and the
every-suffix error guarantee are unchanged. Formula (6), not an
unconditional affine shift, handles deviations that never absorb.

Finally,
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
selects one fixed original-table payoff from terminal approximate Nash
profiles at all positive errors, for every finite player set. This supplies
the uniform finite-horizon conclusion. Neither a punishment floor nor P=s
is assumed or inferred.

## 6. Included classes and exact boundary tests

### 6.1 Ordered peeling is a special case

Suppose every nonempty A contains an i such that d_i(S)≤0 for every
i∈S⊆A. Set w^A=e_i. Every coalition inequality is then either zero or
d_i(S)≤0. This is exactly the signed ordered-premium/weak support-peeling
input of the ordered-premium theorem.
The ordering ranks player labels, not chronological quitting dates.

### 6.2 Global strictly positive weights are a special case

If one λ_i>0 satisfies Σ_(i∈S)λ_i d_i(S)≤0 for every nonempty S⊆I,
use w_i^A=λ_i/Σ_(j∈A)λ_j. This recovers the global-positive-weight
sufficient condition.
For example, the cyclic Fin4 pair premiums +1 to j and −1 to j+1 at
{j,j+1} (indices modulo 4), and zero at all other own coordinates, satisfy
this input with equal weights. Every player has a positive own premium,
so weak peeling fails on I. This holds for arbitrary passive completion.

Conversely the canonical table whose only positive own premium is
d_1({0,1})=1, all other own premiums zero, has an ordering but no strictly
positive global weights. Its (SLP) witnesses are nevertheless supplied by
Section 6.1. Thus the unified premise includes both previously incomparable
raw-table tests.

### 6.3 The unified input can hold when neither special case holds

Take Fin4, s=(1,0,0,0), and core K={0,1,2}. Set all own premiums to zero
except those at the three oriented core pairs, with indices modulo 3:

    d_j({j,j+1})=1,       d_(j+1)({j,j+1})=−1,
    d_3({0,3})=1,        d_0({0,3})=0.

All passive rewards remain arbitrary. For A meeting K use the uniform
weights on A∩K and weight zero on 3. For A={3} use w_3^A=1. At each
core pair contained in A the member sum is zero; at {0,3} it is zero;
all other constraints are identically zero. Hence (SLP) holds.

Weak peeling fails already on A=K, since each core player has a positive
premium in a contained core pair. Global strictly positive weights fail
at {0,3}, which would require λ_3≤0. Thus the generalized input is
strictly larger than the union of these two special inputs, with canonical
singletons and without restricting passive completion. This is a raw-class
comparison, not a claim that any chosen completion avoids all other known
equilibrium classes.

### 6.4 One global semipositive vector is still insufficient

Take three players, s=(1,0,0), and initially r_i(S)=s_i for every S,i.
Change only the row {1,2} to (2,1,1). The global vector (1,0,0) satisfies
all its participant inequalities. But q=(0,1,1) is an exact Nash root
against every continuation and both active players have Q_i=1>s_i=0.
The inactive player 0 prefers passive reward 2 to its joining reward 1.

This table does NOT satisfy (SLP). At A={1,2}, its pair inequality is
w_1^A+w_2^A≤0, contradicting nonnegativity and normalization to 1.
The EACH-support requirement resolves precisely the active-weight defect;
it does not invalidate the original counterexample.

## 7. Source correspondence

The narrow map/source check used `docs/TOOLKIT.md` and `docs/FRONTIER.md`;
the additional premise-generalization check was at HEAD c652261. No Lean
build was run. Exact source dependencies inspected were:

- `quittingRootQuitPayoff_eq_sum_opponentCoalitionMass` in
  `UniformEquilibrium/Quitting/Root/OpponentCoalitionPayoff.lean`, underlying
  (1); the new weighted aggregation is proved here.
- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`.
- The unit-only periodic full-response extraction and all-player fixed-target
  consumer named in Sections 4--5.
- `quittingTerminalPayoff_playerwiseAffine` in
  `UniformEquilibrium/Quitting/Terminal/TerminalAffineReward.lean`, giving
  the exact absorption correction in (6).

Solan and Vieille, *Quitting Games*, Mathematics of Operations Research
26(2), 265--285 (2001), DOI 10.1287/moor.26.2.265.10549, Propositions
2.2--2.4 on printed pp.270--272, provide the classical low-payoff root,
charged periodic sequence, and full-response mechanism. The original pages
were inspected in the preceding frozen proof/source work. Their root
condition is expressly weaker than capped rewards. The present finite-net
argument states the actual producer rather than inserting its output as a
new hypothesis. `Literature/SolanAndVieille2001.lean` is an unbuilt
paper-transcription lane, not a checked implementation of this new class.

The source comparison distinguishes participant-only premiums from the
all-player weighted social chamber in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`
and affine membership-gain symmetrization in
`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`.
The former constrains all payoff coordinates at each outcome, including
nonquitters; the latter requires affine membership gains and positive
within-component symmetrizing weights. Neither is the participant identity
(2), and neither mechanism is used in this proof. No necessity of (SLP),
realization of LP-dual mixtures
by independent laws, common-box boundary identity, or worldwide novelty
claim follows from this note.

## 8. Lean handoff

A finite-table predicate can record (SLP) directly, using one normalized
nonnegative weight vector for each nonempty finite support. Its fields
contain only reward inequalities, not a root, strategy, consumer, or
existence conclusion. The first new lemma should prove (2), including zero
and sure root coordinates, then derive the active-player conclusion (3).

Suggested new declaration shapes are:

- `IsSupportwiseBalancedQuittingPremiumTable`: the finite predicate (SLP).
- `exists_active_quitPayoff_le_singleton_of_supportwiseBalance`: for every
  positively absorbing product root, an active player has Quit endpoint
  no larger than its own singleton reward; no Nash assumption is needed.
- `supportwiseBalance_playerwiseNormalized`: the exact normalized weights
  and inequalities in (5), including zero weights and zero singletons.
- `exists_periodic_allSuffix_terminalNash_of_supportwiseBalance`: the
  actual-profile all-errors conclusion, using the unit-only extraction.
- `quittingGame_exists_uniformEquilibriumPayoff_of_supportwiseBalance`:
  the fixed-target consequence for the original reward table.

These names describe proposed statement shapes; no new implementation is
claimed here. Sections 3--4 supply the full root/finite-net producer if the existing
producer wrappers still assume capped joint rewards. Reuse the generic
unit-only full-response extraction; do not reintroduce the stronger capped
hypothesis merely to reuse those wrappers. The ordered and global-weight
inputs are direct corollaries, not separate strategic constructions.

The source consumers and affine-payoff primitive are named in Sections
4--7. The narrow mathematical checks are the product-sum identity, exact
active support with zero weights, normalization (5), and all fifteen
support certificates in Section 6.3. Formalization should check its new
modules and existing extraction/target consumers under the repository's
ordinary trust and import policies. No new Lean check was run for this
packet.

## 9. Scope

No sign restriction is placed on passive rewards or on own quitting
premiums. Nonnegative own singleton rewards and independent behavioral
randomization are required. The proof neither constructs a correlated
coalition lottery nor assumes that arbitrary deviations absorb. Periodic
profiles and their periods may vary with accuracy; the payoff target may
not. No exact stationary equilibrium, necessary table classification,
polynomial-time equilibrium algorithm, or negative certificate from failed
LPs is asserted. The general finite-player and four-player conjectures are
not settled by this sufficient class.
