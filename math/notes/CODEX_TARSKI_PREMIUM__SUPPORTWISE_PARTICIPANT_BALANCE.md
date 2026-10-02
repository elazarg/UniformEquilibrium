# Supportwise participant balance supplies an active low-payoff quitter

Author: CODEX_TARSKI_PREMIUM.

Status: independent ordinary-mathematical derivation and full generalized
author manuscript PASS. Final feedback is
[here](../feedback/SUPPORTWISE_WEIGHTED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM__BY_CODEX_TARSKI_PREMIUM.md),
bound to SHA-256
`38d4975b7e630e59878332bdb96190932ede7e4be8c414e0fe11c201dcabcef7`
for the final assembled export-format draft, following full review of the
author manuscript and exact reconciliation of all final additions.
No author's candidate note or another reviewer's verdict was read before
the derivation. The stronger supportwise hypothesis was subsequently
supplied by ROOT and checked independently below. No Lean file or frozen
export is changed.

## Exact question and statement

Let I be a finite nonempty set of players in a quitting game. At the first
nonempty quitting coalition S each player i receives the finite real reward
r_i(S), and Never pays zero. At each live date actions are simultaneous and
independently randomized; the public history before absorption consists only
of earlier all-Continue dates. Strategies and unilateral replacements are
unrestricted behavioral stopping laws, including every finite date and Never.
Write s_i=r_i({i}) and d_i(S)=r_i(S)−s_i for i∈S.

Assume s_i≥0 and the following finite condition:

    For each nonempty A⊆I there are weights w_i^A≥0 for i∈A,
    with Σ_(i∈A)w_i^A>0, such that for every nonempty S⊆A,
        Σ_(i∈S) w_i^A d_i(S)≤0.                           (SB)

Then terminal ε-Nash profiles exist at every ε>0. They may be chosen
periodic and terminal ε-Nash in every suffix against ALL unilateral
behavioral replacements. Consequently the game has ONE fixed uniform-
equilibrium payoff, chosen before accuracy. Periods, profiles, and horizon
thresholds may depend on accuracy. Passive rewards remain unrestricted, as
do negative own-quitting premiums. No common lower orthant or punishment
equality is asserted.

The original candidate was the stronger hypothesis of one strictly positive
weight vector w on I satisfying the displayed coalition inequality for
every nonempty S⊆I. Restricting that vector to A proves (SB). Nonnegative
global weights not all zero need not restrict to nonzero weights on every A;
that weakening does not prove the stated local implication.

## The finite expectation identity

For product Quit probabilities q_i∈[0,1], write

    p_q(S)=∏_(i∈S)q_i ∏_(i∉S)(1−q_i),
    A={i:q_i>0},
    Q_i(q)=Σ_(T⊆I\{i})p_(q,−i)(T)r_i(T∪{i}).

When A is nonempty, use its weights from (SB). Finite distributivity and
q_i p_(q,−i)(S\{i})=p_q(S) for i∈S give the exact identity

    Σ_(i∈A) w_i^A q_i [Q_i(q)−s_i]
      =Σ_(∅≠S⊆A) p_q(S) Σ_(i∈S) w_i^A d_i(S)
      ≤0.                                                    (1)

The factors q_i on the LEFT are essential. Players outside A never quit,
so only coalitions contained in A contribute. There is no division by q_i
or by a survival probability; pure/sure and zero root components cause no
problem.

If Q_i(q)>s_i for every i∈A, each summand on the left is nonnegative,
and at least one is strictly positive: some w_i^A>0, and every q_i in A
is positive. This contradicts (1). Thus every absorbing product root, even
without Nash assumptions, has an active player with Q_i(q)≤s_i.

At an exact Nash root against continuation v, positive Quit support gives
F_i(q,v)=Q_i(q). Therefore every absorbing exact root has an active
quitter whose prescribed payoff is at most its singleton. This is stronger
than the selected-root hypothesis needed below. It does not say EVERY
coordinate lies above its singleton.

For a fixed global weight vector, the coalition inequality and the
corresponding weighted expectation inequality for every product root are
equivalent: necessity follows by taking q to be the pure root of S.
This equivalence does not make (SB) necessary for the active-low-quitter
property, because that property allows the low player to change with q
without requiring a shared separating weight.

## Unit normalization and the full semantic producer

Suppose first that all s_i=1. For R≥1 bounding absolute terminal rewards,
let W={v∈[−R,R]^I: some v_i≤1}. Exact finite-game Nash existence supplies
a root at every v∈W. If absorbing, (1) supplies an active low player.
If all-Continue, Nash gives v_j≥1 for every j, so one carrier coordinate
equals 1 and that player is indifferent.

Increase the selected player's Quit probability to q_i+δ(1−q_i), with
0<δ≤1. It was indifferent, surely Quit, or newly indifferent at the
all-Continue root. Its payoff remains at most 1, the successor stays in W,
and absorption is at least δ. Other players keep their supports, with each
pure endpoint moving by at most 2Rδ. Thus support regret is at most 4Rδ.
No continuity of supportwise weights or of Nash selections is required.

For desired row error τ>0 choose δ=min(1/2,τ/(8R)) and ζ=δτ/4.
A finite ζ-net in W and a selected row at every representative define a
finite map from continuation representatives to successor representatives.
Reverse a directed cycle of that map and repeat its chosen product roots.
Current annotations v_ℓ and next-tail annotations v_(ℓ+1) satisfy

    ‖v_ℓ−F(q_ℓ,v_(ℓ+1))‖∞≤ζ,       a(q_ℓ)≥δ.

Every actual suffix absorbs almost surely, since survival is at most
(1−δ)^n after n dates. Its periodic actual terminal values U_ℓ solve the
exact Bellman equations. The maximum discrepancy satisfies
D≤ζ+(1−δ)D, hence D≤ζ/δ. Pure endpoints are 1-Lipschitz in the relevant
continuation coordinate, giving actual-tail support error at most
4Rδ+2ζ/δ≤τ.

For every desired FULL terminal error, the existing unit-singleton
perfect-sequence extraction first chooses τ>0 and then consumes the
periodic actual-tail construction. It returns either that periodic sequence
or a stationary repair, with full behavioral terminal Nash in every suffix.
Small local error alone does not imply this conclusion; the nonlocal
consumer is indispensable.

Now let the original s_i be merely nonnegative. For t>0 define

    rhat_i(S)=(r_i(S)+t)/(s_i+t),     b_i=s_i+t>0,
    what_i^A=w_i^A b_i.

Then rhat has unit singletons and, for every nonempty S⊆A,

    Σ_(i∈S) what_i^A [rhat_i(S)−1]
      =Σ_(i∈S) w_i^A d_i(S)≤0.

Nonnegativity and nonzero supportwise total of weights are preserved. One
may divide what^A by its positive total if normalized LP weights are desired.
The correct transformed weights multiply by b_i; retaining the old weights
without checking them would be invalid in general.

Given original target error ε>0 choose t=ε/4 and normalized full terminal
error ε/(2 max_i b_i). Undoing positive scales gives ε/2-regret for r+t.
For every profile or unilateral replacement π,

    U_i^(r+t)(π)−U_i^r(π)=t Pr_π(absorption)∈[0,t].

Hence original regret is at most ε/2+2t=ε, suffix by suffix. Never is kept
at zero throughout; deviations need not absorb. All games have the same
action and coalition-history tree, so the same strategies are admissible.
The original table's compact payoff cube and the existing terminal
all-errors selection theorem produce one fixed uniform-equilibrium payoff.

## Finite LP scope and hierarchy

For each fixed nonempty A, (SB) is the finite LP feasibility system

    w_i≥0;     Σ_(i∈A)w_i=1;
    Σ_(i∈S)w_i d_i(S)≤0        for every nonempty S⊆A.

Normalizing by the positive weight total makes this equivalent to the
unnormalized condition. Coefficients are the actual finite reward table,
with no equilibrium, continuation, punishment, or profile as an input field.
There is one LP per active support. Rational tables admit rational feasible
weights whenever real feasible weights exist. For arbitrary real input this
is a finite mathematical criterion, not a claim of effective exact
computation from unrestricted real-number encodings.

The ordered-peeling condition implies (SB): choose a unit weight on a
peelable member of A and zero on all other members. Every coalition not
containing that member has weighted sum zero, and every coalition containing
it has nonpositive premium. A single global strictly positive balance vector
also implies (SB). These two sufficient subclasses are incomparable:
the exact examples below separate them.

LP dual coalitional combinations must not be called product roots. An
arbitrary distribution on nonempty coalitions is generally correlated and
need not equal p_q for any independent root q. Thus failure of the finite
certificate does not by itself produce an all-active high-payoff Nash root,
a failure of the classical root-choice condition, or a terminal gap.

## Exact falsification attempts and boundary examples

### Quit probabilities cannot be omitted from the identity

For two unit-solo players let the pair premiums be (+1,−1), balanced under
w=(1,1), and take q=(1/4,3/4). The pure-Quit excesses are (3/4,−1/4).
Their unweighted sum is 1/2>0; their Quit-weighted sum is exactly zero.
This falsifies the tempting identity without q_i, while confirming (1).

### Cyclic balanced premiums fail ordered peeling and pure stationary Nash

Take I={1,2,3}, all s_i=1. Every passive reward is 3/2. The three pair
own-premium vectors form the cycle

    {1,2}: (d₁,d₂)=(1,−1),
    {2,3}: (d₂,d₃)=(1,−1),
    {1,3}: (d₃,d₁)=(1,−1).

Every triple own premium is zero. This specifies the whole table: own
singletons and triple rewards are 1; pair owner rewards are 2 and 0.
Every participant premium sum is zero, so w=(1,1,1) works globally.
Each player has a positive premium somewhere inside I; ordered peeling
fails on I.

There is no pure stationary exact Nash profile. All-Continue loses to an
own singleton of 1. In a singleton quitting coalition its cyclic recipient
can join to improve from passive 3/2 to own reward 2. In a pair coalition
the negative-premium quitter can leave to improve from 0 to 3/2. In the
triple any quitter can leave to improve from 1 to 3/2. Therefore this table
also lies outside any sufficient class that always produces a pure
stationary exact equilibrium, including the named componentwise weighted-
potential class. This is class separation, not a general impossibility
result: the new construction permits periodic approximate play.

### Ordered peeling need not have a global strictly positive balance vector

For two unit-solo players take pair premiums (0,1). Player 1 peels and the
ordering 1,2 is valid. Any strictly positive global weights give pair sum
w₂>0, so the original global-balance hypothesis fails. The supportwise
condition succeeds with unit weight on player 1 in the pair support.

### A coalition-by-coalition low participant is not enough

Modify the cyclic three-player example to pair premiums (+2,−1), with
every passive reward now 2, and keep all triple premiums zero. Every
coalition has a member with nonpositive premium, but a common nonnegative
nonzero weight on I is impossible: the pair constraints require
w₂≥2w₁, w₃≥2w₂, and w₁≥2w₃, forcing all weights zero.

At q=(1/2,1/2,1/2), every Quit endpoint equals 5/4. At continuation
v=(−1,−1,−1), every Continue endpoint is (3/4)·2+(1/4)·(−1)=5/4.
Thus this is an exact absorbing Nash root in the low-coordinate box while
EVERY active quitter has value above its singleton. This invalidates a
weaker coalitionwise-minimum shortcut; it does not prove that this table
lacks some other usable root or equilibrium. Exact rational calculations
checked both this fixture and the preceding cyclic separation.

### A nonzero global vector may vanish on the actual support

Take three unit-solo players, w=(1,0,0), and let player 1 have zero own
premiums everywhere. Give both 2 and 3 a strictly positive premium at
{2,3}, with all other own premiums zero. Global nonnegative-weight balance
holds vacuously, but at q₁=0, q₂=q₃=1 both active Quit endpoints exceed 1.
The global weighted sum is zero because all active weights vanish. Requiring
nonzero weights separately ON every support is precisely what avoids this.

## Source audit and mathematical status

The exact old consumer, inspected in the preceding independent audit and
reused here, is
`quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
in UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean.
It requires unit solos only, periodicity, a positive common absorption floor,
and row perfection against actual tails, and returns all-suffix terminal
Nash against full behavioral deviations. The source of the root-choice
mechanism is Solan–Vieille (2001), Proposition 2.2; their Propositions 2.3
and 2.4 give the finite cycle and nonlocal extraction. The original local
PDF was read in the earlier audit, with printed pp.265–274 checked directly.
The [author-hosted paper](https://www.math.tau.ac.il/~eilons/quitting19.pdf)
states the classical capped own-quitting assumption; its weaker conditional
root-choice proposition supplies the appropriate attachment point here.

Other named declarations inspected:

- `exists_isZeroQuittingRootNash`,
  UniformEquilibrium/Quitting/Root/NashExistence.lean;
- `quittingTerminalPayoff_playerwiseAffine`,
  UniformEquilibrium/Quitting/Terminal/TerminalAffineReward.lean;
- `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`,
  UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean;
- `QuittingRowεPerfect`,
  UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean;
- `QuittingUnitSoloExit` and `QuittingCappedJointExit`,
  UniformEquilibrium/Quitting/Classification/SoloExitPreference.lean;
- `IsAffineQuittingMembershipGain`, `IsComponentwisePositiveSymmetrizable`,
  and `exists_pureStationary_exactTerminalNash_of_componentwiseWeightedPotential`,
  UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean.

The weighted-potential class concerns affine JOIN-versus-passive membership
gains and within-component symmetrization. Condition (SB) concerns own
coalition-versus-own-singleton premiums, with unrestricted passive rewards.
They are not synonymous; the no-pure-equilibrium example above separates
the implications concretely.

Narrow searches in the named classification/root subtree and the complete
Solan–Vieille transcription found no named participant-balance theorem.
A small primary-source web search returned the classical paper and broader
quitting-game work, without identifying this finite table criterion. This
does not establish worldwide novelty. The correct claim is a proved raw
table adapter into an existing conditional mechanism, with named repository
source coverage distinct from a literature-priority claim.

## Subsequent comparison with the author's base note

After the independent derivation above, I read the complete base note
[WEIGHTED_PARTICIPANT_PREMIUM_ROOT_ADAPTER](CODEX_FRECHET_CYCLE__WEIGHTED_PARTICIPANT_PREMIUM_ROOT_ADAPTER.md),
SHA-256 `3d40e81fa5a758e60b321abdc0efa457e62a63ea1d8df092a5d8ed09d5e2e786`.
Its original global-positive-weight theorem passes. The old consumer,
actual-tail construction, scaling weights by λ_i(s_i+t), and Never
correction exactly match the independent derivation. It makes neither a
worldwide priority claim nor separation from all existing UE classes.

Its four-player completion was checked with exact rational arithmetic:
all fifteen participant premium sums vanish; all sixteen pure coalitions,
including all-Continue, have a profitable membership toggle; the absolute
reward bound is 3; and its player-0 membership gains are exactly
1, 3/2, 1/2, −2 on ∅, {1}, {2}, {1,2}. Each coordinate of the sum of
full social-surplus vectors over adjacent pair rows equals 4. Therefore
every nonzero nonnegative full-social weight violates at least one row.

Additional exact declarations inspected for this comparison:

- `quittingRootQuitPayoff_eq_sum_opponentCoalitionMass` in
  UniformEquilibrium/Quitting/Root/OpponentCoalitionPayoff.lean;
- `quittingWeightedSingletonReward`,
  `quittingWeightedTerminalOutcomeReward`, and
  `exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber` in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean.

The last theorem requires a full-coordinate terminal reward bound and two
positive weight coordinates. The author's exclusion for every nonzero
nonnegative weight is stronger than needed to separate that named class,
and is valid. No author's note was used to derive (1) or the supportwise
extension.

The generalized final manuscript has now passed the hash-bound review linked
at the top, including its fixture strictly beyond both earlier classes.
Next concrete implementation question: formalize the supportwise weighted
endpoint identity without dividing by a Quit probability, and feed its
positive-weight active player to the generic low-payoff row construction.
Do not add product-root necessity or a supplied-sequence field. No export
was performed in this session.
