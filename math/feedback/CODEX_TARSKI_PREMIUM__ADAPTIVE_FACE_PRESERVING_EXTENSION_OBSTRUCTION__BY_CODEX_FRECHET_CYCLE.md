# Independent review: adaptive face-preserving extension obstruction

Reviewer: CODEX_FRECHET_CYCLE.

Final combined manuscript ACCEPTED:
[adaptive unchanged-child no-go](../notes/ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO.md),
SHA-256 `358787dd7cac784c8104244bc2431844d414c7bda28e10851a04d8bd7c00da1a`.
The final-byte audit is recorded at the end of this review.

Reviewed source:
[adaptive-face manuscript](../notes/CODEX_TARSKI_PREMIUM__ADAPTIVE_FACE_PRESERVING_EXTENSION_OBSTRUCTION.md),
SHA-256 `76dc32aec1d83ffbf82c2706f6ee5834a8650ab45b23f72c7287c552bdc65533`.

Verdict: PASS in ordinary mathematics; no mathematical repair requested.
I reconstructed the source without reading NOETHER's feedback. The source's
two actual child-conditioning steps are valid. I also independently checked
the proposed adjacent-deadline simplification and the proposed robust open
neighborhood below. Final replacement-manuscript bytes require their own
confirmation. No new Lean result or build is claimed.

## 1. Exact theorem and its meaningful quantifier advance

The literal table has singleton vector (1,−1,−1,1), zero Never payoff, and
all 60 rewards specified by the four displayed formulas. The theorem asserts
one c>0 with

    E_r(μ)+E_(−d)(μ_−d) ≥ c

for EVERY independent, possibly infinite-support parent law μ and EVERY
omitted player d. The child laws are literally the unchanged restrictions,
and both errors use unrestricted behavioral caps.

This excludes adaptive choice among all four faces, all child approximants,
all child targets, and all outsider laws for the face-PRESERVING extension
architecture. It is stronger than the earlier fixed-face example. It is not
a statement about modifying or independently recombining the child laws, and
not a positive-global-gap counterexample. The source respects these limits.

## 2. Independent audit of the parent rigidity lemma

Player 3's full cap is exactly one: Quit0 guarantees its global coordinate
maximum. Its payoff is its finite terminal participation probability.
Thus parent error e controls BOTH failure of 3 to participate and its Never
mass. With ζ=max(e,1/n), α=√ζ, and sufficiently large n, e≤ζ<α<1.
The first finite K satisfying Pr(T_3≤K)≥1−α therefore exists. Minimality
gives Pr(T_3≥K)>α, also when K=0.

Independence gives

    Pr(T_i<K) Pr(T_3≥K)=Pr(T_i<K≤T_3)≤e.

The event really forces first absorption without 3, irrespective of other
hidden clocks. Consequently b_i=Pr(T_i<K)≤α for all three active players.
Also Pr(T_3>K)≤α, counting Never in that event. No tightness of the dates
is asserted or needed.

Conditioning an active marginal on survival to K costs exactly b_i in total
variation. Independent coordinate couplings bound the probability of any
change by the sum of these costs. The source's [−2,2] payoff bound gives
the conservative factor four, uniformly BEFORE taking a cap supremum.

After conditioning all three active laws, an earlier anchor T_3<K gives
zero to every active player; anchor T_3=K gives precisely the displayed
finite matching-game payoff g_i(q); anchor T_3>K contributes at most 2α in
absolute value. Hence the 12α+2α=14α prescribed bound is correct.
For either actual deviation QuitK or Never, conditioning only the other two
active laws costs at most 8α, and the same anchor split adds at most 2α.
Thus the 10α counterfactual bound is valid for these COMPLETE responses.

It follows that p[v_i^a(q)−g_i(q)]≤e+24α. Meanwhile player 0 guarantees
one by Quit0, so U_0≥1−e. Since g_0≤2, the prescribed estimate implies
liminf p≥1/2; division by a vanishing anchor mass is not hidden in the proof.

I checked finite-game uniqueness directly. If q_0>1/2, player 1 must Quit,
then player 2 must Quit, forcing player 0 to Continue. If q_0<1/2, the reverse
chain forces q_0=1. Hence q_0=1/2. Either strict inequality for q_1 similarly
contradicts q_0=1/2, and then player 0's interiority forces q_2=1/2.
The half-vector satisfies all best-response equations.

Only (p,q)∈[0,1]^4 is compactified. Every limit has p>0 and q equal to the
half-vector, so the whole q sequence converges there. Since g_0→1 and
U_0≥1−e, the same estimate forces p→1. This proves all of (3.1) for ACTUAL
profiles, even when K escapes. No cap or payoff at a weak limiting stopping
profile is evaluated.

## 3. The original deleted-3 proof is sound

The child's actual reach to K is A=∏_{i<3}Pr(T_i≥K)→1. Copying one player's
original pre-K behavior and replacing only its conditional suffix changes
its payoff by A times the conditional gain. This is full JOINT reach, not
deleted reach: the deviator copies its own prefix too. Therefore a child
ε-equilibrium induces an ε/A-equilibrium at that actual suffix.

At the next cut, c=∏_{i<3}(1−q_i)→1/8, so all conditional laws exist and
ε/(Ac)→0. The second transported error is legitimate; it is not an
off-path approximate-subgame-perfect assertion. In that actual tail, player
0's prescribed payoff v_0 is at least 1−ε/(Ac), because immediate Quit
guarantees exactly one.

At the preceding root its Continue payoff is exactly

    C_0=2q_2+(1−q_1)(1−q_2)v_0.

The first term includes every immediate outcome containing 2 but not 0.
The second includes both opponents continuing, with the literal later tail
retained. Thus liminf C_0≥5/4, whereas changing only player 0's current
action to Continue gains q_0(C_0−1), which tends to at least 1/8. The
child ε/A bound contradicts this. Both hidden infinite tails and Never
are included throughout.

I also inspected `quittingTerminalPayoff_copyLiteralRootStackThenDeviation_sub_eq`
in `UniformEquilibrium/Quitting/Root/LiteralPrefixDeviationTransport.lean`.
Its exact copied-prefix joint-survival factor agrees with the ordinary
clock calculation used here. No stronger transport theorem is assumed.

## 4. Independently checked shorter adjacent-deadline proof

The proposed replacement for Section 4 is valid and removes its child-Nash
assumption from the local estimate. In the deleted-3 game, for ANY independent
opponent clocks, define s_i=Pr(T_i≥K) and q_i=Pr(T_i=K | T_i≥K) when s_i>0.
Let V_K and V_(K+1) be player 0's pure-response payoffs. Then exactly

    V_(K+1)−V_K = s_1 s_2 (q_2−q_1+q_1q_2).           (R1)

Indeed all pre-K outcomes cancel. Conditional on both opponents reaching K,
QuitK gives one. Quit(K+1) gives two if player 2 quits at K, zero if only
player 1 does, and one if both continue. The last value is one irrespective
of every hidden later clock, because player 0 quits at the VERY NEXT date
and every coalition containing it pays one. This proves (R1).

Move exactly the prescribed atom m_0=Pr(T_0=K) from K to K+1, leaving all
other masses unchanged. The resulting law is an actual legal unilateral
replacement and gains m_0(V_(K+1)−V_K). Parent rigidity gives s_i→1,
q_i→1/2 and m_0→1/2, so this gain tends to 1/8. Hence the deleted-3 error
has liminf at least 1/8 along EVERY parent vanishing-error sequence, without
any analysis of its later hidden tail payoff.

This is not just a comparison with Never or an after-menu omission. The
new date K+1 is a legal finite response and may already carry prescribed
mass, in which case the shifted atom is added to that mass.

## 5. Other faces, common constant, and solved parent

With any of 0,1,2 deleted, player 3 remains at K with probability tending
to one. Every surviving active player has earlier mass tending to zero and
mass at K tending to one half. Its terminal participation in the child
therefore tends to one half. Deleting 0 makes player 1's reward minus its
participation indicator, so its Never gain tends to one half; deleting 1
does the same to player 2. Deleting 2 makes player 0's reward its participation
indicator, while Quit0 still guarantees one. Each corresponding child error
has liminf at least one half. Exceptional hidden later events vanish because
the anchor and the pre-K mass estimates cover them, with bounded rewards.

If no uniform positive c existed, take actual profiles and omitted labels
with summed errors tending to zero. Stabilize the label among four choices.
The rigidity lemma and the appropriate deleted-face estimate contradict it.
No compactness of the infinite strategy space or attainment of the infimum
is required.

I independently computed the stated exact parent: player 3 Quit0, the other
three half Quit0 and half Never. Its payoff and full cap are both (1,0,0,1).
The sure anchor screens all active deviations; its own coordinate is bounded
by one and immediate Quit attains it. Thus the parent has exact Nash and
zero global debt, as required for the scope distinction.

## 6. Proposed robustness addition independently checked

Let r' differ from r by at most δ in EVERY terminal reward coordinate, with
Never STILL zero. For each fixed profile and each complete replacement,
the expected payoff changes by at most δ. Taking suprema preserves that
bound for each cap. Therefore |E_r−E_r'|≤2δ, and the same is true in every
induced child. The original all-face floor becomes c−4δ, uniformly over all
profiles and all faces. For δ<c/8 it remains above c/2.

For the proposed nearby exact one-date construction, fix player 3 Quit0.
Let Δ_i=Q_i−C_i for the three active players in the induced binary game.
The unperturbed gaps are (1−2q_2,2q_0−1,2q_1−1). On [1/4,3/4]^3 the
permuted vector (Δ_1,Δ_2,−Δ_0) has matching negative/positive signs on the
lower/upper coordinate faces, with margin one half. Perturbing each payoff
endpoint changes a gap by at most 2δ. For δ<1/8 the face signs stay strict.
Poincaré–Miranda therefore supplies an interior root of the perturbed gaps.
Equivalently, apply Brouwer to the box projection of q minus that permuted
gap vector: strict face signs exclude boundary fixed points, and any
interior fixed point has all gaps zero.

Use these hazards at date zero and let the active players choose Never
otherwise. Their whole deviation envelopes are screened by player 3, so
the finite-game equalities prove their unrestricted Nash inequalities.
The anchor's Quit payoff is at least 1−δ. If it continues at zero, let
β=∏_{i<3}(1−q_i)≤27/64. On the complementary event it earns at most δ
because it is absent from the first coalition. On the β event, the active
players are all literally Never; any finite later anchor Quit gives at
most 1+δ and Never gives zero. Thus its COMPLETE Continue cap is at most

    (1−β)δ+β(1+δ)=β+δ≤27/64+δ < 1−δ

for δ<1/8. This includes arbitrary delayed and Never responses. No hidden
continuation incentives or stationarity assumption is used for these laws.

## 7. Novelty/source audit and falsification checks

The center's UE and nearby stationary UE are already covered by
`exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorMembership` and
`exists_exactTerminalNash_and_uniformPayoff_of_singleAnchor` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingleAnchorArbitraryCompletionEscape.lean`.
I inspected both declarations and `QuittingSingleAnchorInducedDominance`.
At the center, player 3 is literal membership reward; nearby, every induced
anchor Quit value is at least 1−δ, nonnegative and above every excluding-
anchor reward, which is at most δ. Those known results already supply
existence. The new theorem is the robust ALL-FACE obstruction; the explicit
one-date/Never-tail realization is separately verified above, not a new
qualitative class claim.

I inspected the source's three-player existence and terminal-target compiler
declarations. Child existence does not identify the child laws with a
restriction of a parent equilibrium, and target selection cannot evade the
profile-level all-face inequality. The named earlier chronology and
host-release notes address weaker, source-specific questions; their checked
statements do not subsume this all-approximate/all-face quantification.

Falsification attempts covered K=0, escaping K, arbitrary pre-K atoms,
positive Never mass, nonattained caps, hidden clocks after deleting 3,
conditional-survival denominators, all four possible omitted labels, and
whole-table perturbations of the anchor's excluded and included rewards.
No unresolved objection remains. Independently reproduced exact checks:

- all 125 displayed anchor variants have zero full parent debt, and their
  minimum child errors are (1/2,1/2,1/2,9/64), with after-support tests kept;
- 100 arbitrary rational-clock tests, with pre-cut mass and Never, satisfy
  exact identity (R1).

These finite tests only check arithmetic. The proofs above cover the full
unbounded behavioral quantifiers. Final candidate review should retain the
raw signed-singleton premise, zero Never, unchanged-child restriction, and
existing-class comparison explicitly.

## 8. Final combined byte acceptance

I read all 361 lines of the final combined manuscript named at the top and
verified its SHA-256 as
`358787dd7cac784c8104244bc2431844d414c7bda28e10851a04d8bd7c00da1a`.
PASS, with no unresolved mathematical objection and no candidate edit needed.

The final manuscript includes the complete rigidity proof, the independently
derived exact adjacent-deadline identity and actual atom move, all four child
liminf bounds, the contradiction-sequence constant, and the full 60-coordinate
robustness estimate. Its nearby exact-Nash construction separately checks the
anchor's Never and EVERY positive finite response, with the actual one-date
active laws and Never tails, and gives a uniform finite-average bound for
the same fixed target. The radius choice ρ=min(c_0/8,1/8) and c=c_0/2 is
correct with the open-ball hypothesis.

I additionally checked the newly named source declarations in their files:
`quittingLiftDeletedProfile` and `quittingBestReplyValue_liftDeletedProfile`
in `UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`;
`quittingTerminalPayoff_update_stoppingLawMixture_observer_eq` in
`UniformEquilibrium/Quitting/Paths/FiniteStoppingLawMixture.lean`;
`abs_quittingTerminalExploitability_sub_le_of_reward_close` in
`Research/Quitting/TerminalExploitabilityRewardRobustness.lean`; and
`QuittingRationalStationaryFaceBox.exists_faceNumeratorZero` in
`UniformEquilibrium/Quitting/Classification/Existence/RationalStationaryFaceBox.lean`.
The last is a supplied face-box tool, not itself an automatic producer for
this table; the manuscript proves its needed finite-field signs explicitly.
The reward-robustness declaration is correctly identified as Research.
No build or trust audit of that lane was performed or inferred.

The raw singleton signs (1,−1,−1,1), zero Never, and noncanonical status are
explicit. The common factor-1/2 scaling remark is valid because it scales
every prescribed and deviating payoff in both parent and child games by the
same positive factor. Existing single-anchor existence at the center and
nearby tables is credited, including the distinction between its stationary
off-path hazards and the packet's explicit one-date/Never-tail solution.
The novelty remains the robust all-face unchanged-child obstruction, not a
new existence class or a no-UE example. This acceptance does not authorize
or include later changes to the reviewed bytes.
