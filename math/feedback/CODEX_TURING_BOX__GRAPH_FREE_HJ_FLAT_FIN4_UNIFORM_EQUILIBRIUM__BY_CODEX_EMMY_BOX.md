# Independent review: graph-free H/J and proper-flat Fin4 theorem

Reviewer: CODEX_EMMY_BOX.

Reviewed object: the COMPLETE file
[`CODEX_TURING_BOX__GRAPH_FREE_HJ_FLAT_FIN4_UNIFORM_EQUILIBRIUM.md`](../notes/CODEX_TURING_BOX__GRAPH_FREE_HJ_FLAT_FIN4_UNIFORM_EQUILIBRIUM.md),
frozen SHA-256
`0140a9eb121dff1ff140cde52f7e733e9066b4dfeb1abc07914c72dd4ad1e927`.
The hash was verified before review. This is an independent ordinary-
mathematical reconstruction, not a Lean check or export approval. No
other review or coordinator interpretation was used to establish soundness.

## 1. Separate verdicts

**Soundness: PASS for the exact frozen theorem.** I found no unresolved
mathematical objection after reconstructing the complete argument from
its raw guards. In particular the non-Nash paid prefix uses the FULL cap
defect, preserves the SAME constrained chamber, and closes the equality
case P=N. The final passive perturbation legitimately removes strictness
without matching nearby targets. No unproduced strategic witness remains.

**Conjecture-facing coverage: a complete raw-data producer, with bounded
guard expansion established; nonredundancy against all existing existence
classes remains UNESTABLISHED.** This is not another supplied-object
verifier: finite rewards and one finite nonzero nonnegative weight vector
are the only inputs. It removes both the prior sink/receiver graph guard
and strict singleton seed guard. It does not decide arbitrary Fin4.
The frozen numerical calibration itself, and two simple variants examined
below, have an explicit quiet-child stationary Nash equilibrium. They
must not be presented as witnesses of a newly solved actual game family.
This coverage limitation does not affect soundness of the class theorem.

No Lean command was run. Named source statements and their imports were
opened statically; the new raw-class mathematics is not claimed Lean-checked.

## 2. Exact claim and unrestricted semantics reconstructed

There are four players, finite real r_i(S) for every nonempty coalition,
zero live/Never payoff, independent private randomization, and unrestricted
complete unilateral behavioral replacements. Put s_i=r_i({i})≥0. For one
nonzero a≥0, every nonempty proper S obeys

    H(S)=∑[i] a_i*(r_i(S)−s_i) ≥ 0,
    J(S)=∑[i∉S] a_i*(r_i(S∪{i})−r_i(S)) ≤ 0.

Every nonempty proper A has a participant i whose EVERY participant
subrow inside A is at most s_i. The desired conclusion is one original
uniform-payoff target, chosen before accuracy, against the full behavioral
deviation space at all sufficiently long finite horizons.

The deadline-law reduction does not lose deviations. Before absorption,
all publicly active histories are repeated all-Continue. One player's
private behavioral randomization determines a private deadline law;
conversely a private deadline draw is executable. A complete replacement
has expected terminal payoff equal to a mixture of pure finite deadline
payoffs and literal Never. Independent private draws do not supply a
correlation device. Thus the full cap B_i is precisely the supremum over
that entire law space, not a bounded menu. It need not be attained.

There is an independent source-level safeguard: the actual definition
`quittingContinuationBestResponseValue` in
`UniformEquilibrium/Quitting/Root/FirstBranch.lean` is the supremum over
ALL behavior strategies. The splice theorem
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean` has exactly
the required unrestricted Continue branch. The proof does not need to
replace that supremum by an attained or finite optimizer.

Let K be the closure of actual pairs (U,B). The finite reward box is
bounded and B≥U because the prescribed own strategy is a legal replacement.
Both facts survive closure. This gives a compact, generally nonconvex K;
no point in its boundary is silently declared an actual profile.

For a selected root q and fixed carrier point, define c, α_i, Q_i, b_i,
C_i=b_i+α_i B_i and g_i=Q_i−C_i as in the candidate. Complete prefixing is

    U_i'=q_i Q_i+(1−q_i)*(b_i+α_i U_i),
    B_i'=max(Q_i,C_i).

Continuing retains all possible old responses, including Never. The map
is continuous in (U,B) for this FIXED q. Actual prefixing and closure
therefore preserve K even when q is chosen after the carrier point is
known. No continuous Nash selector is needed.

## 3. Arbitrary-root identities and the two ledgers

The elementary two-endpoint identity gives

    Δ_i=q_i*(-g_i)_+ +(1−q_i)*(g_i)_+,
    B_i'=q_i Q_i+(1−q_i) C_i+Δ_i,
    d_i'=c d_i+Δ_i.

Consequently E'≤cE+max_i Δ_i. At full root Nash, EVERY Δ_i vanishes,
including for inactive players. Hence E'=cE exactly. Checking Nash only
on the root support would not suffice; the frozen argument never does so.

If q has proper support, all nonempty realized root coalitions are proper.
Since q_i Q_i+(1−q_i)C_i is the successor payoff evaluated at continuation
B, weighted summation yields exactly

    L(B')=c L(B)+∑[S≠∅] p_q(S) H(S)+∑[i] a_i Δ_i.

There is no missing singleton subtraction: probabilities including the
all-Continue mass sum to1. The Δ term has the POSITIVE sign in this cap
ledger. It harms the ratio chamber only through the E' error term.

These are the exact identities in
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`)
and `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart`
(`UniformEquilibrium/Quitting/Root/NashDefect.lean`). The independent
derivation agrees with those declarations, including the True/Quit and
False/Continue probability orientation.

## 4. Seed, chamber and exact-Nash preservation

With H({j})>0, the sure-owner-j actual profile has precisely the caps (6).
For the owner the possible payoffs are s_j and0, so the use of s_j≥0 is
explicit and valid even when s_j=0. For another player, Quit at the root
and waiting past it give the two stated rewards; its own singleton is
not an omitted earlier deadline because the owner's quit is already at0.
Thus L(B)≥H({j})>0 and B_j=s_j. If E>0, the produced positive λ=L(B)/E
defines a nonempty compact chamber C.

For a full cap-Nash root, c=0 gives a diagonal immediately. Otherwise,
full support would make all rates interior. Dividing indifference by
opponent survival and using positive odds z_i gives

    B_i−s_i=∑[∅≠A⊆I\{i}] z_A*(r_i(A∪{i})−r_i(A)).

Regrouping the weighted sum by A gives L(B)=∑ z_A J(A)≤0, impossible
at a positive-E chamber point. Every other nonempty full root therefore
has proper support D. A flat participant of D has Q_i≤s_i and supported
Nash optimality makes B_i'=Q_i. This preserves the low-cap face. The
ledger and exact contraction preserve L≥λE with the SAME λ.

Minor wording clarification, not a gap: "All Continue fixes the input"
in Section3 is true when All Continue is a cap-Nash root, as it is in
that paragraph. For an arbitrary non-Nash all-Continue prefix the cap map
is max(s_i,B_i), not automatically B_i. Section7 correctly excludes the
all-Continue Nash root whenever some B_i<s_i.

No claim about an unconstrained/global minimum is needed. The only
minimum used is E on C, and every proposed improving operation is proved
to stay inside C. This is the correct use of constrained compactness.

## 5. Complete finite graph escape audit

For B≥s with tied set T, a sink i gives a one-owner root. Its own endpoints
are equal, and every other Continue-minus-Quit difference is exactly (9).
Tied-player inequalities follow from absence of outgoing positive arrows;
strict outside margins handle all other players simultaneously at a small
positive rate. This is a FULL root, not a subgame equilibrium.

For a universal recipient, assume zero is the only original full root.
Perturbed finite Nash roots exist. Every cluster as ε→0 is an original
Nash root because the finite payoff inequalities are continuous. Hence
the whole chosen family tends to0, with no selection continuity assumed.
Every outside-T coordinate has a strictly negative original gap at0,
so it is EXACTLY inactive in all sufficiently small perturbed roots.

The recipient's own rate never enters its endpoint gap. On the remaining
opponents, the positive incoming linear term dominates the finite quadratic
remainder; for a singleton T the original gap is identically0. Adding ε
therefore makes its Quit gap positive near0. Nash would force its rate1,
contradicting convergence to0. The conclusion is a distant ORIGINAL full
root, not a purported nonzero limit of perturbed roots.

The finite census is exhaustive. For |T|=1 there is a sink. For |T|=2,
either there is a sink or both arrows occur and there is a universal
recipient. For |T|=3, no sink forces each outdegree≥1; no universal
recipient forces each indegree≤1. Total degree is then exactly3 and every
degree is1, hence a bare directed triangle. Negative and zero insertion
differences are both absent arrows; positive reverse chords are not lost.

In that triangle, the displayed w when P>N has strictly positive column
sums wᵀh. Its construction is valid with zero reverse coefficients: η>0
is selected before the product bound and no n_i is divided by. Under the
same unique-zero-root assumption, all outside coordinates again vanish
exactly. Then ∑w_i g_i≥μt−Kt² and the positive ε∑w_i term force a rate1.
This correctly supplies a nonzero FULL root without H/J or flatness.

## 6. Paid non-Nash prefix: exact face and quadratic charge

For N≥P>0 every reverse n_i is positive. The interval (10) is nonempty
because its lower endpoint is at most its upper endpoint exactly when
P≤N. Direct multiplication verifies

    (hz)_0=0,     (hz)_1≤0,     (hz)_2≤0.

After making the flat participant0, its original gap at tied cap is

    g_0=−n_0 q_1+p_0 q_2+κ q_1q_2.

The rational correction (11) sets this gap EXACTLY to0, not just to
second order. Its denominator tends to p_0>0, so for small τ all three
rates lie in (0,1), with q=τz+O(τ²). Flatness applies to every possible
forced-Quit coalition of0 and gives B_0'=Q_0=C_0≤s_0. No strict pair or
triple participant deficit is required for the low-face preservation.

For the other tied coordinates the positive part of the gap is O(τ²),
whereas its negative part is O(τ). Multiplying the latter by q_i=O(τ)
proves Δ_i=O(τ²). At the inactive outsider, its strict original margin
keeps g_k<0 and q_k=0, hence Δ_k=0 EXACTLY. Its entire unrestricted debt
contracts; there is no paid-prefix loophole in a late or Never deviation.

The same selected τ gives three estimates: Δ_max≤Kτ², 1−c≥Zτ/2 and
p_q({j})≥z_jτ/2. Therefore E decreases strictly. The weighted cap ledger
and H≥0 give exactly

    L(B')−λE' ≥ c*(L(B)−λE)
                 +(z_j H({j})/2)*τ−λKτ² ≥ 0

after shrinking τ. The strict singleton surplus funds the FULL root
defect, and λ is not reselected. This proves improvement inside the
same C. Product equality N=P creates no singularity: the interval can
collapse, hz can be0 in every coordinate, and the rational correction
still gives the exact required low face and the quadratic bound.

## 7. Minimum contradiction and final reward closure

At a hypothetical positive minimum in C, if B_i<s_i for some i then
all-Continue is not Nash and finite full Nash existence gives an escaping
root. Otherwise B≥s. Its tied set is nonempty by the low face, and cannot
be all four players because that would give L=0<λE. Thus the census in
Section5 applies to EVERY possible tied set. The only extra case is a
bare triple; P>N uses the exact-root escape, and N≥P uses the paid prefix
provided a strict singleton is inside that triple. Two strict singleton
labels suffice to meet every proper triple. The minimum is consequently0.

A diagonal (v,v) in the ACTUAL semantic carrier supplies actual profiles
with U and full B tending to this SAME v. The diagonal consumer therefore
selects a fixed target before accuracy. It is not an exact terminal Nash
existence argument, and it needs no public randomization or chronology.

For the all-passive singleton perturbation, own s_i and EVERY participant
subrow are unchanged literally. For singleton {j}, H gains
ε*(∑a_i−a_j) and J loses the same number; other H/J entries are unchanged.
At most one of these increments can vanish since a≥0 is nonzero. Thus at
least three singleton H values become strict, so the intermediate theorem
applies regardless of the perturbed graph. Zero weights cause no exception.

Each perturbed game is ε-close coordinatewise. Reusing the same laws changes
each prescribed and deviating payoff by at most ε, hence the full cap by at
most ε and terminal regret by at most2ε. The proposed ε=δ/4 and nearby
regret≤δ/2 give original regret≤δ. Applying the all-errors compiler then
selects one ORIGINAL uniform-payoff target. Alternatively, the named
reward-closure theorem has exactly the allowed varying-nearby-target
quantifier. Neither route synchronizes nearby targets or needs uniform
control of their λ, rates or horizon thresholds.

All strategic inputs are produced. The seed is actual; the minimum comes
from compactness; finite roots come from full finite Nash existence and
the verified escape proofs; the paid prefix has explicit rates; carrier
membership yields actual approximants; perturbation and the named semantic
consumer yield one original target. I found no assumed child equilibrium,
quiet extension, optimal-response attainer or rate/convergence selector.

## 8. Optional valid strengthening; not an expansion of this review's scope

The same final theorem holds for any NONEMPTY finite player set of size
at most4. For two or three players, a positive chamber's tied set is
proper and therefore has size at most2; the paid-triangle case is absent.
Passive perturbation gives at least n−1 strict singleton labels, so gives
a strict seed when n≥2. For n=1, the sole sure-quitter is exact Nash
because s≥0. This is optional; the reviewed frozen statement remains Fin4.

The finite P>N lemma also admits a clean standalone generalization: for
ANY finite tied set T, a nonnegative nonzero w with every column of wᵀh
strictly positive implies a nonzero full root. Perturb all tied Quit
actions by ε. Under a unique-zero-root assumption, outsiders vanish and
∑w_i g_i≥μt−Kt²; adding ε∑w_i forces a rate1. The same proof works even
if some w_i=0. This generalization does not supply the paid low-face
construction for larger arbitrary tied sets and is not a Fin5 theorem.

## 9. Exact tests, bounded separation and the quiet-extension overlap

The frozen Section9 H/J values and listed flat participants check out.
The profile with player0 sure Quit1 has U=(1,−1,1,4), B=(1,1,1,4), E=2
and L=3. The sure-owner1 seed has E=1,L=5/4, so the calibration point is
inside its chamber, not asserted to minimize it. Its outsider gap is
strictly negative for every child root, and the three displayed child
gaps give only the all-Continue full Nash root at that cap. The proposed
paid correction has g_0=0; explicitly its other gaps are
g_1=−2τ²/(1−τ), g_2=−τ². This is a valid operation test, not UE exclusion.

For an exact bounded guard separation, modify the frozen table at just
two entries: set the grand reward vector to (3,3,3,3), and set r_3({0,3})=0.
All s_i=a_i=1 remain. H(03) becomes3 instead of4, J({0}) becomes−4 instead
of−3, and the four triple J values become (−1,0,0,0) in the order
012,013,023,123. Every other H/J and every listed proper-flat witness
survives. The insertion graph is unchanged, so it still fails the prior
sink/receiver guard on the bare child triangle.

This variant also fails `HasWeightedQuittingTrapLeavers`: grand rewards3
make I a premium trap, but at coalition {0,1} the four inserted-own-premium
coordinates are (−1,−1,−1,0). Every weight strictly positive on the full
trap therefore gives a negative global floor. It fails the protected
participant half of `IsCommonQuittingPremiumLeaver` for EVERY player:
child pair01 disqualifies0,1; pair02 disqualifies2; pair03 disqualifies3.
The source definitions used for these two separations are listed below.

The singleton comparison matrix Γ is not standard-Q either. For offset
b=(−1,−1,−1,1), any hypothetical LCP solution x≥0, y=Γx+b≥0 has
y_3=3x_0+(9/4)x_1+2x_2+1>0, hence x_3=0. But then
y_0=−2x_2−1<0. This is an elementary raw-matrix separation, not a claim
that no other implementation solves the game.

Crucially, this variant is STILL NOT a nonredundant actual-coverage
witness. Independently, let r∈(0,1) be the unique root of

    r+r²+r³=1,

and prescribe stationary hazard q=1−r to child players0,1,2, with player3
Never. Each child's forced-Quit payoff is r² and its opponent-only root
absorption payoff is q². Its forced-Continue value at tail r² is
q²+r⁴=r², by the displayed cubic. Its pure Never payoff is
q²/(1−r²)=r² as well. Iterating this elementary root equality shows EVERY
finite deadline and Never pays r²; consequently its full cap and prescribed
payoff are both r². No bounded-deviation restriction is used.

For player3, every child-only realized absorption reward is at least3,
while every own-Quit terminal reward in the variant is at most3.
Coupling the same child clocks, suppressing any own Quit therefore weakly
improves reward PATHWISE: if it had quit first, allowing the proper child
clocks to terminate instead pays at least as much. Never is a full best
response. This constructs an actual stationary exact Nash profile in
the variant. It also works for the frozen original table and the
grand-only variant, whose participant3 rewards are still at most3.

For completeness, the grand-only variant additionally satisfies the
implemented strict common-leaver theorem with protected player3: every
participant3 reward is at least1, all proper supports are nontraps, and
all seven remaining-core leave inequalities are strict. Thus merely
changing the grand row does not establish even that guard separation.

The two-entry variant is useful evidence that the new raw guard set is
not syntactically contained in those named raw criteria. Its explicit
stationary equilibrium prevents promoting that observation to a new
actual-family coverage claim. A separate nonredundancy witness, if sought,
must disrupt this quiet extension or compare against the exact applicable
stationary producer; it is not needed to repair this proof's soundness.

## 10. Bounded source audit and remaining work

The route was selected through the diagonal-semantic and weighted-trap
entries of `docs/TOOLKIT.md`. Exact declarations opened under their imports:

- In `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`:
  `quittingTerminalSemanticCarrier`,
  `exists_terminalProfile_sequence_tendsto_semanticPair`,
  `quittingTerminalSemanticCarrier_isCompact`,
  `continuous_quittingTerminalSemanticPrefix`,
  `quittingTerminalSemanticPair_rootThenContinuation`, and
  `quittingTerminalSemanticPrefix_mem_carrier`.
- In `UniformEquilibrium/Quitting/Root/NashExistence.lean`:
  `exists_isZeroQuittingRootNash`, with arbitrary continuation vector.
- The exact arbitrary-root and defect declarations cited in Section3;
  plus `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
  and `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
  in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`.
- `abs_quittingRootEndpointDifference_sub_solo_sub_tail_sub_collisionFlow_le`
  in `UniformEquilibrium/Quitting/Root/FirstOrderProductFlow.lean`. Its
  additional linear baseline term vanishes on tied coordinates, as required.
- `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier`
  in `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.
  Its only extra typeclass premise is a nonempty finite player type.
- `abs_quittingContinuationBestResponseValue_sub_le_of_reward_close`,
  `abs_quittingTerminalExploitability_sub_le_of_reward_close`, and
  `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
  in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`;
  `quittingGame_exists_uniformEquilibriumPayoff_of_arbitrarily_close_rewards`
  in `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/UniformPayoffExistenceClosure.lean`;
  and `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
- For bounded coverage only: `HasWeightedQuittingTrapLeavers` and
  `quittingWeightedInsertedPremium` in
  `UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`;
  `IsQuittingPremiumTrap` in
  `UniformEquilibrium/Quitting/Classification/QuittingPremiumCore.lean`;
  `MathUE.IsFiniteCoalitionPremiumTrap` in `MathUE/FiniteCoalitionPremiumCore.lean`;
  `HasPositiveOwnQuittingPremium` in
  `UniformEquilibrium/Quitting/Classification/QuittingPremiumSupportPeelingOrder.lean`;
  `IsCommonQuittingPremiumLeaver` in
  `UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`;
  and `exists_uniformEquilibriumPayoff_of_commonLeaver_strictLeave` in
  `UniformEquilibrium/Quitting/Classification/Existence/CommonQuittingPremiumLeaverUniformPayoff.lean`.

The prior sink/receiver export's exact raw guards were also read for the
bounded graph comparison. No exhaustive Lean-tree, literature-novelty or
all-class coverage audit was attempted.

Remaining mathematical objection to the frozen SOUNDNESS claim: none
identified. Remaining COVERAGE question: exhibit and audit a genuinely
nonredundant raw-table family rather than the calibration's quiet-child
stationary family. The optional cardinal strengthening need not delay
the exact Fin4 result and must not silently change the reviewed snapshot.

## 11. Independent final-packet and coverage review, frozen cb7ef9ec

Reviewed `notes/CODEX_TURING_BOX__GRAPH_FREE_HJ_FLAT_FIN4_PACKET_DRAFT.md`
completely, all905 lines, at SHA-256
`cb7ef9ece47a9319859abc8ba76c5aa7c6a4c7abec3a3b5814b4f2b8f8e13e3d`.
The hash was verified before and during this review. This is a new independent
check of the packet's actual witness and quantified exclusions, not adoption
of another review. All calculations below are ordinary mathematics. No Lean
command, author-note edit, export, staging, commit or push was performed.

Exact-hash verdict:

- Main raw theorem and Sections1--8: SOUNDNESS PASS, consistent with the
  earlier independently reconstructed proof. No new strategic input or
  mathematical objection was found.
- New witness and bounded complete-selector exclusions: the mathematical
  separation succeeds with the two explicit repairs below. It is a genuine
  witness beyond the named raw selections and fixed calendar families, not
  the old quiet-child stationary calibration.
- FINAL CONTENT AT THIS EXACT HASH: REPAIR REQUIRED. Section9.1 has a wrong
  block-constant test point and wrong values at that printed point.
  Section9.5 unnecessarily asserts continuity of literal Never where it can
  fail. Neither error requires changing the raw theorem, witness table or
  intended coverage conclusion. A new final-content hash needs confirmation
  after these repairs; this review does not silently approve changed bytes.

### 11.1. Required point correction in the response-quotient census

For partition `0|13|2`, the printed q=(0,1/2,0,0) is NOT block-constant:
players1 and3 belong to the same block but have different rates. Moreover,
the actual residuals there are F_1=0 and F_3=−7/4, not the printed values.
This point therefore does not prove failure of the actual invariant-cube
predicate at the stated partition.

REPAIR: replace that point by

    q=(0,0,1/2,0).

It is block-constant, and direct evaluation gives EXACTLY the packet's
intended residuals F_1=−1/2 and F_3=3/4. Only the coordinate location of
the half-rate needs changing. All other displayed residual pairs are
correct at their displayed block-constant points.

Independently enumerating the15 partitions from the raw Gamma block-row
sums leaves precisely the seven partitions printed in the packet. Thus
this repair completes the original exhaustive census, not a reduced census.
The actual source predicate is `QuittingResponseInvariantOnUnitCube`, and
its necessary derivative test is
`quittingSingletonBlockRowSum_eq_of_responseInvariant`, both in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
The zero-discount `quittingDiscountedDisplacement` in
`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean` is
exactly F=(1−alpha)Q−b. No singleton-only response equivalence is assumed.

### 11.2. Required continuity correction in exact-stationary reward closure

At a nonzero stationary root the prescribed terminal formula and finite
root endpoints are continuous, but literal Never need NOT be continuous.
On this same table take q_0=1/2, q_2=epsilon>0, q_1=q_3=0. Player0's
Never payoff is4 for every epsilon>0, but0 at epsilon=0. This refutes the
printed general sentence that its Never floor is continuous at a nonzero
joint-absorption root. The example need not be Nash to refute that asserted
continuity property.

The intended closure argument nevertheless has a complete repair. If
exact stationary roots q^n on converging tables have a nonzero limit q,
joint absorption stays bounded away from0. Actual stationary values and
finite Quit/Continue endpoints pass continuously to the limit, so q
satisfies exact stationary Bellman recursion and finite root Nash.
For a player with alpha_i<1, opponents absorb almost surely, so iterating
the endpoint inequalities controls EVERY behavioral replacement including
Never. If alpha_i=1, this player is the sole positive-rate label, its
actual prescribed value is its own singleton1, and literal Never pays0.
The singleton remains nonnegative; there is no unpaid Never deviation.
Thus the limit is full terminal Nash, contradicting the proved exclusion.

This is also exactly the contracting-or-nonnegative-singleton boundary in
`IsQuittingCycleZeroDeviationMismatchAt` and
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_admissible` in
`UniformEquilibrium/Quitting/Cycles/AdmissibleCycleTerminalEquilibrium.lean`.
No continuity of full caps or Never payoffs is needed. The separate q=0
case in Section9.5 is correct: normalized rates give a nonzero homogeneous
Gamma-complementary vector, contradicting R0. Hence the claimed closure
exclusion for exact stationary producers survives after the sentence and
argument are replaced explicitly.

### 11.3. Independent raw-table and root checks

I recalculated every H and J, all flat-member tests, the entire insertion
matrix, Gamma and its inverse, and the indicated response values using
exact rational arithmetic. The table satisfies the raw theorem:

- H(singletons)=(1,1,1,1), J(singletons)=(−3,−4,0,−3).
- H(02)=5; all other pair H=0. Pair J values are exactly
  (−5,−6,−5,−8,−6,−5) in the packet's order.
- Every triple has H=3 and J=−1. The listed flat triple members are valid.
  Every proper nonempty coalition has a flat participant.
- The insertion matrix is

      h=[0,−1,1,2; 2,0,−3,−4; −4,1,0,−1; −1,−4,2,0].

  Its positive arrows are exactly the printed five. On012, P=2 and N=12,
  so this is genuinely the reverse-product paid-prefix branch. Every
  singleton has strict H, so the needed quadratic charge has a produced
  funding label, not an assumed favorable one.

Gamma has determinant45 and precisely the printed strictly positive
inverse. All six two-player principal determinants are either−1 or−9;
every triple determinant is6. A homogeneous complementary support of
size at least2 is impossible by invertibility. A singleton support has
an external negative Gamma entry. This verifies R0 and its stated stable
neighborhood directly. Each triple inverse has negative diagonal entries,
so every raw nonnegative-inverse triple choice fails. The source
`childMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`
is the literal deleted singleton block. The discrete response quotient
therefore has degree1 and positive determinant, not either named escape.

I also reconstructed the whole sure-owner induced correspondences. The
three dominance reductions for owners0,1,3 are correct. For owner2,
player1 strictly Continues; the residual two-player gaps are
1−(7/2)y and2−5x. They have exactly the two pure roots and one mixed
root printed. At the mixed root (x,y)=(2/5,2/7), the exact owner accounts
are Q_2=1/7, b_2=46/35, alpha_2=3/7. In particular b_2 already exceeds
Q_2, even at zero continuation. Every case fails owner optimality at
EVERY nonnegative continuation.

All passive recipient rewards are nonnegative, so literal Never gives
every player at least0 against arbitrary opponents. Consequently both
full caps and the ACTUAL `quittingPunishmentValue` are nonnegative. The
actual singleton-base floor condition is b_i+alpha_i*punishment_i<=Q_i,
as `quittingSingletonBaseOwnerFloorExcess_nonpos_iff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
states; it is not merely Q_i>=punishment_i. The printed calculation
excludes this exact floor condition, including owner2's positive Q.
Partial free carriers cannot help a complete nonpositive-excess screen:
the missing free labels must still satisfy their outsider joining
inequalities. Multiple sure labels are included by choosing any one
as owner and retaining the others in its induced correspondence.

### 11.4. Weighted, protected, boxed and quiet-extension quantifiers

The global floor obstruction uses the ACTUAL inserted-premium definition
over every coalition, not only coalitions inside a trap. Its two coefficient
rows are (−2,0,0,−1) and(1,−1,−2,0). Their sum is strictly negative on
the normalized nonnegative weight simplex. Thus nonzero weights, weights
approaching its boundary, and unnormalized diverging weights are all
excluded, including reward closure. The grand row makes the full set a
trap, so the trap predicates cannot become vacuous. Each player's strict
proper-triple participant deficit excludes every protected participant;
the definitions do not permit a merely selected favorable subrow instead.

For the boxed criterion, singleton{2}'s inserted-premium sum is1, whereas
`QuittingTrapChargeCoefficients.singleton` requires it to be at most a
strictly negative number. No coefficient or threshold can cure this; its
strict sign also excludes reward closure. At grand, every nonzero
nonnegative upper-average weight gives surplus8 times its total mass,
so that distinct alternative fails too. The all-Quit root correctly
falsifies the ALL-root `HasProductLowQuittingPremium` predicate, not a
different support-local statement.

For all thirteen tested children I checked the displayed sole owner,
strictly negative internal joins, and an actual strictly positive omitted
join. These are full unrestricted child Nash laws with zero joint-Never
mass, so ANY universal outside-debt bound of the stated form is false,
at every nonnegative child-weight choice and finite Never slack.
For child012 the A={2} rows are exactly

    1<=−3lambda_0+lambda_1,       2<=lambda_0−3lambda_1,

after discarding the nonpositive withdrawal terms. I read the five gain,
futureWeight and restart-floor definitions in
`WithdrawalFutureJoinRaw.lean` and its named quiet-extension dependencies.
The discarded terms really are nonpositive for every kind: nonmembers'
gain is0; the singleton member's restart floor is no greater than its
positive singleton. In particular terminal security uses the actual
`deadlineWithdrawalSecurityValue_le_singleton`, not an unsupported0
upper bound. The same contradiction applies to the capped-clock rows.
Its member2 advance coefficient is identically0 under perturbation,
while the summed other coefficients remain negative. Arbitrary large
weights do not invalidate the reward-neighborhood contradiction.

The inspected full behavioral consumers are
`quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin`
in `WithdrawalFutureJoinFixedTarget.lean` and
`quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_slack`
in `CappedClockChildDeletionAdapter.lean`, in that directory. The packet
correctly separates these UNIVERSAL raw certificates from a conditional
consumer supplied only with one favorable actual child equilibrium.

### 11.5. Nonstationary calendars and transport: independent confirmation

The named paired raw definitions were checked in place. In
`PairedCycleSchedule.lean`, the exact
`RawRegion.eq_partner_of_singleton_lt` allows at most one below-own
singleton per recipient. Here each row has two. For `RawSource`,
`WeakRawSource`, `InverseRawSource`, `ScheduledPairCapSource` in
`CrossedMatchingPhaseSource.lean`, and `BelowSingleton.RawFamily` in
`BelowSingletonJointPhaseSource.lean`, BOTH off-scheduled participant
pairs must be capped by the recipient's singleton (strictly below for
the last family). Player0's two positive premiums at02 and03 defeat
EVERY matching. These signs are strict, affine-invariant under positive
recipient scaling, and remain under reward closure.

The separate passive-reward ray's specified mate-pair participants A,A
both exceed own1; every target pair has a participant strictly below1.
This necessary-premium exclusion is correct for that entire raw family,
all relabelings and positive recipient-affine images and their closure.
The actual family definition was checked in the author's notebook
Section19.1, rather than inferred from a selected four-phase solution.

I independently derived the complete four-positive-singleton field(15).
Its opposite-equation subtraction has the stated strictly positive
coefficient determinant, forcing all four Continue probabilities equal.
The unique proper solution is u=(3−sqrt(5))/2. The edited pair02 then
gives the actual positive deviation (3sqrt(5)−5)/2. Favorite-adjacent
orders are also correctly rejected without assuming symmetric hazards.
This is a whole ordering/rate exclusion for exactly one positive proper
phase per owner, not a search over selected numeric schedules.

The balanced-singleton mesh certificate must instead be tested through
its actual `arc`, `active`, `soloFloor` and `opponentDivergence` fields
in `BalancedSingletonCertificate.lean`. The packet's separate soloFloor
failure on THESE four-positive-singleton words is correct: favorite-
adjacent orders force a coordinate below1 immediately after the favorite;
the nonadjacent field has value u<1 before the owner's phase. Finite-root
collision optimality is not substituted for mesh optimality.

The signed-four-cycle source requires a strict positive predecessor
four-cycle in Gamma in BOTH spectral branches; the actual singleton
graph is only a matching. The cyclic-child `RawTable` requires a
strict positive child three-cycle, also absent. I read these literal
fields, as well as the two-pair group and cross-mass raw reward entrances:
grand defeats every designated pair-average bound, and every potential
designated recipient has a favorable singleton defeating the cross-mass
bound. No stronger conditional supplied-source consumer is excluded.

Finally the passive-triple family's own/low singleton values pin every
recipient affine scale and shift to1 and0. Its participant pair values
remain in{−1,0,2}, never5. The sequence argument is valid even for
unbounded triple/grand parameters: finite relabelings have a fixed
subsequence, and the low/own rows force scale→1 and shift→0. This is
table-membership transport only; it never assumes that changing every
terminal reward by a constant preserves literal Never payoff0.

### 11.6. Precisely surviving coverage and strategic-input verdict

After the two stated content repairs, this new table is admitted by the
new COMPLETE raw producer and excluded by the compared complete raw
selections, exact stationary producers (including their reward closure),
and the specifically bounded nonstationary raw/calendar families.
The old quiet-child stationary overlap has been genuinely removed.

It does NOT exclude all-errors approximate stationary witnesses, every
balanced-singleton certificate with arbitrary period/repeated owners,
longer or mixed calendars, arbitrary favorable-child extension, or an
unknown distant implicit neighborhood. In particular the four-positive-
singleton argument is not a classification of the whole general
`BalancedSingletonCycleCertificate` type. The final scope paragraph
already makes these necessary limitations explicit. None is an input
or missing step in the main raw H/J+flat proof.

No unproduced strategic input was found in Sections1--8 or introduced
by the witness comparisons. The theorem still obtains its seed, closed
carrier, constrained minimum, finite root/paid-prefix escape, diagonal,
actual approximants and original fixed target internally. Its reward
closure correctly allows nearby targets to vary and selects one original
target. The two frozen-byte corrections above concern final-content
accuracy in coverage proofs, not the existence theorem's mathematical
mechanism. Final-hash approval remains pending their explicit repair.
