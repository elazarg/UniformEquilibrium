# Independent adversarial review of graph-free H/J-flat Fin4 existence

Reviewer: CODEX_NASH_BOX.

Reviewed the complete frozen candidate
`notes/CODEX_TURING_BOX__GRAPH_FREE_HJ_FLAT_FIN4_UNIFORM_EQUILIBRIUM.md`,
SHA-256
`0140a9eb121dff1ff140cde52f7e733e9066b4dfeb1abc07914c72dd4ad1e927`.
This review is independent ordinary mathematics, not a Lean build or an
export. I did not edit the candidate or consult another review's proof
verdict. The source audit below is static inspection under the displayed
imports; it does not claim a new kernel check.

## 1. Separate verdicts

SOUNDNESS: affirmative. I found no unresolved mathematical objection to
the stated raw-table theorem. The proof supplies its strategic witnesses
and reaches the full original-game fixed-target uniform-payoff endpoint,
not merely a finite-menu equilibrium or a child-game certificate. The
paid non-Nash triangle branch is sound, including product equality.

COVERAGE: not established by this frozen candidate. Removing the old
sink/receiver graph guard and strict-seed requirement genuinely enlarges
those raw predicates, but does not by itself show new UE coverage beyond
all implemented producers and accepted packets. The displayed calibration
table is already covered. An exact witness outside the complete selection
sets of the applicable producers is still needed before export. This is
separate from proof correctness, and is not an objection to the theorem
as an ordinary mathematical implication.

## 2. Claim and semantic boundary checked

There are exactly four players, arbitrary finite real terminal rewards,
zero live and Never payoff, independent private randomization, and one
unrestricted behavioral replacement at a time. Own singleton rewards are
nonnegative. A nonzero nonnegative weight vector satisfies H>=0 and J<=0
on EVERY nonempty proper coalition, and every proper active set has a
participant flat on all its participant subrows. The conclusion is the
existence of ONE original target before accuracy, with profiles and
horizon thresholds allowed to depend on accuracy, and expected-payoff
delivery and deviation control at ALL later finite horizons.

I checked the reduction to complete independent deadline laws, including
literal Never. Conditioning on surviving public history does not provide
correlation: each player's counterfactual all-Continue private path gives
one stopping law, independently of the other private paths. A behavioral
replacement supplies another such law. Its terminal payoff is affine in
that law, so the cap is the supremum of all pure finite deadlines and
Never. No optimizing deadline need exist.

The carrier is the closure of ALL actual payoff/full-cap pairs. It is not
convexified, restricted to a root family, or declared to consist of actual
profiles. Fixed-root prefixing is continuous and preserves this carrier.
Selecting one root after a minimizing point has been fixed does not need
a continuous Nash selector.

## 3. Arbitrary-root identities and Nash preservation

For the cap-root gap g_i=Q_i-(b_i+alpha_i B_i), direct subtraction gives

    d_i'=c d_i+q_i(-g_i)_+ +(1-q_i)(g_i)_+.

This is valid off Nash and at zero/sure hazards. It uses the CAP B_i,
not the prescribed payoff U_i, in the root defect. Weighted summation
then gives the stated exact L ledger. In particular the non-Nash payment
has the favorable sign +sum a_i Delta_i; discarding it in the later
lower bound is legitimate because the weights are nonnegative.

I independently recomputed complete finite-date/Late/Never caps for 80
rational finite-law tests, with arbitrary signed reward tables and root
probabilities including zero and one. Direct prefixing matched (3), the
coordinate debt identity (4), and the proper-support weighted ledger (5)
exactly, using rational arithmetic. These finite tests are a falsification
attempt, not a replacement for the displayed general algebra.

The strict seed has the full caps in (6). Its owner can also choose Never,
which is why s_j>=0 is used. This produces positive L and, unless already
diagonal, a fixed positive lambda. The constrained chamber is compact and
nonempty. No global-minimum theorem is being substituted for its own
constrained minimum.

At full interior support, dividing by the positive opponent Continue
probability and regrouping the weighted insertion terms really yields
L(B)=sum z_S J(S)<=0. This contradicts L>=lambda E>0. Sure hazards instead
give a diagonal by exact debt contraction, so no odds division is made
there. The remaining support is proper, and the supplied flat participant
has Q_i<=s_i. Supported Nash optimality gives B_i'=Q_i and retains the
low-cap face. Proper-coalition H then retains the SAME lambda chamber.
All Continue fixes the pair only in the relevant Nash case B>=s.

## 4. Both triangle alternatives and perturbation contradictions

The sink calculation includes EVERY inactive outsider. Strict outside
cap margins permit one common small owner rate. For a universal
recipient, the hypothesis that zero is the only original root implies
that every selected perturbed Nash root tends to zero: otherwise compactness
and the closed finite Nash inequalities supply a nonzero original limit.
Outside tied labels are exactly inactive near zero. The recipient's
strictly positive linear gap dominates the quadratic remainder, and its
added Quit bonus forces rate one. This contradicts convergence to zero.
The proof does not incorrectly declare a perturbation limit nonzero.

For a bare triangle, I checked all three column inequalities for the
displayed w. If P>N, eta and sigma make w-transpose h strictly positive
in every column, including when a reverse coefficient is zero. Thus the
weighted original gap is nonnegative in a neighborhood of zero, and the
positive bonuses make some perturbed gap strictly positive there. Again
rate one contradicts convergence to zero. Arbitrarily bad higher-order
coalition coefficients do not invalidate this local contradiction; their
finite quadratic bound is all that is used.

For N>=P, the interval in (10) is nonempty exactly as claimed, all z
coordinates are positive, and h z<=0 with its flat-player coordinate
zero. The tied flat-player gap expands EXACTLY as

    -n_0 q_1+p_0 q_2+
      [r_0(T)-r_0({1,2})+n_0-p_0]q_1q_2.

Consequently (11) makes it zero, not just O(tau^2). Flatness then gives
B_0'=Q_0=C_0<=s_0 and retains the low face even at a completely weak
flat boundary. The other tied positive gaps are O(tau^2); negative
gaps are O(tau) but are multiplied by the played Quit probability
O(tau). Thus EVERY tied defect is O(tau^2). The outsider has a strictly
negative gap near zero and zero own rate, so its FULL defect is exactly
zero. Its debt, including all future responses, contracts by c.

The loss of E is linear because E>0, whereas its added defect is
quadratic. The strict singleton H payment is also linear and pays
lambda Delta_max. Equation (13) therefore retains the same chamber
without changing its seed or lambda. Product equality P=N causes no
division by zero or missing linear term: the strict SINGLETON H, not
strict product separation, supplies the payment. Cyclically relabeling
the flat participant to zero works for either directed orientation.

Exact falsification tests included both orientations of the following
finite triangle calibrations, with tied continuation (1,1,1) and an
outside cap4. Own rewards are1, pair participants and triple participants
are0, and a child's pair-passive reward is1.

- Forward gains2 and reverse losses1 give
  g_i=2q_(i-1)-q_(i+1)-2q_(i-1)q_(i+1). Rates1/2 on the triangle give
  an exact nonzero full root; the fourth player's gap is strictly negative.
- Forward gains1 and reverse losses2 give the linear gaps
  g_i=q_(i-1)-2q_(i+1). The corrected rates (tau,tau,2tau) have one
  zero gap and defects (0,3tau^2,2tau^2,0), up to the relabeling.
  This tests the prefix algebra at a formal continuation; I do not
  assert that this particular continuation is an actual carrier point.

These are concrete checks of the two finite mechanisms, not assertions
that the imposed small classes exhaust equilibria.

## 5. Exact frozen-table and degenerate-boundary checks

Rational enumeration of every proper coalition confirmed all of Section9's
H/J values and the listed flat witnesses. For the actual law with player0
sure Quit1 and everybody else Never, direct full deadline/Late/Never
enumeration gives U=(1,-1,1,4), B=(1,1,1,4), E=2,L=3. The sure-owner1
date0 seed has E=1,L=5/4, so the displayed point really lies in its
lambda=5/4 chamber.

At tau=1/100, the corrected equality-product prefix gives exactly

    Delta=(0,1/495000,1/990000,0),
    E'=960499/495000<2,
    B_0'=Q_0=C_0<=1,
    L(B')>=(5/4)E'.

I also checked the zero-own-singleton version obtained by subtracting1
from every nonempty reward entry, and the one-hot weights (0,0,0,1).
They satisfy the raw guards. No positive own reward or positive lower
bound on every weight enters the proof. The all-zero reward table with
a one-hot weight is another exact zero-H/zero-own boundary.

The passive-SINGLETON perturbation is correctly distinguished from
perturbing all passive entries. It leaves every participant-flat
comparison literal, preserves H/J on larger coalitions, and changes
singleton H/J by the stated opposite amounts. At most one A_*-a_j
vanishes, so at least three singleton H values become strict. The
intermediate theorem therefore applies without preserving insertion
graphs. These assertions were also checked with exact rational epsilon
on the zero-own and one-hot boundary tables.

For the reward limit, the same complete laws and replacements are
available at both numerical tables. Every terminal payoff changes by
at most epsilon, hence every full cap by at most epsilon and every
regret by at most2epsilon. The delta/4 plus delta/2 allocation is valid.
The all-errors terminal compiler selects one ORIGINAL target; nearby
targets need not converge along an author-chosen sequence. There is
no hidden game-uniform rate or synchronization of nearby equilibria.

## 6. Bounded named-source audit

I opened the following declarations and their relevant definitions/imports.
Their hypotheses match the uses above.

- `quittingTerminalSemanticCarrier`,
  `exists_terminalProfile_sequence_tendsto_semanticPair`,
  `quittingTerminalSemanticCarrier_isCompact`,
  `continuous_quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`.
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect`
  in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`,
  and `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart`
  in `UniformEquilibrium/Quitting/Root/NashDefect.lean`.
- `abs_quittingRootEndpointDifference_sub_solo_sub_tail_sub_collisionFlow_le`
  in `UniformEquilibrium/Quitting/Root/FirstOrderProductFlow.lean`:
  its extra linear baseline mismatch vanishes on the tied coordinates;
  it is not an unconditional quadratic estimate away from them.
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
  and `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
  in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`.
- `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier`
  in `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.
  It has no missing stationarity, positivity, graph or safe-child premise.
- `abs_quittingContinuationBestResponseValue_sub_le_of_reward_close`,
  `abs_quittingTerminalExploitability_sub_le_of_reward_close`, and
  `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
  in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`;
  `quittingGame_exists_uniformEquilibriumPayoff_of_arbitrarily_close_rewards`
  in `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/UniformPayoffExistenceClosure.lean`;
  and `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

No paper theorem is needed for the new raw argument. No strategic input
remains unproduced: the seed, lambda, chamber minimizer, full roots or
paid prefix, actual approximating profiles, and fixed original target
are all produced by the proof or these named consumers.

## 7. Coverage obstruction and next required evidence

The displayed Section9 table has NO premium trap. In particular players1,
2 and3 never receive a participant reward above their own singleton1.
Thus `HasWeightedQuittingTrapLeavers` is vacuous for this table, and
`exists_uniformEquilibriumPayoff_of_weightedTrap_weakLeave` in
`UniformEquilibrium/Quitting/Classification/Existence/WeightedQuittingTrapLeaversRewardClosure.lean`
already gives its UE. I checked the predicate in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`
and the strict consumer in
`UniformEquilibrium/Quitting/Classification/Existence/WeightedQuittingTrapLeaversUniformPayoff.lean`.

A simple attempted repair is to change the grand row to(2,2,2,2).
That preserves the candidate's guards and creates a full premium trap,
but still does NOT give new coverage. Child012 has a symmetric exact
stationary equilibrium at the unique q in(0,1) satisfying

    q^3-4q^2+6q-2=0,
    U_0=U_1=U_2=(1-q)^2.

For each child player, Q=(1-q)^2 and the opponent-only absorbing
account is q^2, so the stationary indifference equation is exactly
the displayed polynomial. The child is proper. Player3 gets at least3
on every child absorption, but at most2 whenever it quits, including
the changed grand row. Thus Never is strictly optimal against this
child law, including every finite deadline, and the full game is already
solved by quiet extension. The original calibration has the same route
with joining bound1. This is an actual supplied child equilibrium and
complete outside-cap comparison, not just failure/success of one
pointwise screen.

I also compared the raw guards with the accepted sink/receiver and
two-ledger proper-support packets. The old graph restriction really
rejects the bare triangle here, and its original strict seed is absent
on the constant-one zero-H example. But both examples already have UE
by other means. Consequently neither demonstrates the export gate's
new-counterexample-class requirement. My coverage verdict remains
open, not negative for the whole new class, pending an independently
checkable nonredundancy witness. This does not delay or weaken the
affirmative soundness verdict for the frozen hash above.
