# Scope audit of three chronological Fin4 questions

Identity: CODEX_RENY.

Current conclusion: the underlying producer/consumer gaps remain open in the
inspected declarations, and all three are conjecture-facing. They are not
equally self-contained and do not justify three separate priority slots as
currently written. Keep the approximate-forward-packet question as the primary
precise interface; fold the all-summable exact-spine question into its
bounded-capacity alternative. A tightly defined paid-port consumer can remain
as a distinct, source-specific subproblem, but currently its broad alternatives
overlap that same interface substantially.

Read in full, without editing:

- `questions/FIN4_QUANTITATIVE_PAID_PORT_CONSUMER.md`;
- `questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`;
- `questions/FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md`.

This is a bounded declaration/scope audit, not a claim to have audited every
current theorem. The geometric-compression candidate was left unchanged.

## 1. Exact-spine boundedness: narrower named wrapper, valid broader corollary

The direct declaration
`all_marginalQuitHazards_summable_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardNashBellmanSpine.lean`
assumes `IsCanonicalExactQuittingNashBellmanSpine`. Its definition in
`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean`
is exactly:

    |v_t(i)| ≤ quittingRewardBound(r) for every t,i;
    v_t = F(q_t,v_{t+1});
    q_t is exact one-stage Nash against v_{t+1}.

`quittingRewardBound` in `UniformEquilibrium/Quitting/RewardBound.lean`
is the finite sum of the absolute values of every reward coordinate, not an
undefined unit cube. `quittingNashBellmanBox(M)` in
`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean` is the
payoff cube [−M,M]^4 together with the compact root-simplex coordinate.

Therefore the exact-spine question's assertion about **every bounded spine**
is broader than that direct declaration if bounded means an arbitrary
uniform bound B rather than this canonical bound. It should not be cited as
a verbatim restatement of the direct wrapper.

The broader assertion nevertheless follows rigorously from another inspected
declaration; it is not a mathematical counterexample to the question:

1. Under no UE, the same-table residual supplies all-player punishment
   normality by
   `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
   in `.../Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
2. The theorem
   `exists_uniformEquilibriumPayoff_of_unboundedExactBlockHazardCapacity_of_allNormal`
   in
   `UniformEquilibrium/Quitting/Classification/Existence/AllNormalUnboundedExactBlockHazardCapacity.lean`
   accepts **any fixed compact carrier**, not only the canonical box.
3. Given a uniformly bounded exact spine, put all its value/root annotations
   in one fixed compact box [−B,B]^4 times the root simplex. Every positive-
   length prefix is a `QuittingFiniteExactNashBellmanBlock` in that carrier.
4. If any marginal hazard is nonsummable, the prefix sums of the total
   nonnegative marginal hazards are unbounded. The generic all-normal theorem
   then gives UE, contradicting the assumption.

Thus under no UE, every **uniformly bounded in time** exact spine has all
marginals summable. Equivalently, one may instantiate the summable-residual
spine interface with zero errors and use its persistent-label consumers.
No bound uniform over all possible spines is asserted by this argument.

The question should either use the explicit canonical condition or include
this short larger-box argument. Merely saying each individual value vector
is bounded would be vacuous in finite dimension and would not suffice.

## 2. The exact-capacity assertion is current and correctly oriented

`finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`
is the literal canonical-box contrapositive invoked by both questions.

The definitions in
`UniformEquilibrium/Quitting/Bellman/Finite/UnboundedExactBlockHazardCapacity.lean`
specify positive-length blocks, all displayed endpoint annotations in one
carrier, exact Bellman equations in play order, and exact root Nash. Their
charge is

    ∑[t before terminal annotation] ∑[i] q_t(i).

The boundedness predicate is `BddAbove` over **all** such blocks, and
`hasBoundedFiniteExactNashBellmanHazardCapacity_iff` gives one real bound
independent of block length. It is neither a source-trace bound nor a numerical
constant extracted by the source theorem.

The approximate packet uses a different but comparable charge:

    a(q) = 1−∏[i](1−q_i),
    a(q) ≤ ∑[i]q_i ≤ 4a(q).

Thus using either charge for an unbounded-capacity discussion is harmless
with the factor four retained. It does not turn bounded exact capacity into
bounded approximate capacity at every positive tolerance.

## 3. Approximate-forward-packet question: strongest current formulation

Its main producer statement matches `QuittingFiniteForwardPacket` and
`quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets` in
`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`:

- one compact payoff carrier, fixed before all tolerance and charge requests;
- exact construction-order recursion v_{t+1} = F(q_t,v_t);
- support-wise endpoint error at most δ against v_t;
- punishment floor P_i−δ ≤ v_t(i), including both endpoint dates;
- arbitrarily large total absorption charge.

The reversal explanation in the question is correct: play order is the
reverse of the prefix-construction order. Its supported-action condition
matches `IsQuittingRootSupportApproxNash` in
`UniformEquilibrium/Quitting/Boundary/Repair/SupportEnlargementAlternative.lean`.
That condition is **not** ordinary mixed-root ε-Nash: a rarely used action
still needs its unweighted endpoint defect bounded by δ.

The theorem is a consumer of supplied packets; the inspected source contains
no arbitrary hard-residual packet producer. The recent finite-menu or
geometric-pivot reductions do not prove this producer either.

Self-containment issues to fix:

1. Define the game, Never payoff zero, independent randomization, unrestricted
   behavioral cap, and P_i = inf over complete independent opponent plans of
   the supremum over i's behavioral replies. This is
   `quittingPunishmentValue` in
   `UniformEquilibrium/Quitting/Stationary/MinMax.lean`, not a publicly
   correlated or finite-menu punishment value.
2. Replace “positive-minimum hard residual” by an explicit contrary hypothesis
   of no UE and a list of the consequences actually used, or define the
   retained residual. Matrix `ResidualHardClass` alone is not the same as
   `FinFourQuantitativeFullSupportHardResidual`, which also carries a terminal
   exploitability witness and all-player normality.
3. Define the “canonical admissible payoff region.” The consumer requires
   only a fixed compact K; it does not use this undefined phrase. State the
   exact quantifier as one common compact K before every δ,Q. If a particular
   reward cube is intended, write it explicitly. A new finite bound chosen
   separately after Q would not satisfy the consumer.
4. The macroscopic-seam paragraph does not define normalized motion, the
   binding set, or the class of limiting roots. The relevant ordinary-math
   identity in `PAIRED_HULL_REVIEW__NORMALIZED_MOTION_CONVEX_CIRCULATION.md`,
   Section 4.2, assumes b ≥ P and b_i ≥ r_i({i}), and considers positive
   absorption tending to zero with support error tending to zero. Its set is
   conv{r({j})−b : b_j=r_j({j})}, not unshifted reward columns and not all
   arbitrary small product roots. Those restrictions should be stated if
   this optional paragraph remains. It is not a declaration of the finite
   packet consumer.
5. The rank and macroscopic-transition alternatives need a definition of a
   complete source state and a total next-state-or-terminal-consumer rule.
   Otherwise “a rank” or “an accepted charge” is not a standalone theorem.

These are clarifications to a genuinely open, conjecture-facing target, not
a finding that the main packet statement has been solved or is incorrectly
oriented.

## 4. Exact-spine question: overlap and two substantive quantifier gaps

Its old filename emphasizes two persistent labels, but its actual title and
body now concern bounded capacity and all-summable spines. The mathematical
barrier is current; no persistence selector is supplied by the cited results.
Ordinary canonical exact-spine existence is already supplied by
`exists_exact_quittingNashBellmanSpine` in
`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`; it does not
produce a source-compatible spine and may select the phantom all-Continue
spine.

Two stronger wording problems remain:

- The proposed conclusion “every source-compatible all-summable exact spine
  contradicts the retained data” is not by itself a UE proof unless the
  question also supplies or requires the construction of at least one
  source-compatible spine. The compatible class is undefined and could be
  empty. Ordinary exact-spine existence does not discharge this nonvacuity
  obligation. The claimed sentence “Any of these conclusions proves …” is
  therefore missing a producer hypothesis for this alternative.
- “Equivalent useful conclusions” should be “sufficient mechanisms, with the
  following producer/consumer obligations.” No reverse equivalence is stated
  between terminal approximate Nash, a source-preserving restart construction,
  and a finite rank on complete sources. Source-preserving existence is not
  obtained from semantic UE existence just by naming those alternatives.

For the approximate-spine alternative, an exact sufficient interface is
`QuittingSummableResidualNashBellmanSpine` in
`UniformEquilibrium/Quitting/Debt/Dynamic/SummableResidualNashBellmanSpine.lean`:
one uniformly bounded annotation stream, nonnegative summable Bellman errors,
and nonnegative summable one-stage Nash errors, with the displayed inequalities
at every time. A single fixed nonsummable marginal then suffices under
all-player normality, by splitting into the unique-persistent and
two-persistent cases. The relevant consumers are
`isUniformEquilibriumPayoff_soloReward_of_uniquePersistent` in
`.../Classification/Existence/AllNormalUnboundedExactBlockHazardCapacity.lean`
and `exists_uniformEquilibriumPayoff_of_twoPersistent` in
`.../Debt/Dynamic/SummableResidualPersistentClosure.lean`.

The question's phrase “summable in the probability mode required” should be
replaced by those actual error conditions, or by another named consumer's
precise conditions. Generic source-weighted or reach-weighted summability is
not automatically the unweighted summability required by this interface.
Support-wise error summability is stronger than the ordinary root-Nash error
required here. The source/provenance restrictions may be necessary for a
particular construction, but are not additional semantic-consumer fields.

This question now repeats the forward-packet question's bounded-capacity
alternative and its terminal/rank/macroscopic escape options. I recommend
folding it into that question as a proved obstruction plus one precise
source-restart subtask, rather than giving it another full priority slot.

## 5. Paid-port question: still open, but not yet a self-contained packet

There are genuine actual-source declarations behind it. For example,
`exists_finFourMinimumRealizingSequence_offMinimumActualReachPaidPort_of_debtSumInf_pos`
in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourArbitraryClockMinimumActualReachPaidPort.lean`
selects a compact minimum and a realizing sequence, then an actual finite-
replacement descendant carrying a paid row. Its object explicitly retains
the original source index, target profile, replacement ancestry, observer,
source-supported pure witness, and gain/reach bounds. The literal Fin4 bounds
include observer debt ≥ D_*/4 and paid witness gain ≥ D_*/16.

The distinct family interface
`FinFourFullReplacementQuantitativePaidPort` in
`.../StoppingLaw/Endpoint/FullReplacementQuantitativePaidPort.lean`
has one observer fixed before every sufficiently late rank of a retained
subsequence, while its dates and rows may vary. These two scopes should not
be conflated by an unspecified “supplied source sequence.”

The exact cap-lifted trichotomy is
`QuittingPaidCapLiftedSource.chargedNearReturn_or_quantitativeDebtDescent_or_inertStall`
in `.../StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`. It is genuinely
exhaustive and has a terminal consumer on the charged branch. The remaining
descent and inert branches are not consumed by the inspected source.
The sequence-level consumer
`exists_uniformEquilibriumPayoff_of_retainedCharge` in
`.../StoppingLaw/Endpoint/PaidCapPortSequenceNearReturn.lean` still requires
an eventual positive absorption floor and cap displacement tending to zero.
It does not produce that floor.

Specific definition and sufficiency gaps:

1. D_* must be specified as the infimum over actual profiles of the **sum**
   of their four full behavioral debts. Its compact-carrier minimum is not
   assumed to be attained by an actual profile. “One complete actual minimum
   source” should mean a compact minimum plus an actual realizing sequence
   and its retained causal data, not a Nash profile at an attained minimum.
2. A “source passport” is not defined. The question mixes a hard residual,
   minimum point, complete outcome law, actual profiles, ancestry, and paid
   row, but gives no mathematical state type or transition relation. It must
   identify the actual initial datum and what each transition preserves.
3. Distinguish the row's opponent-reach-weighted pure-witness gain
   `row.liveMass * row.reachedGain` from an unspecified full-profile unilateral
   payoff increase. The quantitative row interface carries the former along
   with own-survival and joint-reach bounds; “realized gain” should be defined.
4. The exact inert object retains every finite all-Continue prefix and its
   shifted paid witnesses. Its semantic limit is not an infinite behavioral
   profile which reaches the original suffix after infinitely many prefixes.
   The declaration's `InertStall` comment explicitly excludes that reading.
5. The rank alternative does not explicitly require terminal states with UE
   consumers or total production of a strictly lower child at every nonterminal
   source. A rank that decreases on an optional transition relation is vacuous
   if no transition is supplied. Add both requirements, as actual equations
   or quantifiers rather than a reference to “renewability.”
6. “Prove one of the following exhaustive conclusions” lists possible solution
   strategies, not an established exhaustive mathematical classification. The
   trichotomy of existing ports is exhaustive; the catalogue of desired
   consumers is not a theorem of equivalence or necessity.

This can be a distinct priority subproblem if its input is one explicit
actual paid-port object and its output is one exact checked return/terminal
interface. In its current broad form it is another formulation of consuming
the same bounded/inert chronological residual.

## 6. Recommendation and stopping point

All three remain relevant to the conjecture, but “all current and
conjecture-facing” should not be equated with “all exact, self-contained, and
nonoverlapping.” I recommend one primary approximate-forward-packet source
question and, if desired, one sharply scoped paid-port consumer subquestion.
The exact-spine barrier belongs as a lemma/alternative inside the first,
unless a genuinely distinct source-compatible restart object is specified.

No question was edited. No claim is made that chronology is necessary for
all possible UE proofs; independent table-to-profile selection remains a
legitimate alternative route. The next editorial decision is which exact
source state and next-state-or-terminal rule the retained paid-port question
is meant to quantify over.
