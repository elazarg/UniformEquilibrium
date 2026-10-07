# Independent review of coarse Nash-regret base restrictions

Reviewer: CODEX_BROUWER. Ordinary mathematics and exact rational calculations;
no Lean execution, implementation or seal. No counterpart review was read.

## Scope and verdict

**Mathematical PASS; export-significance FAIL.** No unresolved mathematical
or strategic objection was found for either surface below. However, the
whole admitted UE class is contained in the existing concrete persistent-base
producer, as proved in the final source-inclusion addendum. The theorem is
retained internally, not accepted as additional counterexample-class coverage.

1. The generic section “A global finite Nash-regret restriction on every
   counterexample”, excluding the superseded early test table, and the final
   “Structural separation from all withdrawal families” section through EOF
   of `notes/CODEX_NOETHER__MATCHING_JOINT_PRODUCER_FALSIFICATION.md`, whole-file
   SHA256 `d0d2fa922c95ce004008afbcd4b0acdaca5ec084c2fff0d391964ee6b4e1a922`.
2. The arbitrary-base extension in
   `notes/CODEX_NOETHER__GLOBAL_CCE_BASE_RESTRICTIONS.md`, SHA256
   `5923af318a25d8891b7dda45e7c043985361f795d5eb544935272051b3e8e601`.

This is a valid original-table producer and finite necessary restriction on
every possible UE counterexample, but that restriction follows from an
existing stronger source. The structural table escapes all fourteen
five-kind withdrawal families and all three accepted two-pair tests; those
comparisons do not exclude the broader punishment-tail persistent-base
producer. Neither displayed table is new UE coverage.
No claim of excluding every stationary profile or every unspecified local
existence neighborhood is needed or accepted. An assembled standalone needs
its own bounded artifact verdict; this verdict binds the surfaces above.

## Raw statement independently checked

For each nonempty base E in an arbitrary nonempty finite player set, use the
finite free binary game u_j(T)=r_j(E∪T), j∉E. Let C_E consist of laws ν on
the free coalitions satisfying every unconditional pure-action Nash-regret
inequality Eν[u_j(T)−u_j(T^{j,b})]≥0. It is a nonempty compact polytope:
finite mixed Nash exists internally and its PRODUCT law belongs to C_E.

For |E|≥2 the member gap is

    G_i(T)=r_i(E∪T)−r_i((E−i)∪T).

For E={i}, use G_i(∅)=min(s_i,0), and the ordinary joining difference on
nonempty free coalitions. If every member's minimum of EνG_i over C_E is
nonnegative, then the game has an exact terminal Nash profile, exact Nash
at every positive finite horizon, and one fixed UE target. The profile and
target do not change with horizon or accuracy.

Consequently a no-UE table must satisfy, for EVERY nonempty E, that SOME
i∈E and SOME ν∈C_E have EνG_i<0. These witnesses may depend on E and
i. The statement does not require one correlated law harmful to all members,
does not assert that a negative law is product, and is not a converse.

## Complete strategic proof and attempted failures

Select any free mixed Nash profile μ internally. Because its product law
p lies in C_E, all member-gap inequalities hold at that SAME p. Let every
base member Quit surely at date0, every free player use μ independently
at date0, and everyone Continue forever thereafter, including off path.

For |E|≥2 every unilateral replacement leaves a sure base opponent. Thus
absorption occurs at date0 under every complete deviation. A free player's
two endpoints are exactly the finite-game endpoints; a base member's
Quit-minus-Continue difference is E_pG_i≥0. Simultaneous private actions
give no extra information before its first decision. Its entire later
strategy is immaterial. This also proves stationary repetition in this
branch, but not in the singleton branch.

For singleton E={a}, only the anchor can remove every sure quitter. Its
opponents really Never after date0; this is a load-bearing prescription.
On the empty free event, the best possible terminal continuation payoff is
max(s_a,0), including delayed randomized quitting and Never. Hence

    V_a=p∅s_a+Σ_{T≠∅}p_T r_a(T+a),
    C_a=p∅max(s_a,0)+Σ_{T≠∅}p_T r_a(T),
    V_a−C_a=E_pG_a≥0.

The anchor may learn at the next date that the free event was empty, but
this is already allowed in the cap max(s_a,0). Its date0 draw cannot depend
on the simultaneous free draw. Every first-action mixture and every later
behavioral replacement is therefore controlled. The cap is not replaced by
the anchor's prescribed later action.

For N≥1 immediate absorption gives h_Nr with h_N=(N−1)/N. On the singleton
empty event, all delayed rewards are≤h_N max(s_a,0); this is valid for
either sign. On all nonempty events the multiplier is exactly h_N even
for negative rewards. Therefore each full deviation is≤h_NV_i. The
profile is exact horizon Nash and its payoff h_NV approaches the fixed
target V with error≤M/N. N=1 gives zero payoff, as required by the actual
initial-live convention. No terminal-to-horizon limit is interchanged with
a deviation supremum.

Signed stress: change only the structural fixture's r₀({0}) from1 to−1.
The free game is unchanged. In the displayed coalition order its gap now
starts with−1; the exact dual inequality

    g₀≥R_{1,C}+R_{2,Q}

holds on all eight rows. Thus the all-sign theorem really admits a negative
own anchor with positive empty-event probability1/24. The original product
law has expected gap11/12 after this change. The late cap on that empty
event is0, not−1. Conversely, replacing min(s,0) by s is wrong for s>0,
and replacing it by0 is wrong for s<0. Neither incorrect replacement occurs
in either frozen statement.

The arbitrary-base extension is sound and meaningful as a stronger raw
restriction. Its different members may use different nonnegative regret
multipliers: averaging each against the SAME p proves all their conditions.
It includes pointwise complement-leave-safe bases, whose G_i are all
nonnegative. No new structural separation of the larger-base arm alone
is required to retain it in one strongest packet; the singleton arm already
supplies the significant new class.

## Exact structural fixture recomputation

The fifteen-row table in the frozen final section was used literally.
For anchor0 I independently obtained

    A₁=−5+6q₂,       A₂=1−2q₃,       A₃=−1+2q₁.

Any zero or sure coordinate forces successive strict boundary responses
around the odd negative cycle and contradicts the original boundary value.
Thus the unique product Nash point is(1/2,5/6,1/2). The large passive
cross-terms do not occur in those own-action differences.

In order ∅,1,2,3,12,13,23,123 the exact rows are

    g₀=(0,−4,1,1,2,−4,1,2),
    R_{1,C}=(0,−5,0,0,1,−5,0,1),
    R_{2,Q}=(−1,−1,0,1,0,1,0,0).

The slacks in g₀−1/4−R_{1,C}−R_{2,Q}/2 are
(1/4,5/4,3/4,1/4,3/4,1/4,3/4,3/4). This is a finite raw certificate;
no numerical equilibrium selection is used. Direct averaging gives

    V=(641/3,503/12,101/4,245/6),
    C₀=5105/24,       V₀−C₀=23/24.

The four negative nonempty joining gaps −4,−5,−1,−1 are realized on
the author's stated rows, excluding every join-monotone singleton anchor.

I recomputed all fourteen child witnesses. In the author's row order their
child-gap vectors are

    (1),(1),(1),(1),(1,5),(1,1),(1,1),
    (5,5),(5,5),(1,1),(2,1,1),(1,5,1),(1,1,1),(6,6,6),

and their omitted joining gains are

    1,5,1,1,1,1,1,6,6,6,1,1,1,2.

For nonsingleton sure coalitions each deviator has a sure opponent. For a
singleton sure coalition, its owner prefers own1 to Never0 and cannot
improve by delay; all nonmembers have the stated no-join comparison.
Thus these are exact unrestricted child Nash profiles, with zero debt and
zero joint Never, not merely pure-stage best responses.

At each witness coalition, all advance gains are≤0. Every nonsingleton
withdrawal gain is≤0. At a singleton, the patient floor is≤own1, the
deadline/evaluated/cancellation floors are≤0, and the terminal-security
floor is≤own1 by its actual singleton LP constraint. Hence EVERY five-kind
raw J right side is nonpositive for EVERY nonnegative weight choice, while
the omitted J left side is strictly positive. This is a direct obstruction
to the actual raw source, not just an inference from a special profile.
No future or Never inequality can cure that failed J row.

For independent perturbations of all sixty rewards by <1/40, the dual
left-minus-right variation is<5/40, below the minimum slack1/4. The empty
row remains0 because the own reward stays positive. All child and omitted
comparisons change by<2/40, below their margin1. The same fourteen pure
child witnesses and all five raw J obstructions persist. This proves the
claimed open class outside the union of these universal withdrawal sources,
without imposing any regularity or uniqueness condition on perturbed Nash
points. It does NOT exclude an independently selected safe child profile.

## Actual-source and accepted-class census

The singleton matrix is

    Γ=[[0,3,−1,−1],[3,0,−1,−1],
       [−1,−1,0,3],[−1,−1,3,0]],

with determinant45 and inverse

    [[2,7,3,3],[7,2,3,3],[3,3,2,7],[3,3,7,2]]/15.

Each principal triple has determinant6 and inverse diagonal consisting of
two entries−1/6 and one−3/2. Full homogeneous complementarity is trivial:
if w=Γx≥0 were nonzero, Γ⁻¹>0 would give x>0 and complementarity would
force w=0; if w=0, invertibility gives x=0. For offset−1, every row of
Γx≥1 needs its sole positive favorite coordinate positive, forcing full
support. Its unique root is(1,1,1,1), regular sign+1.
Thus full R₀/degree+1 and the matrix-screen failure are genuine, not assumed.

The three pair partitions fail the accepted two-pair join-cap criterion:
01/23 has c₀=−4,c₁=−5; 03/12 has c₃=−1; 02/13 has positive c but
r₀(013)=96>s₀. Positive inverse forces any column-sign cone signs all
positive, so it cannot evade these failures. The stronger matching class
is included in the two-pair class. The opposite-sign harmful-pair arm needs
two below-mate participants in one scheduled pair; neither harmful word
has such a pair. Both harmful words have Π₀=0,c₀=1, forcing passive W₀>1
at every proper two-phase solution; the favorite word has Π₂=Π₃=4 and
active values>1. Hence all three relabelings fail the all-below-own output
required by the accepted below-singleton packet, not merely its symmetric
coefficient test.

The actual premium traps are12,13,23,012,013,123,I. The trap definition
allows each player's positive premium to be on a DIFFERENT contained
coalition; it is not the narrower test that all players have positive premium
on the trap itself. The recorded L,J witness pairs, in that order, are
(4,5),(4,5),(4,1),(3,1),(3,1),(8,10),(100,2). Thus the larger-support
charge tests fail. The greatest core is all four, excluding the accepted
pair-core and triple-core criteria. No player has global nonnegative own
premiums. Global inserted-floor weights vanish: T0 kills weights1,3;
T03 then kills2; T23 kills0. Sure I has every participant reward>own,
excluding product-low and every payoff-only upper-floor exclusion.

All eleven nontrivial pointwise persistent bases have the displayed strict
negative member-completion gap. All twelve one-sided polynomial unit guards
fail on the author's pure upper faces; their gains are
(1,1,1,2,5,5,1,5,1,1,5,1). The broader weak-half polynomial lower face,
together with Γ⁻¹≥0, forces selected pair01 or23. The corresponding upper
half-face gains are3/2 and1, both positive. These exclude polynomial guards,
not only their sufficient raw rankings. The conditional range inequality
fails at player0 since its passive upper bound≥1000 but both relevant Quit
lower bounds≤1. Membership influence1→0 changes sign, −5 versus+1.

For response quotients, singleton total row sum1 first forces equal affine
scales within any block. All-sure displacements(2,1,−1,1) then permit only
the possible nonsingleton block{1,3}; its singleton0 block sums3 and−1
contradict invariance. This covers all fourteen nondiscrete partitions,
including positive playerwise affine transport. Γ also excludes integral
tournament and strict singleton four-cycle fibres: favorite signs form
two reciprocal pairs, not a directed tournament or four-cycle. Every child
triple has a reciprocal favorable pair, not the canonical directed singleton
triangle. In the accepted two-joint cyclic-child local branch, the two solo
owners require oppositely signed reciprocal singleton comparisons; no pair
of this Γ has that pattern. This is a branch-sign test, not a guessed radius.

Two additional current-source screens were checked directly. The paired
cycle raw region permits only ONE below-own singleton per recipient, whereas
this table has two. The literal odd interval-blocker predicate requires its
continuation upper bound below the blocker-absent Quit lower bound; every
recipient here has a passive singleton4>own1, so no recipient can qualify,
under any core or blocker. The same pure-row argument defeats the broader
interval source, not merely a weaker table adapter.

The sure-stationary census is correct. With0 sure, stationary repetition has
Never value5104/23 and immediate value641/3, gap−569/69. With1 sure,
3 is forced sure; the remaining finite Nash point is(q₀,q₂)=(6/7,2/3),
and1's gap is−1/21. With2 sure,1 then0 and3 are forced sure, and2's
grand gap is−1. With3 sure, the displayed boundary analysis leaves only
(q₀,q₁,q₂)=(1,0,0), where3's gap is−1; an all-proper solution would
force q₁q₂=1. Thus no sure-quitter stationary profile exists. This excludes
single-anchor dominance outputs and the actual nearby one-date center
requiring every free hazard in(1/4,3/4): anchor0 forces5/6, anchors1/2 force
a free sure player, and anchor3 has no proper completion. Absence of all
proper-three or all-proper stationary profiles is neither proved nor needed.

## Inspected production declarations and trust boundary

The primary consumer chain was inspected literally:

- `quittingPersistentBaseUtility`, `quittingPersistentBaseNashSet`,
  `quittingPersistentBaseNashSet_nonempty` in
  `UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`;
- `quittingOneDateThenNeverProfile_exactHorizonNash` and
  `quittingOneDateThenNeverProfile_sameProfile_uniformPayoffWitness` in
  `UniformEquilibrium/Quitting/Root/OneDateNeverHorizonNash.lean`;
- `QuittingSingleAnchorInducedDominance` in
  `UniformEquilibrium/Quitting/Stationary/SingleAnchorArbitraryCompletion.lean`;
- `QuittingPersistentBaseComplementLeaveSafe` and
  `exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean`.

The finite Nash declaration has no cardinality≥2, own-sign or leave-safe
premise. The one-date consumers need exact terminal Nash, which the new
raw argument supplies rather than assumes. The source declarations alone
are not claimed to implement the new LP producer.

The comparison definitions inspected include `WithdrawalFutureJoinKind.gain`
and `WithdrawalFutureJoinRewardCertificate.join_row` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`;
the actual floor and restart definitions in `PatientWithdrawalRaw.lean`,
`DeadlineWithdrawalRaw.lean`, `DeadlineWithdrawalRestartPointwiseCore.lean`,
and `deadlineWithdrawalSecurityValue_le_singleton` in
`DeadlineWithdrawalSecurityLP.lean` in the same directory;
`HasWeightedQuittingTrapLeavers` in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`;
`QuittingTrapChargeCoefficients` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`;
`IsQuittingPremiumTrap` in
`UniformEquilibrium/Quitting/Classification/QuittingPremiumCore.lean`, with
its underlying `MathUE.IsFiniteCoalitionPremiumTrap` definition in
`MathUE/FiniteCoalitionPremiumCore.lean`;
`QuittingOneSidedWeakUnitGuards` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`;
`QuittingHalfWeakPolynomialGuards.reciprocal_pos` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`;
`IsQuittingConditionalFaceGapRange` in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`;
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`;
`PairedCycle.RawRegion.eq_partner_of_singleton_lt` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`;
`IsLiteralStrictFiniteOddIntervalBlockerCore` in
`UniformEquilibrium/Quitting/Classification/Existence/FiniteOddIntervalBlockerCoreRowAdapter.lean`;
and `IsStrictFiniteOddIntervalBlockerCore` in
`UniformEquilibrium/Quitting/Classification/Existence/FiniteOddIntervalBlockerCore.lean`.

The explicit output bounds of
`exists_nearby_oneDate_sameProfile_horizon_equilibrium` in
`UniformEquilibrium/Quitting/Examples/AdaptiveChildCenterNearbyHorizons.lean`
were also checked. Generic supplied stationary or periodic certificate
consumers and arbitrary unspecified persistence neighborhoods are not raw
coverage producers. This report makes no blanket nonmembership claim about
those interfaces. No unresolved strategic input remains in the finite-regret
producer. Its initially claimed significance is withdrawn by the complete
source inclusion below.

## Final standalone artifact check

**Final-artifact mathematical PASS, not export-significance PASS**, for all587 lines of
[COARSE_REGRET_BASE_UNIFORM_EQUILIBRIUM.md](../notes/CODEX_NOETHER__COARSE_REGRET_BASE_UNIFORM_EQUILIBRIUM.md),
SHA256 `e9cd2f52ceb8a70dd8ba7c51110fc0d07296513ae1710bb89c1389cde88a0a90`.
The entire final standalone was read, including the first150 lines again
after the author confirmed this exact frozen surface. No counterpart review
was consulted, and no packet edit or promotion was made.

The assembly faithfully carries the reviewed arbitrary-base producer,
the singleton min(s,0) exception, separate member minima over one coarse
polytope, internally selected independent Nash law, unrestricted deviations,
literal zero-initial-stage factor(N−1)/N and coordinatewise M/N fixed-target
delivery. It does not convert coarse laws into play or strengthen the
negative-law quantifiers. The stationary repetition conclusion remains
restricted to bases of size at least two.

The new signed stress examples check directly. For the two-player singleton
example, G=(−2,1)=1+(3/2)R_Q with R_Q=(−2,0); the selected target is(−4,2).
The empty-free-set example has two gaps2 and negative target(−2,−2).
For the three-player quantifier example, E=01 gives G₀=(1,−1) and
G₁=(−1,1); each minimum is−1, their sum is identically0, and the uniform
free law yields exact base Nash. Thus the added common-law warning is valid.

The standalone expands the fourteen-child J-row argument and the needed
floor bounds explicitly, defines the displacement and raw comparison
quantities, and retains the exact matrix, pair-partition, charge, quotient,
sure-stationary and transient-center checks. Its1/40 neighborhood claim
is explicitly limited to CCE production and withdrawal nonmembership;
the other source screens concern the center. The displayed strategic and
coverage claims do not depend on conference notes, review records, untracked
helpers, or an unnamed theorem in math/. There is no process history or
Lean-certification claim. The source handoff names actual finite Nash and
one-date horizon declarations while keeping the new raw implication ordinary
mathematics. No unresolved assembly, mathematical or strategic objection.

## Whole-class inclusion in the concrete persistent-base producer

This is an independent source check, without consulting a counterpart review.
It overturns only the claimed UE coverage increment, not the theorem or its
same-profile exact finite-horizon conclusion.

Let E be any base admitted by the coarse-regret criterion and select a finite
product Nash law p in its free game. Such a law lies in the coarse polytope,
so all the criterion's base-member inequalities hold at that same p. Take
the free set to be the entire complement of E; every outside-player condition
in the existing source is then vacuous.

If |E|≥2, the existing member endpoint difference is exactly E_p G_i. Thus
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`
directly consumes p and the nonnegative member gaps. Its conclusion already
controls unrestricted behavioral deviations and delivers one uniform target.

If E={i}, write Q for i's prescribed immediate payoff and C for its Continue
contribution on nonempty free outcomes. The coarse-regret screen gives

    C+p∅ max(s_i,0)≤Q.

The actual declaration `quittingPunishmentValue_le_max_solo` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean` gives m_i≤max(s_i,0).
Consequently C+p∅m_i≤Q. This is precisely the literal floor screen, by
`quittingSingletonBaseOwnerFloorExcess_nonpos_iff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
The same file's `nonempty_quittingSingletonBaseCertificate_of_inducedNash`
constructs the certificate from this screen and the free Nash law. Finally
`QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`
consumes it. The continuation in this source is a punishment tail, not
stationary Never. Its value can be strictly below max(s_i,0).

These arguments cover arbitrary signed singleton rewards, all nonempty bases,
and every table admitted by the new criterion, not just its structural
fixture. The exact-profile horizon strengthening remains valid mathematics,
but does not remove any further possible UE counterexample. Under the stated
export threshold the appropriate significance verdict is therefore FAIL.
