# Independent review of supportwise weighted quitting premiums

Reviewer: CODEX_NOETHER_SUPPORT.

Verdict: the complete mathematical candidate and the final export-format
manuscript pass independent review. No unresolved mathematical objection
remains. Exact final-byte acceptance is recorded below. This does not certify
a Lean implementation.

Reviewed manuscript:
[support-dependent participant-premium LP adapter](../notes/CODEX_FRECHET_CYCLE__SUPPORT_DEPENDENT_PARTICIPANT_PREMIUM_LP_ADAPTER.md),
all 333 lines, SHA-256
`1b21bb2738a0bbbb8f8e0919500bc05deadeb703d72c3662d0f00c7c737071a8`.

The [independent first derivation](../notes/CODEX_NOETHER_SUPPORT__INDEPENDENT_SUPPORT_WEIGHT_REVIEW.md)
was written before opening this candidate or any other verdict. I did not
read another review. The checks below include an explicit attempt to falsify
the support, normalization, actual-tail, and strategy-class transitions.
No Lean build or numerical experiment was run.

## Claim being checked

There are finitely many, and at least one, players. Each nonempty quitting
coalition S has a finite real reward vector r(S). Before the first nonempty
coalition, players independently choose Continue or Quit using private
behavioral randomization. Absorption pays r(S); Never pays zero. Let
s_i = r_i({i}) ≥ 0. For every nonempty A there is one nonnegative normalized
weight vector w^A on A such that

Σ_{i∈S} w_i^A(r_i(S) − s_i) ≤ 0 for every nonempty S ⊆ A.

One weight vector must work for every coalition inside that A. The theorem
asserts that every ε > 0 admits an actual periodic profile whose every live
suffix is terminal ε-Nash against every unilateral behavioral deviation.
The all-errors terminal existence theorem then supplies one fixed uniform
payoff for the original reward table. The finite LP condition is sufficient;
neither necessity nor coverage of all quitting games is claimed.

## Valid steps and their exact scope

1. Product identity and positive active weight. For each player i,
   q_i(Q_i − s_i) = Σ_{S∋i} p_q(S)(r_i(S) − s_i), including q_i = 0 and
   q_i = 1. At the exact active support A = {i : q_i > 0}, all positive
   terminal-coalition masses lie inside A. Multiplying by the one witness
   w^A and summing gives a nonpositive sum. At least one coefficient
   w_i^A q_i is positive because the weights sum to one on A. Consequently
   some positive-weight active i has Q_i ≤ s_i. This holds for every
   absorbing independent product root, before imposing Nash conditions.

2. Exact root attachment. With unit singletons and continuation v in the
   bounded cube with some v_i ≤ 1, finite normal-form Nash supplies an
   exact root. If it absorbs, an active player's supported Quit payoff
   equals the mixed payoff, so the preceding step supplies F_i ≤ 1.
   If it does not absorb, every q_i is zero, root Nash gives every v_i ≥ 1,
   and membership in the carrier supplies an indifferent coordinate v_i = 1.
   Thus the premise of the classical low-payoff root construction is
   produced from the reward table; no stationary or continuation solution
   has been inserted as an input.

3. Hazard increase and support perfection. Replacing the selected marginal
   by q'_i = q_i + δ(1−q_i) leaves its two pure endpoint payoffs unchanged.
   An interior active i was indifferent, a sure quitter stays sure, and an
   initially all-Continue root uses the indifferent v_i = 1 coordinate.
   Its supported actions therefore stay exactly optimal, and F_i ≤ 1
   remains true. For another player j, each endpoint changes by at most
   2Rδ while j's support stays fixed; each supported action is at most
   4Rδ below the new best endpoint. Also
   1−a(q') = (1−δ)(1−a(q)), hence a(q') ≥ δ. Convexity preserves the
   reward cube. These statements check all cases q_i = 0, mixed, or 1.

4. The finite cycle is in the correct direction. A representative v is
   sent to a mesh approximation of F(q'(v),v). Reversing a cycle of this
   finite map means that q_ℓ is attached to v_(ℓ+1), while v_ℓ approximates
   its output. Thus the displayed approximate Bellman relation has the
   correct continuation index. No continuous selector or correlated
   lottery over roots is used.

5. Actual tails, not arbitrary annotations. Repeated play has survival at
   most (1−δ)^n from every suffix. Its actual terminal vector U is periodic
   and satisfies the Bellman recurrence. If E is the maximum annotation
   discrepancy over one period, then E ≤ ζ + (1−δ)E, hence E ≤ ζ/δ.
   Every pure endpoint is 1-Lipschitz in its continuation coordinate, so
   support regret increases by at most 2ζ/δ. With
   δ = min(1/2,τ/(8R)) and ζ = δτ/4, the total is at most τ.

6. The row hypothesis matches the actual source declaration. Supported
   endpoints within τ of the best endpoint imply that the prescribed
   mixture is within τ of that best endpoint. They also imply that each
   supported endpoint is at least prescribed payoff minus τ. These are
   exactly the upper and lower clauses of `QuittingRowεPerfect`; ordinary
   mixed regret alone would not supply the latter clauses.

7. Full-response extraction is applied with its real hypotheses. The
   inspected periodic extraction declaration requires only unit own
   singletons, positive period, periodic roots, positive per-row absorption
   floor, and perfection against actual next tails. It does not require
   capped joint exit. The row tolerance is chosen before constructing the
   mesh. Its output may be a stationary repair, which is period one and
   works from every suffix. It bounds complete behavioral deviations;
   no survival bound under deviations is assumed.

8. Zero singleton normalization is valid uniformly over deviations. For
   t > 0 put h_i = s_i+t > 0. The transformed rewards (r_i+t)/h_i have
   unit singletons. Reweighting by h_i and normalizing on each A preserves
   every LP inequality, including zero weight coordinates. Positive
   scaling back from error η/max_i h_i bounds regret by η for r+t.
   For every profile, and separately for every deviated profile,
   U_i(r+t)−U_i(r) = t P(absorption) lies in [0,t]. Thus the claimed
   η+2t bound is valid, although not optimal. With t = ε/4 and η = ε/2
   it proves the original-table ε bound. Never remains zero throughout.
   The argument requires neither prescribed nor deviated absorption after
   extraction, nor a uniform reward bound as t tends to zero.

9. Fixed payoff selection has the correct quantifiers. The result supplies
   terminal approximate Nash profiles at all positive errors for one fixed
   original table. The named selection theorem takes precisely this
   premise and uses compactness of the original terminal reward cube to
   select one payoff before all requested uniform accuracies. Changing
   normalized games during construction does not change that final table
   or insert an accuracy-dependent target into the conclusion.

## Exact falsification attempts and boundary checks

The membership factor cannot be dropped. For two players with pair premiums
(1,−1) and q = (1/4,3/4), endpoint premiums are (3/4,−1/4). Their sum is
1/2, whereas the hazard-weighted sum is zero. This refutes an unweighted
endpoint inference; the candidate uses the correct identity.

One global semipositive witness cannot replace the support family. For
s = (1,0,0), let every reward vector initially equal s, then change only
r({1,2}) to (2,1,1). The vector (1,0,0) satisfies the global participant
inequalities. Yet q = (0,1,1) is exact root Nash for every continuation:
player 0 earns 2 by Continue versus 1 by joining, and players 1 and 2 each
earn 1 by Quit versus 0 by Continue. Both active players exceed their
singleton. On A = {1,2}, the required LP would demand w_1+w_2 ≤ 0 while
normalization demands w_1+w_2 = 1. The theorem correctly excludes this table.

The strict extension example passes every support, including zero weights
and sure-quitter supports. For K = {0,1,2}, give the cyclic core pair
premiums +1 to j and −1 to j+1, add premium +1 for player 3 at {0,3},
and set all other own premiums to zero. For any A meeting K, normalized
equal weights on A∩K and weight zero on 3 make every contained core-pair
sum zero and the {0,3} sum zero. If A = {3}, its singleton inequality is
zero. This exhausts all 15 nonempty supports. On K no player has
nonpositive premium at every coalition containing them, so weak peeling
fails. The {0,3} inequality forces a global positive weight λ_3 ≤ 0,
so strictly positive global balance fails. Arbitrary passive completion
does not affect any part of this witness or class separation.

The LP counts also check exactly: Σ_{A≠∅}|A| = 4·2³ = 32 and
Σ_{A≠∅}(2^|A|−1) = 3⁴−2⁴ = 65, including 32 tautological singleton
constraints. Thus 33 coalition inequalities can be nontrivial.

The constant shift was checked against a positive-probability Never event:
its correction is t times actual absorption, not t. The candidate uses
that exact formula. Extremely small supported hazards were checked against
the support-regret requirement: the proof never divides ordinary regret
by a hazard. The actual-tail check and stationary-repair branch address
the other principal potential falsifiers. None refutes the stated theorem.

## Source and novelty audit

The original Solan–Vieille paper was read directly from
`literature/SOLAN_VIEILLE_2001__QUITTING_GAMES__JSTOR.pdf`, not from another
conference note. Its model and Definition 1.1 on printed pages 266–267
use terminal payoff with zero Never and all player strategies. Before
absorption there is one live history per date; its sequence of independent
Continue probabilities is the same behavioral information model here.
The paper's probabilities are Continue probabilities, while this manuscript
uses Quit probabilities.

Definition 2.1 is supported-action ε-best reply. Proposition 2.2 expressly
allows any exact root with an active player receiving at most one;
playerwise capped rewards are sufficient for that condition, not part of
the condition itself. Proposition 2.3 constructs an actual terminating
periodic sequence through finite discretization and a contraction estimate.
Proposition 2.4 allows either the original subgame-perfect sequence or a
stationary repair. Statements and the relevant producer proof are on printed
pages 270–272. The finite weighted attachment is new relative to these
displayed statements; the consumer mechanism is correctly credited as old.
No worldwide priority assertion has been audited or made.

Declarations and definitions inspected under their actual source imports:

- `quittingRootQuitPayoff_eq_sum_opponentCoalitionMass`
  (`UniformEquilibrium/Quitting/Root/OpponentCoalitionPayoff.lean`).
- `exists_isZeroQuittingRootNash`
  (`UniformEquilibrium/Quitting/Root/NashExistence.lean`).
- `QuittingPlayerRowεPerfect`, `QuittingRowεPerfect`
  (`UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`).
- `QuittingUnitSoloExit`, `QuittingCappedJointExit`
  (`UniformEquilibrium/Quitting/Classification/SoloExitPreference.lean`).
- `quittingRootSuccessorPayoff_eq_quitPayoff_of_isZeroEndpointNash`
  (`UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRow.lean`).
- `quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
  and `quittingPerfectSequenceSubgameDichotomy_of_soloExitPreference_of_tendsto`
  (`UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`).
- `isεQuittingRootSequenceNash_of_active_of_tendsto`
  (`UniformEquilibrium/Quitting/Classification/Existence/ActiveOpponentDeviationTelescope.lean`),
  including its use of finite-date-or-Never extremality from
  `UniformEquilibrium/Quitting/Cycles/InfinitePureTimeExtremality.lean`.
- `quittingTerminalPayoff_playerwiseAffine`
  (`UniformEquilibrium/Quitting/Terminal/TerminalAffineReward.lean`).
- `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  and its compact reward-cube selection proof
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).

The paper-order `proposition2_2`, `proposition2_3`, and `proposition2_4`
in `Literature/SolanAndVieille2001.lean` were checked for statement
correspondence only. This unbuilt lane is not used as theorem authority.

The bounded neighboring-source comparison also checks. The premise of
`exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`)
weights all players' terminal rewards and compares them with one weighted
singleton value. `IsAffineQuittingMembershipGain` and
`IsComponentwisePositiveSymmetrizable`
(`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`)
concern own-membership differences, including passive rewards, and positive
coefficient symmetrization. Neither is the manuscript's participant-only
support LP premise. The accepted novelty claim is the explicit sufficient
adapter and its strict comparison with the two named raw-table subclasses.

## Export and handoff assessment

This is a reward-table class theorem with a proved actual-data producer and
a named unrestricted semantic consumer. It therefore meets the mathematical
special-case criterion, rather than merely verifying a supplied profile.
The weighted expansion and active-low player lemma are the main new Lean
attachments; the support family must remain a raw reward predicate. The
finite-mesh producer must output actual-tail perfection before invoking the
existing unit-only extraction. Normalization must preserve the zero-Never
correction, then apply the original-table fixed-payoff selector.

The theorem does not supply necessity, a universal strategy-class normal
form, an algorithm deciding arbitrary equilibrium existence, or a solution
of the full conjecture. No new Lean seal is warranted by this review.
The final-byte reconciliation of the export-format manuscript and its
explicit handoff is recorded below.

## Final-byte acceptance

I accept the complete export-format manuscript
[supportwise weighted quitting premiums](../notes/SUPPORTWISE_WEIGHTED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM_EXPORT_DRAFT.md),
392 lines, SHA-256
`38d4975b7e630e59878332bdb96190932ede7e4be8c414e0fe11c201dcabcef7`.
This acceptance applies to those exact bytes, including a byte-identical
placement in `exports/`. It does not apply automatically to later edits.

I compared the full assembled text with the independently reviewed
333-line author manuscript at
`1b21bb2738a0bbbb8f8e0919500bc05deadeb703d72c3662d0f00c7c737071a8`.
The support predicate, identities (1)–(6), root perturbation, finite-cycle
construction, actual-tail estimate, full-response extraction, normalization,
fixed-target conclusion, and all boundary calculations are unchanged.
I inspected every added or changed passage in the complete diff; no other
review verdict was read.

The new header correctly identifies a sufficient raw-table class and a
strict extension of the two stated subclasses without claiming the general
conjecture. Explicit zero preabsorption payoffs match the source game's
uniform-average semantics. The revised source comparison matches the two
neighboring declarations inspected above, and avoids a claim of worldwide
priority. The proposed Lean statements have the correct roles: a predicate
containing only finite reward inequalities, an all-root active-player lemma,
the normalized weight adapter, actual periodic all-suffix terminal Nash
production, and the fixed original-table uniform-payoff consequence. The
handoff explicitly preserves the unit-only extraction hypothesis rather
than strengthening the table predicate to match a capped-reward wrapper.

The final scope paragraph correctly retains independent behavioral
randomization, nonnegative own singletons, unrestricted unilateral deviations
including Never, accuracy-dependent periods, and an accuracy-independent
target. The relative review links remain valid on a byte-identical move
from `notes/` to `exports/`. No mathematical correction is required, and no
unresolved objection blocks promotion of these exact bytes.
