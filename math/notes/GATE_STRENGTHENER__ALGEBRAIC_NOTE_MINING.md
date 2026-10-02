# Algebraic-lane note mining

Author: `GATE_STRENGTHENER`

## Status and scope

This is an exhaustive mining pass over exactly the 79 filenames in
`/tmp/notes_lane_algebraic.txt`.  I inspected every note at least at its
status, theorem headline, conclusion, and stated limitation.  For the live
candidates I then checked the relevant independent feedback, the current
`exports/`, `formalized/`, and `questions/` directories, and the named Lean
declarations or source files.  I did not read another mining report.

The principal verdict is negative but useful:

> No complete result in this lane appears to have been missed by both the
> export process and Lean formalization.  Every reviewed result with an actual
> terminal or uniform-payoff consumer is already exported or formalized.

Several complete finite or algebraic lemmas remain only in conference notes,
but each fails the export gate at the same place: it has no actual-data adapter
to a current source, no semantic consumer, or both.  The strongest remaining
value is in seven possible connections listed below.  None is presently a
completed export.

Classification codes in the ledger are:

- `D`: duplicate, exported, formalized, or strictly subsumed by current work;
- `F`: falsified, retracted, or stale as a route;
- `U`: useful isolated theorem or exact regression, without a live consumer;
- `L`: live missing seam or source-adapter obligation;
- `C`: one of the connection candidates analyzed after the ledger.

Where a note has mixed content, the code records its strongest live
disposition, with secondary status stated in the comment.

## Exhaustive 79-note ledger

| No. | Note | Class | Disposition |
|---:|---|:---:|---|
| 1 | `AGKRS_THEOREM_3_4_FORWARD_TRICHOTOMY_QUESTION.md` | D | The old question is archived, and the checked production theorem is recorded in `formalized/AGKRS_FORWARD_TRICHOTOMY_BY_REFUSAL_COMPACTIFICATION.md`; it is not a live gap. |
| 2 | `ATLAS_FALSIFIER__CONCENTRATED_SINGLETON_FULL_GAP_TOGGLE_CYCLE.md` | C | Valid source-attached all-nonempty horizontal cycle.  It does not enter the checked nonsingleton-monodromy no-cycle theorem; useful only with a new cycle consumer. |
| 3 | `ATLAS_GATEKEEPER__SERIAL_NONEMPTY_TOGGLE_DISPATCH_NOT_MONODROMY.md` | D | Independent audit of the same graph mismatch as 2 and 77; no additional producer. |
| 4 | `CHATGPT_EXTERNAL__CODIMENSION_ONE_QUIET_FACE_ATOM.md` | U | Reviewed codimension-one quiet-face/atom theorem, but the separately chosen faces are not aligned into one chronology or common law. |
| 5 | `CHATGPT_EXTERNAL__COMPONENTWISE_WEIGHTED_POTENTIAL_QUITTING.md` | D | Fully formalized as `formalized/COMPONENTWISE_WEIGHTED_POTENTIAL_QUITTING.md`, including its sure-exit terminal consumer. |
| 6 | `CHATGPT_EXTERNAL__CURVATURE_PREFIX_RENEWAL.md` | U | Exact curvature transport/accounting; no renewable rank or chronological consumer. |
| 7 | `CHATGPT_EXTERNAL__FIN4_INERT_PAID_MASS_RECTANGLE.md` | U | Sound local rectangle/inertness separation, not a positive-minimum consumer. |
| 8 | `CHATGPT_EXTERNAL__FIN4_RECTANGLE_CAPSTONE_SPECIFICATION.md` | F | An old producer specification, not a theorem; current questions state the sharper minimum-return, uniform-escape, and inert obligations. |
| 9 | `CHATGPT_EXTERNAL__FIN5_FACE_CYCLIC_SEED.md` | U | Reviewed conditional finite-period Green estimate; automatic production from quiet-face data was refuted. |
| 10 | `CHATGPT_EXTERNAL__REPAIRED_STRESS_CYCLE_NO_SIMON_LYAPUNOV.md` | D | Formalized as `formalized/REPAIRED_STRESS_CYCLE_NO_SIMON_LYAPUNOV.md`; it is a candidate-level certificate-language falsifier, not a Fin4 counterexample. |
| 11 | `CLAUDE_EXTERNAL__PURE_TOGGLE_COLLAPSE_AND_SCC_BOUNDARY.md` | U | Correct pure-toggle collapse and terminal-SCC normal form; the claimed SCC trichotomy is not valid for arbitrary SCCs and there is no temporal consumer. |
| 12 | `CLAUDE_EXTERNAL__TERMINAL_TOGGLE_SCC_CARDINALITY_BOUNDS.md` | C | Complete ordinary finite-graph theorem: every terminal toggle SCC has minimum size at most `n-2` and maximum size at least `2`; on Fin4 every terminal SCC meets level two.  No semantic consumer. |
| 13 | `CODEX_AGKRS__MINIMAL_FORWARD_TRICHOTOMY_ARCHITECTURE.md` | D | Useful proof-engineering minimization of the already exported corrected AGKRS proof; no new theorem. |
| 14 | `CODEX_AMPERE__FINITE_STATE_ORIENTATION_FARKAS_AND_PLATEAU_NOGO.md` | C | Exact finite Farkas alternative plus checked plateau regression; identifies a common-response chart as the missing anti-circulation field. |
| 15 | `CODEX_AMPERE__HOPF_FORCED_PAIR_ATTACHMENT.md` | D | The zero-minimum HOPF attachment and related maximal-ray regressions are checked in the owner-risky/HOPF regression modules. |
| 16 | `CODEX_AMPERE__HOPF_OWNER_UNSAFE_STATIONARY_CLOSURE.md` | D | Independently reviewed and now formalized by `sharpReward_exists_uniformEquilibriumPayoff` and its rational stationary-face certificate. |
| 17 | `CODEX_ARCHIMEDES__ROBUST_JOIN_CYCLE_PERSISTENT_BASE_AUDIT.md` | D | Subsumed and formalized by `formalized/ROBUST_JOIN_PREDECESSOR_BASE_UNIFORM_PAYOFF.md`. |
| 18 | `CODEX_CAUCHY__AGKRS_CONTINUOUS_REFUSAL_REPAIR.md` | D | One of the reviewed ingredients incorporated in the current AGKRS export. |
| 19 | `CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md` | F | The proposed finite toggle negative route is killed by exact pure or mixed equilibria; retain only as a gadget regression. |
| 20 | `CODEX_CEDAR__PROJECTIVE_Q_DETERMINISTIC_KILOBLOCK.md` | F | The one-active deterministic route is explicitly refuted; surviving estimates do not form a producer. |
| 21 | `CODEX_CURIE__UNIQUE_DEBTOR_RECYCLE_DOES_NOT_PRODUCE_HOPF_SIGN.md` | U | Exact sign-separation no-go; useful boundary test, no positive source theorem. |
| 22 | `CODEX_DISCRETIZATION__AGKRS_SMALL_BLOCK_AUDIT.md` | D | Reviewed no-terminal-jump arm used by the AGKRS export. |
| 23 | `CODEX_EULER__AGKRS_FIXED_FACE_LIFT_DEFECT_AND_SOURCE_MISMATCH.md` | U | Exact lift-defect/source mismatch; the corrected AGKRS proof bypasses this attempted attachment. |
| 24 | `CODEX_EULER__AGKRS_PRIORITIZED_REFINED_SOURCE_CLOSURE_AUDIT.md` | F | A negative audit of an older prioritized-source route; the current refusal proof makes it non-frontier. |
| 25 | `CODEX_EULER__AGKRS_REACHED_ROW_FLOOR_LIFT_CONSUMER.md` | D | Reviewed core is covered by `formalized/AGKRS_PRIORITIZED_ATTACHMENT_TO_SINGLETON_DEFECT.md` and reached-row localization declarations. |
| 26 | `CODEX_EULER__CURVATURE_INERT_CAP_CHRONOLOGY_SEPARATION.md` | U | Reviewed rational no-go separating signed curvature from executable cap chronology. |
| 27 | `CODEX_EULER__ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md` | D | Exported, formalized, and part of the exact Fin4 search route. |
| 28 | `CODEX_EULER__FIN4_COLLISION_CYCLE_FACE_SIGN_CANCELLATION.md` | D | The static screen is superseded by the stronger formalized robust-join-predecessor uniform-payoff theorem; its face-cancellation component has no separate consumer. |
| 29 | `CODEX_EULER__FIN4_FULLY_MIXED_FACE_ZERO_PRODUCER_AUDIT.md` | D | The positive supplied-face-zero compiler is already checked; the note's negative part is only a source-interface audit. |
| 30 | `CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY.md` | D | Large historical inventory whose theorem-strength pieces are already separately reviewed/formalized; its remaining connector is explicitly open. |
| 31 | `CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING.md` | D | Formalized as the quarter-ceiling and fixed-prefix barrier packets. |
| 32 | `CODEX_EULER__MINIMUM_MIDPOINT_OFFMIN_CURVATURE_PAID_PORT.md` | C | Reviewed fixed-half chord theorem with the sharp `Delta/12` paid port; the existing trichotomy still leaves the inert stall. |
| 33 | `CODEX_EULER__POSITIVE_NEVER_OFF_MINIMUM_CORNER_CAP_FACE_REDUCTION.md` | L | Valid strict singleton-over-cap reduction; the all-Continue cap-face arm remains. |
| 34 | `CODEX_EULER__POSITIVE_NEVER_RECTANGLE_CAP_RAY_REGENERATION.md` | L | Reviewed one-step support rotation or unique-all-Continue off-minimum point; not renewable and not attached to the current normalized slice. |
| 35 | `CODEX_FARADAY__STRICT_BLOCKER_TIGHT_FACE_ADAPTER.md` | C | Correct conditional matrix-to-tight-face adapter; no checked source currently supplies the strict principal blocker with the required actual path. |
| 36 | `CODEX_FERMAT__FINITE_DEADLINE_NASH_HORIZON_ESCAPE.md` | D | Reviewed duplicate of the stronger formalized finite-deadline producer and adjusted-debt theorem. |
| 37 | `CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md` | L | A research notebook containing many later-superseded propositions; its current live endpoint is still the small-debt/initial-debt input to chronological shadowing.  It should not be exported wholesale. |
| 38 | `CODEX_HOPF__CARD_THREE_MAXIMAL_RAY_REGRESSION.md` | D | Formalized in `FIN4_MAXIMAL_RAY_FORCED_PAIR_ZERO_MINIMUM_REGRESSIONS.md`. |
| 39 | `CODEX_HOPF__HOPF_COMPLETION_SAFE_BASE_CHAMBERS.md` | D | Pure safe chambers are checked generally and the hard owner-risky stationary chamber is formalized by the sharp table. |
| 40 | `CODEX_KOLMOGOROV__FINITE_DEADLINE_PROJECTIVE_BOUNDARY.md` | C | Exact adjacent-deadline alternative and response square; no minimum-fibre reprojection retaining the consecutive-deadline separation. |
| 41 | `CODEX_LAGRANGE__PAID_NONSINGLETON_CYCLE_RECHARGE_ATOM_DISPATCH.md` | C | Formalized local contraction with charge `7 lambda D_*/96`; its regenerated source is not chronologically adjacent to the paid edge. |
| 42 | `CODEX_LEIBNIZ__SOURCE_FAITHFUL_RESPONSE_CHORD_COCYCLE_BOUNDARY.md` | C | Reviewed exact upper-chord cocycle and persistent-zero conditional consumer; adjacent source charts are not produced. |
| 43 | `CODEX_MINER__AGKRS_DIAGONAL_EXACT_PREFIX_PORT_CLOSURE.md` | D | Reviewed and formalized; the endpoint already yields the uniform payoff. |
| 44 | `CODEX_MINER__AGKRS_POSITIVE_ENDPOINT_FULL_SUPPORT_STATIONARY_NOGO.md` | F | Corrected S.2-only interface no-go; the current AGKRS proof does not rely on the false implication. |
| 45 | `CODEX_MINER__AGKRS_POSITIVE_RESIDUAL_BRANCH_PRIORITY_REGENERATION_GAP.md` | F | Historical regeneration audit, superseded as a route by the corrected AGKRS export. |
| 46 | `CODEX_MINER__AGKRS_SOURCE_CLOSURE_NONPOSITIVE_ENDPOINT_CONSUMER.md` | F | Main endpoint-to-S.1 claim retracted; surviving one-player S.2 no-go is only a boundary example. |
| 47 | `CODEX_MINER__AGKRS_SUMMABLE_ENDPOINT_PORT_BALLISTIC_DISPATCH.md` | D | Reviewed and formalized as `AGKRS_SUMMABLE_ENDPOINT_RETURN_BALLISTIC_DISPATCH.md`. |
| 48 | `CODEX_MINER__ESCAPE_AWARE_SEMIALGEBRAIC_BARRIER_ENCODING.md` | D | Sound certificate language, strictly subsumed for approximation/semidecision by the formalized quantile hierarchy and exact scale resolver. |
| 49 | `CODEX_MINER__FIN4_COLLISION_CYCLE_PAIRBASE_MISSING_FACE_ALIGNMENT.md` | C | Reviewed alternating-base alignment plus an exact regression showing weak cancellation does not supply the required negative face average. |
| 50 | `CODEX_MINER__FIN4_LATE_RELEASE_RECTANGLE_THREE_LABEL_BOUNDARY.md` | L | Reviewed three-label positive-Never dispatch; the support-entry/minimum-fibre consumer is missing. |
| 51 | `CODEX_MINER__FIN4_SIMON_RESIDUAL_CONNECTION.md` | F | Negative connector showing the constrained-root source lies on Simon's fixed-motion side; current formalized Simon/atlas work does not gain a consumer from it. |
| 52 | `CODEX_MINER__FINITE_DEADLINE_NASH_ESCAPE_CERTIFICATE_FORMALIZATION_PACKET.md` | D | Consolidated result is covered by the formalized finite-deadline producer, horizon escape, and projective-boundary packets. |
| 53 | `CODEX_MINER__POSITIVE_NEVER_MAX_SUPPORT_RECTANGLE_EXCURSION.md` | L | Reviewed source-faithful off-minimum rectangle excursion; no consumer for the resulting corner. |
| 54 | `CODEX_MINER__SIGNED_CAUSAL_RECTANGLE_ORIENTATION_COMPILER_BOUNDARY.md` | C | Reviewed exhaustive signed orientation and reset lift; endpoint flip and iterability remain unresolved. |
| 55 | `CODEX_RAMSEY__AGKRS_DIVERGENT_EXCEPTIONAL_OWNER_S3_DISPATCH.md` | D | Formalized in `AGKRS_DIVERGENT_EXCEPTIONAL_OWNER_S3_DISPATCH.md`. |
| 56 | `CODEX_RAMSEY__AGKRS_HARD_POSITIVE_SOURCE_SUPPORT_FACE_NORMAL_FORM.md` | F | Valid internal normal form, but its old source-classification role is superseded by the direct corrected AGKRS theorem. |
| 57 | `CODEX_RAMSEY__AGKRS_PRIORITIZED_ATTACHMENT_SPINE_CONTRACTION.md` | D | Reviewed contraction is incorporated in the formalized prioritized-attachment packet; remaining old residual is not frontier. |
| 58 | `CODEX_RAMSEY__FIN4_STATIONARY_DEBT_RELAY_CYCLE.md` | C | Reviewed finite stationary relay and exact nonchronological boundary; needs simultaneous source-coherent choice or a seam account. |
| 59 | `CODEX_RAMSEY__FIN5_FACE_ATOM_COVER_AND_CYCLIC_ALIGNMENT_BARRIER.md` | U | Correct Fin5 atom-cover theorem and alignment separation, without a common phase law or consumer. |
| 60 | `CODEX_RAMSEY__FIN5_FULL_FACE_SOURCE_PHASE_SEAM_SEPARATION.md` | U | Exact Fin5 source/phase seam no-go; no general-player producer. |
| 61 | `CODEX_RAMSEY__GROK_INERT_RECTANGLE_EXCLUSION_AUDIT.md` | F | Decisive audit: the proposed inert-rectangle exclusion is false at several independent steps.  Only reached-row residualization survives. |
| 62 | `CODEX_RAMSEY__POSITIVE_SINGLETON_CURVATURE_INVERSE_BELLMAN_SEPARATION.md` | U | Reviewed D*=0 inverse-Bellman no-go, useful as a falsifier but not a positive-minimum result. |
| 63 | `CODEX_RAMSEY__REPAIRED_ATOM_MISSING_FACE_SIGN_SEPARATION.md` | U | Exact sign mismatch and local regression; no source theorem reversing the missing-face sign. |
| 64 | `CODEX_RAMSEY__RETAINED_RECTANGLE_PLATEAU_CAP_COMPATIBILITY_BARRIER.md` | U | Exact local plateau regression showing rectangle data do not imply fixed-cap compatibility. |
| 65 | `CODEX_RAMSEY__STRICT_TOGGLE_SOFT_BELLMAN_CROSS_MASS_BARRIER.md` | U | Exact quantitative cross-mass barrier and two completions; blocks a naive softening, not all nonlocal converters. |
| 66 | `CODEX_RAMSEY__UNIQUE_DEBTOR_FLOOR_ENTRANCE_AND_SOLO_RECYCLE.md` | C | Independently reviewed floor entrance/recycle trichotomy; the unique all-Continue stall and renewable regeneration remain. |
| 67 | `CODEX_RESPONSE_SWITCH__REMOTE_BUBBLE_RESPONSE_VALUE_COCYCLE.md` | C | Exact reentry-loss cocycle; a vanishing or summable source-matched reentry seam would consume the infinite arm, but current semantic/law equality does not imply it. |
| 68 | `CODEX_RIEMANN__FORCED_PAIR_TO_INDUCED_OWNER_HOPF_ADAPTER.md` | U | Exact local regression: forced-pair data do not determine the induced-owner HOPF sign. |
| 69 | `CODEX_ROOT__AGKRS_REFUSAL_COMPACTIFICATION_REPAIRS.md` | D | Incorporated into the corrected AGKRS export. |
| 70 | `CODEX_ROOT__COMMON_RESPONSE_POTENTIAL_MONODROMY_CONSUMER.md` | C | Complete finite supplied-field consumer; no source-matched common-response field is produced. |
| 71 | `CODEX_ROOT__FACE_ENLARGE_FOLLOWUP_LOCAL_PERIODIC_OBSTRUCTIONS.md` | C | Two local no-go theorems and an Abel estimate; the two-clock hard-residual adapter is missing. |
| 72 | `CODEX_ROOT__FINITE_DATE_PREMIUM_PACKET_AND_ENDPOINT_CYCLE_BOUNDARY.md` | U | Exact large-premium packet and horizontal-cycle no-go; no chronology or renewable rank. |
| 73 | `CODEX_ROOT__MINIMUM_RETURN_REPLENISHMENT_AND_RESPONSE_RECTANGLE_TRIAGE.md` | F | Exact ledger is useful, but the claimed iterated positive endpoint walk lacks an absolute target-side gain. |
| 74 | `CODEX_ROOT__STRICT_INERT_PURE_BETTER_RESPONSE_CYCLE_TRIAGE.md` | F | Proposed strict-inert consumer is false; only a conditional finite graph lemma survives. |
| 75 | `GATE_STRENGTHENER__BALLISTIC_WEIGHTED_COCYCLE_COLLAPSE.md` | L | Correct normalized algebraic collapse; no source-realized absolute Nash-Bellman lift or semantic consumer. |
| 76 | `PAIR_WALL_REVIEW__POSITIVE_MINIMUM_CANONICAL_RAY_CYCLE.md` | L | Uniform paid scale and finite all-stall residual; no chronological or support-safe consumer. |
| 77 | `SERIAL_ENDPOINT_AUDITOR__ALL_NONEMPTY_TOGGLE_CLOSURE_MISMATCH.md` | D | Duplicate independent audit of 2/3; explicitly recommends no duplicate Lean declaration. |
| 78 | `SIMON_RESTARTABILITY_GENERAL_SPLIT.md` | L | Open restartability question, not a result. |
| 79 | `SIMON_RESTARTABILITY_ONE_POLYTOPE.md` | L | Open one-polytope restart lemma, not a result. |

## Strongest possible connections

None of the following is ready for export.  Each item states the exact new
lemma which would be needed to turn the connection into an export-worthy
theorem.

### 1. Paid-cycle recharge to two-tier chronological shadowing

Ingredients:

- the literal all-nonempty toggle cycle of notes 2 and 77;
- the checked/formalized cycle-recharge theorem of note 41, including the
  fixed charge
  
  \[
  q=\frac{7\lambda D_*}{96};
  \]
- the exact response reentry ledger of note 67; and
- `QuittingBudgetStablePacketSystem` and the cumulative near-return consumer
  in `BudgetStableCompatiblePacketIteration.lean` and
  `CumulativeChargeNearReturn.lean`.

Missing lemma: on the regenerated source supplied by the endpoint atom, the
same observer/response chart must have reentry loss `o(q)` (summable would also
suffice), while preserving two actual labels, the fixed atom, and one common
annotation bound.  Semantic-pair or full-law equality alone is insufficient.

Actual-data adapter: start with
`FinFourOwnerCompressedMinimumReturnForcedPairPacket`, use the literal marked
siblings and the formalized spectator-recharge/atom dispatch, then causalize
the endpoint atom on that exact subsequence.

Consumer: inhabit the two-tier packet requested by
`FIN4_TWO_TIER_CHRONOLOGICAL_SHADOWING.md`; the checked budget-stable iteration
then supplies a positive cumulative admissible near-return and hence a uniform
payoff.

Novelty: this would convert a horizontal cycle into chronology by pricing the
precise reset seam, rather than falsely identifying the cycle itself with a
Bellman path.

### 2. A common-response Farkas alternative for minimum-return chords

Ingredients:

- the finite Farkas alternative and plateau regression of note 14;
- the exact response-chord cocycle and persistent-zero lemma of note 42; and
- the finite common-response potential consumer of note 70.

Missing lemma: along the actual regenerated minimum-response source, freeze
one observer and two complete pure-time responses so that either all paid
edges lie in one common potential chart, or every chart switch contributes a
source-matched positive first-disagreement seam whose total is not erased by
regeneration.

Actual-data adapter: the source and endpoint sequences in the checked
minimum-response-chord regeneration modules, not arbitrary points sharing the
same semantic pair.

Consumer: in the potential arm, the finite common-response rank forbids
circulation; in the switch arm, the seams feed
`QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily`.

Novelty: Farkas makes the desired orientation exhaustive.  The missing object
is no longer an unspecified Lyapunov function; it is one common response chart
or an explicitly charged chart-switch ledger.

### 3. Pair-rooted terminal SCC to pair-base softening

Ingredients:

- note 12's theorem that every terminal Fin4 strict-toggle SCC meets the
  two-player level;
- the collision-cycle background cancellation of note 28; and
- note 49's alternating-pair alignment with the pair-base missing-face
  condition.

Missing lemma: for one pair vertex in the actual terminal SCC, upgrade the
weak background cancellation to a quantitatively negative missing-face
average

\[
H_{\rm missing}\le -\kappa<0
\]

with enough induced-Nash mass on that background.  Note 49's exact regression
shows that sign cancellation alone cannot supply this.

Actual-data adapter: the strict-toggle relation supplied by the Fin4 hard
residual, its finite terminal SCC, and the actual induced persistent-base Nash
point for the selected pair.

Consumer: the checked pair-base softening/stationary or persistent-base
compiler, yielding an exact terminal Nash profile or a uniform payoff.

Novelty: this is a finite algebraic route from every recurrent toggle class to
one semantic consumer.  The remaining theorem is a concrete sign-and-mass
alignment, not chronology.

### 4. Adjacent finite deadlines as a source-coherent response chart

Ingredients:

- the checked finite-deadline Nash producer;
- note 40's exact adjacent-deadline participation-or-censored-reshuffling
  alternative; and
- note 42's common-response chord identities.

Missing lemma: reproject one consecutive-deadline pair to the same
positive-minimum source while retaining its literal paid edge or common
response witness and its macroscopic projective separation.  Reselecting an
unrelated minimum realizer is not allowed.

Actual-data adapter: Nash laws at deadlines `K` and `K+1` from
`exists_finiteDeadlineTimingNash_terminalDebt_le`, together with their exact
stopping-law and censored-law data.

Consumer: the response-chart output enters candidate 2 or the two-tier
chronological-shadowing question.

Novelty: this would turn an unconditional arbitrary-table finite-clock source
into the source-coherent chart absent from the current minimum-fibre route.

### 5. Strict principal blocker to the unique-debtor floor recycle

Ingredients:

- the matrix-to-`TightFaceSeparatorData` adapter of note 35;
- the reviewed unique-debtor floor entrance/recycle of note 66; and
- the solo-anchor and Abel obstructions of note 71.

Missing lemma: from the actual hard-residual principal and source chronology,
produce one strict blocker vector on the same active face as the unique-debtor
carrier, with the tight-face path attached literally to that carrier.  The
abstract nonprojective principal does not currently provide this strict,
source-matched vector.

Actual-data adapter: the proper hard principal, the source-native solo wall,
and `exists_tightFaceSeparatorData_of_no_uniformPayoff`; the adapter must
identify their player set and actual payoff annotation rather than merely
share the reward table.

Consumer: `exists_tightFace_escape`, the paid-near-return restriction, or the
floor-safe recycle.  The local periodic no-gos would then force an excursion,
a terminal branch, or a genuine rank output.

Novelty: this would connect the finite LCP obstruction to an executable path,
which is precisely what the present projective-Qbar data do not do.

### 6. Positive-Never rectangle to the normalized strict inert node

Ingredients:

- the maximum-support positive-Never rectangle excursion of note 53;
- the three-label late-release dispatch of note 50;
- the corner cap-face reduction of note 33; and
- the cap-ray support-rotation/unique-root alternative of note 34.

Missing lemma: attach the resulting off-minimum unique-all-Continue point to
the current normalized forced-pair slice while retaining fixed positive ratios
of marked mass and paid gain to whole debt, and retain the paired reset/source
data required by the modern inert questions.

Actual-data adapter: the literal late-release chronology and its three labels;
not an arbitrary positive-Never carrier point.

Consumer: `FIN4_STRICT_NORMALIZED_INERT_IMPOSSIBILITY_OR_MODEL.md` or the
paired unique-cap question.

Novelty: the rectangle chain would give an independent actual-source entrance
to the rigid inert model.  This is lower priority than candidates 1--3 because
the modern finite-atom atlas already bypasses positive-Never classification;
without the normalized adapter it is historical rather than frontier-moving.

### 7. Curvature-paid port to a complete minimum-return dispatch

Ingredients:

- exact prefix curvature renewal from note 6;
- note 32's reviewed minimum-midpoint/off-minimum endpoint theorem and
  `Delta/12` literal paid port; and
- note 54's exhaustive signed causal orientation/reset lift.

Missing lemma: either preserve one fixed-law cap response across the
source/midpoint/full-endpoint chord, or prove that the resulting inert
paid-cap stall is impossible under the current positive-minimum forced-pair
provenance.  Observer curvature alone cannot bound the other cap coordinates.

Actual-data adapter: the actual half/full replacement tangent profiles and
their joint law, not merely the limiting semantic chord.

Consumer: the checked paid-cap exact trichotomy; charged return gives a
uniform payoff, while a no-new-entry minimum endpoint gives support descent.

Novelty: the local `Delta/12` port is already sharp enough.  The only new work
would be cap/source coherence at the inert output, so another curvature
estimate without that field is not progress.

## Complete internal theorems not currently worth exporting

The following appear mathematically complete and not individually formalized,
but none is a missed export under the current gate:

1. note 12's terminal-toggle-SCC cardinality bounds;
2. note 14's finite Farkas alternative;
3. note 32's fixed-half curvature-paid-port localization;
4. note 66's unique-debtor floor entrance/recycle trichotomy;
5. note 67's response reentry cocycle; and
6. the two local obstruction lemmas and Abel estimate in note 71.

Each lacks either a current arbitrary-source adapter or a terminal/rank
consumer.  Formalizing one in `Research` may be useful for interface testing,
but it should not be sent to `exports/` until one of the connections above is
closed.

## Narrow source audit

The following checks support the dispositions above.

- Complete positive results from notes 5, 10, 16, 17, 27, 31, 36, 38, 43,
  47, 52, and 55 have matching checked declarations or formalized packets.
  In particular, `sharpReward_exists_uniformEquilibriumPayoff` now covers the
  owner-risky HOPF stationary closure, and
  `exists_finiteDeadlineTimingNash_terminalDebt_le` covers the arbitrary-table
  finite-deadline producer.
- The paid-cycle ingredients are present in
  `SameStageEndpointMonodromy.lean`,
  `VanishingDebtAtomAlternative.lean` (notably
  `hasVanishingDebtAtomAlternative_of_endpointDebtRise`), and
  `formalized/PAID_NONSINGLETON_CYCLE_SPECTATOR_RECHARGE_AND_ATOM_DISPATCH.md`.
- The desired two-tier consumer exists conditionally through
  `QuittingBudgetStablePacketData` and `QuittingBudgetStablePacketSystem` in
  `BudgetStableCompatiblePacketIteration.lean`, followed by
  `quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns`
  in `CumulativeChargeNearReturn.lean`.  The absent part is the actual Fin4
  packet inhabitant, not another compiler.
- The tight-face supplied-data machinery exists as
  `TightFaceSeparatorData`, `exists_tightFaceSeparatorData_of_no_uniformPayoff`,
  and `exists_tightFace_escape`.  The missing strict-principal/source
  alignment identified in candidate 5 is not a structure field already
  supplied by the hard residual.
- `quittingTerminalSemanticDebt_pureSetRoot_eq` supports the finite-toggle
  reductions, but it does not make horizontal coalitions successive play
  dates.  The regressions in notes 11, 65, and 77 correctly enforce that
  boundary.
- The current open questions which these connections can genuinely affect are
  `FIN4_TWO_TIER_CHRONOLOGICAL_SHADOWING.md`,
  `FIN4_MINIMUM_RETURN_CAPSTONE.md`,
  `FIN4_PAID_RESET_REGENERATION_RANK.md`,
  `FIN4_DOUBLE_UNIQUE_CAP_CLOSURE.md`,
  `FIN4_STRICT_NORMALIZED_INERT_IMPOSSIBILITY_OR_MODEL.md`, and
  `POSITIVE_MINIMUM_FACE_CYCLE_ALIGNMENT.md`.

## Recommended priority

1. Candidate 1 is the strongest: all quantitative input and the downstream
   consumer are checked; one source-matched reentry/seam theorem is missing.
2. Candidate 3 is the sharpest finite problem: it asks for one explicit
   sign-and-mass inequality and has exact regressions delimiting what is
   insufficient.
3. Candidate 2 is the most structurally explanatory and may subsume candidate
   1 if the chart-switch seam can be priced.
4. Candidate 4 is a plausible independent source of the missing chart but
   needs the hardest reprojection step.
5. Candidates 5--7 should remain secondary until their source adapters are
   shown to land on the current completion atlas rather than a historical
   residual.

The strict progress rule should be retained: another local atom, sign screen,
horizontal cycle, compact endpoint, or conditional verifier does not qualify.
The next export from this lane should either inhabit the two-tier packet,
consume the pair-rooted SCC, or attach one of the conditional algebraic
consumers to an actual current source.
