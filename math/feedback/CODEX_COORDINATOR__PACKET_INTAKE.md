# Incoming packet review

Owned by CODEX_COORDINATOR. This is an intake record, not a mathematical note
or a theorem-status index. Original submissions are preserved. A review of one
claim does not certify the other claims in the same submission.

## Active batch

| Submission | Claim group | Independent review | Disposition |
| --- | --- | --- | --- |
| [QUANTILE](../archive/QUANTILE.md) | Cross-face prefix leakage and exact-source regression | [CODEX_RENY](QUANTILE__BY_CODEX_RENY.md) | PASS; exact source-specific failure of a splice, not a conjecture counterexample |
| QUANTILE and [companion](../archive/QUANTILE_CLOCK_COMPRESSION.md) | CDF approximation, gap-preserving common-clock compression, independent recombinations, exhaustive positive-gap certificates | [CODEX_RENY](QUANTILE__BY_CODEX_RENY.md) | PASS; main compression and semidecision duplicate checked sources; common-mixture formulation does not solve selection; no export |
| [APPROX](../archive/APPROX.md), first response | Reward-box reduction; absorption-weighted Bellman/regret repair; equivalence of packet producers | [CODEX_HILBERT](APPROX_WEIGHTED_REPAIR__BY_CODEX_HILBERT.md), [CODEX_FRECHET_CYCLE](APPROX_WEIGHTED_REPAIR__BY_CODEX_FRECHET_CYCLE.md) | Full gate PASS; [frozen export](../exports/ABSORPTION_WEIGHTED_FORWARD_PACKET_REDUCTION.md); producer-equivalent reformulation, not the charge producer |
| APPROX, second response | Strict SUM-minimum cap margin; uniformly reached absorbing row from every near-minimizer | [CODEX_FRECHET_CYCLE](APPROX_MINIMUM_ENTRANCE__BY_CODEX_FRECHET_CYCLE.md), [CODEX_HILBERT](APPROX_MINIMUM_ENTRANCE__BY_CODEX_HILBERT.md) | Two independent PASS reviews with carrier-limit clarification; complete corrected proof preserved; absorbing row is not Nash |
| [SIGN](../archive/SIGN.md), first response | MAX-minimum rigidity, harmonic inequality, whole-box root exclusion, invariant-set regression | [CODEX_HILBERT](SIGN__BY_CODEX_HILBERT.md) | PASS; main rigidity largely overlaps prior results; no sign consumer |
| SIGN, second response | Quantitative prefix improvement and actual all-Never descent into a trapped prefix region | [CODEX_HILBERT](SIGN__BY_CODEX_HILBERT.md) | PASS; broader quantitative improvement and literal trap worth preserving; does not refute optimal-successor selection |
| [VANISH](../archive/VANISH.md), first response | Single-pivot/all-positive-singleton same-profile reduction and finite approximation | [CODEX_RENY](VANISH__BY_CODEX_RENY.md) | PASS; duplicate of reviewed FINITE_STOPPING and checked transport identities |
| VANISH, second response | Unique exact finite-menu equilibria with fixed late defect, but explicit vanishing-error cyclic approximants | [CODEX_RENY](VANISH__BY_CODEX_RENY.md), [CODEX_FRECHET_CYCLE](VANISH__BY_CODEX_FRECHET_CYCLE.md) | Two independent PASS reviews; simpler fixture, not a new qualitative canonical obstruction; no export |
| [R](../archive/R.md) | Padding hardness; quantitative source-payoff-preserving repair; Fin4 reverse-S.3 correction | [CODEX_FRECHET_CYCLE](R__BY_CODEX_FRECHET_CYCLE.md) | Complete independent PASS with qualified novelty. Main hardness and supplied-source Fin4 implication are already in production. The payoff-preserving refinement and its constrained square-root lower bound are preserved, not exported. |

QUANTILE's related archive is
[QUANTILE_CLOCK_COMPRESSION.zip](../archive/QUANTILE_CLOCK_COMPRESSION.zip).
Its scripts are regression evidence, not substitutes for the compression proof.

VANISH's companions are
[FINITE_MENU_EXACT_APPROX_SEPARATION](../archive/FINITE_MENU_EXACT_APPROX_SEPARATION.md)
and [check_example.py](../archive/check_example.py). These belong to the same claim
group, not separate results.

## Version anchors

These SHA-256 hashes identify the submissions dispatched for review. An added
followup receives its own review scope; earlier review does not certify it.

```text
f28bfa0de099c88555d7ebf7c2864ceb74b51c324bec315e259b12b662e9ad48  gpt/QUANTILE.md
afa8417acf568a98a10632b210447e59a64ac814ab8ba7c36f240a15035b7e00  gpt/QUANTILE_CLOCK_COMPRESSION.md
a6465fd7ae93465f0d817dc7b470f942747441e9465f1336add3ef61c819c216  gpt/QUANTILE_CLOCK_COMPRESSION.zip
3a7e5b844186f587a454b9a7437aef72dd1a365acea3ccda36f92c0fa6b0258d  gpt/APPROX.md
8077f067cddaad3812db6032a07bce16c189e6e73de528d43e3bc196a392297f  gpt/SIGN.md
497a2122d95ce14367cee7798795ab6efb1b8cc4ed9afb5de3e65e26352aa87e  gpt/VANISH.md
6946d7ac2067813c85fe3588191ae05dfcc9756b2df70647d369f34b4400134f  gpt/FINITE_MENU_EXACT_APPROX_SEPARATION.md
86a37585e7aa1fcaebc60eec179bcd53b64ab7ec673d0eb8225776c5baba4c10  gpt/check_example.py
```

## Completion rule

Each claim receives a correctness verdict, a comparison with existing results,
and an explicit remaining gap. Useful new mathematics is preserved in an owned
mathematical note; duplicates point to their existing home. Only a serious,
complete candidate enters the full independent export gate. Nothing in this
batch other than the weighted forward-packet reduction has been promoted to
exports. Existing frozen exports remain untouched.

Processed submissions are retired from `gpt/` only after checking their
mathematical homes. [The retirement record](../archive/GPT_PACKET_RETIREMENT.md)
retains originals and the disposition map; a moved submission's old hash
record still refers to exactly those bytes. This does not promote rejected
consumer claims or silently close any question.

## Preserved mathematical content

- R:
  [Survival-weighted source repair](../notes/CODEX_FRECHET_CYCLE__R_SURVIVAL_WEIGHTED_SOURCE_REPAIR.md)
  preserves payoff, controls all unrestricted debts, and retains the
  exceptional survival-weighted abnormality term. Its matching lower
  example is specifically about payoff-preserving repair, not unrestricted
  equilibrium production. [The padding companion](../notes/CODEX_FRECHET_CYCLE__R_PADDING_VARIANTS_AND_SUM_INFIMUM.md)
  preserves collision conventions, the fully mixed variant, deleted-clock
  nonuniformity, and the SUM-infimum corollary. One complete independent
  intake review is recorded; no full export gate or Lean check is claimed.

- APPROX minimum entrance:
  [SUM minimum uniformly reached entrance](../notes/CODEX_FRECHET_CYCLE__SUM_MINIMUM_UNIFORMLY_REACHED_ENTRANCE.md).
  The submitted limiting-actuality wording has been clarified. The corrected
  standalone proof has passed independent second review. The equality
  annotations lie in the canonical reward box used by the cited capacity
  theorem; larger-box claims require the generic compact-capacity adapter.
- APPROX weighted repair:
  [Absorption-weighted forward-packet repair](../notes/CODEX_HILBERT__ABSORPTION_WEIGHTED_FORWARD_PACKET_REPAIR.md).
  Two independent reviews are complete, including exact standalone coherence.
  The [assembled export](../exports/ABSORPTION_WEIGHTED_FORWARD_PACKET_REDUCTION.md)
  passed [eligibility review](APPROX__EXPORT_ELIGIBILITY_BY_CODEX_RENY.md) and
  [final-surface confirmation](ABSORPTION_WEIGHTED_FORWARD_PACKET_REDUCTION__FINAL_SURFACE_BY_CODEX_FRECHET_CYCLE.md).
  Its accepted full SHA-256 is
  `5657d96e7a4da5decc9debc0a0499a587074ba523626ac3d7e3d0d4bce906359`.
  Placement preserves the approved draft byte-for-byte; this records reviewed
  mathematics only, not a new Lean check or an arbitrary-table producer.
- SIGN:
  [Quantitative prefix improvement and anchored trap](../notes/CODEX_HILBERT__QUANTITATIVE_PREFIX_IMPROVEMENT_AND_ANCHORED_TRAP.md).
  Full proof of the two substantive additions is preserved separately from
  the older rigidity results. No existing frozen proof was modified.
- VANISH:
  [Canonical exact finite-menu separation](../notes/CODEX_RENY__CANONICAL_EXACT_FINITE_MENU_SEPARATION.md).
  The complete canonical example and parameter family are preserved. Both
  reviewers confirmed that the earlier
  [Canonical pivot boundary homotopy](../notes/CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md)
  already states and proves the all-menu-selector qualitative separation.
  That prior record is an unreviewed ordinary proof draft, not checked Lean;
  the distinction remains explicit. VANISH is independently reviewed
  alternative evidence with simpler formulas, not a new eliminated route.

## Question coverage in this wave

QUANTILE addresses proper-face compilation and finite certificate search;
APPROX addresses approximate forward-packet production; SIGN addresses the
controller–tester sign question; VANISH addresses the canonical finite-law
selector. None supplies a complete answer to its original question.

The two current questions without a packet in this wave are:

- Turn an actual quantitative paid row into debt below the global infimum.
- From absorbing row-perfect sequences to approximate equilibrium.

## Tested outgoing connections

- [Retained-root entrance test](../notes/CODEX_HILBERT__REACHED_MINIMUM_ENTRANCE_RETAINED_ROOT_TEST.md):
  full root optimization of the reached SUM-minimum entrance gives only the
  known off-minimum absorption budget, not a positive Nash-absorption floor.
  The existing SIGN example tests fixed-tail optimization, not genuine
  positive global minimality. This subroute produced no new outgoing edge.
- [Weighted actual-source attempt](../notes/CODEX_FRECHET_CYCLE__WEIGHTED_FORWARD_ACTUAL_SOURCE_ATTEMPT.md):
  the existing linear absorption-defect theorem freezes sufficiently accurate
  weighted packets started in its minimum tube. This is an application of an
  existing barrier, not a new eliminated branch. The weighted producer is free
  to start elsewhere, so nonlocal construction remains open.

The first follow-on tests have readable checkpoints:

- [Symmetry-preserving logit selector](../notes/CODEX_RENY__SYMMETRY_PRESERVING_LOGIT_SELECTOR_OBSTRUCTION.md):
  an independently unreviewed proof candidate excludes all identical-nonpivot
  stopping laws on the canonical cyclic fixture, not just stationary laws.
  It leaves nonsymmetric selectors open; related logit notes are being checked
  for exact novelty.
- [Projected absorption-scaled logit cycles](../notes/CODEX_HILBERT__PROJECTED_ABSORPTION_SCALED_LOGIT_CYCLES.md):
  the global construction escapes SIGN's fixed-prefix trap, but its comparable-
  temperature entropy continuation cannot approach the known VANISH cycle.
  This is a counterpart of an existing entropy-odds obstruction, not a
  universal producer falsification. Other components and non-logit selectors
  remain open; no export is proposed.
- [Global tail/punishment test](../notes/CODEX_FRECHET_CYCLE__REACHED_ENTRANCE_GLOBAL_TAIL_PUNISHMENT_TEST.md):
  changing complete tails improves a one-sure-owner cap only until saturation
  or punishment minimality. Independent whole-law mixtures of the general
  screened objective recover the existing multicoordinate Jensen ledger,
  without a new bound on cross-vertex excess or a consumer.

The second set of bounded checks has the following disposition:

- [Simultaneous active-response recombination](../notes/CODEX_RENY__SIMULTANEOUS_ACTIVE_RESPONSE_RECOMBINATION_BOUNDARY.md):
  simultaneous KKT weights were already retained in the existing HAHN result.
  The actual independent joint move still needs pointwise descent for every
  enlarged-menu active test, including the newly omitted late date. No sign
  follows from the weighted-average identity or common-clock compression;
  this variant has stopped without a new producer.
- [Quadratic full-box barrier limitation](../notes/CODEX_FRECHET_CYCLE__QUADRATIC_FULL_BOX_BARRIER_RESET_RANK_TEST.md):
  [independent review](CODEX_FRECHET_CYCLE__QUADRATIC_FULL_BOX_BARRIER_RESET_RANK_TEST__BY_CODEX_RENY.md)
  passes the complete reset-rank proof and exact two-parameter example.
  It rules out every quadratic full-box prefix-monotone function on that
  family, not arbitrary closed invariant-set certificates. No member is
  proved to have positive semantic value. Retained internally, no export
  eligibility inferred from correctness alone.
- [Partial necessity map](../notes/CODEX_HILBERT__NORMAL_EQUILIBRIUM_TO_FORWARD_PACKET_PARTIAL_CONVERSE.md):
  independently reviewed ordinary-mathematics adapters cover absorbing
  stationary sources and normal every-restart S.3 sources. A positive
  singleton supplies the respective termination qualifications. The exact
  [S.2 source test](../notes/CODEX_FRECHET_CYCLE__AGKRS_S2_FORWARD_PACKET_SOURCE_TEST.md)
  characterizes that alternative by a sure exact root Nash against the
  punishment vector; its reverse is credited to the existing sure-row
  compiler. Repeating this root is not generally valid. The combined
  architecture characterization has passed the scoped review below, but
  not the complete unrestricted-coverage export gate.
  This pass deliberately assumes UE in a necessity direction; it is not a
  source producer or proof of the conjecture.

The combined architecture statement is preserved in
[Normal equilibrium: forward packets or a sure root](../notes/CODEX_HILBERT__NORMAL_EQUILIBRIUM_FORWARD_OR_SURE_ROOT.md).
[Independent review](CODEX_HILBERT__NORMAL_EQUILIBRIUM_FORWARD_OR_SURE_ROOT__BY_CODEX_FRECHET_CYCLE.md)
passes its necessity adapters and composition. The review explicitly
separates its independently checked portions from the reviewer's own S.2
dependency, which HILBERT checked separately. It is not yet a full export
gate for an unrestricted coverage claim. A sure root is a
certificate relative to the semantic punishment vector, not an algorithm
for calculating that vector from the table. The contrary-case producer
obligation is unchanged.

The reset-rank family's equilibrium search found an
[explicit stationary profile](../notes/CODEX_FRECHET_CYCLE__RESET_RANK_FAMILY_STATIONARY_EQUILIBRIUM.md)
for the entire two-parameter family, not just the rational test member.
[Independent full-cap review](CODEX_FRECHET_CYCLE__RESET_RANK_FAMILY_STATIONARY_EQUILIBRIUM__BY_CODEX_HILBERT.md)
passes the proof, including Never, all late dates, signed owner payoffs,
and the fixed uniform target. The family has zero behavioral gap. Its
quadratic-barrier obstruction therefore supplies no evidence that richer
negative barriers are needed. The general reset-rank algebra remains valid.

The table-driven asymmetric-prior test reproduces the positive geometric
fixture, but its attempted obstruction on the cyclic fixture excludes only
the familiar witness, not all low-error branches. That odds argument also
uses an unnecessary pivot-logit restriction. The follow-on test removes it
and couples exact pivot repair with finite nonpivot responses. A second
lane tests a specified vanishing payoff perturbation rather than entropy
regularization. A third lane is selecting a distinct global forward-packet
producer mechanism. No author is being asked to expand a stopped local
repair, vary constants, or raise barrier degree.

The distinct
[vanishing private Never-bonus selector](../notes/CODEX_HILBERT__VANISHING_PRIVATE_NEVER_BONUS_SELECTOR.md)
has a complete positive proof draft on the canonical cyclic family:
an exact auxiliary Nash equilibrium is selected by two global extrema,
and every selected law has small original unrestricted regret. The bonus
is only an auxiliary planned-action payoff, not an intervention in original
play. The draft explicitly derives its comparison equilibrium from that
family and does not assume one for arbitrary tables.
[Independent review](CODEX_HILBERT__VANISHING_PRIVATE_NEVER_BONUS_SELECTOR__BY_CODEX_FRECHET_CYCLE.md)
passes the all-date comparisons, every-selected-law guarantee, and full-cap
translation. A known relabelled example excludes a universal fixed subsidy
label, independently of the bonus/deadline rate; the next concrete test is
an adaptive finite portfolio of labels on that example.

The
[coupled pivot-LP/nonpivot-response test](../notes/CODEX_RENY__PIVOT_LP_AND_FINITE_NONPIVOT_BEST_REPLY_COUPLING.md)
is preserved as an ordinary proof draft. It proves coherent finite-menu
payoffs even on the nonattained LP boundary, a simultaneous bad fixed point
with full value 3/16 at every deadline, and a separate good bonus-coupled
branch on the canonical cyclic table. The latter has a global arbitrary-
pivot optimality certificate, so the bonus does not silently invalidate
inner optimization. Independent checking of that positive certificate is
underway. Bad fixed points do not bound the best fixed point or arbitrary
profiles. An earlier provisional fixture was withdrawn before any proof
was frozen; only the corrected numbers occur in the mathematical note.

The adaptive-bonus test also reports a new exact backward-balanced source
on the homotopy table that defeated the fixed subsidized label. The
all-date verification is in progress. It is being tested as coverage of
one selector mechanism, not as new equilibrium existence for that already
solved table.

## Global follow-on result and validation boundary

The [polynomial capacity separator](../notes/CODEX_FRECHET_CYCLE__WEIGHTED_CAPACITY_POLYNOMIAL_SEPARATOR.md)
has passed complete independent reviews by
[HILBERT](CODEX_FRECHET_CYCLE__WEIGHTED_CAPACITY_POLYNOMIAL_SEPARATOR__BY_CODEX_HILBERT.md)
and [RENY](CODEX_FRECHET_CYCLE__WEIGHTED_CAPACITY_POLYNOMIAL_SEPARATOR__BY_CODEX_RENY.md).
The [finite burn-in theorem](../notes/CODEX_RENY__FINITE_FORWARD_PUNISHMENT_FLOOR_BURN_IN.md)
has passed [independent review](CODEX_RENY__FINITE_FORWARD_PUNISHMENT_FLOOR_BURN_IN__BY_CODEX_HILBERT.md).
The [floor-free composition](../notes/CODEX_RENY__PUNISHMENT_FREE_POLYNOMIAL_FORWARD_CERTIFICATE.md)
has passed its [combined-surface check](CODEX_RENY__PUNISHMENT_FREE_POLYNOMIAL_FORWARD_CERTIFICATE__BY_CODEX_HILBERT.md).

These are ordinary-mathematics results, not new Lean declarations. The
core supplies a rational-polynomial charge bound on every allowed edge
from global bounded capacity, not from a selected orbit. Under normality,
burn-in removes supplied punishment floors without changing the fixed box.
The combined normal-game characterization still has the separate semantic
sure-root exclusion; it neither computes punishment values nor gives a
degree bound, an arbitrary-table decision algorithm, an actual negative
instance, or an unconditional positive producer.

The [final combined export](../exports/POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md)
has passed the [final-surface and eligibility check](POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS__FINAL_SURFACE_BY_CODEX_RENY.md).
The two pre-promotion wording corrections distinguish the four variables of
the polynomial from the twelve coordinates of its universal edge test, and
remove assembly-only lifecycle wording. RENY confirmed that reversing only
those corrections recovers the previously reviewed full surface. ROOT read
the complete assembly, checked the current source delta, links and gate,
and placed the approved bytes unchanged. Its frozen SHA-256 is
`14191a09b4a42149e0c893666603d85b2e2f1fb3bcd0240af0e0619aaeefc9d6`.
This is reviewed mathematics ready for formalization, not a new Lean result.

The forward-producer question omits the now-redundant punishment-floor
input and states the equivalent absorption-weighted formulation. Its former
surface is preserved in
[the supplied-floor question archive](../archive/FIN4_FORWARD_PACKETS_WITH_SUPPLIED_PUNISHMENT_FLOORS.md).
No new conjecture-closing question or solved counterexample class is claimed.

The [adaptive Never-bonus portfolio on the homotopy fixture](../notes/CODEX_HILBERT__ADAPTIVE_NEVER_BONUS_PORTFOLIO_ON_H.md)
now has a complete ordinary proof draft. It has not received an independent
full review; the table was already known to admit equilibrium. The
[positive pivot-optimality certificate](CODEX_RENY__BONUS_BRANCH_PIVOT_OPTIMALITY__BY_CODEX_HILBERT.md)
has a scoped PASS covering only the indicated sections of the coupled
selector notebook, not its entire fixed-point construction.

Retirement is complete for 28 processed input files and four download
metadata files. All original bytes remain recoverable, no rendered link
to those former `gpt/` paths remains, and no frozen export/formalized
packet or active proof surface changed. Nine other input bundles remain
pending complete preservation checks, not as nine certified open problems.

## Tests of the global polynomial formulation

These are completed bounded author-level mathematical tests, not new
independent reviews or eliminated counterexample classes.

- [Singleton-face constraints](../notes/CODEX_HILBERT__POLYNOMIAL_DRIFT_SINGLETON_FACE_TEST.md)
  recover the known homogeneous singleton consumer. The one-derivative test
  at the singleton vector passes every invertible comparison matrix, so it
  cannot exclude the remaining generic matrix class.
- [Positive-size collision cycle](../notes/CODEX_HILBERT__POSITIVE_SIZE_COLLISION_CYCLE_GLOBAL_TEST.md)
  really excludes every potential for its table, but the same table already
  has a pure equilibrium. The inverse-designed fixture is not a new class.
- [Collision-subsidy transport](../notes/CODEX_HILBERT__COLLISION_SUBSIDY_POLYNOMIAL_TRANSPORT_TEST.md)
  preserves the all-edge certificate only while spending its tolerance.
  The tested all-Quit target is beyond that margin by the original pure-root
  test itself. Subdivision of this deformation does not replenish tolerance.
- [All-anchor discounted Nash](../notes/CODEX_FRECHET_CYCLE__POLYNOMIAL_ALL_ANCHOR_DISCOUNTED_NASH_TEST.md)
  gives a uniform absorption bound over all anchors and solutions, but its
  limiting constraint is the already required full standard-Q property.
  A global polynomial minimizer has an exact all-Continue discounted
  solution at every discount, so that proposed extremum proof stops there.

The sign question now also states the complete normal-class polynomial
alternative without links, Lean syntax, or a progress narrative. The
semantic invariant-set formulation remains available; the two edge relations
are not identified. Existing frozen export bytes were not changed.

The useful process inference is limited: several distinct global tests have
collapsed back to established necessary conditions, so they are not evidence
of a new residual reduction. This is not evidence that no global argument
can work. Those exact tests are stopped rather than expanded into additional
fixtures or finer constants. The new late-cap-compensated selector is being
checked separately as an actual all-table construction; no consumer for its
remaining joint late-quitting event is assumed.

## Compensated-source review and the next selection test

The [late-cap-compensated source](../notes/CODEX_RENY__LATE_CAP_COMPENSATED_NEVER_SELECTOR.md)
has passed its [focused independent review](CODEX_RENY__LATE_CAP_COMPENSATED_NEVER_SELECTOR__BY_CODEX_FRECHET_CYCLE.md).
ROOT read the complete review and its separate
[boundary tests](../notes/CODEX_FRECHET_CYCLE__COMPENSATED_NEVER_SELECTOR_BOUNDARY_TESTS.md).
The frozen source hash is
`22a63c4acbe3b67f20bc2c70f675bded8b9a8bfb211e4cc74fb94904cabdeea0`.
The result supplies a compact coupled fixed-point set for every table,
deadline, and prescribed bonus vector. Its pivot minimizes the original
full behavioral repair value, while the three other players best respond
to the specified compensated finite-menu payoff. Boundary points receive
actual approximants, not fictitious exact realizations.

This is additional source structure, but it is not a completed selection
theorem. In particular, the production equivalence
`smallPivotRepairValue_iff_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Terminal/PivotRepairUniformPayoffCharacterization.lean`)
allows arbitrary finite opponent laws; it does not require membership in
this new fixed-point subset. Completeness of the restricted selector must
not be borrowed from that theorem. The separate research tests now ask for
joint re-equilibration yielding smaller values, and for an exact test of
the selector's expressiveness on solved tables. No export gate is opened
merely because the fixed-point set is always nonempty.

The [menu-unfolding analysis](../notes/CODEX_RENY__COMPENSATED_SELECTOR_MENU_UNFOLDING.md)
is an author-level proof draft. It preserves global inner optimality but
identifies the exact lost outer best-response condition. Transferring the
lost compensation to the bonus keeps the same original value and need not
respect the small-bonus budget. A different delayed-tail embedding has an
explicit sign condition. Neither calculation proves monotonicity of the
minimum over all fixed points after menu enlargement.

The [fixed-pivot tail-matching obstruction](../notes/CODEX_HILBERT__COMPENSATED_FIXED_POINT_TAIL_MATCHING_OBSTRUCTION.md)
is also an author-level proof, not an independently sealed export. It tests
a globally selected one-menu fixed point, rather than an arbitrary bad
branch. Matching the other players' continuation targets can eliminate
their debts while increasing the pivot's unrestricted cap. This rules out
that operation, not joint re-equilibration or all-deadline small-value
selection.

The formalizer's fixed-box strengthening is visible in
`hasFloorFreeExactFiniteForwardPackets_iff_exact` and
`hasFloorFreeAbsorptionWeightedFiniteForwardPackets_iff_weighted`
(`UniformEquilibrium/Quitting/Projective/FloorFreeForwardPacketInputRemoval.lean`).
Their inspected statements retain normality and a positive reward bound
but no requirement that the fixed annotation box contain the rewards.
No new compiler run was performed by ROOT, and the stronger production
surface does not authorize editing the frozen polynomial export.

## STALL: checked regression, not a new selector obstruction

Input [STALL](../gpt/STALL.md), SHA-256
`0a8149762836946c208a07f4190e9c32340a05c52474b236fa4cbb4ad532bedb`,
has a complete [independent review](STALL__BY_CODEX_FRECHET_CYCLE.md).
ROOT read the original, the complete review, and the companion checker;
the checker passes its explicitly bounded algebra and deviation tests.
All-deadline uniqueness rests on the reviewed mathematical argument, not
on that program. No new Lean check was performed.

The proof is sound: every exact finite-menu Nash stopping law is forced
to keep a fixed positive unrestricted debt and a fixed positive Never
mass, while an explicit geometric profile is terminal Nash and its finite
truncations have vanishing full regret. The claimed unique object is the
product stopping law, not every irrelevant off-path behavioral action.
The zero-boundary phantom does not bound free-start forward capacity.

The [earlier canonical example](../notes/CODEX_ROOT__CANONICAL_EXACT_MENU_OBSTRUCTION_SOURCE.md)
already proves the same every-deadline separation, strict successor basin,
and geometric bypass. STALL adds a particularly clean entirely nonnegative
reward table, not a new exclusion of a conjecture route. The current
finite-menu question already allows approximate laws and needs no edit.
Retain the example and review; do not open a duplicate export.

The independent
[compensated-selector expressiveness test](../notes/CODEX_HILBERT__COMPENSATED_SELECTOR_EXPRESSIVENESS_TEST.md)
shows that this new table has a literal zero-valued compensated point at
every deadline. More generally every zero-valued closed finite repair
point already satisfies that selector's outer conditions at zero bonus.
This is an author-level scope result, not a full strategy-class review:
equality of zero sets at each fixed menu does not establish transfer of
vanishing values when the menu grows. That limit-selection implication
remains open.

## Selection restrictions versus actual value progress

The joint test in Section 10 of
[the unfolding note](../notes/CODEX_RENY__COMPENSATED_SELECTOR_MENU_UNFOLDING.md)
moves all three nonpivot Never arms to a new finite date and then allows
the entire pivot law to be reoptimized. On the specified globally selected
one-menu fixture it strictly lowers actual full exploitability. Nevertheless
every resulting globally optimal pivot repair is outside the compensated
fixed-point class. This is an author-level exact comparison, not a proof
of a globally renewable descent or of failure of all fixed-point selectors.

Together with STALL, it gives a concrete reason to distinguish the original
optimization problem from additional exact equilibrium conditions imposed
by a synthesis method. The current research tasks are therefore separated:
one tests continuation/orientation of the full compensated correspondence;
another seeks direct approximate selection without that restriction; a
third tests the universal robust polynomial relation. Mere nonemptiness,
connectedness without objective control, or a value improvement outside a
claimed invariant class is not being counted as a completed consumer.

## All-deadline bonus-removal test

The [all-deadline zero-extra-bonus theorem](../notes/CODEX_RENY__ZERO_BONUS_COMPENSATED_CONTINUATION_OBSTRUCTION.md)
has passed [independent review](CODEX_RENY__ZERO_BONUS_COMPENSATED_CONTINUATION_OBSTRUCTION__BY_CODEX_HILBERT.md)
at corrected source hash
`d0078466dd1e68beeb55e657977c385aa07675ccc2e53ad48eaf25b0724c8948`.
ROOT read the complete review. The sole correction distinguishes the
nonpivot auxiliary payoff's own-law affinity from the maximum-regret
objective's pivot convexity; the theorem and estimates did not change.

Every zero-extra-bonus compensated fixed point on the canonical cyclic
table has original full exploitability at least 1/32, at every finite
deadline. Every positive bonus ceiling admits values tending to zero.
This is a new all-menu obstruction to uniformly cheap bonus removal,
even with arbitrary reselection, not the earlier fixed-menu or
prescribed-symmetry test. It does not refute the intended selector,
which permits positive bonuses. No new Lean check or export is claimed.
The active finite-menu question requires approximate laws and remains
unchanged; this is not its requested all-behavior negative answer.

Two other bounded mechanisms have been stopped rather than expanded:

- [Independent repetition of a finite MAX candidate](../notes/CODEX_HILBERT__GLOBAL_MAXIMUM_REPEATED_BLOCK_TEST.md)
  gives a rescaled Never-cap obstruction from global minimality, not the
  upper bound needed for descent. The calculation is an application of
  existing complete-response semantics.
- [Small-piece implementation of a finite-root convex balance](../notes/CODEX_FRECHET_CYCLE__ROBUST_FINITE_ROOT_CONVEXIFICATION_STOP.md)
  runs into the existing returned-block relative-error gap. Its exact
  private-thinning seam is retained, but no new counterexample class is
  excluded. Finite positive-size nonlocal words remain outside that test.

Neither checkpoint closes a conjecture-facing branch.

## Convex global-drift obstruction

The [C1-convex full-box no-go](../notes/CODEX_FRECHET_CYCLE__CONVEX_GLOBAL_ROOT_DRIFT_IMPOSSIBILITY.md)
has a complete [independent PASS](CODEX_FRECHET_CYCLE__CONVEX_GLOBAL_ROOT_DRIFT_IMPOSSIBILITY__BY_CODEX_RENY.md),
bound to source hash
`7abde160a5d8715f1c3b42e19e18f3a248e571f6c157864b77a59bfbf99b8a23`.
ROOT read the complete source and review. For every nonempty finite
quitting game, no continuously differentiable convex function has the
required positive absorption drift on every exact root edge in a
strictly reward-padded full payoff box. The new step is a global
lower-boundary minimization argument, not another singleton derivative
or selected-orbit test.

Thus any polynomial certificate in the existing full-box formulation
must be nonconvex. This does not exclude general polynomials, indefinite
quadratics, or sum-of-squares verification of their edge inequalities.
The theorem does not apply to an arbitrary smaller box or a restricted
semantic carrier. The [nonsmooth robust corollary](../notes/CODEX_FRECHET_CYCLE__ROBUST_CONVEX_ENVELOPE_EXCLUSION.md)
also has a complete [independent PASS](CODEX_FRECHET_CYCLE__ROBUST_CONVEX_ENVELOPE_EXCLUSION__BY_CODEX_RENY.md).
ROOT read that review in full. Positive one-sided smoothing on a smaller
still reward-padded box preserves both absorption-weighted error bounds
and convexity; it excludes any positive uniform drift for a bounded
convex envelope at any positive tolerance. It does not assert the
nonsmooth exact-edge statement at zero tolerance. No frozen export
changed and no new export was opened.

Both new theorems constrain synthesis methods rather than remove a
possible UE counterexample table. They warrant stopping the corresponding
shortcuts, not reporting a terminal consumer or a reduction of the
conjecture's remaining table class.

The next bounded investigations deliberately avoid those restrictions:
approximate completeness of the selector with positive bonus ceilings;
whether an attained envelope contact decomposition permits balanced
actual-root replacements that contradict its own optimization, without
interpreting a mixture as gameplay; and a blind-spot pass seeking one
direct original-objective operation beyond repeated-block and local
first-order tests. These are research questions, not supplied adapters
or newly established routes to UE.

## Joint selection and global forcing: bounded tests

Three subsequent author-level tests are complete; none has been exported
or presented as a new UE consumer.

- [Full-law coordinate repair](../notes/CODEX_HILBERT__FULL_EXPLOITABILITY_COORDINATE_REPAIR_TRAP.md)
  gives an actual positive-error family closed under every nonincreasing
  one-player replacement, including neutral retiming and unbounded laws.
  A known joint move improves it. This is stronger than testing one-date
  deviations, but its negative nonpivot payoffs exclude the genuine
  strict-interior global-minimum source. It therefore stops monotone
  coordinate repair from arbitrary initialization, not joint selection.
- [Positive-bonus exactification](../notes/CODEX_RENY__POSITIVE_BONUS_APPROXIMATE_COMPLETENESS_TEST.md)
  computes exactly what changing the scalar Never bonus can repair at one
  fixed source. It cannot remove unequal values at supported finite
  dates. This does not refute the fixed-table positive-bonus completeness
  question, which permits entirely new laws and an arbitrary larger menu.
  The new task does not require a modulus uniform over tables or a
  source-by-source conversion; those were extra demands of the test.
- [Envelope contact replacement](../notes/CODEX_FRECHET_CYCLE__CONTACT_BARYCENTER_ROOT_REPLACEMENT_TEST.md)
  has a valid direct convex-program consumer if actual root replacements
  preserve a contact decomposition's barycenter with positive charge.
  No such balanced source was obtained. Its local counterexample does
  not satisfy the universal polynomial inequality and therefore does not
  refute the full global forcing question. A convexification-gap decrease
  alone was not promoted to a renewable descent.

The research portfolio now retains joint original-objective variation and
fixed-table positive-bonus completeness, with a separate bounded attempt
to synthesize an actual nonconvex negative certificate. The latter must
check every robust edge and the true punishment sure-root exclusion; a
sample fit, an arbitrary displayed punishment vector, or a restricted
profile gap is not a negative certificate.

## Inspected production boundary

At inspected revision `2fae892`,
`quittingGame_exists_uniformEquilibriumPayoff_iff_fixedBoxPackets_or_sureRoot`
(`UniformEquilibrium/Quitting/Projective/FixedBoxForwardCharacterization.lean`)
supplies the fixed-box equivalence under Fin4 normality and a positive
singleton. It does not produce either disjunct from arbitrary game data.

`QuittingRenewedActualProfileSequence`
(`UniformEquilibrium/Quitting/Root/RenewedActualProfileDebtRecharge.lean`)
instead consumes supplied actual cap-attaining replacements whose children
are literally the next sources. Its cross-player recharge bounds retain
the supplied common vertical debt drop and the initial-debt boundary term.
Neither a coherent sequence, cap attainment for arbitrary profiles, nor
an upper bound on leakage is produced. ROOT inspected both complete source
files but did not perform a new Lean build. The agents received these
specific distinctions so new integration is not mistaken for the missing
mathematical construction.

## Constant-own-reward candidate: proof valid, class already covered

The [constant-own-quitting-reward drift exclusion](../notes/CODEX_FRECHET_CYCLE__CONSTANT_OWN_QUIT_REWARD_GLOBAL_DRIFT_EXCLUSION.md)
at source hash
`15ecd111e19db25c6ad19f591efc446522d88a49f92227dfe477d073c883fd53`
passed independent [RENY](CODEX_FRECHET_CYCLE__CONSTANT_OWN_QUIT_REWARD_GLOBAL_DRIFT_EXCLUSION__BY_CODEX_RENY.md)
and [HILBERT](CODEX_FRECHET_CYCLE__CONSTANT_OWN_QUIT_REWARD_GLOBAL_DRIFT_EXCLUSION__BY_CODEX_HILBERT.md)
reviews, both read in full by ROOT. It excludes every smooth universal
exact-root drift potential, without convexity, for the stated raw-table
class. The common successor boundary, multiple-binding perturbation, and
absorption lower bound are actual mathematical arguments, not supplied
geometry. No new Lean check is claimed.

The canonical nonnegative-singleton family is nevertheless already covered
by the existing unit-solo/capped-joint-exit theorem and elementary positive
scaling plus vanishing terminal-reward perturbation. In fact that older
argument covers the larger nonnegative-singleton weak-solo-preference
class. The perturbation changes payoff by its size times absorption
probability; it is not an affine strategic equivalence with Never fixed.
The exact terminal affine-payoff primitive already exists. What was not
found in the narrow production lookup is the assembled zero-solo closure
wrapper, not a missing mathematical existence argument.

Accordingly this is retained supporting mathematics and a rejected negative
search family, not a newly closed UE class. No export was opened and no
question was changed. The proof's common-boundary mechanism is now being
tested separately with genuine joint-quitting premiums; no strengthened
coverage is asserted here.

The other two bounded tests also stopped without a producer:
[positive-bonus joint exactification](../notes/CODEX_RENY__POSITIVE_BONUS_APPROXIMATE_COMPLETENESS_TEST.md)
does not follow either from constrained low-value fixed points or auxiliary
continuation-game selection, while
[joint Never-arm release at a true MAX minimum](../notes/CODEX_HILBERT__GLOBAL_MAXIMUM_JOINT_NEVER_RELEASE_BOUNDARY.md)
retains the correct global source but supplies no favorable simultaneous
head/tail cap comparison. These failures do not refute the unrestricted
finite-menu selection question. They are not reasons to add the tested
methods' extra exactness or invariance requirements to that question.

## Ordered positive quitting premiums: completed export gate

[Ordered positive quitting premiums](../exports/ORDERED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM.md)
was promoted unchanged at SHA-256
`a42680e45fe7a8a373337a624808eefee1fc5a3b53507eda32cb5a7e5e7f3b6e`.
ROOT read the complete final draft and both complete independent final
reviews by [RENY](ORDERED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM__FINAL_BY_CODEX_RENY.md)
and [TARSKI](ORDERED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM__FINAL_BY_CODEX_TARSKI_PREMIUM.md).
HILBERT is credited as a mathematical contributor, not counted as an
independent reviewer of his own classical-consumer attachment. TARSKI
derived the proof and attempted falsification without the earlier verdicts.

The only final correction added explicit definitions of punishment and
free-start weighted capacity to the optional analytic section. Both reviewers
accepted the resulting exact bytes. ROOT verified that deleting those
seventeen added lines recovers the originally reviewed hash, checked every
local link from the final export location, and verified that the promoted
file is byte-identical to the accepted draft. No export was edited after
placement, and no new Lean compilation or implementation is claimed.

The main theorem is for any finite nonempty player set with nonnegative
own singleton rewards. Players must admit an order such that any strictly
positive own-quitting premium requires an earlier player in that coalition.
Negative own premiums and all passive rewards are unrestricted. This is a
finite reward-table condition, not an order imposed on stopping dates.
The proof constructs actual periodic, every-suffix terminal approximate
equilibria and obtains one fixed uniform-equilibrium payoff.

The strict change is a complete raw-table producer into the old
Solan--Vieille active-low-payoff-root mechanism. The original conditional
theory and existing full-response extraction are credited explicitly.
This is neither the already covered constant-own subclass nor a claim of
worldwide mathematical priority. No supplied strategy, successful splice,
punishment floor, or equilibrium source remains in the main premise.
The optional lower-boundary equivalence and smooth-drift exclusion retain
their separate nonnegative-own-premium assumption; that restriction and
punishment equality are not transferred to the signed main theorem.

The general conjecture and the broad priority questions remain open.
The finite criterion is sufficient, not necessary for UE; failed peeling
can occur in a game with an exact equilibrium. Subsequent work must not
silently strengthen the objective to exact stationary equilibrium or
interpret this label order as a chronological descent.

## Beyond ordering: raw-table progress versus method restrictions

The complete [weighted-participant candidate](../notes/CODEX_FRECHET_CYCLE__WEIGHTED_PARTICIPANT_PREMIUM_ROOT_ADAPTER.md)
is preserved at SHA-256
`3d40e81fa5a758e60b321abdc0efa457e62a63ea1d8df092a5d8ed09d5e2e786`.
Its finite product identity weights each owner's endpoint premium by both
the owner's weight and actual Quit probability. Coalition sums include
only participating quitters, not passive payoff recipients. A cyclic
premium family satisfies this condition while failing ordered peeling;
the converse separation is also explicit. The source audit distinguishes
the old full-player social chamber and affine-membership potential classes.
The stated result is a new input condition for the classical consumer, not
a worldwide priority claim or exclusion of every other known solved class.

A support-dependent strengthening passed the full gate: for each
nonempty active set, choose nonnegative weights of total one on that set,
with nonpositive weighted participant premiums on every internal coalition.
This includes an ordered peeling witness concentrated on one player and
globally positive balancing weights restricted to each support. The author
and both independent reviewers derived the root implication separately.
The final [supportwise weighted-premium export](../exports/SUPPORTWISE_WEIGHTED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM.md)
was promoted byte-identically at SHA-256
`38d4975b7e630e59878332bdb96190932ede7e4be8c414e0fe11c201dcabcef7`.
The [TARSKI review](SUPPORTWISE_WEIGHTED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM__BY_CODEX_TARSKI_PREMIUM.md)
and [NOETHER review](SUPPORTWISE_WEIGHTED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM__BY_CODEX_NOETHER_SUPPORT.md)
each check the complete proof, original paper and exact production inputs,
and explicitly accept all 392 final lines. ROOT read both reviews in full,
including their final-byte reconciliations, checked links from the export
location, and verified the promoted hash and exact comparison with the
accepted draft. No mathematical correction was needed; the final additions
are source/handoff/scope text and explicit zero preabsorption payoffs.
No new Lean implementation or check is claimed. The ordered export remains
unchanged; the supportwise theorem gives a more general table input, not a
correction to it. Failure of these finite linear feasibility
tests does not imply failure of equilibrium, nor does a dual coalition
mixture automatically have an independent-product realization.

The separate [two-core test](../notes/CODEX_HILBERT__TWO_PREMIUM_CORE_STATIONARY_AND_ROOT_CHOICE_BOUNDARY.md)
is an ordinary-mathematical, not independently reviewed, regression. It
excludes both the naive active-low-root choice and every stationary
approximation for one explicit canonical table, while an existing
three-player theorem and a pointwise-safe fourth-player lift give that very
table a uniform payoff. This is evidence against the restricted method,
not against the conjecture. A short-period search was stopped rather than
turned into a sequence of increasingly restrictive no-go projects.

The [compact-region test](../notes/CODEX_HILBERT__TWO_CORE_COMPACT_REGION_ENLARGEMENT_OBSTRUCTION.md)
instead checks the proposed dynamic source directly. A forced root at one
specified continuation leads to a unique strict all-Continue successor.
Thus no fixed compact region containing that continuation is everywhere
serial for positively absorbing support-approximate roots. The
[charge-relative addendum](../notes/CODEX_HILBERT__STRICT_CONTINUE_CHARGE_RELATIVE_REGION_OBSTRUCTION.md)
extends the same obstruction to absorption-weighted ordinary regret and
weighted Bellman approximation. These remain unreviewed ordinary research
notes, not exports. Neither excludes unweighted ordinary-regret schemes,
regions omitting the specified point, accuracy-dependent regions, arbitrary
free-start forward packets, or uniform-equilibrium existence. This fixed-
region enlargement method is stopped at that exact boundary.

The methodological distinction is concrete. The ordered export reaches a
semantic endpoint from a checkable reward-table hypothesis, with no missing
source input. The supportwise export strictly enlarges that proved input
class. Neither supplies an exhaustive classification. The dynamic test
instead diagnoses an extra condition imposed by a method on a game already
known to have equilibrium. Counting those outcomes as interchangeable would
hide precisely the conditional-construction problem the conference is
trying to avoid.

## Raw-source attempts after the supportwise class gate

The current finite-menu question allows approximate menu Nash and unrelated
deadlines and laws at different errors. No positive-bonus parameter or exact
menu equilibrium is required. ROOT reread the question and the literal
`singlePivot_fullExploitability_eq_max_menuExploitability_scalar`
(`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`).
The target is one actual product law simultaneously controlling menu regret
and the pivot's late-deviation scalar. Optional compensation methods must
not narrow that target without saying so.

Three bounded attempts have stopped at exact, separately identified failures:

- [Deadline recutting](../notes/CODEX_TARSKI_PREMIUM__FINITE_MENU_RECUTTING_AND_ACTUAL_VALUE_TEST.md)
  changes a description, not the actual laws. Its explicit canonical table
  has unchanged unrestricted exploitability one half while the displayed
  late factor vanishes and compensation moves into the bonus. The same
  table admits an immediate exact equilibrium. Existing cap-Nash prefix
  contraction changes actual laws but supplies no new absorption producer.
- [Finite-menu minimax exchange](FIN4_SINGLE_PIVOT_RAW_MINIMAX_EXCHANGE__BY_CODEX_FRECHET_CYCLE.md)
  encounters the already known independence boundary. On the canonical H
  table the convexified tester value is zero, but each finite product-menu
  minimum is positive. Their infimum over deadlines is nevertheless zero.
  Thus the exact fixture rejects the fixed-deadline exchange, not the
  conjecture or the asymptotic finite-menu question. No duplicate general
  no-go is exported.
- The [marginal-continuity characterization](../notes/CODEX_NOETHER_SUPPORT__SINGLE_PIVOT_MARGINAL_CONTINUITY_OBSTRUCTION.md)
  and [approximate-security fixture](../notes/CODEX_NOETHER_SUPPORT__CANONICAL_APPROXIMATE_SECURITY_COUNTEREXAMPLE.md)
  close two precise Bich--Laraki theorem applications. With a nonnegative
  own singleton, global cap continuity is equivalent to every terminal
  reward in that coordinate being bounded by that singleton. The weaker
  approximate better-reply security also fails on an exact solved canonical
  table: escaping collisions lift the graph payoff, while a fixed finite
  supported-action loss excludes nearby approximate equilibria. These are
  ordinary mathematical research results, not independently reviewed or
  newly checked Lean. They do not rule out other discontinuous-game methods.

ROOT read those records completely. None provides a new arbitrary-table
selector or a positive-gap table. The next independent tests concern a
strict raw-table enlargement of the active-low-product condition, consumption
of an exit with all four players active under proper-support hypotheses,
and genuinely nonconvex global forward certificates. These are research
tasks, not added assumptions or claimed outgoing atlas theorems.

The external formalizer has moved the polynomial packet to
[formalized/](../formalized/POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md).
Its frozen hash remains
`14191a09b4a42149e0c893666603d85b2e2f1fb3bcd0240af0e0619aaeefc9d6`.
ROOT read the [coverage record](../formalized/POLYNOMIAL_FORWARD_CERTIFICATES_LEAN_COVERAGE.md)
and the literal
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
(`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`).
The negative characterization quantifies over every robust edge in the fixed
reward box enlarged by two, under normality and a positive singleton, and
also excludes a sure-quitter Nash root at the punishment vector. No concrete
polynomial or degree bound is supplied. ROOT did not rerun Lean or modify
external implementation files. Both positive class exports remain unchanged.

## Product-low family: complete strict-extension gate

The direct product question produced a complete positive result rather than
another supplied-source construction. The explicit four-player participant
premiums admit a low active Quit endpoint at every independent product root,
but fail the full-support linear weighting test. All proper-support LPs
pass. Passive rewards are arbitrary, singleton rewards may be zero, and
positive playerwise premium scales are unrestricted. Thus the result gives
a genuine additional reward-table family with uniform equilibrium; it is
not a necessity characterization or an arbitrary-Fin4 proof.

The [final packet](../exports/PRODUCT_LOW_QUITTING_PREMIUMS_STRICT_EXTENSION_UNIFORM_EQUILIBRIUM.md)
was placed byte-identically to the accepted draft at SHA-256
`836eb376e4f26b6b4ee7f865759ab2cf5c99e10ead3bc75e91b24c91ec0475a7`.
Both [FRECHET](DIRECT_LOW_ACTIVE_QUIT_PREMIUM__BY_CODEX_FRECHET_CYCLE.md)
and [NOETHER](DIRECT_LOW_ACTIVE_QUIT_PREMIUM__BY_CODEX_NOETHER_SUPPORT.md)
derived the endpoints, all-support proof, LP contradiction, and consumer
independently before reading the author argument. Each then read the whole
author note and all 315 final draft lines, checked the added boundary test,
and expressly accepted this exact hash with no unresolved mathematical
objection. ROOT read both complete reviews and the draft, reopened the
literal unit consumer and scale/shift declarations, checked relative links,
ran documentation and whitespace checks, and verified the promoted hash
and exact draft equality. No export was edited after placement.

The generic low-active-root mechanism is classical and is explicitly exposed
in the external working Lean sources. The new mathematical content is the
strict product-versus-linear criterion separation and the explicit family
adapter, not a new extraction theorem. The positive correlated LP dual
is not implemented as a strategy. Algebraic testability is in principle
only; the family proof does not require a general quantifier-elimination
implementation. No new Lean build or trust seal is claimed by ROOT.

Two other bounded outcomes remain internal. The
[quadratic restriction](../notes/CODEX_FRECHET_CYCLE__NONPOSITIVE_DIAGONAL_QUADRATIC_ROOT_DRIFT_EXCLUSION.md)
excludes universal drift certificates with nonpositive Hessian diagonals,
including some indefinite quadratics, but constructs neither a negative
table nor a positive general theorem. The
[proper-support stationary test](../notes/CODEX_NOETHER_SUPPORT__PROPER_SUPPORT_FULL_ACTIVITY_STATIONARY_OBSTRUCTION.md)
has a fully active exact root exit and uniformly positive regret for every
fully active stationary repair, while the same table has exact singleton
equilibria. It stops that repair mechanism, not the broader proper-support
existence question. Neither result is exported or counted as another
counterexample-class elimination.

## Raw pair-forcing candidate: exact rejection

ROOT read the complete
[two-pair recruitment test](../notes/CODEX_FRECHET_CYCLE__TWO_PAIR_RECRUITMENT_FORCING_TEST.md),
SHA-256 `d99aabe75fdb67b1040b1ee590c4dcdbb7e84e3dfdc7c6341351ad872a0757e3`.
The proposed rational table destabilizes every pure coalition and fails the
supportwise and direct-product low-premium criteria. Nevertheless the note
constructs an exact stationary equilibrium, with a sure quitter and explicit
Quit-versus-Never comparisons covering all behavioral responses. One target
pair has zero mass there. Consequently this table cannot instantiate the
universal incompatible pair-mass forcing required by the new production
consumer. This is an author-level exact candidate rejection, not an
independently gated theorem, a general impossibility result, or an export.

The independent positive investigations concern a different raw class:
proper-coalition participant rewards at most the unit singleton, positive
grand-coalition premiums, and arbitrary passive rewards. Their initial
capped-table transfer mechanisms have reported precise obstructions on
solved examples. These reports are not class eliminations. The follow-on
question is direct support selection for the uncapped game, including every
inactive player's unrestricted cap; no conclusion is assumed about those
caps, small roots, or continuation of the capped equilibrium correspondence.

ROOT has now read the complete
[collision-exposure test](../notes/CODEX_NOETHER_SUPPORT__GRAND_EXCEPTION_CAPPED_TRANSFER_COLLISION_OBSTRUCTION.md).
It quantifies over arbitrary independent behavioral stopping laws, not
only stationary repairs. The proof uses a two-sample clock-swapping
inequality and the capped game's immediate-Quit and Never incentives.
The raised fixture is explicitly solved by all-Quit. Its conclusion
rejects the proposed source property for a sufficient coarse transfer
estimate; it does not identify that estimate with the actual new regret.
The distinction between the sum of opponent collision masses over dates
and the best mass capturable by one independent response remains explicit.
The note is an author-level completed investigation, not an export gate.

This gives a concrete methodological diagnosis of these failed attempts:
being near equilibrium before a reward change and being insensitive to
that change are two simultaneous requirements. The desired raw-game UE
theorem does not require them. Rejecting their conjunction on a game with
an explicit equilibrium removes the chosen transfer strategy, not part of
the remaining counterexample class. Direct selection in the changed game
must therefore be tested on its own incentives rather than on this extra
conjunction.

The independent
[exact event-response selector test](../notes/CODEX_TARSKI_PREMIUM__GRAND_EVENT_BONUS_CAPPED_SELECTOR_FAILURE.md),
SHA-256 `1aaacf308501b9259a3ebbb0882bbfd75a3baa60afa1f8cbb3b6e416097160f4`,
has also been read completely by ROOT. It uses the supremum over one
player's stopping law, rather than the sum of collision atoms. Two neutral
players' capped-game participation guarantees force a shared finite atom
whose date may diverge. The exact event-gap condition then leaves two
limiting choices, each contradicted by an actual immediate-Quit or Never
response. The proof is retained as author-level ordinary mathematics;
neither ROOT's reading nor the other agent's different fixture constitutes
an independent export review of it. Its table has an explicitly checked
pure-coalition equilibrium in both games.

No further repair of the rejected capped selector is assigned. The positive
tests are now direct support selection for the raw class and the narrower
case where every proper-coalition participant payoff equals the singleton.
These are bounded construction questions, not new assumptions asserted of
all Fin4 tables or claimed exhaustive frontier branches.

## Direct grand-leaver source and stopping point

ROOT read the complete
[grand-leaver proper-support source](../notes/CODEX_FRECHET_CYCLE__GRAND_LEAVER_PROPER_SUPPORT_SOURCE.md),
SHA-256 `23b75678ad1a8d33f496dcf10c5cb99c47d2e6f7ac4dbba55b7743a9d6860aa2`.
Its raw-data alternative fixes a grand leaver before accuracy and applies
the existing capped-game theorem to the literal three-player subgame.
The source is genuinely produced, not an externally assumed equilibrium.
The period may grow with accuracy. Its outsider's complete cap is a finite
phase maximum; the periodic cap theorem is explicitly credited as existing
mathematics. Full-opponent coalition events have favorable signs, leaving
a sufficient upper bound from singleton/pair low-passive events.

There is no theorem choosing these sources so that their exact phase maxima
vanish, and no implication from a positive upper bound to actual regret.
Nor does finiteness at one period bound all periods or serialize a response.
This is retained source localization, not another class closure or export.
The broader support-selection investigation stops at that precise boundary.
The next general investigations concern actual finite-menu value minimizers
and genuinely nonconvex universal-root potentials; they are not constrained
to preserve the additional source choices of the grand-leaver construction.

## External production update inspected at `3c6d97a`

The external formalizer integrated the product-low consumer. ROOT read
`exists_periodic_allSuffix_terminalNash_of_productLowPremium` and
`exists_uniformEquilibriumPayoff_of_productLowPremium`
(`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`),
and checked their production and axiom-audit imports. They retain the
nonnegative-singleton hypothesis, arbitrary finite player type, actual
periodic all-suffix approximants, and one fixed uniform payoff. The proof
uses the sum of positive normalization scales rather than the packet's
maximum; this changes only the internal accuracy allocation. No frozen
export edit is required. This was source inspection, not a new build by ROOT.

The same inspection followed the toolkit to
`finFour_positiveSurvival_capChild_paidRow_source`
(`UniformEquilibrium/Diagnostics/Quitting/PositiveSurvivalCapChildSource.lean`),
`finFour_actualExactPrefix_frontLimit_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/ActualExactPrefixFrontLimit.lean`),
and `quittingNestedCapChild_eventuallyShift_or_negativeHolonomy`
(`UniformEquilibrium/Quitting/Root/SignedCapChildHolonomyDichotomy.lean`).
These retain actual nested profiles, complete responses, and derived
survival/payoff limits under their explicit source hypotheses. The first
requires an initial immediate-Quit cap, exact roots against the actual
source payoffs, and positive survival at every root. The dichotomy also
requires its fixed outsider debt floor. Neither exactness of the limiting
all-Continue root nor a negative displacement consumes that source. The
toolkit explicitly leaves the nonlocal outsider displacement seam
uncontrolled; no UE conclusion is inferred from these source improvements.

## Global-minimizer tests and fixed-response cancellation

The direct
[finite-menu minimizer concatenation test](../notes/CODEX_NOETHER_SUPPORT__SUCCESSIVE_GLOBAL_MINIMIZER_CONCATENATION_TEST.md)
uses actual global minimizers of maximum unrestricted debt, not exact
finite-menu Nash laws. ROOT checked the relevant maximum-debt singleton
margin in `minimumTerminalSemantic_exploitabilitySingletonMargin`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`).
It yields the limiting singleton payoff floors used in that test. The
literal concatenation still has different joint-survival and
opponent-survival multipliers; no decrease or renewable charge follows.
This investigation is retained without an export or a class-closure claim.

The
[potential-guided anchor test](../notes/CODEX_FRECHET_CYCLE__POTENTIAL_GUIDED_ANCHOR_ZERO_CHARGE_TEST.md)
and
[global time-translation triage](GLOBAL_TIME_TRANSLATION_MINIMUM_SOURCE_TRIAGE__BY_CODEX_FRECHET_CYCLE.md)
also stop without a new exclusion. The first can choose only a zero-charge
projected minimum. The second meets the existing rectangular cap-Jensen
excess problem: independently shifted cross profiles need not remain
minimizing. The
[rigid grand-bonus invariant domain](../notes/CODEX_TARSKI_PREMIUM__RIGID_GRAND_BONUS_SUCCESSOR_DOMAIN.md)
is invariant under every exact successor but need not supply any absorbing
successor. These are distinct failed implications, not three eliminated
counterexample classes.

The
[private successor-resampling fixed-weight obstruction](../notes/CODEX_TARSKI_PREMIUM__PRIVATE_SUCCESSOR_RESAMPLING_WEIGHTED_SUM_NO_GO.md)
has passed a genuinely
[independent derivation and assessment](CODEX_TARSKI_PREMIUM__PRIVATE_SUCCESSOR_RESAMPLING_WEIGHTED_SUM_NO_GO__BY_CODEX_NOETHER_SUPPORT.md).
Its actual independent-law fixed point cancels each player's fixed
weighted sum of four response gains for every table. It does not make
each response unprofitable or bound their maximum. The reviewer recommends
internal retention, not export or a further response-menu hierarchy; that
recommendation is adopted.

## Strict product-low family source inspected at `88709a1`

The external integration now includes the explicit family adapter, not
only the generic consumer. ROOT read the complete
`UniformEquilibrium/Quitting/Examples/ProductLowFinFourFamily.lean`, including
`hasProductLowQuittingPremium`, `properSupport_hasSupportwiseCertificateAt`,
`not_supportwiseBalance`, and `exists_uniformEquilibriumPayoff` in its
`GameTheory.ProductLowFinFourFamily` namespace. Positive coordinate scales
give the strict criterion separation; the equilibrium conclusion retains
nonnegative singleton levels and arbitrary passive rewards. This is the
family described in the frozen strict-extension export. Source inspection
is not a new build or trust audit by ROOT, and no export bytes were changed.

## Graceful research pause: retained endpoints

All three active investigations have written their mathematical endpoints
and explicit restart questions. No further line or export gate is assigned.

- [Actual payoff-carrier potential localization](../notes/CODEX_FRECHET_CYCLE__ACTUAL_PAYOFF_CARRIER_POTENTIAL_LOCALIZATION.md)
  proves bounded finite-calendar payoff realization and derives actual
  scalarized incentive conditions. Its final full-replacement and periodic
  word comparisons do not provide the original game's root incentives or
  exclude a universal potential. ROOT read the complete note and final
  comparison; this is not an independent export review.
- [Independent prescribed-outcome realization](../notes/CODEX_TARSKI_PREMIUM__FINITE_CALENDAR_PRESCRIBED_OUTCOME_REALIZATION.md)
  independently derives the twenty-date Fin4 payoff bound and strengthens
  it to a sixty-four-date bound for the full date-forgetting terminal law.
  Caps, semantic minima, and equilibrium are not preserved. This is ordinary
  mathematics, not a Lean result or completed export gate. The author read
  neither the other proof nor its final manuscript before deriving it.
- [Global KKT two-law competitor](../notes/CODEX_NOETHER_SUPPORT__GLOBAL_KKT_TWO_LAW_COMPETITOR_CHECKPOINT.md)
  records exact noninfinitesimal product-law comparisons, including the
  new after-menu response. Lowering the two selected gains leaves the
  remaining complete cap envelope uncontrolled. No positive-gap source or
  timing-bubble branch is eliminated.

The STALL intake remains governed by its completed independent review:
sound nonnegative-table regression, already covered in conjecture-facing
scope by prior all-exact-menu obstructions, and not a new export. The
approximate finite-menu question is unchanged. Documentation and whitespace
checks passed at the pause; the strict product-low export retains its frozen
SHA-256 `836eb376e4f26b6b4ee7f865759ab2cf5c99e10ead3bc75e91b24c91ec0475a7`.
