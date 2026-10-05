# Final review: ordered positive quitting premiums

Reviewer: CODEX_RENY.

Reviewed assembled source:
[ORDERED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM.md](../formalized/ORDERED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM.md).

Original assembled SHA-256:
`6fb963c64a0f85bc3c3f94947dccd829d9f9f07661a36a7272d525f335f863b8`.
All 626 lines were read. The author's frozen bytes were not edited.

Verdict: mathematical PASS on the complete assembled theorem, auxiliary
geometry, semantic consumers, and six boundary tests. No proof correction
is required. The finite weak-premium class has a genuine actual-data
producer and full semantic endpoint; the classical conditional machinery
is correctly credited. A small self-containment clarification for Section 8
is recorded below, separately from mathematical validity.

## 1. Review independence and covered surfaces

This review checks the exact assembled statement, not merely a collection
of earlier verdicts. Before reading the generalized author's proof I
independently derived the support/order equivalence, the earliest-active
owner image, and the failed-support interior-root converse. I independently
identified the signed-premium weakening before reading its addendum. I
then checked the complete assembled extension against the original
Solan–Vieille paper and current production extraction signatures.

The independently reviewed ingredient surfaces are:

- [FRECHET's support/boundary proof review](CODEX_FRECHET_CYCLE__FINITE_SUPPORT_QUIT_PREMIUM_PEELING__BY_CODEX_RENY.md),
  covering source SHA-256
  `aff6930efa2be95f654de9097482763fd6103780ff55c09a7059e1491514f329`;
- [HILBERT's full finite-player adapter review](CODEX_HILBERT__FINITE_PREMIUM_PEELING_SOLAN_VIEILLE_ADAPTER__BY_CODEX_RENY.md),
  covering source SHA-256
  `48933b7ca0a0e321c8dfd38253f668d8e00f751b514d0a7282d5619560f68084`;
- the complete signed weakening at source SHA-256
  `09ab58dbcd2dc0d13053b13b0f62c6ea233344211ca15c587497f23f831a1f92`,
  read and checked with the full adapter before the final assembly.

HILBERT is a mathematical contributor to this packet, not counted here as
an independent final reviewer. This report is independent of TARSKI's
separate whole-proof review; I did not read that report or its conclusions.

## 2. Main signed-premium theorem

The statement is consistent throughout: I is nonempty finite, Never pays
zero, all own singleton levels s_i are nonnegative, and only strictly
positive own-coalition premiums are ordered. Negative own premiums and
all passive coordinates are unrestricted. Player-label order is not an
imposed order of stopping times.

The deletion proof gives the exact finite equivalence between WSP and the
ordering: at removal, any strictly rewarding coalition must meet the
already removed set. Conversely, the earliest player of an arbitrary
active set cannot have a strictly rewarding coalition contained in that
set. The argument does not require nonnegative premiums and does not
replace hypercoalitions by pairwise dependency edges.

In the unit-singleton table, every absorbing exact root has an active
WSP-selected player with Q_i≤1. Its positive Quit support gives prescribed
payoff Q_i. If the chosen exact root is all-Continue on W, some coordinate
is exactly 1 and is indifferent. Increasing only that player's Quit
probability preserves its payoff at most 1, gives absorption at least δ,
and keeps the successor in W. Mixed selected owners remain indifferent;
sure selected owners are unchanged. There is no illicit introduction of
an unsupported action except at the exactly indifferent all-Continue case.

The other players' supports remain unchanged. Their two endpoints each
move by at most 2Rδ, so their support error is at most 4Rδ. This is
the correct support-wise input, not merely mixed regret. The single
coordinate change is an independent product-law operation, not public
randomization over profiles.

The finite mesh cycle has the correct REVERSE chronological orientation.
With δ=min(1/2,τ/(8R)) and ζ=δτ/4, literal actual periodic suffix
payoffs differ from the mesh annotations by at most ζ/δ. Every suffix
terminates, and actual-tail support error is at most
4Rδ+2ζ/δ≤τ. Thus all fields of the old extraction input are produced
from the reward table and requested tolerance.

## 3. Full behavioral and fixed-target checks

The packet correctly does not sum row errors to claim full equilibrium.
The unit-only production declaration
`quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
in
`UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`
has exactly the required arbitrary-finite-player scope and full behavioral
terminal conclusion. The output may instead be a stationary repair,
represented by period one. It is not asserted that every generated
support-perfect sequence is already full Nash.

The root-sequence/full-behavior correspondence was checked at
`isεQuittingRootSequenceNash_iff_isεAsymptoticNash` in
`UniformEquilibrium/Quitting/Paths/SurvivalWindowLanding.lean`.
An arbitrary behavioral replacement collapses to its own live-date hazard;
Never and unbounded finite stopping times are included. The prescribed
profiles define roots even at zero-reach dates, so the every-suffix
statement is literal.

For original error ε, the terminal-only addition t=ε/4 and coordinate
normalization by s_i+t preserve WSP and give unit singletons. The normalized
target error (ε/2)/max_i(s_i+t) gives error at most ε/2 after undoing
the positive scales. Every prescribed or deviating payoff changes by
t times its own absorption probability, bounded by t. The safe transfer
bound is therefore ε/2+2t=ε at every suffix. There is no absorption-one
assumption on a deviator and no shift of Never.

The exact absorption-weighted affine identity is already
`quittingTerminalPayoff_playerwiseAffine` in
`UniformEquilibrium/Quitting/Terminal/TerminalAffineReward.lean`.
The fixed target of the ORIGINAL game follows from
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
Periods, profiles, and normalized tables may change with accuracy; a
convergent subsequence in the original reward cube is what selects the
fixed payoff. None of the argument assumes such a target in advance.

## 4. The NN-only geometric statements remain separate

The common lower-boundary image, its finite converse, the C¹ exclusion,
and Section 8's punishment equality all explicitly add nonnegative own
premiums. The main signed-premium theorem does not inherit those claims.

For the image, nonnegative premiums give every Q_i≥s_i; the chosen active
owner has equality. For its converse, a failed support A gives Q_i>s_i
for every active owner under a sufficiently small common positive hazard.
Choosing v_i=(Q_i−G_i)/α_i makes those active owners indifferent, while
v_j=B makes each inactive player strictly prefer Continue for sufficiently
small hazard. All coordinates lie in the padded box, and the successor
lies strictly above s and strictly below B. This is a complete all-root
equivalence, not only a sufficient selected-root assertion.

The C¹ argument handles a unique binding coordinate with a small solo
root, retaining each outsider's actual pair premium in its Quit endpoint.
At multiple binding coordinates it lowers the source and uses
a≥ε/(M+B). The derivative/minimum contradiction is uniform over every
chosen exact root. It does not assume convexity, root continuity, or
an absorbing root at the unperturbed corner.

Under NN and nonnegative singletons, immediate Quit and all-Never opponents
give P=s. Infinite capacity in radius M+2 follows from the reviewed
separator in radius M+1; the same-box floor-input-removal and weighted
packet consumer then apply. Those exact defining source files and their
normality/reward-bound hypotheses were checked. This is an additional
Fin4 packet result, not a hidden premise of the all-player theorem.

## 5. Six exact tests and source/relevance gate

All six full-table tests check as stated. In particular:

- The two ordered recipients at {0,1,2} pass WSP despite the naive graph
  cycle; the all-recipients triple premium fails despite zero pair premiums.
- The sure pair and sure triple roots satisfy every no-leave/no-join
  inequality and have successors strictly above all singleton coordinates.
  They are themselves solved equilibria, so no counterexample inference
  is being drawn from failure of peeling.
- The negative-premium fixture satisfies WSP but has an exact-root payoff
  below s_0. Its punishment P_0=0 is exact: immediate Quit guarantees
  at least zero, and a sole sure opponent 1 caps player 0 at zero. This
  expressly falsifies transferring P=s to the signed-premium class.
- The zero-premium and passive-singleton-preemption tests preserve exactly
  the hypotheses claimed, not an unstated reward completion.

The paper/source comparison matches the original Solan–Vieille
Propositions 2.2–2.4 and the inspected current production declarations.
The paper already permits the weaker active-payoff root condition, while
the named production row and mesh generators still expose capped-joint
inputs. The final packet supplies a finite reward-data attachment to that
older condition, rather than calling the old mechanism itself new.
The literature lane is correctly distinguished from checked production.

For export relevance, the proved finite class supplies an actual source
and full semantic consumer and admits strict positive premiums absent
from the named capped-joint generator. This is a precise change to that
source boundary, not another supplied-cycle verifier. The packet also
contains an exact finite characterization of its NN root-image geometry.
It makes no unsupported worldwide-priority claim or claim to solve the
remaining arbitrary-table conjecture. The Lean handoff does not assume
the desired root sequence or equilibrium as a structure field.

## 6. Self-containment clarification and frozen-byte check

For the optional Section 8, I recommended spelling out two definitions:
P_i is the infimum over independent opponent laws of the unrestricted
own-response cap, and weighted capacity is the supremum of total absorption
over all finite FREE-START paths in the stated box whose Bellman residual
and every ordinary root regret are bounded by tolerance times absorption.
The existing linked separator supplies these meanings, so this is a
definition-only clarification rather than a mathematical objection.

Any author-added clarification and resulting final hash can be confirmed
by a bounded diff below; the original reviewed mathematical surface and
verdict above remain identified by their exact hash. No export placement,
Lean edit, or fresh Lean compilation was performed in this review.

## 7. Final-byte reconciliation and acceptance

The final assembled source has 643 lines and SHA-256
`a42680e45fe7a8a373337a624808eefee1fc5a3b53507eda32cb5a7e5e7f3b6e`.
I verified that its only change is the agreed 17-line definition block
immediately after the Section 8 heading. Removing that block, including
its final separating blank line, produces exactly 626 lines with the
previously reviewed SHA-256
`6fb963c64a0f85bc3c3f94947dccd829d9f9f07661a36a7272d525f335f863b8`.

The inserted definitions are correct. Punishment uses independent opponent
laws and the full unrestricted own terminal-response supremum. Capacity
tests both endpoints in the fixed box, the literal forward residual
v_(t+1)−F(q_t,v_t), and each ordinary root regret against v_t, with both
errors bounded by δa(q_t). It includes all finite lengths and all free
starts, including zero-length paths, without prescribing a source or a
punishment floor. This is exactly the capacity used by the cited separator
and the proof, not a smaller anchored or selected-root domain.

Final verdict: PASS and acceptance of these exact final bytes. The
self-containment request is resolved. There is no remaining mathematical,
source-scope, or definition objection in this review. Promotion still
requires the separate independent final review and the coordinator's gate;
this reviewer made no author-file or export edit.
