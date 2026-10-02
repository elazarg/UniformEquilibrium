# CODEX_MINER — long-interval proof mining, 2026-08-25

Author: `CODEX_MINER`

Status: `ACTIVE LONG-INTERVAL LOG; LATEST SOURCE-AWARE DUAL CRAWL IN SECTION 20`

This is an owned proof-mining notebook.  It does not assign a Lean, adapter,
or consumer seal to any ordinary argument.  The new monotone-padding proposal
in Section 8 is a proof draft and has not been independently reviewed.

Follow-up on the live Fin4 lane is recorded in Sections 12--13.  The Simon
constrained-root adapter fails for an exact reason, while a newer independently
reviewed singleton-base source has been moved through a narrow export gate.

## 1. Question and corpus boundary

Which mathematically complete and independently reviewed conference results
are not yet represented by a checked Lean declaration, and which of them are
worth sealing even though they do not settle the finite-quitting conjecture?
Can two or more retained notes be combined to strengthen a named interface,
or to expose a sharper obstruction than either note records separately?

The crawl was made at repository commit `d1a404c`.  The worktree was changing
concurrently, so the exact source tree, not a note's status sentence, was used
as the authority for Lean coverage.  In particular, the Fin4 same-source
paid/reset cap-port wrapper was exported and a Lean file was created while
this crawl was in progress.  I did not edit either object.

I read the conference instructions, [`SOURCES.md`](../SOURCES.md),
[`GOAL.md`](../GOAL.md), the export gate in
[`exports/README.md`](../exports/README.md), and the current
[`FRONTIER.md`](../../../docs/FRONTIER.md) and relevant
[`TOOLKIT.md`](../../../docs/TOOLKIT.md) entries.  I made a filename,
headline, and status crawl of all 78 files then present in `notes/`, all files
in `revisit/`, `formalized/`, `exports/`, and `questions/`, and the feedback
stems attached to plausible candidates.  I then read the candidate notes and
their load-bearing reviews in full and ran narrow declaration/phrase searches
in the named Lean subtrees.  I did not read all 402 feedback files linearly;
reviews were routed by candidate stem and status.

This method matters.  For example, the odd interval-blocker note still says
that its interval extension lacks Lean coverage, but the current tree contains
`FiniteOddIntervalBlockerCore.lean` and
`FiniteOddIntervalBlockerCoreRowAdapter.lean`.  Conversely, the Simon note
contains both normalized-motion and near-total-absorption arguments, but only
the latter currently has a production theorem in
`CompactQuantitativeAlternatives.lean`.

## 2. Ranked result

The two cleanest high-priority sealing candidates are:

1. the normalized-motion-to-stationary-prefix compiler in Proposition 44 of
   `CODEX_NOETHER`, which closes one explicitly named Simon quantitative
   producer and has two independent reviews; and
2. the strengthened Solan--Vieille solo-hazard floor
   `E >= 464/14141`, which is strictly stronger than the checked
   `1 <= 14 E^2 + 67 E` / `1/68 < E` result and already has a dedicated
   adversarial review.

The strongest recent API-level candidate is the combination of exact
deleted-player finite-time provenance with the sharp block-deletion cap

```text
P + min(1,A) (C-P)_+.
```

It strictly strengthens the named checked `P+A*C` deletion interface, but it
currently lacks a packet-level importance/consumer decision.  It should not be
mistaken for a chronological producer.

The reviewed hidden-selector packet, the five-player spare-cancellation
verifier, and the Fin4 stationary debt-relay cycle are mathematically sound
reserve results.  Their missing items are producers or active consumers, not
repairs to their stated local mathematics.

## 3. High-priority sealing candidates

### H1. Simon normalized motion produces the stationarily generated branch

**Result.** Proposition 44 in
[`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)
starts with `gamma_k -> 0`, `gamma_k`-rational continuation vectors `r_k`,
rows `p_k in E_(gamma_k)(r_k)`, positive absorption `q_k`, and

```text
||f(r_k,p_k)-r_k|| < gamma_k q_k.
```

Under failure of the instant branch it constructs, for every punishment slack
and equilibrium slack, a stationary prefix of length greater than one followed
by an actual punishment, and proves the resulting profile is an approximate
equilibrium against every unilateral behavioral deviation.  Its largest-
hazard exposure window

```text
L = ceil(1 / (max_i p_i * sqrt(gamma)))
```

removes the apparent need for a lower bound on
`max_i p_i / gamma`.  The pure-time formula and production extremality theorem
cover finite quit times, `Never`, and unrestricted behavioral deviations.

**Independent reviews.** Gauss reconstructed the endpoint algebra, the
selected/nonselected player bounds, the punishment splice, and the inclusive
horizon in
[`ROUND_16`](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_16.md).
Cedar independently found the necessary `gamma_k`-rationality repair and then
passed the corrected statement in
[`ROUND_12`](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_CEDAR__ROUND_12.md).
The repair is incorporated in the source note.

**Novelty/coverage audit.** The production tree now checks the other
quantitative arm:

```text
HasArbitrarilySmallQuittingNearTotalSupportRows
quittingInstantPunishmentεEquilibriumExistence_of_nearTotalSupportRows
```

in
`UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/CompactQuantitativeAlternatives.lean`.
No normalized-motion producer was found in that file or the neighboring
SimonFiniteOrbit subtree.  The current frontier explicitly says that the
near-total branch is checked while the normalized-motion producer remains
open.  The available checked semantic endpoint is
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.

**Source honesty.** This is a rigorous expansion of the mechanism sketched in
Simon (2012), Section 2.3, corrected Lemma 2.1, rather than a theorem-level
novelty claim over that paper.  The project transcription lives in
`Literature/Simon2007.lean`; its relevant producer remains `sorry` and its
notation is not itself the production API.

**Missing gate items.** Extract a focused packet containing Proposition 44,
the two reviews, the precise literature/production mismatch, and a Lean
handoff to a production predicate parallel to the checked near-total one.
The formalizer must write the `E_gamma(r)` / rationality / punishment adapter
instead of appealing to the non-built transcription.  No full Simon lemma,
positive-solo sign theorem, or finite-orbit necessity seal should be claimed.

**Gate follow-through (2026-08-25).** This extraction is now assembled as
[`SIMON_NORMALIZED_MOTION_STATIONARY_PREFIX_PRODUCER.md`](../exports/SIMON_NORMALIZED_MOTION_STATIONARY_PREFIX_PRODUCER.md),
after rechecking that the explicit `gamma_k`-rationality repair and the
`c_j = 1` / Never caveat are present in the live source.  The packet contains
only Proposition 44 and its direct fixed-scale contrapositive; no later Simon
claim was included.

**Rank: high.** This closes a named current producer rather than merely adding
an auxiliary inequality.

### H2. Strengthen the checked Solan--Vieille solo-hazard floor

**Result.** The strengthened export candidate
[`CLAUDE_BANACH__EXPORT_CANDIDATE__SOLAN_VIEILLE_SOLO_HAZARD_FLOOR.md`](CLAUDE_BANACH__EXPORT_CANDIDATE__SOLAN_VIEILLE_SOLO_HAZARD_FLOOR.md)
proves, for every finite or infinite deterministic at-most-one-owner schedule
on `boundaryReward`, against arbitrary unilateral behavioral deviations,

```text
E(schedule) >= 464 / 14141 = 0.0328122...
```

The proof is a discrete rational certificate: a quadratic-over-linear
potential, exact telescoping, and two polynomial inequalities.  The numerical
upper certificates are separate and need not be part of the handoff.

**Independent review.** Hilbert hand-rederived every load-bearing identity,
checked the constants, and ran an independent exact-rational falsification
battery in
[`ROUND_5`](../feedback/CLAUDE_BANACH__SOLO_HAZARD_EXPLOITABILITY_FLOOR__BY_CLAUDE_HILBERT__ROUND_5.md),
with verdict `CONFIRMED — no unresolved objection`.

**Novelty/coverage audit.** The checked files

```text
UniformEquilibrium/Quitting/Examples/
  SolanVieilleBoundarySoloHazardFloor.lean
  SolanVieilleBoundarySoloHazardSemantic.lean
```

prove `explicitFloor_of_errorData`, the semantic explicit-floor wrapper, and

```text
Schedule.one_over_sixtyEight_lt_exploitability
Schedule.one_over_sixtyEight_lt_literal_exploitability.
```

Their quantitative content is `1 <= 14 E^2 + 67 E`, hence `1/68 < E`.
A narrow search found no `464/14141` or `14141` declaration in the Lean tree.
The older disposition in
[`revisit/SOLAN_VIEILLE_SOLO_HAZARD_FLOOR.md`](../revisit/SOLAN_VIEILLE_SOLO_HAZARD_FLOOR.md)
predates this strengthened lower certificate and discusses the already checked
constant plus optional upper certificates.

**Missing gate items.** Reopen only the strengthened lower-bound delta.  The
existing source packet already says that the incremental formalization is one
certificate and two polynomial inequalities.  A whole-packet gate should
confirm that the formalization obligation excludes the large numerical upper
schedule.  This is an architecture-separation theorem, not a counterexample
to the conjecture; the same table has a checked two-owner periodic uniform
equilibrium.

**Rank: high.** The result is complete, reviewed, strictly quantitative, and
small relative to the already checked semantic reduction.

### H3. Exact deleted-player provenance plus the sharp deletion cap

**Result.** The repaired note
[`CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION.md`](CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION.md)
proves that if a proper block-deleted survivor profile is terminal
`epsilon`-Nash with `epsilon < gamma`, while the ambient game has terminal
gap `gamma > 0`, then the ambient witness is a deleted player.  Moreover the
particular behavioral witness's stopping-law mixture contains a **finite
deterministic Quit time with the full weak gain `gamma`**, not merely
`gamma-eta`.  Cardinal minimality supplies such a quiet-lift source for every
nonempty proper deletion block.

The companion audited note
[`CODEX_EULER__OPERATIONAL_ESSENTIALITY_SHARP_DELETION_PASSPORT.md`](CODEX_EULER__OPERATIONAL_ESSENTIALITY_SHARP_DELETION_PASSPORT.md)
then gives, for the selected deleted player `d` and retained set `J`,

```text
P_d(J) = max(0, r_d({d}) - ell_d(J)),
C_d(J) = max(0 and all nonempty insertion toggles),
max(P_d(J), C_d(J)) >= gamma,
```

with a positively reached row realizing the relevant unweighted toggle.  If
retained-row absorption is bounded by `A >= 0`, every behavioral deviation is
bounded by

```text
P_d(J) + min(1,A) * (C_d(J)-P_d(J))_+.
```

**Independent reviews.** Euler's review
[`REVISE -> PASS`](../feedback/CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION__BY_CODEX_EULER.md)
found the full-gap support-atom improvement and audited the sharp cap.  Ramsey
then independently passed the amended exact stopping-law extraction and all
block/minimality quantifiers in
[`PASS`](../feedback/CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION__BY_CODEX_RAMSEY.md).

**Novelty/coverage audit.** The old checked interface in
`UniformEquilibrium/Quitting/Classification/BlockDeletionInequality.lean`
uses

```text
quittingBlockDeletionExcessBound = P + A*C
quittingBestReplyValue_liftDeletedProfile_le_add_excessBound
exists_mem_gap_le_blockDeletionExcessBound.
```

The exact ingredients for the refinement are checked separately:

```text
quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
quittingRootSequencePureTimeTerminalValue_some_sub_none_eq
quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle.
```

No named theorem returning the localized deleted player and a finite time at
the exact gap, and no deletion cap with the positive-part formula, was found.

**Combination opportunity.** The unreviewed Fin4 screen
[`CODEX_CEDAR__FIN4_SHARP_DELETION_PASSPORT_SCREEN.md`](CODEX_CEDAR__FIN4_SHARP_DELETION_PASSPORT_SCREEN.md)
applies the passport to every nonempty proper retained face.  In particular,
singleton deletion improves the checked necessary inequality from
`P+C >= gamma` to `max(P,C) >= gamma`.  Combining the exact provenance,
sharp cap, and this Fin4 corollary would strictly strengthen the named block-
deletion interface in one coherent packet.

**Missing gate items.** The Fin4 application still needs its requested
independent falsification.  A packet then needs an importance decision: the
result is a sharp static API and actual finite-time passport, but it supplies
no Bellman edge, punishment completion, common witness across blocks, or
rank decrease.  If the export policy insists on an active downstream
consumer, formalize the two reusable core lemmas without overstating the Fin4
screen.

**Rank: high for API formalization; medium for immediate export.**

## 4. Medium-priority reserve results

### M1. Hidden-selector information-gap and Boolean-cube packet

The reviewed external note
[`CHATGPT_EXTERNAL__HIDDEN_RESET_VALUE_OF_INFORMATION_PASSPORT.md`](CHATGPT_EXTERNAL__HIDDEN_RESET_VALUE_OF_INFORMATION_PASSPORT.md)
packages four facts not found as named declarations:

1. exact payoff affinity, cap convexity, and
   `debt(hidden) = average debt - information gap` for independent private
   complete-stopping-law selectors;
2. a uniform total-debt Boolean--Möbius remainder
   `O(h^2 lambda)` with edge constant `(4N-2)M` (`14M` in Fin4);
3. a common approximately optimal pure time on the source and every
   positive-weight singleton face under flat tangent balance; and
4. one-bit information-gap localization to a witness-switch rectangle and a
   paid first-disagreement row, plus no-entry observer/debtor alignment.

`CODEX_ROOT` independently passed these claims and their explicit nonclaims in
[`the review`](../feedback/CHATGPT_EXTERNAL__HIDDEN_RESET_VALUE_OF_INFORMATION_PASSPORT__BY_CODEX_ROOT.md).
The checked tree contains the component reset-cube, mixture, tangent, and
paid-row lemmas but no product-selector / Möbius / singleton-star package.

**Missing gate.** The packet's former flat-circulation consumer was removed by
checked support-rank descent.  It does not construct a fixed-gain paid
near-return or a reachable selector context.  It therefore fails the current
importance/adapter gate, not the mathematical-review gate.  The finite
selector identity and Möbius remainder remain plausible medium-priority
library lemmas because they are reusable outside the retired branch.

### M2. Same-profile five-player spare cancellation

[`CHATGPT_EXTERNAL__SAME_PROFILE_SPARE_PLAYER_CANCELLATION.md`](CHATGPT_EXTERNAL__SAME_PROFILE_SPARE_PLAYER_CANCELLATION.md)
is a correct conditional verifier at a source with two sure base quitters,
two free players, and one spare.  Endpoint complementarity makes every
unrestricted behavioral deviation collapse to date zero and gives the exact
debt formulas

```text
d_b(q) = (a_b-q lambda_b)_+,
d_f(q) = 0,
d_s(q) = q kappa.
```

At the common cancellation threshold it either gives exact terminal Nash
when `kappa=0`, or, under the scalar budget and global-minimum hypothesis, a
two-to-one positive-debt-support drop.  It also gives the exact epsilon-Nash
interval.  Cedar and Euler independently passed it, with only source/profile
typing clarifications, in
[`CEDAR`](../feedback/CHATGPT_EXTERNAL__SAME_PROFILE_SPARE_PLAYER_CANCELLATION__BY_CODEX_CEDAR.md)
and
[`EULER`](../feedback/CHATGPT_EXTERNAL__SAME_PROFILE_SPARE_PLAYER_CANCELLATION__BY_CODEX_EULER.md).

A narrow search found no corresponding Lean declaration.  However,
[`CODEX_RAMSEY__FIN4_SPARE_CANCELLATION_PRODUCER_SCREEN.md`](CODEX_RAMSEY__FIN4_SPARE_CANCELLATION_PRODUCER_SCREEN.md)
and the exact rational independence examples in
[`CODEX_EULER__SPARE_CANCELLATION_HYPOTHESIS_INDEPENDENCE.md`](CODEX_EULER__SPARE_CANCELLATION_HYPOTHESIS_INDEPENDENCE.md)
show that current Fin4 pair-base fields produce neither free endpoint
complementarity nor the scalar budget.

**Missing gate.** There is no actual-data producer.  Seal only as a conditional
algebraic verifier if such verifiers are wanted in the reusable API; do not
advertise a five-player existence theorem or a Fin4 consequence.

### M3. Fin4 stationary debt-relay cycle

[`CODEX_RAMSEY__FIN4_STATIONARY_DEBT_RELAY_CYCLE.md`](CODEX_RAMSEY__FIN4_STATIONARY_DEBT_RELAY_CYCLE.md)
uses the checked prescribed-owner stationary handoff for all four owners,
takes the minimum positive repair gain, and extracts a simple cycle of length
two, three, or four in the fixed-point-free owner-to-repaired-debtor map.
Each arrow is co-realized on one actual source/Always-Continue repair pair:
the source has one debtor, the repair gains uniformly and kills it, and the
distinct target label has full-gap debt and a paid row on the same repaired
profile.  Euler independently passed the theorem and its nonchronological
scope in
[`the review`](../feedback/CODEX_RAMSEY__FIN4_STATIONARY_DEBT_RELAY_CYCLE__BY_CODEX_EULER.md).

No named relay-cycle declaration was found.  This is a useful finite wrapper
around
`QuittingTerminalExploitabilityWitness.exists_prescribedOwner_stationaryHandoff`,
but the repaired profile on one arrow is not the independently selected source
on the next.  It has no profile chronology, payoff return, or monotone debt
rank.

**Missing gate.** A source connector or a finite invariant insensitive to
source reselection.  Without one, rank this as a medium/low wrapper rather
than an export that claims a new frontier closure.

## 5. Low-priority reserve and regression candidates

### L1. Exact rational independence tests for spare cancellation

[`CODEX_EULER__SPARE_CANCELLATION_HYPOTHESIS_INDEPENDENCE.md`](CODEX_EULER__SPARE_CANCELLATION_HYPOTHESIS_INDEPENDENCE.md)
contains two bounded rational five-player tables separating the free-endpoint
complementarity hypothesis from the scalar spare-debt budget.  The examples
are useful future Lean regressions because they prevent either producer
hypothesis from being inferred from the other.  They have not received a
dedicated independent review, and they do not advance a live consumer by
themselves.

**Rank: low; retain as regression data pending review.**

### L2. Numerical passive-padding pointwise and infimum API

[`revisit/TERMINAL_EXPLOITABILITY_PASSIVE_PLAYER_PADDING_POINTWISE_INFIMUM.md`](../revisit/TERMINAL_EXPLOITABILITY_PASSIVE_PLAYER_PADDING_POINTWISE_INFIMUM.md)
records the pointwise numerical exploitability inequality and two-sided
infimum comparison omitted from the checked gap packet.  The checked gap and
nonexistence transport already carry the mathematical application, so this is
an optional API refinement rather than missing conjecture evidence.  The
underlying pointwise balancing argument was independently checked in the
[`ARCHIMEDES` review](../feedback/CHATGPT_EXTERNAL__TERMINAL_EXPLOITABILITY_PASSIVE_PADDING__BY_CODEX_ARCHIMEDES.md);
the `revisit/` file is the authoritative scope record for the unimplemented
numerical declarations.

**Rank: low; leave in `revisit/` until a numerical consumer appears.**

### L3. Large Solan--Vieille upper certificates

The exact finite/transient-periodic schedules in the Banach/Hilbert notebooks
give upper bounds down to `889/20000`.  The data are retained in
[`CLAUDE_HILBERT__SV_CERT_04445_DATA.md`](CLAUDE_HILBERT__SV_CERT_04445_DATA.md),
and Banach independently confirmed the certificate and bound in
[`ROUND_11`](../feedback/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS__BY_CLAUDE_BANACH__ROUND_11.md).
They are useful information about the solo-hazard infimum but require a large
data/evaluator formalization and do not sharpen the architecture no-go.  They
should remain separate from H2's compact lower certificate.

**Rank: low for Lean formalization; preserve the data and reviews.**

## 6. Already sealed, concurrently sealed, or deliberately left in revisit

These items should not be re-exported from this crawl.

- Passive-player padding is checked by
  `HasTerminalExploitabilityGap.passivePlayerPadding`,
  `HasTerminalExploitabilityGap.passivePlayerPadding_canonical`, and the two
  nonexistence corollaries in the three
  `UniformEquilibrium/Quitting/Terminal/PassivePlayerPadding*.lean` files.
  The optional pointwise numerical exploitability and infimum comparison are
  honestly isolated in
  [`revisit/TERMINAL_EXPLOITABILITY_PASSIVE_PLAYER_PADDING_POINTWISE_INFIMUM.md`](../revisit/TERMINAL_EXPLOITABILITY_PASSIVE_PLAYER_PADDING_POINTWISE_INFIMUM.md)
  and are unnecessary for gap/nonexistence transport.
- The Fin4 same-source paid/reset cap-port composition entered
  [`exports/FIN4_SAME_SOURCE_PAID_RESET_CAP_PORT.md`](../exports/FIN4_SAME_SOURCE_PAID_RESET_CAP_PORT.md)
  during this crawl, and
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourSameSourcePaidResetCapPort.lean`
  appeared concurrently.  Its content was already checked componentwise; the
  only requested novelty is the named composition wrapper.  Do not create a
  duplicate packet.
- The odd interval-blocker extension is now covered by
  `FiniteOddIntervalBlockerCore.lean` and
  `FiniteOddIntervalBlockerCoreRowAdapter.lean`, notwithstanding the stale
  status sentence in its notebook.
- The signed-influence cycle-balanced no-go is checked in
  `SignedInfluenceCycleBalance.lean`; the participant-only, six-player,
  acyclic-solo, strict-basin, cap-pump, support-rank, paid-cap-port, and Fin4
  handoff packets likewise have named current declarations.  Their notebook
  syntheses are not fresh results.
- The generic reachable-label rank in
  `CODEX_RAMSEY__FINITE_REACHABLE_PAYOFF_LABEL_RANK.md` is mathematically
  correct, but its closing content is subsumed by checked
  `MathUE/FiniteChargedReturn.lean` and
  `MathUE/CompactFiniteChargedReturn.lean`.
## 7. Combination screens which do not close

### Operational deletion plus the stationary relay

Both inputs are exact at one actual source, but not the same kind of source.
The deletion passport starts from a quiet lift of a newly solved proper
survivor game.  A relay source makes its owner Quit surely; its repaired
profile makes that owner play Never but already has another survivor with
debt at least the ambient gap.  Hence deleting the old owner does not leave an
`epsilon < gamma` survivor equilibrium.  Re-solving restores the deletion
hypothesis only by losing the relay's terminal law and paid row.  The
combination yields a static table intersection, not a connector or rank
decrease.

### Passive padding plus the Solan--Vieille solo-hazard floor

The schedule floor is an obstruction only inside the at-most-one-owner
strategy architecture.  `boundaryReward` itself has a checked two-owner
periodic uniform equilibrium and therefore no all-profile terminal gap.
The all-profile hypothesis of passive-padding transport is absent, so the two
theorems cannot be composed to create higher-cardinality counterexamples.

### Canonical passive padding plus spare cancellation

At a source where old players already Quit surely, canonical padding is too
passive to cancel debt.  On every coalition containing an old quitter, old
coordinates ignore the fresh player, and every fresh coordinate is zero.
Thus toggling a canonical fresh player gives

```text
Delta_i^1 = Delta_i^0  for every old i,
lambda_i = 0,
kappa = 0.
```

The spare therefore changes neither old endpoint gap.  This exact negative
screen rules out a tempting direct composition of the two recent packets.

## 8. A stricter combined interface: what the sharp deletion packet would buy

The operational and sharp-cap notes can be packaged as one named interface
without adding a false chronology:

```text
proper survivor epsilon-Nash + ambient gap gamma
  -> selected deleted d
  -> finite deterministic Quit time with gain gamma
  -> positively reached local coalition
  -> max(P_d(J),C_d(J)) >= gamma
  -> BR debt <= P_d(J)+min(1,A)(C_d(J)-P_d(J))_+.
```

This strictly strengthens the checked `BlockDeletionInequality` API in three
ways simultaneously: it retains the actual deleted player, retains an
attaining finite time for the particular witness at the full weak constant,
and avoids double-charging the solo and join alternatives.  The strength is
local and quantitative.  The exact limitation should be a field or theorem
comment: the reached row has positive probability, but neither that
probability nor the probability-weighted toggle is bounded below by `gamma`.

This is the best combination currently ready for a formalizing agent after
the Fin4 delta review, even if no immediate conjecture consumer is found.

## 9. New proof draft: participation-penalized monotone padding

The canonical padding/spare no-go suggests a useful sibling of passive
padding which allows old collision rows to change while still transporting a
terminal gap.

### Proposed theorem

Let `I` and `J` be finite nonempty player sets.  Let old rewards satisfy
coordinate bounds, with `Omega >= 0`,

```text
L_i <= 0 <= H_i,
L_i <= r_i(S) <= H_i,
H_i-L_i <= Omega.
```

For every nonempty old coalition `S` and nonempty fresh coalition `T`, choose
an old-coordinate collision reward `R_i(S,T)` with

```text
r_i(S) <= R_i(S,T) <= r_i(S)+Omega.
```

Define a reward table on `I ⊕ J` by:

- old-only absorption pays `r(S)` to old players;
- simultaneous old/fresh absorption pays `R(S,T)` to old players;
- fresh-only absorption pays `H_i` to old player `i`; and
- fresh player `j` receives `-A` whenever `j` participates in the terminal
  coalition and zero otherwise, where `A>0`.

Then the expected terminal gap should transport exactly as

```text
HasTerminalExploitabilityGap r gamma
  -> HasTerminalExploitabilityGap padded
       (A / (A + card(J)*Omega) * gamma).
```

### Proof

Fix an arbitrary padded behavioral profile and project its actual old live
roots.  Let `x` be the probability that the padded first terminal coalition
contains at least one fresh participant.

For an old player's baseline, couple the padded and projected paths until the
first fresh participation.  On simultaneous old/fresh absorption the padded
reward exceeds the projected old reward by a number in `[0,Omega]`.  On
fresh-only preemption the padded payoff is `H_i`, while the projected eventual
payoff lies in `[L_i,H_i]`; since `L_i<=0`, this difference is again at most
`H_i-L_i<=Omega`, including projected `Never`.  Therefore

```text
U_i(padded) <= U_i(projected) + Omega*x.              (8.1)
```

Lift the old gap-witnessing behavioral deviation while leaving fresh players
unchanged.  A simultaneous old/fresh outcome now pays at least the old reward
for the projected old coalition, and a fresh-only preemption pays the upper
endpoint `H_i`.  Hence the deviating padded payoff is at least its projected
counterpart.  The selected old deviation retains gain at least

```text
gamma-Omega*x.                                       (8.2)
```

For fresh player `j`, changing permanently to `Never` pays zero on every
outcome.  Its baseline is `-A` exactly when it belongs to the first terminal
coalition.  If `x_j` is that participation probability, its exact Never gain
is `A*x_j`, and

```text
sum_j x_j = E[|T_fresh| at terminal] >= x.            (8.3)
```

Some fresh player therefore gains at least `A*x/card(J)`.  Balancing this
against (8.2) gives the displayed factor.  The proof uses the same live-root
projection and arbitrary-deviation lift as passive padding; the new work is
the simultaneous-collision event partition and the broader fresh-player gain
identity.

This is ordinary proof-draft mathematics only.  It needs an independent
review of the infinite stopping-law comparison and a narrow source search
before it can be proposed for export.

### Interaction with spare cancellation

At a two-sure-old-base source, the new `R` rows can program old endpoint
shifts.  For an old coordinate `i`, add one amount on fresh-containing rows
where `i` Quits and another where `i` Continues.  Then

```text
Delta_i^1 = Delta_i^0 + lift_i^Quit-lift_i^Continue.
```

Thus base debt can be pushed upward while equal lifts preserve a free
player's endpoint complementarity.  This is exactly the freedom missing from
canonical padding.

The combination nevertheless does not close:

1. the fresh player's collision premium is `kappa=A`, so cancellation merely
   transfers debt to the fresh coordinate;
2. the fresh payoff at the sure-fresh endpoint is `-A`, while `Never` pays
   zero, so the spare endpoint is not punishment-floor safe;
3. if the old source's only debt lies in the base, its largest base debt is at
   least the old gap `gamma`; whenever cancellation is possible (so
   `Omega>0`), any cancellation threshold satisfies
   `q_* Omega >= gamma`, hence the fresh debt is at least
   `A gamma/Omega`, which is larger than the transported guaranteed gap
   `A gamma/(A+Omega)`; and
4. the current Fin4 pair-base source is not a global minimum of total debt,
   while the spare support-drop arm needs minimum-fiber alignment.

So participation-penalized monotone padding is a plausible reusable
generalization and a way to manufacture collision lifts, but it also exposes
an exact **gap preservation versus floor safety** tradeoff.  A useful next
question is whether a two-coordinate fresh gadget can finance the aggregate
gap while leaving one collision-control coordinate floor safe.  Any such
claim must beat the same aggregate Never-gain accounting rather than hide it.

## 10. Future long-interval crawl protocol

A periodic proof-mining crawl should maintain four separate queues:

1. `reviewed + no checked declaration + named consumer` — packet/export
   candidates;
2. `reviewed + strict API refinement + no consumer` — formalization-library
   candidates;
3. `reviewed conditional verifier + missing producer` — reserve results,
   linked to the exact producer hypothesis; and
4. `subsumed / checked / revisit-only` — explicitly excluded results.

For each candidate, the crawler should record the exact theorem statement,
every independent review, the narrow Lean declaration search, its current
consumer, and one missing gate item.  It should also test pairs of recent
results at their quantifier boundary: actual versus supplied source,
terminal versus uniform payoff, arbitrary behavioral versus stationary
deviations, unweighted row toggle versus probability-weighted gain, and
profile chronology versus independent reselection.

The most important operational lesson from this crawl is that notebook status
sentences become stale quickly.  A future crawl should begin with the current
frontier and exact source declarations, then use notes and reviews to recover
unsealed mathematics.  This prevents both losses: overlooking a reviewed
result which deserves formalization, and re-exporting work already checked
under a newer declaration name.

## 11. Concrete next checks

1. Ask for a packet extraction/gate of Noether Proposition 44 alone, using the
   checked near-total theorem as the target API pattern.
2. Ask the Solan--Vieille packet owner whether to reopen the strengthened
   `464/14141` lower delta while leaving all upper certificates in `revisit/`.
3. Obtain the requested independent falsification of the Fin4 sharp deletion
   screen, then decide whether to export the combined provenance/sharp-cap
   interface or hand it directly to a library formalizer.
4. Independently review Section 9's participation-penalized monotone-padding
   event partition, especially deviation-dependent preemption and the fresh
   `Never` payoff identity.
5. Keep the hidden-selector, spare-cancellation, and relay-cycle results in a
   reserve queue with their exact missing producers, rather than letting them
   disappear inside large notebooks.

## 12. Simon source audit: the full-support roots force fixed-rho failure

The dedicated follow-up is
[`CODEX_MINER__FIN4_SIMON_RESIDUAL_CONNECTION.md`](CODEX_MINER__FIN4_SIMON_RESIDUAL_CONNECTION.md).
Its exact conclusion is negative but conjecture-facing.

Let `p^n` be the constrained stationary roots used to construct the actual
full-support packet, let `mu` be a compact limit of their normalized hazards,
and put

```text
e_i=sum_j mu_j reward({j})_i-reward({i})_i.
```

The packet gives `e_i>=0`; the terminal witness's checked uniform packet
defect gives `max_i e_i>0`.  If `r^n` makes the fully mixed root `p^n`
support-locally `gamma_n`-optimal with `gamma_n->0`, the exact affine endpoint
identity gives

```text
h_i(p^n)-r_i^n -> e_i,
||f(r^n,p^n)-r^n||/q(p^n) -> max_i e_i>0.
```

Thus this actual root family cannot feed the exported Simon small-motion
producer.  Exact endpoint repair makes the tails converge to the own-
singleton vector and hence makes them rational under punishment normality,
but it retains the same nonzero normalized motion.  After formalization of
the Simon contrapositive, these rows land on its fixed-rho failure side.

The zero-collision completion of the checked paired-singleton hard matrix is
an exact residual-compatible boundary test: it has full normal core,
standard `Q`, no homogeneous solution, nonprojective `Q`-bar failure,
punishment normality, uniform full-support packet mass, and singleton surplus
`1/4` in every row.  Its equal-hazard endpoint repair has exact normalized
motion tending to `1/4`.  It lacks the terminal witness because all four
players Quitting surely is an exact equilibrium.  This falsifies the missing
static/source implication without claiming a counterexample game.

This result should remain a reviewed route screen, not an export producer.
Trying to recover a positive surplus floor from the fixed-rho bound would only
reprove a weaker version of the checked uniform packet-defect theorem.

## 13. New high-priority producer found after the initial crawl

The recently completed note
[`CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md`](CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md)
was newer than the initial crawl snapshot.  Its Sections 1--9 passed the
existing `CODEX_RAMSEY` review.  I independently reviewed the singleton-base
source and same-law reset composition in
[`CODEX_MINER`](../feedback/CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT__BY_CODEX_MINER.md).

Corollary 4.3 has the direct arrow missing from the earlier reserve results:

```text
FinFourQuantitativeFullSupportHardResidual + prescribed owner j
  -> collision-selected d != j
  -> actual singleton-base stationary source
  -> debt support exactly {j}, three solved free coordinates
  -> quantitative strict-superset atom and paid row
  -> d has zero debt and unit incidence of j
  -> checked fixed-law reset dispatch on the same pair and law.
```

This has an actual no-uniform-branch adapter and a named downstream semantic
consumer.  A narrow search found no wrapper retaining the unique-debtor,
atom, paid-row, collision-selected reset owner, and complete-law fields
together.  I therefore assembled the focused packet
[`FIN4_SINGLETON_BASE_SAME_LAW_RESET_PRODUCER.md`](../exports/FIN4_SINGLETON_BASE_SAME_LAW_RESET_PRODUCER.md).

The packet deliberately excludes the source note's later unreviewed Section
10.  Its remaining conjecture obstruction is explicit: the fixed-law reset
dispatcher may return the all-Continue cap-face arm.  No payoff near-return,
iterable rank descent, uniform payoff, or full Fin4 theorem is claimed.

## 14. All-Continue arm screen and source-changing pivot

The dedicated follow-up is
[`CODEX_MINER__FIN4_SINGLETON_BASE_ALLCONTINUE_RESET_WALL.md`](CODEX_MINER__FIN4_SINGLETON_BASE_ALLCONTINUE_RESET_WALL.md).
It gives a literal four-player singleton-base regression, obtained by
canonical passive padding of the checked Boolean cap regression.  One actual
stationary profile has unique debtor `j`, three unrestrictedly solved and
floor-safe free coordinates, a unit paid first-disagreement row, a unit-mass
strict-superset atom, a distinct unit-gap collider/reset owner `d`, and unit
same-law incidence.  Its pair and law themselves satisfy every field of
`QuittingFixedLawResetDispatch`, but the unique exact cap root is
all-Continue.

The regression has a terminal equilibrium and therefore intentionally lacks
the hard residual and positive-global-minimum hypothesis.  It proves that the
ambient witness/minimum must enter through a genuinely new implication;
source/law/atom alignment alone is exhausted.  The checked reset-face,
strict-basin, surcharge, endpoint, and solo-wall declarations do not add that
implication.

The direct Fin4 pivot is the strict-solo conditional-suffix source in Euler
Section 10: after the independent review's mandatory witness-localization
repair it yields an exact carrier edge with debt drop
`Gamma^2/(12M)`.  The source note now incorporates that repair: the gap is
localized to `e` on the actual conditional suffixes only after all three
retained debts become smaller than `Gamma`.  Its remaining seams were
punishment-floor safety of the selected debtor and graft/iteration while
preserving the other three zero-debt coordinates; Section 15 consumes the
floor/iteration seam to the constrained plateau boundary.

## 15. Strict-solo regeneration reaches a constrained plateau

The follow-up
[`CODEX_MINER__FIN4_STRICT_SOLO_REGENERATION_PLATEAU_BOUNDARY.md`](CODEX_MINER__FIN4_STRICT_SOLO_REGENERATION_PLATEAU_BOUNDARY.md)
starts only after independently rechecking the mandatory Section 10
witness-localization repair.  The corrected strict-solo source and the
independently reviewed floor-deficit recursion prove nonemptiness of the
compact invariant face

```text
K_e = {floor-safe carrier pairs with d_i=0 for i!=e}.
```

It then makes a same-table compact selection minimizing total debt on this
whole face; no exact-prefix reachability from the original source to that
minimizer is asserted.  The terminal witness gives `D=d_e>=Gamma` everywhere
on the face.  At a
`K_e`-minimum every exact prefix remains in `K_e`, while the checked
unique-debtor contraction would strictly lower debt if any opponent of `e`
absorbed.  Hence every exact root has zero opponent absorption.  Adaptive
solo recycling then either has nonsummable charge, which the checked floor
orbit compiler turns into a uniform payoff, or converges to a floor-safe
`K_e`-minimum at which all Continue is exact.  This is a real extremal
regeneration theorem; it does not mistake a Zeno-capable strict real decrease
for a finite rank.

At the resulting plateau an asymptotic same-profile best-response reset of
`e` kills its debt, raises its payoff to the old envelope, gives it at least
`Gamma` of punishment-floor slack, and--by the terminal witness--forces one
fixed `f!=e` to carry debt at least `Gamma` on a subsequence.  The bounded
Fin4 audit finds no checked continuation beyond that point: the other two
debts and all target floors are uncontrolled, global-minimum transfer
identities do not decrease total debt or support, and best-response resets
are not chronological prefixes.  The local padded regression shows only that
reset algebra alone supplies none of those fields; it does not refute a
stronger implication using the complete hard residual.  The exact remaining
wall is a constrained-minimum unique-debtor all-Continue plateau plus a
non-rank debtor-label relay.

## 16. Selective paid-stall crawl and a finite semantic-pair return

The resumed crawl began from the checked/reviewed paid cap-port inert
trichotomy and the Section 15 unique-debtor constrained plateau. The narrow
duplicate and no-go audit covered:

- `PAID_CAP_PORT_EXACT_TRICHOTOMY_AND_INERT_STALL`;
- Ramsey's reviewed law-enriched paid cap-port/reset dichotomy and
  same-source surcharge-recycling boundary;
- the reviewed linear all-Continue absorption-defect theorem, including its
  already stated uniform tube over the complete minimum debt-segment bundle;
- `FLAT_CIRCULATION_SUPPORT_RANK_ELIMINATION` and
  `FIN4_OFF_MINIMUM_CHARGED_BLOCKER_GATE`;
- the reviewed finite reachable payoff-label rank; and
- Proposition 66 of `CODEX_CEDAR__PAID_ROW_REENTRY` and its independent
  review.

### Exact failed combination at the inert boundary

The natural global-minimum combination is already present in Ramsey's linear
defect note: the whole compact bundle

```text
{X.B-t(X.B-X.U) : X is a global minimum, 0<=t<=1}
```

lies in one unique-all-Continue/linear-defect tube. Thus nontrivial cap
motion must remain a fixed debt distance off the minimum fiber. This does
not eliminate an inert paid source: all-Continue prefixing fixes its semantic
pair and preserves the outward-shifted paid row exactly, while the original
stationary source is not asserted to be a global minimum.

The newest normalized finite-cut calculation also stops exactly at zero cap
displacement. A positive signed terminal-label mass gives an actual finite
prefix with strict debt descent while preserving normalized paid density,
but its mass floor depends on the source's port displacement. In the inert
arm both displacement and label mass are zero. Neither the Fin4 same-law
incidence nor the terminal-gap atom supplies a uniform positive port
displacement: the checked all-Continue reset regression realizes the
underlying static fields with zero charge, though it is not a full-hard-
residual counterexample.

The strongest honest failed implication is therefore

```text
full-gap normalized paid mark
+ Fin4 unique debt / same law / positive incidence / heavy terminal atom
+ terminal witness and positive global minimum
  -> positive cap displacement or a recursively preserved finite rank.   (16.1)
```

No current declaration proves `(16.1)`. The regressions show that its local
cap/reset algebra is insufficient; they do not universally refute an as-yet
unknown implication using the complete hard residual. The off-minimum
charged-blocker gate cannot help at zero charge, and the flat-circulation
support rank applies only to a global-minimum tangent endpoint, not to the
off-minimum paid source or a best-response reset.

### Duplicate screen: deterministic recurrence was already checked

Proposition 66 was at real risk of being forgotten inside the very large
paid-row notebook. It is independently reviewed and a narrow search found no
checked Lean statement: a terminal gap gives a bounded deterministic
pure-time unilateral-update loop with exact prescribed-payoff return, fixed
gain on every update, and arbitrarily small post-update debtor debt.

The dedicated follow-up
[`CODEX_MINER__TERMINAL_GAP_DETERMINISTIC_SEMANTIC_PAIR_RETURN.md`](CODEX_MINER__TERMINAL_GAP_DETERMINISTIC_SEMANTIC_PAIR_RETURN.md)
initially appeared to strengthen it. Against deterministic pure-time opponents, player
`i`'s unrestricted behavioral cap is the maximum of at most three terminal
reward values, indexed only by the opponents' first quitting coalition and
whether its first date is zero.
Consequently deterministic profiles realize at most
`2^(|I|*(|I|+1))` complete
terminal-semantic pairs. The same update recursion and pigeonhole argument
therefore produce an exact return of **both** `U` and `B`, hence of the whole
debt vector, while retaining the reviewed per-update gain and small updater
debt.

The broader toggle-language search then found strict subsumption by checked
declarations. Starting from all Never, exact best replies can remain in the
two-point class `{Quit at date zero, Never}`. This is the checked strict-toggle
closed orbit. Since a pure row gives each mover only its two membership
actions, every strict selected toggle already attains the mover's pure-row
unrestricted cap and leaves its debt zero. Coalition recurrence therefore
returns the literal profile, law, `U`, `B`, and debt vector. The reviewed
Section 70 cap formula states exactly this local fact.

Accordingly neither Proposition 66 nor the apparent semantic-pair refinement
should be exported or separately formalized. Their useful lesson is the
already-known boundary: a static unilateral-update recurrence, even with
exact profile return and zero mover debt, is not a root-then-continuation
chronology. The exact remaining arrow is a connector/Nashification theorem,
not a stronger recurrence or another finite label count.

### Notes at risk of being lost

1. Proposition 66 and its exact-return addendum are buried near Section 66 of
   a notebook exceeding nine thousand lines, but the duplicate audit shows
   they should be indexed as consequences of the checked strict-toggle orbit,
   not sent for separate formalization.
2. `CODEX_RAMSEY__LAW_ENRICHED_PAID_CAP_PORT_RESET_DICHOTOMY` is independently
   reviewed and proves a genuine joint semantic/law limit with retained
   incidence, debt ray, heavy atom, and reset reapplication. Its reviewer
   correctly recommends keeping it internal because its exact output is
   still strict real debt descent or the same all-Continue stall;
   nevertheless the joint-law compactness lemma should not disappear inside
   the paid-port discussion.
3. The new normalized paid finite-cut lemma is locally strong but still under
   review. It should be retained as a conditional quantitative tool, not
   advertised as well-founded closure until a source-uniform label-mass floor
   or an attained compact marked minimum is produced.

## 17. Minimal deletion passports versus the singleton double-inert laws

The conjecture-facing synthesis is recorded separately in
[`CODEX_MINER__FIN4_MINIMAL_PASSPORT_DOUBLE_INERT_LAW_BRIDGE.md`](CODEX_MINER__FIN4_MINIMAL_PASSPORT_DOUBLE_INERT_LAW_BRIDGE.md).
Two items should not be lost in later broad crawls.

First, the checked original singleton-base law and its literal owner-Continue
repair have an exact affine relationship. If `a` is the one-stage free
absorption probability and `e` is the sure singleton owner, then

```text
mu_source = (1-a) delta_{e} + a (A |-> A union {e})_* mu_repaired.
```

This gives mutually singular support but complete quantitative coupling. The
source owner debt and exact repair-cap identity then yield a repaired-law atom
of mass at least `Gamma/(28M)` carrying a half-gap solo-or-leave comparison.
This ordinary-mathematics result is new, source matched, and worth independent
review/formalization even though it is not a Bellman edge.

Second, a rational four-player table co-realizes all four exact operational
codimension-one deletion passports with a floor-safe pair-base source whose
cap game has unique all-Continue root. It escapes precisely through exact
date-zero singleton equilibria, hence `D_*=0`. Thus the broad implication
from independently selected passports plus local inert source fields is
false; the positive global minimum/terminal witness must enter through a
profile or law connector. The repaired restriction does not supply that
connector: a checked free observer retains debt at least `Gamma` in the
owner-deleted game.

The exact retained alternatives are regeneration of paid/reset/profile
provenance at a quantitative cap-descent limit, or a continuation theorem
linking the affinely coupled repaired stationary law to an independently
selected equilibrium of the owner-deleted three-player game.

## 18. Shared AGKRS all-Continue phantom: bounded consumer audit

Current source audit: `QuittingLowSurvivalAllContinuePhantom`,
`QuittingLowSurvivalPositiveRhoAllContinueSourceResidual`, and
`QuittingSupportBellmanPositiveSingletonDefectResidual` in
`PositiveRhoLandingCompactLimit.lean` and
`PositiveRhoLandingClassificationBoundary.lean`; the current
`PositiveJointSummablePortPhantomReduction.lean`; the prioritized exclusions
in `PrioritizedRefinedSourceBoundary.lean`; and the acyclic escape in
`AcyclicSoloPreemption.lean`.  Narrow searches also checked the no-harm
singleton compiler and the preemption-cycle/transport files.  No declaration
consumes the common phantom after a directed preemption cycle appears.

The exact information common to the two source lanes is weaker than an
executable equilibrium:

```text
x != 0,  P_i <= x_i,  r_i({i}) <= x_i for every i,
and r_p({p}) > 0 for some p,
```

together with an actual positive-singleton suffix defect.  The positive-joint
zero-charge specialization additionally retains a diagonal punishment
endpoint `E` and one punished coordinate `E_o=P_o`; its canonical port is
literally constant.  The ballistic signed-label theorem cannot be used in
this arm: zero charge implies zero displacement and supplies no signed mass.
In the displaced positive-charge arm, the signed label and singleton defect
do co-realize on the same port, but the label's player/coalition/sign is not
identified with the positive-singleton owner.

Two tempting implications fail at the available interface.

1. A positive singleton is punishment-normal, because
   `quittingPunishmentValue_le_max_solo` gives
   `P_p <= max(r_p({p}),0)=r_p({p})`.  It does **not** give the outsider
   no-harm inequalities required by
   `quittingStationarilyGeneratedApproximateEquilibria_of_normal_noHarmSingleton`.
2. If the augmented solo-preemption graph were acyclic, the checked sink
   theorem would in fact give S.1.  Therefore global failure of S.1 forces a
   directed augmented cycle.  This is only a necessary combinatorial
   obstruction: the current preemption-cycle files explicitly retain
   uncontrolled observer-switch/collision terms and provide no S.2/S.3
   compiler or decreasing source rank.  Recording the cycle as another arm
   would merely rename the residual and is not a conjecture-facing advance.

There is a valid but presently nonclosing regeneration observation.  If an
all-Continue phantom target `x` is approached by unrestricted terminal Nash
profiles and some coordinate is punishment-tight, `x_o=P_o`, then inserting
any finite literal all-Continue prefix before sufficiently accurate members
of that same sequence preserves approximate Nash: a prefix deviation is a
mixture of the own singleton payoff (bounded by `x_i`) and a tail deviation.
For player `o`, the selected tail is also a small punishment because its
best-response value approaches `P_o`.  Hence the tight subcase is
stationarily generated.  This does not prove S.1/S.2/S.3, and in the
positive-joint lane it regenerates the source class already being analyzed;
it is not a well-founded descent.  I therefore do not promote it as another
residual theorem.

The strongest exact remaining implication is:

```text
same reached endpoint/port
+ positive singleton suffix defect
+ (in the charged arm) source-native ballistic signed terminal mass
+ global failure of S.1, S.2, and S.3
  -> a no-harm owner, a sure-exit/punished first row,
     a support-perfect absorbing chronology, or a finite terminating rank.
```

No checked or reviewed note supplies the missing label alignment or
chronological return.  The zero-charge arm sharply shows why the ballistic
data cannot be assumed, while the cyclic preemption boundary shows why
singleton positivity alone cannot select a no-harm owner.  This bounded pass
therefore stops without adding a residual split.

## 19. Quantile hierarchy and causal-atom dual crawl

This bounded crawl selected only three plausible connections after narrow
duplicate searches in the named terminal-semantic, occupation-flow, and
chronological subtrees.

### 19.1 Promotion completed: the quantile hierarchy has both existing semantic consumers

The hierarchy passed a second independent unrestricted-strategy and
whole-packet review and is now
[`formalized/ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md`](../formalized/ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md).
It is no longer starved.  No duplicate packet or procedural re-export is
needed.

The named compiler bridge is exact and should be retained in any export or
formalization handoff.

* If an exact real-algebraic certificate proves `0<gamma<=L_M`, every carrier
  point lies in `R_M` and has maximum semantic debt at least `gamma`.  Carrier
  debts are coordinatewise nonnegative, so total semantic debt is also at
  least `gamma`.  The checked equivalence

  ```text
  TerminalSemanticGlobalDebtBarrierCertificate.
    nonempty_certificate_iff_globalDebtFloor
  ```

  therefore supplies an inductive barrier certificate (using the carrier
  itself as the semantic barrier), and the checked
  `not_exists_uniformEquilibriumPayoff_of_certificate` consumes it.  The
  finite CAD/RCF trace remains the effective proof object; the carrier barrier
  is only the already checked semantic consumer and is not misdescribed as a
  finite semialgebraic invariant.
* If `eta(r)=0`, the hierarchy's actual finite-clock minimizers satisfy
  `U_M<=2n(n-1)/M`.  Choosing `M` after each requested positive error gives
  literal unrestricted terminal approximate-Nash profiles at all errors.
  The checked
  `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  consumes them directly.  This is conditional on the zero branch and does
  not make equality to zero finitely decidable.

Thus the hierarchy is not a local verifier: the positive finite certificate
and zero-gap sequence each have an existing semantic endpoint.  What remains
open is a terminating branch decision or a proof that the maintained Fin4
hard residual lies in the zero branch.

### 19.2 New sharp boundary: prescribed-defect occupation is not one gain

Euler's causal-suffix aggregate lemma gives, in one arm, a fixed lower bound
on

```text
sum_t liveMass(t) * prescribedTailLocalNashDefect(t).
```

The generic occupation and flow/co-state libraries do not consume that sum
into one deviation.  The obstacle is not missing finite-dimensional
separation: it is causal stopping compatibility.  The exact rational
regression is now recorded in Section 3 of
[`CODEX_MINER__QUANTILE_CLOCK_LINEAR_SUPPORT_LOWER_BOUND.md`](CODEX_MINER__QUANTILE_CLOCK_LINEAR_SUPPORT_LOWER_BOUND.md).

On the same Fin4 table, let `c` be uniform on `n` finite dates and let `a`
Never.  At each reached date `t`, player `a`'s prescribed-tail local defect is
the conditional atom `1/(n-t)`, while live mass is `(n-t)/n`.  Hence every
one-row best-endpoint deviation gains `1/n` and the occupation sum is exactly
one.  But an arbitrary behavioral replacement of `a` earns only the
probability that its independent stopping time ties the uniform clock, at
most `1/n`.  The full behavioral cap attains exactly `1/n`.

The cap-tail semantic defect account diagnoses the mismatch exactly: all
earlier cap-tail defects are zero because the continuation envelope already
prices the same future tie option, and only the last row contributes.  Its
occupation sum is `1/n`, in agreement with actual debt.  Therefore no
horizon-independent positive constant can turn the prescribed-defect sum
alone into one behavioral gain.  A sound dual must retain causal stopping-law
weights, or switch to cap-tail defects and lose the macroscopic lower budget.

This does not refute a new implication using the complete Fin4 hard residual;
the regression has global minimum zero.  It does decisively remove the
source-free Farkas/occupation conversion suggested by the aggregate branch.
It is under independent review as an internal no-go, not an export packet.

### 19.3 Duplicate and incompatible-field screens

The following two candidates do not merit promotion.

1. [`CLAUDE_ERDOS__EVERY_SUFFIX_FORCING_COLLAPSE.md`](CLAUDE_ERDOS__EVERY_SUFFIX_FORCING_COLLAPSE.md)
   correctly observes at proof-draft level that actual root sequences with
   arbitrarily small initial semantic debt already enter the checked terminal
   all-errors consumer, without survival.  Applied to the quantile zero branch
   this is exactly the preceding checked compiler bridge, not a stronger
   chronology.  Its literal chronological-certificate equivalence still
   requires survival-vanishing roots and produces none from causal atoms.
2. `FlowCostateDuality.lean`,
   `FlowCostateObstructionAdapter.lean`, and the product-root gluing-minor
   result were checked against both live candidates.  The flow/co-state
   adapter explicitly supplies no strategic feasible set or decoder, while
   the gluing theorem requires already compatible conserved stage fluxes.
   The causal-atom window is already one literal product chronology, so
   probability-row gluing adds no missing semantic annotation.  The quantile
   hierarchy already retains exact marginal simplexes and product monomials,
   so relaxing them to a flow would only weaken provenance.  Neither result
   supplies the missing causal policy or strengthens the finite hierarchy.

The inspected checked files were
`TerminalSemanticPlateauDefectTelescope.lean`,
`TerminalSemanticPlateauLocalizedOtherDefect.lean`,
`TerminalSemanticReachedRowDebtLocalization.lean`,
`TerminalSemanticCausalQuitAggregation.lean`,
`TerminalSemanticCausalQuitAggregationNoGo.lean`,
`MathUE/LinearProgramming/FlowCostateDuality.lean`,
`MathUE/Probability/OccupationFlowAlternative.lean`, and
`Quitting/AbsorptionPath/FlowCostateObstructionAdapter.lean`.

Current ranking from this pass is therefore: quantile hierarchy **promoted**;
prescribed-versus-cap aggregate regression **medium as a
formalization/no-go regression after review**; all other tested combinations
**low/duplicate or missing a strategic decoder**.

## 20. Source-aware dual and global-barrier continuation

This continuation began after the hierarchy passed its second review.  The
search was deliberately restricted to checked source-aware identities and
named semantic consumers.  The files inspected were:

- `TerminalSemanticPlateauDynamicCostate.lean`;
- `TerminalSemanticPlateauMaxDebtConsumer.lean`;
- `TerminalSemanticPlateauMaxDebtFlow.lean`;
- `TerminalSemanticMinimumSpine.lean` and
  `TerminalSemanticMinimumSpineFlow.lean`;
- `TerminalSemanticGlobalDebtBarrierCertificate.lean`;
- `TerminalSemanticCausalQuitAggregation.lean` and its checked no-go;
- `FlowCostateDuality.lean`, `OccupationFlowAlternative.lean`, and
  `FlowCostateObstructionAdapter.lean`; and
- the recent causal-atom and quantile notes named in Section 19.

### 20.1 The positive quantile certificate already has a checked global barrier consumer

Suppose a finite hierarchy certificate proves `0<gamma<=L_M`.  Every carrier
point lies in `R_M`, so its maximum nonnegative semantic debt is at least
`gamma`; consequently its total semantic debt is at least `gamma`.  The
checked equivalence

```text
TerminalSemanticGlobalDebtBarrierCertificate.
  nonempty_certificate_iff_globalDebtFloor
```

then produces an inductive barrier certificate, and
`not_exists_uniformEquilibriumPayoff_of_certificate` consumes it.  This is a
genuine all-root prefix-invariant semantic consumer.  Its witness in the
reverse direction is the whole carrier, however, not a finite semialgebraic
barrier extracted from the RCF trace.  Thus it adds source-aware semantics but
no stronger effective certificate than the hierarchy's direct
`gamma<=Expl(sigma)` conclusion.  It should be cited in formalization, not
presented as a second export result.

There is nevertheless a useful robust adapter, now stated and proved in
[`CODEX_MINER__QUANTILE_OUTER_PREFIX_HULL_BARRIER.md`](CODEX_MINER__QUANTILE_OUTER_PREFIX_HULL_BARRIER.md).
Every `z in R_M` lies within `delta_M` of its actual current-scale center.
The checked semantic prefix map is nonexpansive, so the same distance bound
survives every common finite root word.  Closing `R_M` under arbitrary
prefixes therefore preserves total debt at least

\[
 \gamma-2n\delta_M,
\]

which is `gamma-96/M` for Fin4.  If positive, this prefix hull itself supplies
the three fields of the checked barrier certificate.  The hull has unbounded
word length and is not claimed semialgebraic; the finite evidence remains the
original RCF certificate.  This is a formalization addendum under independent
review, not a second export.

### 20.2 Exact source-aware collision/costate corollary

There is one clean composition with the causal collision producer.  Let
`reference>=0`, let an actual profile `sigma` have every shifted semantic tail
through a finite cutoff `N` in the maximum-debt tube

\[
 \operatorname{Expl}(\operatorname{Spine}(\sigma,t))
 \le reference+\varepsilon\qquad(0\le t\le N),       \tag{20.1}
\]

and suppose every carrier point has exploitability at least `reference`.  Fix
a coalition `S` of cardinality at least two.  The checked theorem
`exists_maxDebtSelector_reference_mul_sum_opponentAbsorptionMass_le` gives a
debt-maximizing owner `o_t` at each actual row and

\[
 reference\sum_{t<N}L_t\,A_{-o_t}(q_t)
 \le \varepsilon+2\sum_{t<N}L_t\delta_{t,o_t}.       \tag{20.2}
\]

For every `t`, `S` contains a player different from `o_t`.  The checked
coalition/opponent-incidence inequality therefore gives

\[
 a_t^S\le L_tA_{-o_t}(q_t).                          \tag{20.3}
\]

Since `reference>=0`, summing (20.3) and using (20.2) proves the entirely
source-matched corollary

\[
 \boxed{
 reference\sum_{t<N}a_t^S
 \le \varepsilon+2\sum_{t<N}L_t\delta_{t,o_t}.}      \tag{20.4}
\]

In particular, if the coalition occupies mass at least `s` in the window,

\[
 \sum_{t<N}L_t\delta_{t,o_t}
 \ge {reference\,s-\varepsilon\over2}.               \tag{20.5}
\]

This is stronger in label provenance than the unweighted total-defect
account: every defect is charged on the maximum-debt coordinate selected from
the same literal tail and root.  It is nevertheless a direct corollary of
checked declarations, not an export candidate by itself.

### 20.3 Why the corollary does not upgrade the causal atom

The finite-atom/deep-causal source gives a near-minimum semantic pair at the
head and a macroscopic literal suffix coalition.  It does **not** supply
(20.1) for every intermediate shifted tail.  The checked causal collision
dispatch already records the exact alternative: either a shifted tail exits
the minimum tube, or a positive local endpoint defect is exposed.  Thus
applying (20.4) does not remove the tail-excursion arm; it only refines the
labels in the defect arm.

Even under the additional tube hypothesis, the right side of (20.4) is not
one player's behavioral gain.  Section 3 of
[`CODEX_MINER__QUANTILE_CLOCK_LINEAR_SUPPORT_LOWER_BOUND.md`](CODEX_MINER__QUANTILE_CLOCK_LINEAR_SUPPORT_LOWER_BOUND.md)
gives an exact rational finite-clock family in which the original-reach sum
of nonnegative prescribed-tail row defects is one while every complete
behavioral replacement gains at most `1/n`.  The cap-tail account collapses
to `1/n`, exactly because it prices the mutually exclusive future stopping
opportunities only once.  Dynamic selection of debt labels cannot repair
this causal duplication without a signed stopping-policy decoder.

The checked source-aware causal identity
`quittingFiniteHazardValue_sub_eq_causalQuitGain` confirms the required data:
a simultaneous Continue-to-Quit modification is a survival-weighted sum of
**signed** row advantages.  It does not lower-bound that gain by the sum of
positive prescribed defects.  `TerminalSemanticCausalQuitAggregationNoGo`
gives a complementary stationary signed-cancellation regression.

### 20.4 Exact-minimum and abstract-flow routes also stop sharply

One might avoid the suffix tube by moving to the checked exact minimum
semantic spine.  This does give a state-matched infinite prefix chronology,
but it conserves every debt coordinate.  Consequently

```text
not_nonempty_maxDebtMatchedFlow_chronological_of_conserved
```

proves that no positive reset/incidence matched flow can be obtained by
reading transfer from consecutive minimum-spine states.  This is a theorem,
not merely missing implementation.

Conversely, `QuittingFiniteMaxDebtMatchedFlow` and
`exists_pure_maxDebt_matched_path` provide an abstract positive label
skeleton, while
`QuittingFiniteMaxDebtMatchedCut.exists_maxDebtSource_vertex_or_weightedMinimumSurplus`
gives a useful game-facing consequence from a supplied strict Hall cut.
Neither side currently has the producer needed here:

- the matched flow lacks co-realized consecutive semantic-state provenance;
- no checked max-flow/min-cut result manufactures the strict cut from failure
  of the strategic flow; and
- the whole-carrier global barrier carries no chronological incidence or
  marked coalition coordinate.

`FlowCostateObstructionAdapter` is honest about the same boundary: it embeds
one literal finite window and proves exact survival-adjoint pairing, but
supplies neither a strategic feasible set nor a decoder for a separating
costate.

### 20.5 Disposition and starvation check

No new export-qualified composition results.  The hierarchy itself is now
properly promoted.  The productive certificate-or-all-errors note was
independently checked in
[`feedback/CODEX_EULER__QUANTILE_CLOCK_PRODUCTIVE_CERTIFICATE_OR_ALL_ERRORS_FORK__BY_CODEX_MINER.md`](../feedback/CODEX_EULER__QUANTILE_CLOCK_PRODUCTIVE_CERTIFICATE_OR_ALL_ERRORS_FORK__BY_CODEX_MINER.md):
its online fork is correct but is a thin procedural corollary of the export,
not a second packet or a terminating zero test.

The only current item at risk of starvation is the exact
prescribed-defect/cap-defect regression in Section 3 of the support-lower-bound
note.  It is useful as a formalization test if independently reviewed, but it
does not meet the export gate because it has no positive residual consumer.
The shortest still-unconsumed source-aware object is therefore precisely the
right side of (20.4): a dynamically label-matched occupation sum of local
defects on one actual chronology.  Closing it requires a signed causal policy
or a source-native return/rank theorem, not another finite separator.

## 21. Grok fallout: retained-hazard partial Nashification

The failed Grok inert-rectangle capstone leaves one valid, source-matched
input: after conditioning at its positive rectangle row, an observer Quits
surely and a distinct mover retains positive Quit hazard.  Fully Nashifying
all three complementary players solves their debts but erases the mover
hazard and terminal atom.  The bounded crawl found a stronger intermediate
construction, recorded with proof and an exact separation model in
[`CODEX_MINER__FIN4_REACHED_SURE_ROW_FIXED_COORDINATE_NASHIFICATION.md`](CODEX_MINER__FIN4_REACHED_SURE_ROW_FIXED_COORDINATE_NASHIFICATION.md).

Freeze the mover's exact Bernoulli rate `a` and Nashify only the other two
labels in the finite binary game obtained by averaging over that fixed
Bernoulli action.  The sure observer makes the two induced Nash inequalities
exact against arbitrary behavioral deviations.  The resulting literal
stationary profile has:

```text
two solved complementary coordinates;
positive-debt support contained in {observer,mover};
a full-terminal-gap debtor and start-zero paid row in that pair;
and a terminal atom containing the pair of mass at least a/4.
```

If the starting product row has a coalition cell of mass `w` containing both
labels, then `a>=w`, giving the source-matched floor `w/4`.  This is not a
chronological restart: Nashification reselects the other two marginals.

The exact table

\[
 r_i(S)=2\ (i\notin S),\qquad r_i(\{i\})=1,
 \qquad r_i(S)=0\ (i\in S, |S|\ge2)
\]

shows the sharp remaining boundary.  For every `a in (0,1]` the constructed
source has the localized two-debtor/heavy-pair packet, while its cap vector is
constant two and all Continue is the unique exact cap root.  A singleton
sure-exit profile is exact terminal Nash, so `D_*=0`; this is a local no-go,
not a counterexample.  Hence the new packet is a genuine rectangle-to-paid-
source adapter but does not consume the inert port without the missing global
minimum/common-law bridge.

The common-lower small-hazard idea tested in the same pass is duplicate:
`exists_quantitative_normalTerminalGap_root` and
`exists_fullSupport_normalizedSingletonSourcePacket_of_normal_terminalGap` in
`NormalTerminalGapConstrainedStationary.lean` already prove the vanishing
root, full-support direction, and normalized singleton packet with sharper
constants.  It should not be repackaged.

### Starvation checkpoint

Euler's repaired exact finite-clock prototype now has a second scoped audit:
[`feedback/CODEX_EULER__FIN4_QUANTILE_CENTER_OUTER_PROTOTYPE__BY_CODEX_MINER.md`](../feedback/CODEX_EULER__FIN4_QUANTILE_CENTER_OUTER_PROTOTYPE__BY_CODEX_MINER.md).
Its midpoint lemma is exact, and the stored rational `lambda=3/4` center
certifies `L_M=0` through precisely `M=2677`, failing at `2678`.  This is a
valuable exact algorithmic regression/formalization candidate after the
constraint-generator repairs, but remains internal because it supplies no
positive lower certificate.

## 22. Positive-Never law mass plus finite-clock compression

The current positive-Never minimum-law arm admits one new source-matched
composition, developed in
[`CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY.md`](CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY.md).

The essential combination is:

1. the point-specific checked Fin4 theorem supplies, on the same globally
   minimum joint-law point, positive finite mass `m` and (in this arm)
   positive Never mass `q`;
2. profilewise common-quantile compression of joint-law realizers preserves
   every marginal Never atom exactly, makes the fixed finite outcome converge
   through its bad-cell coupling, and gives literal clocks supported on
   finitely many dates plus Never;
3. fresh arbitrarily deep exact cap--Nash prefixes over those sources have
   Continue product tending to one by the positive-minimum debt ratio; and
4. capping one fixed terminal-gap singleton owner after the entire finite
   support changes exactly the joint-Never event into that singleton.

Consequently the exact source chronology retains an early `S`-window of mass
at least `m/4`, while one later legal endpoint move creates singleton mass
at least `q/4`, payoff gain/own-debt drop at least `Gamma*q/4`, opposite-face
transfer at least `Gamma*q/8`, and one fixed recipient increase at least
`Gamma*q/24`.  The checked endpoint-atom decoder applies at that literal
source edge.

This is the strongest nonduplicate producer found in the bounded crawl.  It
uses the newly checked finite-clock theorem in a law-honest way: semantic
density alone would not retain the selected `mu`, whereas profilewise
compression does.  It is not yet exportable because the late cap is a legal
profitable row, not an exact Nash--Bellman successor, and the endpoint decoder
still ends in its known prescribed-atom/rectangle seam.  Ramsey's delta audit
passed the exact finite-support strengthening, and Euler independently passed
the same-law compression, unrestricted late cap, transfer, and decoder after
the stage indexing was repaired to use the actual reindexed root length
`ell_n>=n+1`.

No additional reviewed result is presently starving for export.  The late
geometric joint-Never estimate in
`CHATGPT_EXTERNAL__FINITE_WATCHDOG_GEOMETRIC_SECURITY_NO_GO.md` is a useful
ingredient and has already been independently reviewed, but by itself lacks
minimum-law provenance and an exact chronological consumer; the new note is
the correct place to preserve its conjecture-facing composition.

## 23. Late-release rectangle sharpening and exact consumer boundary

The direct consumer pass produced one nonduplicate theorem and one exact
boundary, recorded in
[`CODEX_MINER__FIN4_LATE_RELEASE_RECTANGLE_THREE_LABEL_BOUNDARY.md`](CODEX_MINER__FIN4_LATE_RELEASE_RECTANGLE_THREE_LABEL_BOUNDARY.md).

For a finite-support `Never -> {a}` late release and a fixed recipient `b`
whose debt rises by `Delta>0`, the generic endpoint decoder sharpens as
follows.  Either the prescribed-loss atom is forced at `{a}` with magnitude
at least `Delta/2`, or `b` has an attained pure-time response at or after the
release.  The response difference is exactly one of

```text
r*(r_b({a,b})-r_b({b})),
r*(r_b({a})-r_b({b})),
r*r_b({a}),
```

according as the response is at the release, strictly after it, or Never.
Only `{a}`, `{b}`, and `{a,b}` can occur, and one same-deviation atom has
magnitude greater than `Delta/4`.  On the reviewed Fin4 packet this improves
the generic scales to `Gamma*q/48` or `Gamma*q/96`.

The exact rational regression retains a cofinal literal all-Continue
cap--Nash source stack, early `{b}` mass `3/8`, later `{a}` mass `3/8`, fixed
gain and recipient transfer `3/8`, and a forced `{a,b}` rectangle atom
`9/16`.  Source, late target, and the recipient's exact best-response corner
all have total debt `111/32`, but positive-debt support rotates
`{a,b}->{a,c}`.  The payoffs are punishment-floor safe, while both positive
rows fail endpoint Nash.  Its global debt minimum is zero, so it is a
post-minimum interface regression rather than a hard-residual countermodel.

The exact remaining use of the ambient hypothesis is now exposed: positive
global minimality or another hard-residual field must be applied **after**
the sharp rectangle to eliminate/consume its new support entry.  Equal local
debt, floor safety, cofinal exact source depth, and better atom constants do
not supply that consumer.  The theorem received an independent **PASS** from
[`CODEX_EULER`](../feedback/CODEX_MINER__FIN4_LATE_RELEASE_RECTANGLE_THREE_LABEL_BOUNDARY__BY_CODEX_EULER.md),
including the three-label dispatch, strict constants, full rational
regression, and cofinal-index convention.  It remains internal and is not an
export candidate without such a consumer.

## 24. Genuine minimum-fiber support entry forces a rectangle excursion

The follow-up global-minimum pass produced
[`CODEX_MINER__POSITIVE_NEVER_MAX_SUPPORT_RECTANGLE_EXCURSION.md`](CODEX_MINER__POSITIVE_NEVER_MAX_SUPPORT_RECTANGLE_EXCURSION.md).
Choose the initial minimum joint semantic/law point, among those with positive
Never coordinate, to maximize the cardinality of its positive-debt support.
For a literal two-player response rectangle, three successive applications
of the checked near-minimum stopping-law chord-gap theorem show that if all
four corner limits have total debt `D_*`, then every proper two-coordinate
interior mixture also has total debt `D_*`, with debt vector equal to the
strictly positive bilinear average of the four corner debt vectors.  Its
support is therefore their union.

The interior mixture is an actual product behavioral profile, not a
correlated whole-profile mixture.  Moreover it retains joint Never mass at
least `(1-lambda)(1-theta)q>0`, by selecting both source branches of the two
independent complete-law mixtures.  Maximal support in the positive-Never
minimum class therefore forces every corner support to be contained in the
source support.

Consequently a decoded newcomer cannot be a cost-free minimum-fiber support
exchange: at least one actual rectangle corner has a fixed positive total-
debt excursion above `D_*`.  If the decoded endpoint itself is on the
minimum fiber, one of the two side corners is strictly off it.  This is the
first use of the genuine `D_*>0`/global-minimum provenance which rules out the
local rotation mechanism from Section 23.

The theorem received an independent **PASS** from
[`CODEX_EULER`](../feedback/CODEX_MINER__POSITIVE_NEVER_MAX_SUPPORT_RECTANGLE_EXCURSION__BY_CODEX_EULER.md),
with no mathematical repair.  It does not yet close the conjecture: an
off-minimum zero-debt response endpoint gives absorbing cap return or another
all-Continue face, while an off-minimum side corner feeds the existing paid
descent/inert trichotomy.  The missing step is an actual positive-charge
return from the fixed excursion or an incompatibility of its inert face with
the retained positive-Never source.
