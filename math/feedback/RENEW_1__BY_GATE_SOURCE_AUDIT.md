# Source and freshness audit of `RENEW_1.md`

Reviewer: `CODEX`

## Verdict

**FAIL for export.**  The note correctly refuses to identify a sequence of
horizontal cap-attaining strategy replacements with one chronological
punishment-floor path.  Its only genuinely new mathematical component is a
small and sound strengthening of the finite reset finish: arrange two distinct
literal finite stoppers, after which an arbitrary tail graft is invisible to
the prescribed payoff and every unilateral behavioral deviation.

That component does not construct the missing simultaneous root inequalities,
positive admissible path, terminal approximation, or renewable rank.  It is a
local seam lemma without the consumer required by the export gate.  The
note's other headline reduction—extracting a full-gap paid cap port at every
actual profile and reducing it to quantitative descent or inert stall under a
terminal gap—is already checked and documented in stronger form.

One claimed Fin4 sharpening is also not source-faithful as written.  The
checked *double*-unique-cap alternative belongs to the specialized stationary
singleton-base source and its literal owner repair.  An arbitrary final
profile produced by `QuittingActualProfileFixedLawResetHandoff` can enter the
single-source maximal-root alternative, but it does not thereby acquire that
specialized owner-repaired double port.

Accordingly the packet does not answer or strictly narrow any maintained
question in its present form.  The two-stopper lemma should be retained in a
note, or formalized as a small API strengthening if a later consumer needs it.

## Claim-by-claim audit

### 1. Global refusal ledger

The fixed-sequence distinction is correct and already checked in
`UniformEquilibrium/Quitting/Classification/Existence/GlobalRefusalLedger.lean`.
In particular:

```text
quittingFiniteRefusal_terminalValue_sub_eq_sum
delta_mul_finiteRefusalCharge_le_gain
```

use one root sequence throughout.  The survival weights are those of the
modified refusal sequence, and the comparison with the original selected
Quit clock follows from monotonicity of survival after forcing Continue.
Nothing in these declarations allows gains from a chain

```text
P_0 -> P_1 -> ... -> P_k
```

of different complete profiles to be inserted into one telescope.  The note's
warning about the horizontal seam is exact.

This is not fresh content.

### 2. Actual-profile reset arrival

`UniformEquilibrium/Diagnostics/Quitting/
TerminalSemanticFinitePureTimeResetArrival.lean` defines and proves:

```text
QuittingFiniteStopperExactFinish
nonempty_finiteStopperExactFinish
QuittingActualProfileFixedLawResetHandoff
nonempty_actualProfileFixedLawResetHandoff
```

The last theorem starts from an arbitrary literal behavioral profile, retains
a bounded profitable pure-time update path, ends at an actual profile with a
zero-debt owner and positive opponent incidence in its actual law, and attaches
a fresh fixed-law reset dispatch anchored at the supplied positive minimum.
The path is horizontal: each edge changes one complete behavioral strategy.
The public handoff does not assert a root-Nash/Bellman chronology.

This entire arrival and source attachment is already checked and documented
in
`formalized/FINITE_PURE_TIME_RESET_ARRIVAL_AND_FIN4_THREE_ROLE_ASCENT_HANDOFF.md`.

### 3. Two-stopper tail invariance

The displayed theorem is correct.  If distinct players `a,b` use pure finite
stopping times below a cutoff `H`, prescribed play absorbs before `H`.  Under
an arbitrary unilateral behavioral replacement, at most one of `a,b` is
changed, so the other still stops surely before `H`.  Thus two profiles which
agree through `H` have:

- the same prescribed payoff and terminal law;
- the same payoff under every fixed unilateral behavioral deviation; and
- therefore the same unrestricted behavioral cap and complete terminal
  semantic pair.

This covers privately randomized, history-dependent, Never, and arbitrarily
late deviations because none can remove both prescribed sure stoppers.

The exact same screening proof already appears for two sure quitters at one
marked row in
`notes/SINGLETON_INCENTIVE_AUDITOR__TWO_SURE_QUITTER_TAIL_REPLACEMENT_NOGO.md`
and in the pure-nonsingleton screening development.  The staggered-deadline
version is a genuine generalization, but a local one.  It can also be obtained
from the checked retained-tail finite-word identities once every
player-deleted return probability is shown to be zero.

No named Lean declaration currently packages the staggered two-stopper
semantic equality.

### 4. Strengthening the reset finish to retain two finite stoppers

This proposed strengthening is mathematically valid, but is not exposed by
the current structures.

The proof of `nonempty_finiteStopperExactFinish` begins with one literal finite
stopper and chooses an exact pure-time best response for a distinct player.
If that response is `Never`, choose any pure stopping time strictly after the
old stopper's deadline.  The checked theorem

```text
quittingTerminalPayoff_update_pureTime_eq_none_of_opponent_stops_before
```

proves equality of the updating player's payoff with its Never payoff.  Hence
the later finite time still attains that player's full behavioral cap and
retains the edge gain and zero own debt.  Prescribed absorption before the old
deadline also preserves the final terminal law and incidence.  In the
two-step branch the first exact responder already Quits at date zero, so the
same replacement works for a final Never response.

Two qualifications are essential:

1. the cited payoff-equivalence theorem controls the updating player's payoff,
   not every other player's cap between the Never and late-finite profiles;
   no such extra equality is needed for the proposed strengthened finish; and
2. neither `QuittingFiniteStopperExactFinish` nor
   `QuittingActualProfileFixedLawResetHandoff` stores the two stopper labels,
   deadlines, or strategy equalities.  The two-stopper graft theorem cannot be
   invoked from an arbitrary inhabitant of the current public handoff.  A new
   strengthened handoff or explicit fields are required.

Thus this is a plausible small Lean extension, not an already checked field of
the handoff.

### 5. What tail grafting actually supplies

The graft is an actual behavioral profile and preserves the final profile's
complete terminal semantics.  It does **not** make the grafted tail a reached
continuation under prescribed play or under any unilateral deviation; the two
stoppers screen it completely.  Therefore it does not convert the returned
minimum point into a chronological successor or supply positive path charge.

Moreover, a fixed-law reset dispatch returns a carrier semantic point.  That
point need not be attained by one behavioral profile.  If a regenerated
minimum source supplies actual realizing profiles, each such profile can be
grafted separately, but the tail remains screened and the whole semantic pair
remains the reset endpoint's pair.

The note is therefore correct that simultaneous root exactification remains
open, but “the returned minimum source as the actual tail” requires an actual
profile and must not be inferred from the returned carrier point alone.

The proposed type name `QuittingPunishmentFloorAdmissiblePath` is not a current
declaration.  The checked object is a path in

```text
quittingPunishmentFloorAdmissibleChargedRelation reward
```

from
`UniformEquilibrium/Quitting/Bellman/Finite/
PunishmentFloorAdmissibleChargedRelation.lean`.

### 6. Full-gap paid port at every actual profile

This entire part of the note is duplicate checked content.  The exact source is
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/
ActualProfileTerminalGapPaidCap.lean`:

```text
HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at
HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at
HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort
QuittingActualProfileTerminalGapPaidCapPort.exactTrichotomy
QuittingActualProfileTerminalGapPaidCapPort.quantitativeDebtDescent_or_inertStall
```

These theorems already prove, with the full weak gap and unrestricted
behavioral semantics, that every literal profile enters the paid cap-port
trichotomy and that the charged branch is impossible under the same terminal
gap because it would produce a uniform-equilibrium payoff.

The result and its limitations are already documented in
`formalized/ACTUAL_PROFILE_TERMINAL_GAP_PAID_CAP_TRICHOTOMY.md`.  In
particular, the selected observer need not align with any terminal-exit mover,
reset owner, or collision label; quantitative real-valued descent is not well
founded; and inert stall is not consumed.

Consequently the boxed implication from a `FinFourRenewableTerminalExit` to a
descent-or-stall is not a new terminal-exit reduction.  It is an application
of a theorem true at every unrelated actual profile.  To be source-attached,
it must specify which literal profile carried by the terminal node is chosen;
even then it does not use or consume the positive-slope, support-entry, or
off-minimum geometry.

### 7. Renewable terminal exits and support recurrence

`Research/Quitting/FinFourProducerAtlas/
CanonicalPairRenewableSourceRank.lean` defines
`FinFourRenewableTerminalExit` and the checked finite support-descent trace.
`CanonicalPairMinimumEndpointRenewal.lean` exposes the same-residual terminal
node.  The three terminal alternatives are exactly positive total slope, flat
support entry, and off-minimum paid first disagreement.

The note's statements that support expansion and contraction can alternate,
and that repetition of a finite support label is not a punishment-floor
chronology, are correct.  They are already enforced by
`questions/FIN4_RENEWAL_TERMINAL_EXIT_CONSUMERS.md`, whose nonanswers exclude
another paid row or conditional consumer with an unproduced chronology.

### 8. Fin4 double-unique-cap claim

`Research/Quitting/FinFourPaidCapMaximalDoubleRegeneration.lean` proves

```text
FinFourSingletonBaseResetRepairPaidCapDoublePort.
  sourceMaximalRegeneration_or_repairedMaximalRegeneration_or_doubleUnique
FinFourQuantitativeFullSupportHardResidual.
  exists_paidCapDoublePort_maximalRegeneration_or_doubleUnique
```

The first input is a specialized `FinFourSingletonBaseResetRepairPaidCapDoublePort`:
one stationary singleton-base source and its literal owner repair.  The second
theorem constructs that specialized object independently from the hard
residual for a prescribed singleton owner.

An arbitrary `QuittingActualProfileFixedLawResetHandoff` final profile is not
such a double port.  Its zero debt, positive incidence, paid row, and reset
dispatch suffice for the *single-source*
`maximalOneStepPaidResetRegeneration_or_uniqueAllContinue` alternative.  They
do not manufacture the specialized owner repair, its paid source, reset
incidence, or second cap.  Thus equation (2) is valid only as an independent
same-table hard-residual result, not as the claimed direct continuation of
the reset-arrival profile.

## Behavioral and probability audit

- All profile updates in the reset path and tail graft are actual behavioral
  strategy replacements.
- Caps are suprema over complete unilateral behavioral strategies.  The
  two-stopper proof establishes equality before taking the supremum, so it is
  valid for unrestricted caps.
- Pure stopping times use `Option Nat`, with `none` representing Never.
- The full-gap paid-row extraction is an exact comparison of atoms from the
  prescribed and profitable stopping laws; it does not assume cap attainment
  or finite support.
- The global refusal ledger uses survival under one modified root sequence.
  It cannot sum weights taken from different horizontal profiles.
- Fixed-law return points and actual behavioral profiles remain distinct.

## Freshness and maintained-question effect

The common paid-cap reduction, reset arrival, refusal ledger, cap trichotomy,
support recurrence warning, and double-unique-cap alternative are all existing
checked results or maintained boundaries.  The only fresh component is the
two-finite-stopper strengthening and its tail-screening corollary.

That component does not satisfy any accepted output of:

- `questions/FIN4_RENEWAL_TERMINAL_EXIT_CONSUMERS.md`;
- `questions/FIN4_PAID_RESET_REGENERATION_RANK.md`; or
- `questions/FIN4_DOUBLE_UNIQUE_CAP_CLOSURE.md`.

It removes no terminal alternative and supplies no source-preserving rank or
admissible return.  The exact simultaneous-root inequalities which the note
leaves open are the consumer, not a routine source adapter.

## Recommended disposition

Do not export `RENEW_1.md`.  Retain the two-stopper lemma in `notes/`, with a
small Lean handoff that strengthens `QuittingFiniteStopperExactFinish` and
`QuittingActualProfileFixedLawResetHandoff` by explicit stopper/deadline
fields.  Reconsider export only if those fields are used to construct the
simultaneous exact root/admissible path, a terminal approximation, or another
accepted closing output.
