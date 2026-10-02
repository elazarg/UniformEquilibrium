# Source and freshness audit of `RESET_REGEN.md`

Reviewer: `CODEX`

## Verdict

**FAIL for export.**  The displayed Zeno calculations are mathematically sound
for the canonical descendants constructed in the one-step proof, and they use
the project's unrestricted behavioral terminal semantics correctly.  They do
not, however, make a new conjecture-facing change:

1. the scalar ray identities, summable absorption, invariant debt support and
   normalized debt, noncollapsing shifted paid edge and suffix atom, and
   vanishing future canonical charge are already present in stronger checked
   maximal-ray and paid-cap-port results;
2. the only additional composition is a fresh fixed-law reset dispatch at
   every finite iterate, already recorded and reviewed in
   `notes/CHATGPT_EXTERNAL__NONCOLLAPSING_MAXIMAL_PAID_RESET_ORBIT.md`; and
3. the proposed “Zeno-passport charge-renewal lemma” is precisely the missing
   consumer, not a theorem proved by this packet.

The packet therefore remains a useful internal description of the surviving
paid/reset orbit, but it neither answers
`questions/FIN4_PAID_RESET_REGENERATION_RANK.md` nor strictly narrows that
question beyond the checked boundary.

There is also one formal-interface qualification.  The existing one-step
structure does not expose the equality

```text
descendant.gain = continueMass(maximalRoot) * source.gain.
```

Its constructor chooses exactly that annotation internally, so the ordinary
mathematics can define a canonical recursive successor having this equality.
But the equality cannot be recovered from an arbitrary inhabitant of the
public structure.  A Lean handoff must add the equality as a field/theorem or
define the canonical successor explicitly; it may not derive the recursive
gain formula merely from `Nonempty MaximalOneStepPaidResetRegeneration`.

## Exact source correspondence

### One-step actual-source regeneration

`Research/Quitting/PaidCapMaximalOneStepRegeneration.lean` defines

```text
QuittingPaidCapLiftedSource.MaximalOneStepPaidResetRegeneration
maximalOneStepPaidResetRegeneration_or_uniqueAllContinue
```

The positive branch literally prefixes the canonical maximum-absorption exact
cap--Nash root.  Its proof constructs the descendant with:

```text
profile  = quittingMaximalCapPrefixProfile ... 1
minimum  = source.minimum
observer = source.observer
gain     = rootContinueMass * source.gain
```

and supplies zero reset debt, positive reset incidence, membership of the
actual semantic/law point in the carrier, and a fresh fixed-law reset
dispatch.  Thus the finite-stage actual-source and reset-provenance assertions
are correct.  The public structure stores `descendant_profile` and
`descendant_minimum`, but not `descendant_observer` or `descendant_gain_eq`.

### Exact coordinate debt scaling

`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`
proves

```text
d_i(q ▷ x) = continueMass(q) * d_i(x)
```

coordinatewise for an exact root Nash against the full terminal cap.  The cap
is the supremum over all unilateral behavioral stopping strategies.  Summing
this identity gives the packet's total-debt recurrence.  Therefore constant
positive-debt support and constant normalized debt along positive-survival
steps are valid.

### Canonical maximal-ray telescope

The following checked declarations already provide the scalar part of the
packet:

- `quittingMaximalCapPrefixProfile_debt_succ`,
  `quittingMaximalCapPrefixProfile_stage_succ`,
  `quittingMaximalCapPrefixProfile_debt_mul_stage_eq`,
  `minimum_mul_sum_maximalCapPrefix_absorption_le_debtDrop`, and
  `summable_maximalCapPrefix_absorption` in
  `Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean`;
- `QuittingMaximalCapSemanticPrefixRayStall.debt_tendsto`,
  `.survival_tendsto`, `.weightedAbsorption_hasSum`,
  `.summable_absorption`, `.absorptionTailSum_tendsto_zero`,
  `.absorptionTailSup_tendsto_zero`, and `.absorption_tendsto_zero` in
  `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`.

These cover exact multiplicative debt transport, the positive survival floor
forced by the global positive minimum, summable absorption, and vanishing
future canonical charge.  The packet's logarithmic estimate is a correct
alternative proof, but the checked debt-drop estimate is already sufficient.

`formalized/FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md` already records
the Fin4 source adapter, invariant support and normalized debt, persistent
marked mass and paid gain, and the strict-stall conclusion that arbitrarily
late portions of the same canonical ray cannot regenerate a fixed positive
charge.

### Paid-row transport

`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/
PaidCapLiftedSummablePort.lean` proves the generic paid cap-lifted orbit,
including:

```text
QuittingPaidCapLiftedSource.pureTimePayoff_sub_shift
QuittingPaidCapLiftedSource.shifted_gain_le
QuittingPaidCapLiftedSource.absorption_summable
```

and the literal profile, debt, and suffix-reach recurrences.  This is stronger
than the packet in not requiring maximum-root selection merely to retain a
paid row.  Maximum selection is relevant to the canonical branch
classification.

The annotation equality in `RESET_REGEN.md` must be read conservatively:
`g_n` is a selected positive lower-bound certificate.  It is not necessarily
the complete pure-time payoff difference.  The one-step constructor may set
the next certificate to `c_n g_n`; the sharper actual shifted difference is
scaled by the observer-opponent survival, which is at least joint survival.

### Incidence transport

`quittingTerminalOpponentIncidenceMass_lawPrefix` and
`positive_incidence_lawPrefix_of_positive_continueMass` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`
give

```text
incidence(prefix(q,law))
  = rootIncidence(q) + continueMass(q) * incidence(law),
```

and hence the lower bound used in equation (2).  The quantity is a coordinate
of the complete terminal-outcome law.  It is not being identified with
current-root absorption or with a single marked-stage atom.

### Cap-to-payoff seam

The purported new seam is already checked in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
PairBasePaidResetEndpointSeam.lean`:

```text
capNash_isZeroNash_at_prescribed_iff_surcharge_eq_liveDebt
QuittingFixedLawResetDispatch.positiveError_and_not_killedDebt
```

The first theorem is the exact surcharge-versus-live-debt equivalence.  The
second records that positive survival and positive debt exclude the easy
killed-debt conversion.  Thus equation (13) is correct but not fresh.

### Existing near-return consumer

`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/
PaidCapPortSequenceNearReturn.lean` contains the varying-source consumer.  Its
relevant input combines vanishing cap displacement with an eventual fixed
positive total-absorption floor.  Summability of the regeneration-edge
absorptions proves that a *late consecutive segment of this canonical
regeneration ray* cannot supply that floor.  This statement must retain that
qualification: every descendant also has other available cap-lifted ports,
whose total absorption is not identified with the tail sum of the canonical
regeneration edges.

## Freshness comparison

`notes/CHATGPT_EXTERNAL__NONCOLLAPSING_MAXIMAL_PAID_RESET_ORBIT.md` already
states the same exhaustive normal form:

```text
eventual unique-all-Continue cap
or an infinite literal actual-source family with
  summable prefix absorption,
  uniformly positive paid and inherited-law data,
  zero reset debt and positive reset incidence,
  and a fresh fixed-law reset dispatch at every stage.
```

Its existing independent audit in
`feedback/FIN4_HARD__BY_CODEX_ROOT.md` reached the same boundary: the
per-iterate reset composition is plausible/useful source packaging, while the
quantitative ray account is already checked and the composition has no
consumer.  `RESET_REGEN.md` adds a clear discussion of constant candidate
ranks, vanishing future charge, and the surcharge seam, but those discussions
are consequences or already checked no-gos, not a new exported theorem.

## Behavioral and probability audit

- Every finite descendant is a literal behavioral profile obtained by adding
  a finite product root at the front.  No carrier point replaces it.
- Terminal caps remain unrestricted all-behavior best-response envelopes;
  no stationary or bounded-deviation reduction occurs.
- The paid certificate uses deterministic pure stopping times, with `Never`
  allowed, inside the exact behavioral-cap semantics.
- Root absorption, observer-opponent survival, terminal-law incidence, and a
  marked suffix atom are distinct quantities.  The packet's displayed uses of
  them respect those distinctions.
- From a reward bound `M`, one prefix changes prescribed payoff by at most
  `2 M a_n`, changes each cap by the same type of coupling bound, and changes
  the terminal law in total variation by at most `a_n`.  Hence summable
  absorption does give convergence of the full finite-dimensional
  semantic/law packet.
- The limiting semantic/law point need not be attained by a behavioral
  profile, because the construction prefixes outward.  The packet correctly
  refuses to apply the terminal exploitability witness directly to that
  carrier limit.
- For Fin4, `D_n >= D_*` implies `max_i d_n^i >= D_*/4`, so the descendants
  themselves are uniformly separated from terminal approximate Nash profiles.

## Relation to the maintained question

`questions/FIN4_PAID_RESET_REGENERATION_RANK.md` explicitly rejects the
one-step regeneration, a merely decreasing real debt, source reconstruction
without a rank or terminal dispatch, and a compact cluster detached from the
literal chronology.  `RESET_REGEN.md` produces none of its four accepted
outputs.  It shows that several obvious candidate ranks remain constant and
restates the missing consumer as charge renewal.  That is an informative
normal-form diagnosis, but it does not change the maintained question.

## Recommended disposition

Keep the result under `notes/`, preferably by consolidating it into the
existing noncollapsing-orbit note rather than creating a second copy.  If the
recursive decorated source is to be formalized for later use, first expose a
canonical successor or add at least:

```text
descendant_observer_eq
descendant_gain_eq
```

to the one-step API.  Promotion would require the new charge-renewal consumer,
a finite renewable rank, terminal approximants, or a contradiction—not merely
the Zeno normal form itself.
