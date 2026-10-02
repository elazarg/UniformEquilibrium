# Adversarial export-gate review of `RENEW_1.md`

Reviewer: `CODEX_GATE_FALSIFIER`

## Verdict

**FAIL for export in its present form.**

There are two correct mathematical cores:

1. two distinct deterministic finite stoppers screen an arbitrary later tail
   from prescribed play and from every one-player behavioral deviation; and
2. a positive terminal exploitability gap produces a full-gap paid cap port
   at every actual profile, so the charged arm is impossible under the same
   gap and the port lies in quantitative debt descent or inert stall.

The first is a useful generic lemma but currently has no consumer.  The second
is already checked, in stronger and more precise form, by
`HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort` and
`QuittingActualProfileTerminalGapPaidCapPort.quantitativeDebtDescent_or_inertStall`
in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`.

The packet does not answer
[`FIN4_RENEWAL_TERMINAL_EXIT_CONSUMERS.md`](../questions/FIN4_RENEWAL_TERMINAL_EXIT_CONSUMERS.md).
It replaces each exit by the already open paid-cap residual, without producing
a charged return, finite rank, terminal approximation, or contradiction.  Its
last displayed chain also conflates a generic reset-arrival source with the
separately constructed singleton-base double port required for the
repaired-side/double-unique alternative.

Accordingly, this is a useful internal consolidation and one formalizable
tail-screen lemma, not an export-ready strict change to the conjecture-facing
boundary.

## Exact claims audited

The document contains two successive analyses rather than one theorem.

- The first analyzes the mismatch between a horizontal path of exact
  pure-time cap-attaining updates and a chronological punishment-floor path.
  It proposes a two-stopper tail-grafting lemma.
- The second observes that the terminal gap independently produces a paid cap
  port at every actual profile, and claims a common reduction of the three
  renewable terminal exits to paid/reset descent or a double unique-cap
  plateau.

These claims have different hypotheses, source objects, and consumers.  They
must be separated before either can be considered for export.

## 1. Global refusal ledger

### Verdict: essentially correct, but the note should use the checked form

For one fixed root sequence, one player, and a finite date set, the checked
theorem
`quittingFiniteRefusal_terminalValue_sub_eq_sum` in
`UniformEquilibrium/Quitting/Classification/Existence/GlobalRefusalLedger.lean`
gives

\[
 U_i(x^{i\text{-refuse }F})-U_i(x)
 =\sum_{t\in F}S^F(t)\bigl(C_i(t)-V_i(t)\bigr).
\]

The stronger checked estimate is phrased using the local prescribed-value
minus immediate-Quit gap.  It yields

\[
 \delta\sum_{t\in F}S(t)q_i(t)\le \varepsilon
\]

under one global `\varepsilon`-Nash cap.  The arbitrary-set summability
theorem is also checked.

The note's main limitation is correct: these weights all belong to one root
sequence.  Nothing in the ledger permits summing gains from a sequence of
different complete profiles.

## 2. Exact falsifier for horizontal-to-chronological conversion

The asserted obstruction is real even in a one-date two-player table.

Let players be `a,b`.  At date zero let the source pure coalition be `{a}`.
Choose rewards satisfying

\[
 r_b(\{a,b\})=1>0=r_b(\{a\}),
\]

and

\[
 r_a(\{b\})=1>0=r_a(\{a,b\}).
\]

All unspecified rewards may be zero.  Against the source, changing `b` from
Continue to Quit is an exact best response and changes the profile to the
pure pair `{a,b}`.  At that target, however, `a` strictly prefers Continue,
which changes the terminal coalition to `{b}`.  Thus one player's exact
horizontal cap-attaining update does not make the target root simultaneously
Nash for all players.

This is exactly the missing implication from (3) to (4).  Tail grafting does
not change it, because the failure occurs at the current sure-absorbing root.

## 3. Two-stopper tail invariance

### Verdict: PASS as ordinary mathematics

Let distinct players `a,b` use deterministic finite stopping times `T_a,T_b`,
and splice an arbitrary behavioral tail strictly after a time
`H>max(T_a,T_b)`.  Under prescribed play, one of the two stoppers absorbs by
`H`.  Under a unilateral behavioral deviation by player `i`, at most one of
the two prescribed stopper strategies is changed; the other still absorbs by
`H`.  Therefore the spliced tail is never read under prescribed play or under
any one-player behavioral deviation.

It follows pointwise, for every player and every behavioral deviation, that
the deviation payoff is unchanged.  Hence the full unrestricted cap vector
and the prescribed payoff vector are unchanged.  The prescribed terminal law
is also unchanged.  The same argument preserves every one-player-deleted law,
which is a useful strengthening if later source packets retain those laws.

This is not a stationary-only statement.  It covers `Never`, arbitrary late
stopping, randomized behavioral hazards, and calendar-dependent deviations.

### Necessary definition repair

The packet must define the graft literally, including whether “after `H`”
means dates `>H` or dates `\ge H`, and state that the original prefix is kept
on the unique live histories.  With the displayed strict inequalities either
standard convention works after the obvious index adjustment.

### Sharp negative boundary

One stopper is insufficient.  Let `a` Quit surely at date zero and let every
other player Never Quit.  Two tails after a later cutoff are invisible under
prescribed play.  But if `a` deviates to Never, the later tail is reached and
can change `a`'s payoff by the full reward range.  Thus one deterministic
stopper does not preserve `a`'s behavioral cap; the second distinct stopper is
essential.

## 4. Strengthening the finite reset finish to two stoppers

### Verdict: plausible and locally complete, but not yet stated precisely

The checked `QuittingFiniteStopperExactFinish` construction in
`TerminalSemanticFinitePureTimeResetArrival.lean` starts with one retained
finite stopper and makes at most two exact pure-time cap-attaining updates.
If an exact selected response is `Never`, the theorem
`quittingTerminalPayoff_update_pureTime_eq_none_of_opponent_stops_before`
allows replacement by any deterministic time strictly after the retained
opponent deadline, with exactly the same payoff.

Case by case, this can retain two distinct finite stopper players:

- in the one-step finish, keep the original stopper and make the updating
  player finite, replacing `Never` by a later deadline if necessary;
- in the two-step finish, the first updater Quits at date zero and the second
  updater can again replace `Never` by a later finite deadline.

Because the opponents are unchanged and absorption already occurs before the
replacement time, exact cap attainment, zero own debt, the complete law, and
the retained positive incidence are preserved.

This should be written as an exact strengthened finish theorem, not as the
sentence “can also be strengthened.”  It remains a local adapter until a
consumer uses it.

## 5. What tail grafting does and does not provide

The note says the two-stopper result settles the “tail substitution” part of
the desired handoff.  This needs qualification.

It permits the returned minimum source to be placed **syntactically** behind
the final reset barrier without changing the final profile's semantic pair.
But its reach is zero under prescribed play and under every unilateral
deviation.  Consequently the graft supplies no positive absorption charge,
no reached terminal law from the returned source, and no Bellman connector to
it.

In particular, a tail which is completely screened in this sense cannot by
itself be the positive-charge part of a punishment-floor return.  The current
root inequalities still have to be manufactured at the horizontal seams.

The exact falsifier in Section 2 shows that the simultaneous-root problem is
independent of this tail transport.

## 6. Full-gap paid row at every actual profile

### Verdict: PASS and already checked

The apparently delicate full constant `\gamma` is valid.  The argument does
not require the behavioral cap supremum to be attained.  A profitable
behavioral deviation and the prescribed strategy each induce a probability
law on `\mathbb N\cup\{\infty\}`.  Their payoffs are bounded averages of the
same pure-time payoff function.  A support atom above the first average and a
support atom below the second retain the full difference of the averages.

This is precisely
`HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at`, followed
by `exists_paidFirstDisagreementRow_at`.  Therefore every actual profile
constructs a `QuittingPaidCapLiftedSource` with paid scalar `\gamma` and a
summable cap port.

Under the same terminal exploitability gap, the charged-near-return arm would
give a uniform-equilibrium payoff and is impossible.  Hence the checked exact
conclusion is

\[
 \text{quantitative debt descent}\quad\lor\quad\text{inert stall}.

This covers unrestricted behavioral deviations, including `Never`, because
the source cap is the complete behavioral envelope and the stopping-law
average identity covers the complete behavioral strategy.

## 7. The advertised common exit reduction

### Verdict: logically valid only as an unrelated existential reduction

A `FinFourRenewableTerminalExit` is a proposition about a tangent node: it is
positive total slope, flat support entry, or an off-minimum paid endpoint.
The paid-port construction above can ignore that exit entirely and apply to
any actual profile stored by the node's source chronology.  Thus one can prove
an implication of the schematic form

```text
terminal exit
  -> there exists some same-table actual paid cap source and port
       in quantitative debt descent or inert stall.
```

But the conclusion is not source-matched to the slope, entry, or off-minimum
profile unless the selected actual profile is specified and the appropriate
equality is proved.  More importantly, it replaces the three named terminal
obligations by the already open generic paid-cap obligation; it does not
consume or rank them.

The boxed expression

```text
FinFourRenewableTerminalExit -> QuantitativeDebtDescent or InertStall
```

is not a well-typed self-contained theorem because both right-hand predicates
depend on a paid source and a selected summable port.  Those existential data
must appear in the statement.

## 8. Source/provenance break in the double-unique sharpening

### Verdict: SUBSTANTIVE REPAIR REQUIRED

The generic finite reset arrival yields one actual final profile with:

- a zero-debt reset owner;
- positive owner/opponent incidence;
- after the terminal-gap adapter, a paid row; and
- after the fixed-law theorem, a reset dispatch.

Applying
`maximalOneStepPaidResetRegeneration_or_uniqueAllContinue` to that source gives
exactly

```text
source-side maximal paid/reset regeneration
or
unique all-Continue at that source cap.
```

It does **not** produce a literal owner-repaired paid source or a second cap.

The three-way alternative

```text
source-side regeneration
or repaired-side regeneration
or double unique all-Continue
```

is checked only for the separately supplied
`FinFourSingletonBaseResetRepairPaidCapDoublePort` in
`Research/Quitting/FinFourPaidCapMaximalDoubleRegeneration.lean`.  That object
comes from the singleton-base double-port construction.  It is not a field or
consequence of an arbitrary `QuittingFiniteStopperExactFinish` or arbitrary
fixed-law reset arrival.

The packet must choose one honest statement:

1. retain the reset-arrival source and conclude the one-sided maximal
   alternative; or
2. invoke the independently selected singleton-base double port and state
   explicitly that it is not the reset-arrival profile and is not connected
   to the terminal exit chronology.

The present chain silently identifies those sources.

## 9. Support regeneration and rank

The packet correctly observes that alternating strict inclusions such as

\[
 \{0\}\subsetneq\{0,1\}\supsetneq\{1\}
   \subsetneq\{0,1\}\supsetneq\cdots

\]

do not define a natural-valued descent.  A repeated finite support label also
does not imply recurrence of semantic pairs or of a punishment-floor path.

However, the assertion that the flat-entry mixture has already been promoted
to a complete same-residual minimum source is not proved in this packet.  It
lists four necessary adapters—joint compactification, positive-atom
selection, source-faithful causalization, and tangent re-extraction—but gives
neither named declarations nor the construction.  For export, either cite the
checked composite theorem which carries the same literal mixture subsequence,
or retain this as an explicit obligation.  Calling it “genuinely
source-renewable” without that evidence is premature.

Even after those adapters, support **expansion** is not a decreasing rank and
does not answer the terminal-exit question.

## 10. Consumer compatibility

The relevant consumers separate cleanly:

- `ChargedNearReturn.uniformEquilibriumPayoff` consumes the charged cap-port
  arm.
- The current `QuantitativeDebtDescent` arm is only strict real-valued debt
  descent.  A paid/reset source can regenerate a finite actual descendant,
  but no well-founded rank follows.
- `InertStall` has zero selected-port absorption.  It supplies no cumulative
  charge.
- `QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` consumes an
  actual punishment-floor path with fixed positive charge and close payoff
  endpoints.  Neither horizontal reset paths nor the zero-reach tail graft
  construct such a path.

Thus the proposed `QuittingActualProfileFixedLawResetHandoff ->
QuittingPunishmentFloorAdmissiblePath` is not a “remaining declaration.”  It
is the missing producer theorem itself, and the exact two-player falsifier
above shows that it needs hypotheses beyond horizontal cap attainment and two
stoppers.

## 11. Strongest surviving theorem

The following package is mathematically supported.

> **Two-sentinel semantic screen.** In any finite quitting game, if two
> distinct players use deterministic stopping times before a cutoff `H`, then
> replacing the entire live-history tail after `H` preserves the prescribed
> terminal payoff and terminal law, every unilateral behavioral-deviation
> payoff, the full behavioral cap vector, and hence the terminal semantic
> pair.  A finite-stopper exact reset finish can be chosen with two such
> distinct finite stoppers by replacing any selected `Never` response with a
> later payoff-equivalent finite deadline.

Together with the already checked result:

> **Actual-profile paid-port reduction.** Under a positive terminal
> exploitability gap and positive global minimum debt, every actual profile
> supplies a full-gap paid cap source and summable port which lies in
> quantitative debt descent or inert stall.

Neither theorem consumes a renewable terminal exit.  The missing statement
remains simultaneous Nash--Bellman/punishment-floor exactification of the
horizontal reset path, or an independent well-founded/unique-cap consumer.

## Required repairs before reconsideration

1. Split the document into the two-sentinel theorem and the already checked
   actual-profile paid-port reduction.
2. Define the tail splice, cutoff convention, and complete probability mode.
3. State and prove the two-stopper strengthening of the finite reset finish,
   including preservation of zero debt, incidence, and law.
4. Do not describe a zero-reach tail graft as a reached return or charge.
5. Give the common paid-port implication with its existential source and port
   data and specify which actual profile is used.
6. Remove the reset-arrival-to-double-port identification; state either the
   one-sided maximal alternative or the independent singleton-base double
   alternative.
7. Supply named declarations for the claimed source-renewable support-entry
   adapter, or mark it open.
8. State explicitly that no finite rank or positive return is produced.
9. Explain a genuinely new strict change to a named question.  A local
   two-sentinel lemma without a downstream consumer and a restatement of an
   already checked paid-port theorem do not satisfy `exports/README.md`.

