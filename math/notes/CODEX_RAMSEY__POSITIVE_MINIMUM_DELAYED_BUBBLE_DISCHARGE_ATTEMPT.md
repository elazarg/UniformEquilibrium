# CODEX_RAMSEY — delayed inert-bubble discharge attempt

**Status (2026-08-26): IN PROGRESS.  No conjecture-facing conclusion is
claimed.**  In particular, this note does not prove a terminal approximant,
a charged near-return, a debt contradiction, a regenerating rank descent, or
a positive-gap table.  It records the exact producer attempt still being
tested so that the compact bubble is not mistaken for an exact Bellman edge.

## 1. Exact question

Work on `Fin 4` under a hypothetical positive terminal exploitability gap
`gamma > 0` and positive global terminal-semantic minimum `D_* > 0`.  Let
`sigma` be an actual behavioral profile carrying a full-`gamma` paid
first-disagreement row and suppose its paid cap lift is in the literal inert
arm.  For `n : Nat`, let `sigma[n]` be `sigma` preceded by `n` deterministic
all-player-Continue rows.

The required output is one of the maintained consumers:

1. terminal approximate Nash profiles (hence a uniform payoff);
2. exact punishment-floor paths with a fixed cumulative charge and arbitrarily
   close payoff endpoints;
3. a carrier point of debt below `D_*`;
4. a natural-valued source rank which strictly decreases and whose source data
   can be re-extracted; or
5. an explicit `Fin 4` table with a positive all-behavior terminal gap.

Nothing below currently supplies one of these outputs.

## 2. Sources checked

The bounded declaration audit used:

- `QuittingPaidCapLiftedSource.InertStall`,
  `root_eq_allContinue_of_totalAbsorption_eq_zero`,
  `semanticPair_eq_of_totalAbsorption_eq_zero`, and
  `exists_losslessShiftedPaidRow_of_totalAbsorption_eq_zero` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/`
  `PaidCapPortExactTrichotomy.lean`;
- `HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at` and
  `nonempty_actualProfilePaidCapPort` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/`
  `ActualProfileTerminalGapPaidCap.lean`;
- `exists_maximalAbsorption_isZeroQuittingRootNash`,
  `maximalCapPrefix_positivePunishmentCharge_retainingAtom_or_uniqueAllContinue`,
  and
  `maximalCapPrefixPunishmentFloorPrefix_charge_le_semanticBudget` in
  `Research/Quitting/CausalTailEscapeMaxAbsorptionDispatch.lean`;
- the compact-outcome bubble and moving escaping-cap exchange reviewed in
  `feedback/CHATGPT_EXTERNAL__CONCRETE_NONLOCALITY_DERIVATIONS_INTAKE__BY_`
  `TESLA_COMPACT_EXCHANGE.md`;
- the minimum-fiber exact all-Continue tube in
  `UniformEquilibrium/Diagnostics/Quitting/`
  `TerminalSemanticFinFourMinimumFiberIsolation.lean`; and
- the earlier, narrower delay-quotient audit
  `CODEX_MINER__INERT_STALL_NONLOCAL_LITERATURE_QUOTIENT_BOUNDARY.md`.

The checked cap root in the ordinary paid port is an arbitrary selected exact
root.  Therefore selector-independent statements below use the maximal-root
declaration rather than silently reading `InertStall` as uniqueness.  At an
actual minimum-fiber source, positive absorption of *any* exact cap root would
scale the positive debt strictly below `D_*`; hence the exact root
correspondence really is the singleton all-Continue root there.  Off the
minimum fiber, the maximal-root file already supplies the state-changing
charged chronology and its finite semantic budget.

## 3. What deterministic delay genuinely preserves

For every finite `n`, direct prefix recursion gives

```text
Sem(sigma[n]) = Sem(sigma),
B(sigma[n])   = B(sigma).
```

The exact cap-Nash correspondence therefore does not depend on `n`, including
its maximal absorption value.  In the inert/unique arm every exact cap root
remains all Continue.  The paid witnesses, first-disagreement date, and every
finite terminal event are translated by `n`, while their probabilities and
payoff differences are unchanged.

On the one-point compactification of stopping times, the complete stopping
laws of `sigma[n]` converge to all Never.  After the finite outcome
subsequence used by the reviewed compact-bubble theorem, the defect
coordinates are exactly the original terminal outcome masses of `sigma`.
They are actual moving-event limits, not atoms of the all-Never limiting
profile.

For a paid row of gain `gamma`, comparison with Never and the reviewed
escaping-cap identity consequently selects a signed moving collision,
preemption, or all-opponents-Never packet (after a finite label subsequence).
The selected packet is replayed with the same mass and reward difference at
every translated date.  This is genuine chronological provenance.

## 4. The unresolved conversion

The moving packet is a pure-time deviation inside the literal suffix.  It is
not an exact simultaneous product root against `B(sigma)`.  Because both the
tail cap and the exact root correspondence are delay-invariant, translating
the packet cannot turn it into positive maximal root absorption.  At a
minimum-fiber prescribed payoff, the checked open tube also makes all
Continue the unique exact root against the prescribed coordinate.  Thus the
same packet is not an exact floor edge there either.

Switching to the maximal-root chronology handles the only easy alternative:
positive maximal absorption is already legal punishment-floor charge and
retains each fixed suffix atom.  Its total charge is bounded by the source
excess divided by `D_*`; at the minimum it vanishes.  Deterministic delays do
not change this budget.

The one still-live producer test is **block regeneration**.  One would need to
put several translated copies of the suffix packet into one actual product
profile and prove that the resulting block roots are exact (or have aggregate
error tending to zero).  Deterministic translation supplies a common phase
but not repetition; independently mixing a common delay creates cross terms
and loses the retained collision law.  Repeating truncated copies creates an
actual periodic profile, but no checked field makes its block rows Nash
against unrestricted behavioral deviations.  Establishing that exactness,
or showing that its failure lowers `D_*`, would give one of the requested
outputs.  I do not currently have that step.

## 5. Scope

This work log is not a compactification no-go under the full `Fin 4`
terminal-witness/minimum hypotheses.  It uses no `D_*=0` regression and does
not assert that block regeneration is impossible.  It only prevents the
current attempt from conflating:

```text
an actual moving suffix packet
```

with

```text
positive absorption of an exact cap- or punishment-floor root.
```

## 6. Delta: the formalized global inert stack is a depth conjugacy

The subsequently checked structure
`QuittingMinimumLawCausalSuffixInertCapStack` in
`Research/Quitting/CausalTailEscapeMaxAbsorptionDispatch.lean` now packages
the full positive-minimum statement.  Beyond every requested depth it gives
one actual suffix `profile`, an exact root word `roots`, and a positive finite
suffix atom, with

```text
roots = replicate roots.length allContinue,
Sem(Prefix(roots, profile)) = Sem(profile),
Law(Prefix(roots, profile)) = Law(profile),
charge(roots) = 0.
```

This is stronger provenance than was available when Sections 3--5 were
written, but it also makes the direct depth argument completely rigid.  For
each selected suffix, increasing the word length changes only the calendar
location of its events.  It does not change:

- prescribed payoff or unrestricted behavioral cap;
- any coordinate debt, total debt, or positive-debt support;
- the complete terminal outcome law or its finite coalition labels;
- the exact root correspondence at the displayed cap; or
- the coordinatewise inverse-Bellman feasibility system for that cap head.

In particular the positive minimum gives, for every such literal stack
`widehat profile`,

\[
 \operatorname{Expl}(\widehat{\text{profile}})
 \ge \frac{D_*}{|I|}=\frac{D_*}{4}>0.             \tag{6.1}
\]

This is exactly
`minimumTerminalSemanticDebt_div_card_le_terminalExploitability` from
`TerminalSemanticStoppingLawExploitabilityFloor.lean`; no limiting argument
is involved.  Thus the increasingly deep stacks themselves cannot be the
terminal approximate-Nash sequence.  Their cumulative exact charge is
identically zero, and their semantic/support ranks are literally constant,
so neither a charged return nor a rank descent can be read from the word.

There is also no compactness gain from the delay.  The marginal clocks of a
fixed delayed suffix converge to Never on the one-point compactification,
while the checked terminal law stays exactly fixed with its positive finite
atom.  Hence the outcome map is being approached precisely through its
bubble-at-infinity discontinuity.  Passing to the clock limit would erase,
not realize, the retained atom.  Finite-clock compression of the suffix may
approximate its semantic pair, but the error is a function of the suffix
compression and is not improved by adding all-Continue dates in front.

Consequently arbitrary depth is not an additional scalar resource.  Any
successful use of the new object must compare or modify the *different
suffix profiles* selected at different chronology indices.  It must insert
absorption, a reset, or a response inside a suffix while controlling the
resulting full behavioral debt.  Deterministic depth alone cannot do so.

In fact the depth quantifier is logically redundant after one inert source
has been selected.  If every exact cap root at `Sem(profile).2` is all
Continue, then for every `N` the list `replicate N allContinue` is an exact
cap--Nash word over that same `profile`; direct root-prefix recursion gives
all four equalities above and shifts every suffix cylinder by `N`.  Thus the
statement “for every requested depth there is an inert stack” cannot impose
a new compatibility condition across depths unless the theorem additionally
selects one nested family of *modified* suffixes.  The checked structure does
not: its instances at two requested depths may use unrelated chronology
indices, and even a single instance can be delayed again mechanically.

This delta uses the full `D_*>0` premise and rules out the proposed direct
time-translation/compactness consumer.  It is still not a no-go for every
possible comparison between the varying suffixes, and therefore remains an
in-progress boundary rather than an answer to `FIN4_BT_QUESTION.md`.

The remaining bounded construction test is block regeneration: put several
source-matched suffix modifications into one actual product profile and
prove either exactness or vanishing *aggregate* unrestricted error.  A
common deterministic delay supplies no repetition; private independent
delay mixing introduces cross-coalition terms.  No such block consumer is
proved here.
