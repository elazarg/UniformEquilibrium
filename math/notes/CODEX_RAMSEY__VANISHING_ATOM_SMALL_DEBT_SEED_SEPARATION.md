# Vanishing-atom chronology: the actual-endpoint seed separation

Author: `CODEX_RAMSEY`

Status: **complete bounded source/interface audit; sharp negative answer for
the current actual tangent/reset data; internal, no export.**

The missing small-debt seed of the checked budget-stable chronological
compiler cannot be selected from any of the actual positive-minimum tangent,
full-replacement, common-response, or reset-cube endpoints.  Every such
endpoint is an actual terminal semantic pair (or a carrier limit of such
pairs), so its total debt is at least the fixed positive minimum.  Making one
named coordinate small merely forces another coordinate to retain a
scale-free amount of debt.

Nor can one replace the endpoint by an artificial small-debt annotation and
hide the replacement in a summable same-root seam chain.  The checked
actual-versus-candidate comparison then forces

```text
D_* <= 2 * card(I) * eta.
```

Thus at `eta < D_*/(2*card(I))` the desired chain is already contradictory.
The additional datum needed by the chronological route is not another static
atom or another actual reset endpoint.  It must be a nonlocal disjunct which
consumes the surviving terminal discrepancy: a solved game, or a genuine
literal-source change carrying a declared well-founded decrease.  This is
conjecture-facing because it rules out exactly the proposed production of the
open `VANISHING-DEBT-ATOM-ACCESS -> CHRONOLOGICAL-DEBT-SHADOWING` seed; it does
not claim that the whole chronological route is impossible.

## 1. Exact question

Fix a finite nonempty player type `I`, a quitting reward table, and a
`QuittingPositiveMinimumDebtTangentFamily family`.  Write

```text
D_* = quittingTerminalSemanticDebtSum family.base > 0.
```

For a requested `eta>0`, the checked compiler

```text
QuittingBudgetStablePacketSystem
  .exists_chronologicalDebtShadowingCertificate_of_seed
```

requires a port `seed` satisfying, for **every** player,

```text
debt(system.annotation seed)_i <= eta.                 (1.1)
```

The packet system separately requires two fixed distinct actual labels with
block hazard at least `kappa * h`, exact literal-root prefixing inside every
block, a globally bounded candidate family, and endpoint/availability loss
`omega(h)+chi(h)` which is operationally `o(h)`.  Its selected schedule has
divergent total scale and summable total cost.  None of those clock fields
weakens (1.1).

The bounded question is whether (1.1) can be supplied by choosing sufficiently
late actual endpoints from the positive-minimum atom/reset construction,
without declaring their positive semantic-carrier debt to be small.

## 2. What the atom access actually controls

`QuittingVanishingDebtAtomAccess family` fixes a mover, a distinct observer,
and a positive charge.  At every sufficiently late rank it supplies a
`HasQuittingStoppingLawVanishingDebtAtomAlternative` at the literal frontier
source and mover replacement.

That alternative is a disjunction:

1. a prescribed terminal atom, with no debt bound; or
2. a pure-time rectangle atom whose response endpoint has only

   ```text
   endpoint debt(observer) <= decoder error.           (2.1)
   ```

Before the disjunction,
`QuittingStoppingLawCommonResponseWitness.endpointDebt_le` has the same
one-coordinate form.  The full-replacement cluster instead gives

```text
debt(cluster)_mover = 0                                (2.2)
```

by `FullReplacementCluster.mover_debt_eq_zero`.  A support-entry access may
retain one zero-debt recipient at the base.  None of these declarations gives
one co-realized endpoint on which all debt coordinates tend to zero.

The frozen reset cube does not change this accounting fact.  Every face
`(family.frozenSourceResetCubeData rank).profile face` is an ordinary
behavioral profile.  Inserting a reset coordinate is a literal stopping-law
reset by `QuittingStoppingLawResetCubeData.profile_insert_eq_reset_of_not_mem`,
but it remains an actual profile rather than an artificial candidate
annotation.

## 3. Actual-endpoint seed barrier

### Proposition 3.1 (actual selection cannot seed)

Let `sigma` be any behavioral profile.  Then

```text
D_* <= sum_i debt(Sem(sigma))_i.                       (3.1)
```

Consequently, if `eta < D_*/card(I)`, it is impossible that

```text
debt(Sem(sigma))_i <= eta  for every i.                (3.2)
```

The same conclusion holds for every carrier limit of actual endpoints.

### Proof

`quittingTerminalSemanticPair_mem_carrier reward sigma` puts `Sem(sigma)` in
the terminal semantic carrier.  Apply `family.base_minimum`.  Carrier debts
are nonnegative.  If (3.2) held, summing it would give

```text
D_* <= sum_i debt(Sem(sigma))_i <= card(I)*eta < D_*,
```

a contradiction.  A carrier limit is covered directly by its carrier
membership.  This is also the content of
`not_forall_quittingTerminalSemanticDebt_le_of_lt_average` and its tangent-
family specialization `not_baseDebt_le_of_lt_average` in
`PositiveMinimumSeedSeamBarrier.lean`.

### Corollary 3.2 (one-coordinate repair only relocates the debt)

Suppose an actual endpoint `sigma` obeys (2.1) with error `e`.  Then

```text
sum_{i != observer} debt(Sem(sigma))_i >= D_* - e.     (3.3)
```

Since the atom access has `observer != mover`, the player type has at least
two elements.  Hence some other player has debt at least

```text
(D_* - e)/(card(I)-1).                                (3.4)
```

when the numerator is positive.  In particular the right side does not tend
to zero when the decoder error does.  The analogous full-replacement statement
uses (2.2) with `e=0`.  Even if two distinct zero/small coordinates could be
made co-realized, an actual endpoint would still have total debt at least
`D_*`; in `Fin 4` one of the two remaining coordinates would carry at least
half of the residual total debt.

This explains why cycling the selected label or taking a later frontier rank
does not produce (1.1).  Low-debt coordinates obtained at different actual
profiles cannot be pasted coordinatewise into one semantic pair, and any
finite sequence of actual reset operations still ends at a profile subject to
(3.1).

## 4. Artificial seeds and the same-root seam obstruction

The compiler permits `system.annotation seed` to be artificial.  That typing
freedom alone is insufficient.

Let `chain : QuittingBoundedSeamChain reward` be the flattened chain on its
literal root schedule.  Its candidates and successors may be arbitrary
semantic-pair annotations, but they satisfy exact prefix recursion.  Assume:

- prescribed and cap seam streams are summable in every coordinate;
- joint survival tends to zero;
- every player-deleted survival tends to zero;
- the initial candidate debt is at most `eta` in every coordinate; and
- prescribed plus cap seam `tsum` is at most `eta` in every coordinate.

The checked theorem

```text
QuittingBoundedSeamChain.actualDebtGap_le_candidate_add_seams
```

compares the artificial initial candidate with the unrestricted terminal
semantic pair of the **same literal infinite root profile**.  Applying (3.1)
to that actual profile gives

```text
D_* <= sum_i [candidateDebt(0,i)
              + prescribedSeamTsum(i) + capSeamTsum(i)].   (4.1)
```

Its quantitative corollary

```text
QuittingBoundedSeamChain.actualDebtGap_le_two_mul_card_eta
```

therefore gives

```text
D_* <= 2 * card(I) * eta.                              (4.2)
```

For `eta < D_*/(2*card(I))`, no such same-root artificial chain exists.  This
argument uses unrestricted behavioral caps in the `actualPair`; an extra
semantic-closeness declaration between the actual port and the artificial
anchor cannot evade it.

`exists_summableSeamSource_of_seed` assembles precisely these hypotheses from
the budget-stable packet system: the divergent-scale schedule plus the two
fixed `kappa*h` hazards give joint and every deleted-player survival, while
the summable `omega+chi` budget gives the seam bounds.  Thus the clock scale
and decoder scale cannot be traded against the fixed minimum:

The packaged source stores summability and a `tsum` bound for
`totalSeam = prescribedSeam + capSeam`, rather than storing the cap stream
separately.  Nonnegativity of both absolute-value seams recovers cap
summability, and the `totalSeam` identity makes its `tsum` exactly the
prescribed-plus-cap term in (4.1).  There is no extra factor at this handoff.

```text
sum h_n = infinity,      sum (omega(h_n)+chi(h_n)) < infinity,
decoderError(rank) -> 0
```

still leaves the scale-free lower bound (4.2).  The decoder error concerns one
observer endpoint; it is not the all-coordinate initial debt in (1.1).

## 5. The sharp additional datum

There is no missing *local actual-endpoint selector*.  Propositions 3.1 and
3.2 rule out that interface.  There is also no missing *summable same-root
implementation seam*: (4.2) rules it out at sufficiently small accuracy in
the positive-minimum branch.

For a finite artificial block the comparison retains a terminal term rather
than contradicting positive minimum.  In the notation of the finite seam
iteration, small initial candidate debt and small accumulated seams force a
survival-weighted terminal prescribed/cap discrepancy of total size at least

```text
D_* - 2 * card(I) * eta.                              (5.1)
```

This is the finite boundary recorded in Section 6BH of
[`CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md`](CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md).
Vanishing joint and deleted-player survival are exactly what erase (5.1) in
the infinite chain and create (4.2).

Therefore a conjecture-facing producer must add one of the following data:

1. a solved-game or terminal-approximate-Nash disjunct before the infinite
   same-root chain is formed; or
2. a finite source-changing adapter which exports the discrepancy (5.1) to a
   genuinely different literal source and proves a strict decrease of a
   declared well-founded rank/debt invariant.

Merely adding more atom labels, reset faces, or one-coordinate vanishing-debt
endpoints does not supply either datum.  This is the exact seed seam: current
actual tangent/reset data stop on the source side of (5.1).

## 6. Declaration and file audit

The bounded audit inspected the following declarations in place.

- `QuittingChronologicalDebtData` and
  `QuittingChronologicalDebtShadowingCertificate.initial_debt_le` in
  `UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`.
- `QuittingBudgetStablePacketData`, `QuittingBudgetStablePacketSystem`,
  `exists_summableSeamSource_of_seed`, and
  `exists_chronologicalDebtShadowingCertificate_of_seed` in
  `UniformEquilibrium/Quitting/Debt/Dynamic/BudgetStableCompatiblePacketIteration.lean`.
- `QuittingBoundedSeamChain.actualDebtGap_le_candidate_add_seams` and
  `actualDebtGap_le_two_mul_card_eta` in
  `UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalSeamReduction.lean`.
- `QuittingVanishingDebtAtomAccess`,
  `nonempty_vanishingDebtAtomAccess`,
  `exists_vanishingDebtAtomAccess_of_supportEntry`, and
  `VanishingDebtAtomChronologicalConsumer` in
  `UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`.
- `HasQuittingStoppingLawVanishingDebtAtomAlternative`,
  `QuittingStoppingLawCommonResponseWitness.endpointDebt_le`, and
  `exists_endpointGainAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`.
- `FullReplacementCluster.mover_debt_eq_zero` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/MinimumFiberSupportDrop.lean`.
- `QuittingStoppingLawResetCubeData.profile_insert_eq_reset_of_not_mem` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawResetCube.lean`,
  and `frozenSourceResetCubeData` in
  `UniformEquilibrium/Diagnostics/Quitting/Frozen/ResetCube.lean`.
- `not_forall_quittingTerminalSemanticDebt_le_of_lt_average`,
  `exists_directSemanticSeam_ge_average_sub`, and
  `exists_totalBlockSeamNat_ge_average_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/PositiveMinimumSeedSeamBarrier.lean`.

The existing conference comparison was deliberately limited to the relevant
parts of:

- [`CODEX_CEDAR__VANISHING_ATOM_CHRONOLOGY.md`](CODEX_CEDAR__VANISHING_ATOM_CHRONOLOGY.md),
- [`CODEX_EULER__COMPATIBLE_PACKET_ITERATION.md`](CODEX_EULER__COMPATIBLE_PACKET_ITERATION.md), and
- [`CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md`](CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md),
  especially Sections 6BG--6BH.

`docs/FRONTIER.md` and `docs/TOOLKIT.md` already identify the external seed as
open and warn that a positive-minimum actual port cannot supply it.  The
present note adds only the exact specialization to the whole family of actual
tangent/reset endpoints and the quantitative relocation statement (3.3)--
(3.4).  The stronger same-root chain obstruction is already a checked theorem,
so this note is not an export candidate and makes no new Lean claim.

## 7. Requested independent check

Please check two points:

1. that every endpoint class named in Section 3 is indeed either an actual
   behavioral semantic pair or a member of the terminal semantic carrier; and
2. that the flattened output of `exists_summableSeamSource_of_seed` matches the
   prescribed-plus-cap seam convention used in (4.1), with no missing factor.

No review of the already checked probability theorem is requested.
