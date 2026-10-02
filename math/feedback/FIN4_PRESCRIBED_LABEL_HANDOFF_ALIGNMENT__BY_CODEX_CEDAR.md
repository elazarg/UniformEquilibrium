# Source and novelty audit of Fin4 prescribed-label handoff alignment

Reviewer: `CODEX_CEDAR`

Source reviewed:
[`FIN4_PRESCRIBED_OWNER_LABEL_HANDOFF_ALIGNMENT.md`](../exports/FIN4_PRESCRIBED_OWNER_LABEL_HANDOFF_ALIGNMENT.md).

## Verdict

**PASS as an internal mathematical synthesis, with one export-facing wording
repair.  Do not describe the packet as aligning a prescribed label without
qualifying that it aligns only the reset/repair owner coordinate.**

The two component theorems have already received independent ordinary-math
reviews.  I found no checked Lean declaration that states either wrapper in
the exact form used here.  The checked-source situation is nevertheless quite
different for the two wrappers:

- Theorem A contains a real reviewed adapter not already packaged in Lean:
  from an arbitrarily selected positive minimum debtor on literal `Fin 4`, it
  chooses a sure pair base, obtains a complete stationary law with zero debtor
  debt and unit marked incidence, and feeds that law to the checked fixed-law
  dispatcher.
- Theorem B is almost exactly a two-declaration composition.  The uniform
  positive gap over every point and the pointwise stationary handoff are
  already checked separately.  The new wrapper merely places their quantifiers
  together for an owner chosen in advance and invokes nonemptiness when an
  actual stationary point is wanted.

Choosing `d=e` therefore removes exactly one mismatch: the reset owner in
Theorem A and the repaired singleton owner in Theorem B can be the same
preselected positive minimum debtor.  It does not create a common source,
law, observer, carrier point, root, payoff, Bellman edge, or chronology.

## Exact checked-source correspondence

### Theorem A: checked ingredients, but no checked wrapper

The persistent-base construction is supported by

- `quittingPersistentBaseNashSet_nonempty`; and
- `quittingPersistentBaseRoot_free_purePayoff_le`

in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`.
These declarations supply the induced Nash point and its pure endpoint
inequalities.  The fact that two distinct base players Quit surely is what
upgrades those inequalities to the full unrestricted cap for the two free
players in the special pair-base profile; that `Fin 4` adapter is ordinary
mathematics in Section 20, not a named checked theorem.

The semantic/law identifications used by the adapter are supported by

- `quittingTerminalSemanticPair_stationary_envelope_eq_cap` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNegativeVertexGerm.lean`;
- `quittingTerminalSemanticLawPoint_mem_carrier`;
- `quittingTerminalSemanticLawPrefix_mem_carrier`;
- `quittingTerminalOpponentIncidenceMass_lawPrefix`; and
- `positive_incidence_lawPrefix_of_positive_continueMass`

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`.
The definition of the displayed incidence is
`quittingTerminalOpponentIncidenceMass` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDebtTransfer.lean`.
These sources do not themselves state that the particular pair-base law has
unit `(e,b)` incidence; that calculation is the reviewed finite adapter.

The dynamic conclusion is already checked as

- `QuittingFixedLawResetDispatch`;
- `QuittingTerminalExploitabilityWitness.exists_fixedLaw_resetFace_dispatch`;
  and
- `QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch`

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`.
Its underlying dynamic alternative is
`resetExcursion_absorbingReturn_or_allContinue_capFace` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetExcursionReturn.lean`.
The reset-face minimization underneath it is
`exists_fixedLaw_resetFace_minimizer` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`.

The floor propagation and relation orientation are supported by

- `quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorForward.lean`;
  and
- `QuittingPunishmentFloorAdmissibleEdge.ofExactEdge` together with
  `quittingPunishmentFloorAdmissibleChargedRelation` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`.

Thus the checked relation has `src=edge.tail` and `tgt=edge.current`, exactly
as the packet writes `R.2 -> W`.  None of these declarations identifies `W`
with the cap of the semantic prefix `R'`.

Finally, the no-uniform `Fin 4` actual-data source for a positive global
minimum is explicitly checked as
`exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`.

I found no declaration in `UniformEquilibrium/` or `MathUE/` whose conclusion
already packages all of the following at once: arbitrary chosen positive
minimum debtor, complementary sure pair base, zero-debt complete-law target,
unit displayed incidence, and the fixed-law dispatch.  Theorem A is therefore
not a duplicate of a named checked wrapper.  Its new content is exactly the
pair-base source adapter; most subsequent dynamics are the existing checked
dispatcher.

### Theorem B: checked primitives and a new quantifier wrapper

The essential conclusions are already checked in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBaseStationarySemanticHandoff.lean`:

- `QuittingTerminalExploitabilityWitness.exists_pos_ownerFloorExcess_gap`
  accepts an arbitrary `owner`, the equality
  `free=Finset.univ.erase owner`, and returns one `delta>0` valid for every
  point of the induced Nash carrier;
- `QuittingSingletonBaseStationaryHandoff` records the unrestricted free
  semantics, owner repair, returned outside debtor, floor disjunction, and
  literal paid row; and
- `exists_singletonBaseStationaryHandoff` constructs that structure for each
  supplied point and positive owner-floor gap.

Together with `quittingPersistentBaseNashSet_nonempty` from
`PersistentBaseInducedGame.lean`, these declarations prove the quantified
wrapper in Theorem B directly.  I found no single checked declaration with
the exact outer form

```text
forall d, exists delta>0, forall z in Nash({d},univ.erase d),
  Nonempty (QuittingSingletonBaseStationaryHandoff ...).
```

There is a related checked actual-data theorem,
`QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle.exists_largeBasePaidStationaryHandoff`,
in `LargeBaseStationarySemanticHandoff.lean`.  It aligns the owner selected by
a supplied large-base paid-chain residual and is the declaration already
listed in `docs/FRONTIER.md`, `docs/STATUS.md`, and `docs/TOOLKIT.md`.  It does
not quantify over an arbitrary prescribed owner and does not subsume the
minimum-debtor choice used in Theorem A.  Conversely, Theorem B does not
provide the large-base residual's source provenance.

Theorem B is consequently valid and not literally a duplicate declaration,
but its mathematical novelty is only quantifier packaging and owner
preselection over already checked components.

## What the combined packet does and does not align

On the same reward table, fix a positive minimum debtor `e` in Theorem A and
instantiate Theorem B with `d=e`.  This proves only

```text
Theorem-A reset owner = Theorem-B repaired singleton owner.
```

The constructions remain independent reselections.  In particular, the
packet does **not** identify or prescribe any of the following:

- Theorem A's marked incidence label `b` and Theorem B's returned observer
  `j_e`;
- the pair-base induced Nash point and the singleton-base induced Nash point;
- the complete law `lambda`, its supported toggle, or its atom with the paid
  row decoded in Theorem B;
- Theorem A's target `T`, returned reset point `R`, cap tail `R.2`, semantic
  prefix `R'`, or payoff successor `W` with either stationary profile in
  Theorem B;
- floor safety, since Theorem B retains a free-coordinate floor-damage arm;
- a behavioral reach relation, source-matched connector, exact Bellman path,
  debt repayment, payoff near-return, or common uniform payoff.

Applying Theorem B for all four owners gives four unrelated same-table
stationary selections.  Finiteness of the resulting owner/observer choices is
not a path or regenerative transition system.

The sentence in the current `Conjecture-facing change` section saying that
the remaining obstruction is "semantic, not finite incidence" is therefore
too broad: the observer/incidence label is itself still unaligned.  Replace it
by wording such as:

> The equality of the reset-owner and repaired-owner labels is no longer an
> obstruction.  Common-source, common-law, observer/incidence, floor, and
> Bellman/chronological alignment all remain open.

For the same reason, any title or abstract should say
"prescribed-owner-label alignment" rather than unqualified
"prescribed-label alignment."

## Export boundary

The packet may honestly claim an ordinary-mathematical (`M`) alignment
wrapper over named checked ingredients.  It may not claim that either wrapper
itself is Lean checked, and it should not attach an `L`, `A`, or `C` status to
the wrapper.  The two Section reviews establish the ordinary mathematics, not
a new declaration.

Under the default criteria in [`exports/README.md`](../exports/README.md), the
combined observation does not by itself add a downstream semantic consumer or
strictly close the live paid-return obligation.  Theorem A already had its
own reviewed reset-wall narrowing, and Theorem B already had its reviewed
owner-preselection conclusion; choosing `d=e` adds no common semantic object.
Accordingly the conservative gate is:

- keep this synthesis in `notes/` unless a maintained question explicitly
  accepts removal of this precise owner-coordinate mismatch as an alignment
  output; or
- if such an accepted alignment category authorizes export, state the new
  content only as the equality of the two owner labels, cite both component
  reviews, and retain all of the nonclaims above.

Export wording should avoid `source-aligned`, `law-aligned`, `paid-row
aligned`, `observer-aligned`, `chronological handoff`, `connector`, or
`fixed-label paid observer`.  Accurate short wording is:

> For any selected positive minimum debtor in a no-uniform `Fin 4` table, one
> may independently construct (i) a pair-base unit-incidence fixed-law reset
> dispatch using that player as reset owner and (ii) a singleton-base paid
> handoff using the same player as repaired owner.  These are parallel
> same-table reselections; only the owner coordinate is aligned.

With that wording repair, I found no source or novelty objection to retaining
the note as an exact internal alignment record.
