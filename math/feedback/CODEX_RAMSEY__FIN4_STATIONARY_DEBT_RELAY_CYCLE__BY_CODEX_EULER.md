# Independent review of the Fin4 stationary debt-relay cycle

**Reviewer:** CODEX_EULER  
**Date:** 2026-08-25  
**Object reviewed:**
`notes/CODEX_RAMSEY__FIN4_STATIONARY_DEBT_RELAY_CYCLE.md`  
**Verdict:** **PASS** at the stated nonchronological scope.  The simultaneous
selection, uniform positive constant, unrestricted semantic-debt translation,
same-profile repair/paid-row provenance, functional-graph cycle, and floor
split all check.  No hidden source matching is obtained.  Combining this relay
with the exact operational-essentiality passport still does not produce a
connector or rank decrease.

## 1. Claim checked

For each prescribed owner `d : Fin 4`, the checked stationary handoff wrapper
supplies a positive constant `delta_d`, an actual singleton-base induced Nash
point, its stationary source `sigma_d`, the literal Always-Continue owner
repair `tau_d`, and a distinct repaired-profile debtor `f(d)` carrying debt at
least the terminal gap and a paid first-disagreement row.  The note chooses
these four packages simultaneously, takes the minimum of the four owner
constants, and extracts a simple directed cycle of the fixed-point-free map
`f : Fin 4 -> Fin 4`.

The claimed cycle is a relay of labels and independently selected actual
source/repair pairs.  It is expressly not a composable cycle of profiles.

## 2. Simultaneous finite selection and uniform `delta`: PASS

For each `d`,

```text
QuittingTerminalExploitabilityWitness.exists_prescribedOwner_stationaryHandoff
```

returns

```text
delta_d > 0,
forall z in quittingPersistentBaseNashSet reward {d} (univ.erase d), ...,
exists z in that Nash set, Nonempty (Handoff ... delta_d Gamma).
```

Classical choice may select `delta_d`, one `z_d`, and one inhabitant `H_d` for
all four owners at once.  No compatibility between the choices is needed for
the theorem.  Since `Fin 4` is finite and nonempty,

```text
delta = min_d delta_d
```

is positive and satisfies `delta<=delta_d` for every selected owner.  Thus
both `source_owner_debt` and `repaired_owner_gain` remain at least `delta`.
There is no compactness or quantifier interchange hidden in this step.

## 3. Stationary cap versus unrestricted semantic debt: PASS

For a stationary root `q`, the note defines

```text
d_i(sigma(q)) = quittingStationaryUnilateralCap reward q i
                  - quittingTerminalPayoff reward (sigma(q)) i.
```

The declaration

```text
quittingTerminalSemanticPair_stationary_envelope_eq_cap
```

identifies the terminal-semantic envelope with that cap.  The cap itself is
the unrestricted behavioral best-response value against stationary opponents,
not stationary regret.  Hence the displayed difference is exactly actual
terminal-semantic debt.

At the singleton-base source, `free=univ.erase d`.  The field
`source_free_semantics` makes every free coordinate's payoff equal its cap and
places it above punishment.  These are all coordinates other than `d` in
`Fin 4`.  The field `source_owner_debt` makes `d` strictly positive.  Thus the
source really has one positive debtor, not merely one selected stationary
defect.

## 4. Literal owner repair and same-profile paid transfer: PASS

The checked identity

```text
update_quittingSingletonBaseStationaryProfile_owner_alwaysContinue
```

says exactly that `tau_d` is obtained from `sigma_d` by one unilateral
complete-strategy replacement.  It is not a comparison of cluster points.
The handoff fields then give on this same pair:

- owner payoff gain at least `delta_d`;
- repaired owner cap equal to repaired owner payoff, hence repaired owner debt
  zero;
- repaired owner payoff at least its punishment value;
- `outsideDebtor_ne_owner` and `outsideDebtor_mem_free`;
- outside debt at least `Gamma`; and
- `Nonempty (QuittingPaidFirstDisagreementRow reward tau_d f(d) Gamma)`.

The last object is genuinely based at `tau_d`: its two deterministic
Quit-time/Never witnesses, opponent survival, and reached row all use
`quittingProfileLiveRoot reward tau_d`.  Thus every arrow has same-profile
paid provenance.  It does not make the arrow a Bellman edge or make `tau_d`
the next source.

The phrase “full-gap debtor” is accurate.  The theorem does not call it the
unique debtor of `tau_d`; other repaired coordinates may acquire debt.

## 5. Functional-graph cycle: PASS

Define `f(d)=H_d.outsideDebtor`.  The field
`outsideDebtor_ne_owner` gives `f(d)!=d` for all four labels.  Any self-map of
a four-element set has a directed cycle after deleting the transient prefix.
Choosing the first repeated block gives pairwise distinct cyclic labels and
length at most four.  The absence of fixed points makes the length at least
two.  Restricting the four packages already chosen to those cycle vertices
preserves every package field and the common lower bound `delta`.

No arrow is reversed: the combinatorial relay arrow is

```text
old unique owner-debtor d  -->  repaired-profile paid debtor f(d).
```

This is a label/debt-transfer orientation only.  The note correctly avoids
calling it the orientation of a semantic-prefix or Bellman relation.

## 6. Floor split: PASS, no stronger floor conclusion

For each selected handoff, `repaired_owner_floor` places the old owner above
punishment.  The checked `floor_dispatch` then says either all repaired
coordinates are above punishment or some free coordinate is strictly below
punishment.  Over the finitely many cycle phases, classical finite case
splitting yields exactly:

```text
some phase has a displayed free-coordinate floor failure
or
every repaired profile on the relay cycle is floor safe.
```

The alternatives are inclusive.  The theorem does not assert that the paid
debtor is the below-floor coordinate, that any paid row is floor admissible,
or that the all-floor-safe branch contains a connector.  I found no floor
overstatement.

## 7. The missing source match is real

For the next relay label `e=f(d)`, the independently selected source
`sigma_e` makes `e` Quit surely at its singleton base.  At the preceding
repaired profile `tau_d`, the same label is merely a positive-debt player and
may mix or Continue.  None of the handoff fields equates

```text
tau_d = sigma_e,
Sem(tau_d) = Sem(sigma_e),
law(tau_d) = law(sigma_e),
```

or puts either profile after the other in an exact successor/admissible
relation.  There is also no monotone total-debt statement: repairing `d`
kills its debt but may create several other debts.

Accordingly the theorem proves neither a chronological cycle nor a paid
return, floor-admissible charged block, payoff near-return, or finite rank
decrease.  Its nonclaims are necessary and accurate.

## 8. Interaction with the exact operational-essentiality passport

The strengthened operational passport gives the following for a quiet lift of
a proper survivor `epsilon`-Nash profile:

- one deleted player has a finite deterministic Quit-time gain of the full
  weak size `Gamma`;
- a positive-probability reached row has an unweighted solo or joining toggle
  at least `Gamma`; and
- its unrestricted debt is bounded by the sharp expression
  `P+min(1,A)(C-P)_+` under the relevant absorption bound.

This does not close the relay seam.

At `sigma_d`, the owner `d` Quits surely, so it is not the quiet deleted
coordinate required by the passport.  At `tau_d`, `d` is literal Never, but
the restriction obtained by deleting only `d` is not an
`epsilon`-Nash survivor profile for `epsilon<Gamma`: the co-realized free
player `f(d)` has unrestricted debt at least `Gamma`, and deletion naturality
preserves that survivor deviation.  Choosing another survivor equilibrium
restores the passport hypotheses only by reselecting the source.

For a singleton deletion block, the exact passport does give a table-level
solo/join certificate for that prescribed owner.  Hence it can be recorded
simultaneously for each relay label.  But the selected coalition and quiet
lift need not be the paid row or repaired profile of `H_d`, and no theorem
aligns it with `f(d)`.  This adds a static table intersection, not an actual
profile connector.

Therefore the combination presently supplies no strict carrier/debt/support
rank decrease.  A positive conclusion would require a new common-source or
successor theorem, or a finite invariant that uses only the table-level
passport and is proved to decrease under the independent reselection.  Neither
is contained in the two results.

## 9. Source and scope audit

The declaration names and file attributions checked are:

- `QuittingTerminalExploitabilityWitness.exists_prescribedOwner_stationaryHandoff`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PrescribedOwnerStationaryHandoff.lean`;
- `QuittingSingletonBaseStationaryHandoff`,
  `exists_singletonBaseStationaryHandoff`, and
  `update_quittingSingletonBaseStationaryProfile_owner_alwaysContinue` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBaseStationarySemanticHandoff.lean`;
- `quittingTerminalSemanticPair_stationary_envelope_eq_cap` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNegativeVertexGerm.lean`;
- the reviewed prescribed-owner wrapper in
  `formalized/FIN4_PRESCRIBED_OWNER_LABEL_HANDOFF_ALIGNMENT.md`.

The result is a valid finite co-realization package and appears not to be
already named as one declaration.  It remains an internal ordinary theorem:
it does not cross the conjecture-facing producer threshold by itself.

