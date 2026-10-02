# Fin4 prescribed-owner-label handoff alignment

Author: `CODEX_EULER`

Independent reviews:

- [Section 20 review by CODEX_RAMSEY](../feedback/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY__BY_CODEX_RAMSEY__SECTION_20.md): **PASS** for the minimum-debtor fixed-law reset theorem.
- [Section 22 review by CODEX_RAMSEY](../feedback/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY__BY_CODEX_RAMSEY__SECTION_22.md): **PASS** for the universal preselected-owner composition, with the explicit nonemptiness step incorporated below.
- [Source and novelty audit by CODEX_CEDAR](../feedback/FIN4_PRESCRIBED_LABEL_HANDOFF_ALIGNMENT__BY_CODEX_CEDAR.md): **PASS** after narrowing every alignment claim to the owner coordinate.
- [Whole-packet gate by CODEX_RAMSEY](../feedback/FIN4_PRESCRIBED_LABEL_HANDOFF_ALIGNMENT__BY_CODEX_RAMSEY__PACKET_GATE.md): **REVISE, then PASS** after four literal packet edits incorporated here.

## Exact statement

Let `I=Fin 4`, let

```text
reward : {S : Finset I // S.Nonempty} -> (I -> R)
```

be a quitting reward table, and suppose

```text
witness : QuittingTerminalExploitabilityWitness reward.
```

For a terminal-semantic pair `X=(U,B)`, write

```text
d_i(X)=B_i-U_i,       D(X)=sum_i d_i(X).
```

The packet has two parallel prescribed-owner-label outputs on this same
table.

### Theorem A: any chosen minimum debtor has a unit-incidence fixed-law reset dispatch

Assume `X_*` belongs to `quittingTerminalSemanticCarrier reward`, globally
minimizes `D` on that carrier, and has `D(X_*)>0`.  Choose any player `e` with
`d_e(X_*)>0`.  Choose the remaining labels `b,c,f` so that
`e,b,c,f` are pairwise distinct, and set

```text
base={b,c},       free={e,f}.
```

For any exact mixed Nash point `z` of the persistent-base induced game on
`free`, let `sigma` be its ambient stationary profile, and let

```text
T      = quittingTerminalSemanticPair reward sigma,
lambda = quittingTerminalOutcomeMass reward sigma.
```

Then

```text
(T,lambda) belongs to quittingTerminalSemanticLawCarrier reward,
d_e(T)=0,
quittingTerminalOpponentIncidenceMass e b lambda=1.       (A1)
```

There is a returned semantic pair `R` for which

```text
(R,lambda) belongs to quittingTerminalSemanticLawCarrier reward,
d_e(R)=0,
D(X_*) <= D(R) <= D(T),                                  (A2)

d_e(X_*) <= sum_(h != e) (d_h(R)-d_h(X_*)).              (A3)
```

The unchanged law `lambda` has a positive-mass terminal coalition containing
`b` and carrying a strict membership toggle supplied by `witness`.  Moreover,
the following inclusive disjunction holds.

1. There is an exact product root `q` at the cap tail `R.2` with positive
   absorption and positive joint Continue mass such that

   ```text
   R' = quittingTerminalSemanticPrefix reward q R,
   D(R')<D(R),       d_e(R')=0,
   (R',quittingTerminalOutcomeLawPrefix q lambda)
      belongs to the semantic/law carrier,
   ```

   and the prefixed law retains positive `(e,b)` incidence.  Separately, the
   same root defines the exact punishment-floor Bellman edge

   ```text
   R.2 -> W,       W=quittingRootSuccessorPayoff reward R.2 q.   (A4)
   ```

2. The all-Continue root is exact at `R.2` and its semantic prefix fixes `R`.
   The complete law, unit-incidence provenance before reset, retained positive
   incidence, transfer inequality, and supported strict toggle remain.

The semantic prefix `R'` and the payoff-only successor annotation `W` are not
identified.  Relation orientation in (A4) is tail-to-current; executable
chronology reads the row from current `W` to continuation tail `R.2`.

### Theorem B: any preselected owner has a stationary paid handoff

For every preselected player `d`, put `F_d=Finset.univ.erase d`.  There is a
number `delta_d>0` such that every

```text
z in quittingPersistentBaseNashSet reward {d} F_d
```

satisfies

```text
delta_d <= quittingSingletonBaseOwnerFloorExcess
  reward d (quittingPersistentBaseRoot {d} F_d z),          (B1)
```

and returns

```text
Nonempty (QuittingSingletonBaseStationaryHandoff
  reward d F_d z delta_d witness.terminalGap).              (B2)
```

Thus the sure-`d` source solves all three free coordinates against unrestricted
behavioral deviations and lies above their punishment floors, while `d` has
debt at least `delta_d`.  Replacing `d` by Always Continue attains its old cap
and yields a source-matched paid first-disagreement row of gain
`witness.terminalGap`, observed by some `j_d in F_d`.  The repaired profile is
either floor safe in every coordinate or has an explicit free coordinate
below punishment.

The owner `d` may therefore be chosen to equal any same-table label already
selected elsewhere: a minimum debtor, collision owner or collider, hard-pair
member, or hard-triple outsider.  The observer `j_d` is returned, not chosen.
Since
`quittingPersistentBaseNashSet reward {d} F_d` is nonempty, one may select
`z` and obtain an actual stationary source for each chosen `d`; the pointwise
quantifier alone is not being used as an existence assertion.

## Definitions and behavioral semantics

The persistent-base root makes every member of `base` Quit surely, mixes the
players in `free` according to the finite induced Nash point, and makes all
other players Continue.  Its stationary behavioral profile repeats that row.
Terminal-semantic pairs use the actual prescribed infinite-horizon payoff `U`
and the full unrestricted behavioral best-response envelope `B`; debt is
`B-U`, not stationary regret.

For Theorem A, both `b` and `c` Quit surely at date zero.  Hence every
unilateral behavioral deviation of `e` or `f` is resolved at date zero and is
equivalent to choosing the initial Quit/Continue mixture.  The induced Nash
inequalities therefore attain the true unrestricted caps for the two free
players.  Every terminal realization contains `b,c`, so absorption is sure
and `(e,b)` opponent incidence is literally one.

For Theorem B, the sure owner similarly resolves all three free players'
deviations at date zero.  The owner repair is an actual unilateral behavioral
strategy replacement by Always Continue.  The paid-row decoder compares two
deterministic pure stopping times against the same prescribed opponents; it
does not truncate the deviator class used in the cap.

Private behavioral randomization, simultaneous Quit, and arbitrary
history-dependent unilateral deviations are retained.  No public correlation
or stationary-only deviation bound is introduced.

## Proof

### Proof of Theorem A

The set `quittingPersistentBaseNashSet reward {b,c} {e,f}` is nonempty by
`quittingPersistentBaseNashSet_nonempty`.  Choose `z` from it and form the
literal stationary profile above.  Because `b,c` Quit surely, the checked pure
Quit and Continue inequalities at the induced Nash point are the full
behavioral-cap inequalities.  Thus both free coordinates have debt zero; in
particular `d_e(T)=0`.  The actual semantic pair and terminal law belong to
the joint carrier by the literal profile adapter.

Every terminal coalition contains `b`, has probability total one, and
`b!=e`.  Expanding `quittingTerminalOpponentIncidenceMass` gives (A1).

Apply

```text
QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch
```

to source `X_*`, target `T`, law `lambda`, reset owner `e`, and incidence
label `b`.  Global minimality, positive `D(X_*)`, joint-carrier membership,
`d_e(T)=0`, and positive incidence are exactly its hypotheses.  Its returned
`QuittingFixedLawResetDispatch` gives (A2)--(A3), the supported strict toggle,
and the two dynamic arms.

In the absorbing arm, the dispatch itself supplies the strict literal
semantic-prefix contraction and retained prefixed law/incidence.  Exact root
Nash at cap tail `R.2` separately gives `W` in (A4).  Since a carrier cap is
bounded and dominates punishment, the checked exact successor-floor
inequality keeps `W` in the bounded floor-admissible state space.  Nothing in
the dispatch equates this prescribed successor with the best-response cap of
the semantic prefix, so no such equality is used.  The all-Continue arm is
the other field of the same checked dispatch.

### Proof of Theorem B

Fix `d`.  Apply

```text
QuittingTerminalExploitabilityWitness.exists_pos_ownerFloorExcess_gap
```

with owner `d` and free set `F_d=univ.erase d`.  If a point of the compact
induced Nash carrier had nonpositive owner-floor excess, the checked
singleton-base all-behavior certificate would already give a uniform-
equilibrium payoff, contradicting the terminal witness.  Compactness and
continuity therefore give one uniform `delta_d>0` and (B1).

For every induced Nash point `z`, apply

```text
exists_singletonBaseStationaryHandoff
```

with the complement identity, `witness`, `delta_d>0`, and (B1).  Its returned
structure gives (B2), all unrestricted source semantics, the owner repair,
the free observer distinct from `d`, the terminal-gap paid row, and the exact
floor disjunction.  Finally invoke
`quittingPersistentBaseNashSet_nonempty reward {d} F_d` and choose one such
`z` whenever an actual stationary source, rather than the stronger pointwise
statement, is required.

The two proofs are independent same-table selections.  Theorem B is not used
to manufacture the law or returned point in Theorem A.

## Conjecture-facing change

The maintained full-support/full-normal Fin4 residual contains several
independently selected labels: minimum debtors, collision owners/colliders,
and hard-principal labels.  These theorems remove two label-selection losses:

- any chosen positive minimum debtor can be the reset coordinate of a
  complete unit-incidence fixed-law dispatch; and
- any chosen label can be the repaired owner of an actual stationary paid
  handoff.

Theorem A narrows failed absorbing selection to the exact all-Continue
fixed-law reset wall.  Theorem B shows that mismatch between the reset owner
and repaired singleton owner cannot explain failure of a paid-source
connector.  Common-source, common-law, observer/incidence, floor, and
Bellman/chronological alignment all remain open.

## Source correspondence and subsumption audit

Checked sources:

- `quittingPersistentBaseNashSet_nonempty` and the induced Nash endpoint
  inequalities in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`;
- `QuittingFixedLawResetDispatch` and
  `QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`;
- `QuittingTerminalExploitabilityWitness.exists_pos_ownerFloorExcess_gap`,
  `QuittingSingletonBaseStationaryHandoff`, and
  `exists_singletonBaseStationaryHandoff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBaseStationarySemanticHandoff.lean`;
- the checked exact floor-admissible charged-relation orientation in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`; and
- `exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`,
  which supplies the positive minimum source in the no-uniform Fin4 residual.

Most dynamic content of Theorem A is already the checked fixed-law dispatcher;
the new adapter is the arbitrary chosen-debtor pair-base target with unit
incidence.  Most stationary content of Theorem B is already the checked
singleton-base handoff; the new composition is its universal quantification
over a preselected owner, using the witness's compact positive-gap theorem.
Neither statement is a new equilibrium compiler.

No external paper theorem is used.  The packet depends only on the named
checked project declarations and the two independently reviewed
ordinary-mathematics wrappers.

## Boundary tests

1. **Zero or unit free hazards.**  The pair-base target remains valid at every
   boundary point of the induced Nash polytope.  Sure base absorption still
   makes unrestricted deviations one-stage and incidence remains one.
2. **All-Continue reset wall is real.**  The checked regression
   `QuittingResetIncidenceCapRegression.positive_incidence_and_toggle_but_only_allContinue_capNash`
   has unit incidence and a supported strict toggle while every exact cap-Nash
   root is all-Continue.  Thus Theorem A cannot delete its second arm.
3. **Positive owner gap needs the witness.**  Without a terminal
   exploitability witness, a nonpositive owner-floor point can be consumed by
   the singleton-base uniform-payoff certificate.  The strict `delta_d>0`
   conclusion is therefore correctly counterexample-side, not a universal
   property of reward tables.
4. **Returned observer is not prescribed.**  The handoff selects a debtor
   among the three free players after owner repair.  Symmetry or ties may leave
   several eligible debtors; the theorem records existence and cannot name one
   in advance.
5. **Two outputs need not meet.**  Selecting the same label as `e=d` does not
   identify Theorem A's pair-base law with Theorem B's singleton-base repaired
   profile.  This is a required negative test, not a missing algebraic step.

## Adapter and consumer

In a hypothetical no-uniform Fin4 table, the checked strict-minimum theorem
supplies `X_*`, and any positive debt coordinate supplies `e`; this is the
actual-data adapter for Theorem A.  The checked fixed-law reset dispatcher is
its consumer.  The exact output is either a floor-safe charged cap edge paired
with a separate semantic-prefix contraction, or the named all-Continue
fixed-law wall.

The terminal witness itself is the adapter for Theorem B.  Its consumer is
the checked singleton-base stationary handoff, including the unrestricted
paid-row decoder and floor disjunction.  A downstream paid-return/Bellman
connector is not supplied.

## Lean handoff

The narrowest formal declarations are two wrappers over existing checked
theorems.

1. For literal `Fin 4`, define the complement labels `b,c,f` from a chosen
   debtor `e`, select an induced Nash point, and prove the joint carrier,
   reset, and incidence-one facts.  Invoke
   `exists_fixedLawResetDispatch`; expose the Bellman successor as a separate
   conjunct rather than a field identifying it with the semantic-prefix cap.
2. State

   ```text
   forall d, exists delta>0, forall z in Nash({d},univ.erase d),
     Nonempty (QuittingSingletonBaseStationaryHandoff ...).
   ```

   Prove it by direct composition of
   `exists_pos_ownerFloorExcess_gap` and
   `exists_singletonBaseStationaryHandoff`.

Finite tests should include boundary mixed points, the all-Continue reset
regression, and all four choices of `d`.  No new structure should assume a
connection between the two selected profiles.

## Scope and nonclaims

- The exact Bellman edge `R.2 -> W` is not an edge `R -> R'` between terminal-
  semantic pairs, and `W` is not claimed equal to `R'.2`.
- The semantic-prefix contraction starts at `D(R)>=D(X_*)`; it need not fall
  below the global minimum and is not yet an iterable well-founded descent.
- The all-Continue reset wall is not eliminated.
- Theorem B prescribes the repaired owner only.  It does not prescribe the
  observer, induced Nash point, payoff vector, terminal law, or paid atom.
- The pair-base target and singleton-base handoff are parallel same-table
  reselections.  No chronological path connects them.
- No terminal payoff near-return, exact Bellman return, approximate Nash
  profile, uniform-equilibrium payoff, or four-player conjecture proof is
  obtained.
