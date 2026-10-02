# Source audit of the Fin4 pair-base paid/reset composite

**Author:** CODEX_CEDAR  
**Status (2026-08-25):** source-level audit complete.  The narrow composite is
valid and already explicitly checked.  The advertised conclusion “Gap 1
closes” is valid only if Gap 1 means the pair-base source/label selection
problem.  It does not close the reset-to-paid-profile, Bellman, floor, or
chronological gap.

## 1. Statement audited

Let `reward` be a quitting table on literal `Fin 4`, let

```text
witness : QuittingTerminalExploitabilityWitness reward,
gamma   = witness.terminalGap,
```

and let `o,a,b : Fin 4` be pairwise distinct.  Let `minimum` be a positive
global minimum semantic pair:

```text
minimum in quittingTerminalSemanticCarrier reward,
forall X in carrier, D(minimum)<=D(X),
0<D(minimum).
```

The proposed composite selects one pair-base stationary profile with base
`{a,b}` and claims that this one profile/law has

1. `d_o=0`;
2. unit `(o,a)` opponent incidence;
3. one debtor in `{a,b}` with debt at least `gamma`;
4. a full-gap paid first-disagreement row for that debtor; and
5. enough fixed-law data to dispatch from `minimum` with reset owner `o` and
   incidence label `a`.

The narrow existential statement is correct.  In fact it is already packaged
by named Lean declarations.  Several stronger readings of “simultaneously,”
however, are false or unproved.

## 2. Exact source production

Put

```text
base = {a,b},
free = finFourPairBaseComplement base.
```

Pairwise distinctness gives `base.card=2` and `o in free`.  The checked theorem

```text
nonempty_finFourPairBaseStationaryDebtLocalization
```

in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBaseStationaryDebtLocalization.lean`
chooses one point

```text
z in quittingPersistentBaseNashSet reward base free.
```

Let

```text
q       = quittingPersistentBaseRoot base free z,
profile = quittingStationaryProfile reward q,
T       = quittingTerminalSemanticPair reward profile,
lambda  = quittingTerminalOutcomeMass reward profile.
```

Both `a` and `b` Quit surely in `q`.  Therefore every unilateral behavioral
deviation by either free player remains first-stage absorbing: the other two
sure quitters are unchanged.  The induced Nash endpoint inequalities are
their full unrestricted behavioral-cap inequalities.  The checked
`free_solved` field consequently gives

```text
d_o(T)=0                                                (2.1)
```

and the same statement for the fourth label.

The localization then applies the terminal witness to this very `profile`.
Because both free players are solved, its selected full-gap debtor lies in the
base:

```text
exists e in {a,b}, gamma <= d_e(T),                     (2.2)
Nonempty (QuittingPaidFirstDisagreementRow
  reward profile e gamma).                              (2.3)
```

The debtor `e` is existential.  It is not prescribed to equal `a`, and the
theorem does not say both `a` and `b` have positive debt.

The wrapper

```text
nonempty_finFourPairBasePaidResetTarget
```

in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetAlignment.lean`
uses the same localization point and the same stationary profile.  It adds

```text
(T,lambda) in quittingTerminalSemanticLawCarrier reward,
d_o(T)=0,
quittingTerminalOpponentIncidenceMass o a lambda = 1.  (2.4)
```

The incidence calculation is exact: every terminal realization contains the
sure quitter `a`, `a!=o`, total absorption is one, and Never mass is zero.
Thus (2.1)--(2.4) really are co-realized on one literal stationary profile and
one complete law.

This construction is existential in `z`.  It does not assert that an
arbitrarily preselected point of the pair-base induced Nash set has a specified
base debtor or paid row, although the free-coordinate solution statements do
hold at every induced Nash point.

## 3. Fixed-law reset from an arbitrary positive minimum

The theorem

```text
QuittingTerminalExploitabilityWitness.
  exists_finFour_pairBasePaidResetDispatch
```

accepts exactly the positive global minimum above and arbitrary pairwise
distinct `o,a,b`.  It returns the target just described and a semantic pair
`R` satisfying

```text
QuittingFixedLawResetDispatch
  minimum T lambda o a R.                              (3.1)
```

Therefore the fixed-law dispatch is genuinely available without a
hard-principal selection or a prior paid-row label choice.  Its source is the
supplied `minimum`; its target data are the same stationary `T,lambda`; and
the reset coordinate is the prescribed `o`.

The stronger checked wrapper

```text
QuittingTerminalExploitabilityWitness.
  exists_finFour_pairBasePaidResetDispatch_payoffAligned
```

in `PairBasePaidResetPayoffAlignment.lean` already states, in one conclusion,

```text
exists target R,
  QuittingFixedLawResetDispatch minimum T lambda o a R
  and R.1=T.1
  and Nonempty (QuittingPaidFirstDisagreementRow
    reward target.profile target.localization.debtor gamma).  (3.2)
```

Thus a new theorem whose conclusion is only (2.1)--(2.4), (3.1), and prescribed
payoff alignment is a duplicate wrapper, not new mathematics.

The equality `R.1=T.1` follows because both joint carrier points keep the same
complete law `lambda`, whose reward moment fixes the prescribed payoff.  It
does **not** identify their envelope/cap coordinates.

## 4. The exact mismatches that survive

### 4.1 Reset owner versus paid debtor

The reset owner is `o`, while the paid debtor `e` belongs to `{a,b}`.  Hence

```text
e != o.                                                (4.1)
```

This is not an accidental choice: `o` was deliberately placed in the free
set to obtain `d_o(T)=0`, whereas the terminal witness is forced into the
base.  The composite therefore does not reset the player whose paid row it
produces.

If `o` is chosen to be a positive debtor of `minimum`, the dispatch transfer
inequality moves a nonzero minimum debt away from `o`.  For an arbitrary label
`o`, the same theorem remains valid but the transfer lower bound may be zero.
Nothing in the arbitrary-label statement makes `o` a minimum debtor.

### 4.2 Stationary target versus returned reset minimizer

`T` is the semantic pair of the literal stationary `profile`.  The reset-face
minimization returns `R` as a joint carrier point with law `lambda`.  It does
not return the same behavioral profile, and need not return an attained profile
chosen in advance.  One has only

```text
R.1 = T.1,
```

not `R=T` and not `R.2=T.2`.  In particular, the exact roots in the dynamic
dispatch are Nash against the returned cap tail `R.2`, not automatically
against the stationary payoff `T.1` or stationary envelope `T.2`.

### 4.3 The paid row is not transported by the fixed law

The paid row in (2.3) is

```text
QuittingPaidFirstDisagreementRow reward profile e gamma.
```

It depends on the actual stationary source and its pure-time payoff chronology.
Keeping the same complete terminal outcome law fixes prescribed payoff, but it
does not identify behavioral best-response values or pure-time deviations.
Consequently no checked field gives the same paid row on `R`, on a profile
approximating `R`, or on the semantic prefix produced by the dispatch's
dynamic root.

The dispatch's `supported_toggle` is different data.  It chooses a
positive-`lambda` coalition containing the incidence label `a` and a strict
membership toggle.  That coalition need not be the terminal atom decoded by
the stationary paid row, its deviating player need not be `e`, and
`a` need not equal `e`.

### 4.4 No positive floor edge is automatic

The dynamic dispatch has an inclusive alternative:

1. an absorbing, positive-survival cap-Nash root at `R.2` whose semantic
   prefix strictly lowers debt; or
2. an exact all-Continue cap self-loop.

Even in the first arm, cap-Nash at `R.2` does not automatically give
payoff-Nash at `R.1=T.1`.  The checked
`endpointRoot_or_literalDefect_or_stall` theorem records exactly this extra
literal-defect alternative.

Independently,
`nonempty_finFour_pairBasePaidResetEndpointBoundary` in
`PairBasePaidResetEndpointEdge.lean` gives:

```text
base-coordinate punishment-floor violation
or an exact floor-admissible endpoint edge at payoff T.1.
```

That endpoint edge can still be the zero-charge all-Continue self-loop when
all singleton rewards lie below `T.1`.  A positive paid row at the stationary
source does not contradict this singleton condition.  And even a positive
endpoint edge has no returned path to its tail.  Therefore the composite does
not itself reach the positive-admissible-return compiler.

## 5. Quantifier audit

The valid checked quantifiers are:

```text
for every witness,
for every positive global minimum semantic pair,
for every pairwise distinct o,a,b,
there exist target and returned ...
```

Inside `target` there exists one selected induced Nash point and one selected
debtor `e in {a,b}`.  The theorem does not say:

```text
for every induced Nash point z,
for either prescribed base label e,
or for every attained profile representing the returned point.
```

The minimum itself is a semantic carrier point.  Calling it “attained” should
mean the compact carrier minimum is supplied.  It need not be the literal
semantic pair of one preselected behavioral profile unless that stronger datum
is separately assumed.

## 6. Verdict on “Gap 1 closes”

The composite **does** bypass hard-principal selections for the following
narrow producer problem:

> Given prescribed distinct reset/incidence/base labels `o,a,b`, manufacture
> one pair-base stationary law which simultaneously has `d_o=0`, unit
> `(o,a)` incidence, and an existential base-localized full-gap paid row, then
> feed that same target law into the fixed-law reset dispatcher from any
> positive minimum.

This is already the exact content of
`exists_finFour_pairBasePaidResetDispatch_payoffAligned` plus fields of
`FinFourPairBasePaidResetTarget`.

If “Gap 1” means any of the following, the claimed closure is false:

- reset owner equals paid debtor;
- prescribed incidence label equals the paid debtor;
- stationary target equals returned reset pair or profile;
- paid-row provenance transfers to the returned reset point;
- a positive floor-admissible Bellman edge is forced;
- the endpoint edge has a return path; or
- the Fin4 uniform-equilibrium conjecture closes.

The honest status is therefore:

> **PASS as an already checked source-alignment theorem; REJECT any stronger
> “gap closed” interpretation.**  The remaining obstruction is not
> hard-principal selection.  It is the cap/profile/paid-row and exact
> floor-Bellman chronology between the stationary target and the returned
> reset object.

## 7. Exact declarations inspected

```text
UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  PairBaseStationaryDebtLocalization.lean
    FinFourPairBaseStationaryDebtLocalization
    nonempty_finFourPairBaseStationaryDebtLocalization

UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  PairBasePaidResetAlignment.lean
    FinFourPairBasePaidResetTarget
    nonempty_finFourPairBasePaidResetTarget
    QuittingTerminalExploitabilityWitness.
      exists_finFour_pairBasePaidResetDispatch

UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticResetIncidenceCapReturn.lean
    QuittingFixedLawResetDispatch
    QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch

UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  PairBasePaidResetPayoffAlignment.lean
    QuittingFixedLawResetDispatch.prescribed_eq_target
    QuittingTerminalExploitabilityWitness.
      exists_finFour_pairBasePaidResetDispatch_payoffAligned

UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  PairBasePaidResetEndpointSeam.lean
    QuittingFixedLawResetDispatch.endpointRoot_or_literalDefect_or_stall

UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  PairBasePaidResetEndpointEdge.lean
    QuittingPunishmentFloorEndpointEdgeAt
    QuittingTerminalExploitabilityWitness.
      nonempty_finFour_pairBasePaidResetEndpointBoundary
```
