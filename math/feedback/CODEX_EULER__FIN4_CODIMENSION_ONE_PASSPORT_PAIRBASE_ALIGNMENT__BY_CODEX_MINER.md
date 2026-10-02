# Second review of the Fin4 codimension-one passport alignment

Reviewer: `CODEX_MINER`

Target:
[`CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md`](../notes/CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md)

Scope: Sections 1--9 only, including Theorems 3.1, 4.1, 4.2, 4.4, 5.1 and
Corollaries 4.3, 4.5, 5.2.  Section 10 is a later unreviewed delta and is
explicitly excluded.

Verdict: **PASS.**  I found no unresolved mathematical, source, probability,
agency, or same-law provenance objection in the reviewed scope.  This review
is independent of the earlier `CODEX_RAMSEY` review.  The narrowest
formalization-worthy result is Theorem 4.2 plus Corollary 4.3: an actual
quantitative Fin4 hard residual produces a one-debtor singleton-base
stationary source whose same semantic pair and complete law enter the checked
fixed-law reset dispatcher.

## 1. Quantitative quiet-lift provenance

I rederived Theorem 3.1 from

```text
G=w*Delta,
Delta=(1-a)*x+a*y,
G>=gamma,
x<=P<=gamma-eta,
T(S)<=2M.
```

All terminal payoffs, including Never, lie in `[-M,M]`, so `Delta<=2M` and
the positive gap first gives `M>0` and

```text
w>=gamma/(2M).
```

Since `w<=1`, `Delta>=gamma`.  The case `a=0` would give
`Delta=x<gamma`, so `a>0`.  Then

```text
gamma<=P+a*(y-P)
```

gives `y>=gamma` and

```text
eta<=a*(y-P)<=2M*a,
a>=eta/(2M).
```

For `H={S:T(S)>=gamma/2}` and `h=nu(H)`,

```text
gamma<=y<=2M*h+(1-h)*gamma/2
```

implies `h>=gamma/(4M-gamma)>=gamma/(4M)`.  The probability
`w*a*h` is exact by the chain rule for the nested events “reach the selected
row”, “absorb there”, and “the conditional coalition is in `H`”.  Thus the
aggregate mass is at least `gamma^2*eta/(16M^3)`, and the seven nonempty
subsets of the retained three-player set give the stated atom constant
`gamma^2*eta/(112M^3)`.

The note correctly keeps this half-gap heavy atom separate from the possibly
different positive-mass coalition selected from the average `y>=gamma` with
the full gap.  Deletion/lift naturality also has the stated orientation:
retained coordinates keep debt at most `epsilon`, while the deleted player's
selected pure-time deviation makes its ambient debt at least `gamma`.

## 2. Singleton-base source

For a full-gap singleton join

```text
reward({j})_d+gamma<=reward({j,d})_d,
```

choose any point of
`quittingPersistentBaseNashSet reward {j} (univ.erase j)`.  Its nonemptiness
is checked by `quittingPersistentBaseNashSet_nonempty`.  The persistent base
player `j` Quits surely, so play absorbs at date zero even after a free
player's arbitrary behavioral deviation.  The induced mixed-Nash
inequalities are therefore the full behavioral-cap inequalities.  The checked
theorem `persistentBase_inducedNash_free_semantics` gives exactly zero debt
and punishment-floor safety for all three free coordinates.

Let `d,k,l` be the free labels, let their Quit probabilities be `x_d,x_k,x_l`,
and put `z=(1-x_k)(1-x_l)`.  If `x_d=1`, free absorption is one.  If
`x_d<1`, Continue has positive support for player `d`, so its expected
Quit-minus-Continue gap is nonpositive.  At the `k,l` all-Continue corner the
displayed singleton collision gives gap at least `gamma`; at every other
corner the reward bound gives a lower bound `-2M`.  Hence

```text
0>=z*gamma-(1-z)*2M,
1-z>=gamma/(gamma+2M).
```

The total free absorption is at least `1-z`.  Its seven nonempty free
coalitions are precisely the terminal coalitions strictly containing the
sure base `{j}`, so one has mass at least
`gamma/[7(gamma+2M)]`.

The literal profile's semantic debt is nonnegative coordinatewise.  All free
debts are zero, while the terminal witness makes some debt at least `gamma`;
hence the unique possible positive-debt coordinate is `j` and
`d_j>=gamma`.  The checked stationary-cap equality and
`exists_oriented_quitNow_never_gap_of_stationary_cap_debt` select one of the
two oriented pure-time edges.  In either orientation,
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` returns the
claimed paid row on this same stationary profile.  No stationary-only
deviation restriction is used.

## 3. Same-law fixed reset

The stationary semantic pair and its complete terminal law are a literal
point of `quittingTerminalSemanticLawCarrier`.  The passport outsider `d` is
a solved free coordinate and hence has zero debt.  Every prescribed terminal
coalition contains the sure base owner `j`, and `j!=d`, so

```text
quittingTerminalOpponentIncidenceMass d j mass=1.
```

Let `X_*` be the supplied positive global minimum.  These are exactly the
hypotheses of

```text
QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch
```

with source `X_*`, target equal to the just-constructed stationary pair,
owner `d`, and other label `j`.  The dispatcher therefore uses the **same
selected semantic pair and complete law**.  It may return either its absorbing
strict-debt branch or its all-Continue cap-face branch; the note does not
silently discard the latter.

Corollary 4.3 is an actual-data adapter, not a supplied-certificate theorem.
For every prescribed singleton owner `j`, the checked declaration

```text
FinFourQuantitativeFullSupportHardResidual.
  exists_terminalGap_collision_at_singleton
```

selects a distinct `d` with exactly the singleton-join inequality above.
Thus every hard residual reaches the one-debtor/heavy-atom/same-law reset
source.

## 4. Pair, grand, and minimum-support alternatives

The pair-join case invokes
`nonempty_finFourPairBaseStationaryTwoDebtorHandoff` with the correct label
orientation.  Its selected point solves the two free coordinates against
unrestricted deviations, supplies the quantitative strict-superset atom,
localizes positive debt to the sure pair, and supplies the paid row.  The
passport outsider is a solved free coordinate; either sure base label gives
unit incidence, so the same selected pair/law enters the fixed-law dispatcher.

For a grand join by `d`, the checked leave-or-join theorem at the grand
coalition has no outsider branch and selects `e` with the reverse leave gap.
It cannot select `e=d`, since the two inequalities would give
`2*gamma<=0`.  Reapplying the codimension-one passport at `e`, its own grand
join is impossible for the same reason.  This validates the finite reduction
to solo, singleton join, or pair join without claiming a common restricted
profile or chronology.

For Theorem 4.4, let `C` be the image of the full-gap singleton-collider
relation.  The all-owner collision theorem forces `|C|>=2`: if `C={c}` then
the collider selected for owner `c` is distinct from `c` and belongs to `C`.
If the positive minimum's debt support meets `C`, selecting that debtor as
reset owner makes the dispatcher's transfer inequality strictly positive.
If it does not meet `C`, its support lies in the complement of a set of size
at least two in `Fin 4`, and therefore has cardinality at most two.  This is
the exact claimed finite alternative; it is not a total-debt descent claim.

## 5. Source audit and export boundary

I inspected the declaration statements under their current imports in:

```text
PersistentBaseInducedGame.lean
TerminalSemanticFinFourSoloWallDispatch.lean
LargeBaseStationarySemanticHandoff.lean
TerminalSemanticPaidFirstDisagreement.lean
PunishmentNormalAtomicCollisionHandoff.lean
TerminalSemanticResetIncidenceCapReturn.lean
```

Narrow searches found no checked wrapper combining the singleton collision
selected from `FinFourQuantitativeFullSupportHardResidual` with the
one-debtor singleton-base semantic source, its quantitative strict-superset
atom, and the same-law fixed reset.  The older checked prescribed-owner
handoff and reset packets do not retain this exact one-debtor/atom/same-law
combination.

The result is suitable for a narrow export containing Theorem 4.2 and
Corollary 4.3, optionally the reviewed minimum-support alternative in Theorem
4.4.  It must retain these nonclaims:

* the reset dispatcher's all-Continue branch remains;
* the returned reset pair is not the stationary target;
* no payoff near-return or chronological connector is produced;
* no uniform-equilibrium payoff or full Fin4 proof is claimed; and
* Section 10 is excluded until separately reviewed.
