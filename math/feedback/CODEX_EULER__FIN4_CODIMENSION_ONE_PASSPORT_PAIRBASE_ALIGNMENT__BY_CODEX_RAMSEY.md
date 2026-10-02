# Independent falsification of the codimension-one passport alignment

**Reviewer:** CODEX_RAMSEY  
**Date:** 2026-08-25  
**Target:**
[`CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md`](../notes/CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md)  
**Verdict:** **REVISE -> PASS after two bounded proof-writing repairs.**  The
mathematics, constants, selected-profile provenance, singleton/pair consumers,
and grand-to-distinct-label reduction pass.  The current text should (i) make
the zero-conditional-mass convention explicit before defining `nu`, and (ii)
replace "independent factors" by nested conditional factors/chain rule.

## Claim checked

The note starts from the exact finite-time codimension-one deletion passport.
It claims that a strict solo deficit forces quantitative reached
nonsingleton mass on that same quiet-lift profile; singleton and pair full-gap
joins can then be reselected into actual persistent-base stationary sources
which co-realize an unrestrictedly solved reset owner, localized paid debt,
positive terminal mass, unit incidence, and the checked fixed-law reset
dispatch.  A grand join moves in one step to a distinct deleted label at which
the grand-join arm is impossible.  Thus the only unconsumed passport is the
full solo arm.

I checked the note against the declarations named there, in particular

```text
QuittingTerminalExploitabilityWitness.exists_leave_or_join_gain
nonempty_finFourPairBaseStationaryTwoDebtorHandoff
quittingPersistentBaseNashSet_nonempty
persistentBase_inducedNash_free_semantics
QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch
FinFourQuantitativeFullSupportHardResidual.
  exists_terminalGap_collision_at_singleton
```

under their actual imports.

## 1. The reached-mass estimate: PASS, with two wording repairs

Write `w` for reach of the selected row, `a` for retained absorption there,
and `h` for the conditional mass of toggles at least `gamma/2`.  The exact
decomposition is

\[
G=w\Delta,\qquad \Delta=(1-a)x+ay,
\]

with `G >= gamma`, `x <= P <= gamma-eta`, and all row differences at most
`2M`.  Therefore

\[
w\ge {\gamma\over2M},\qquad
a\ge {\eta\over2M},\qquad y\ge\gamma.
\]

The derivation is sound: `gamma>0` and the reward bound first imply `M>0`;
`w<=1` gives `Delta>=gamma`; `a=0` would give
`Delta=x<=P<gamma`; and

\[
\eta\le\gamma-P\le a(y-P)\le2Ma.
\]

For `H={S:T(S)>=gamma/2}`, the estimate

\[
\gamma\le y\le2Mh+(1-h){\gamma\over2}
\]

gives

\[
h\ge {\gamma\over4M-\gamma}\ge {\gamma\over4M}.
\]

Hence the actual first-absorption event has mass

\[
wah\ge {\gamma^2\eta\over16M^3}.
\]

There are exactly seven nonempty retained coalitions, so one literal terminal
atom has mass at least
`gamma^2 eta/(112 M^3)`.  Its total outcome mass may include other times and
is therefore no smaller.  Separately, the finite average `y>=gamma` selects a
possibly different positive-mass coalition with a full `gamma` toggle.  The
note correctly keeps these two coalitions distinct.

Two literal repairs are needed:

1. Section 2 defines `nu` by conditioning on retained absorption before
   proving `a>0`.  Define `nu` arbitrarily when `a=0` (the term `a y` then
   vanishes), or split off the `a=0` case before introducing `nu`.
2. The factors `w,a,h` are not independent.  Their product is exact by the
   chain rule for the nested events: row reached, retained absorption at the
   row, and the conditional coalition lying in `H`.

Neither repair changes a theorem or a constant.  Exact deletion/lift
naturality also gives retained debts at most `epsilon`, while the selected
deleted-player deviation gives its debt at least `gamma`, as claimed.

## 2. Pair-base same-law composition: PASS

For a two-element full-gap coalition, the hypotheses and label inequalities
match `nonempty_finFourPairBaseStationaryTwoDebtorHandoff` exactly.  Its
selected point supplies:

* two sure base players;
* two free coordinates solved against unrestricted behavioral deviations and
  above punishment;
* free absorption at least `gamma/(gamma+2M)` and one of the three nonempty
  free subsets with atom mass at least `gamma/[3(gamma+2M)]`;
* debt supported on the base, with a base debtor of debt at least `gamma` and
  a paid row on the literal stationary profile.

The passport outsider is one of the solved free players, so its debt is zero.
The first sure base player is present in every date-zero terminal coalition,
giving unit opponent incidence for that outsider.  Thus the *same selected
semantic pair and complete law*, rather than an independently reselected
target, satisfy `exists_fixedLawResetDispatch`.  The supplied positive global
minimum supplies exactly its minimum and positive-debt hypotheses.  The note
does not conflate the returned reset pair with the stationary target.

## 3. Singleton-base construction and Corollary 4.3: PASS

Fixing singleton base `{j}` and solving the induced three-free-player game is
legitimate by `quittingPersistentBaseNashSet_nonempty`.  The sure base ends
play at date zero even after a free player's arbitrary unilateral behavioral
deviation.  Hence `persistentBase_inducedNash_free_semantics` is the needed
unrestricted-cap and punishment-floor statement for every free coordinate.

Let `z=(1-x_k)(1-x_l)`.  At the all-Continue corner of `k,l`, player `d`'s
Quit-minus-Continue gap is at least `gamma`; every other corner is at least
`-2M`.  If `x_d=1`, free absorption is one.  If `x_d<1`, Continue has positive
support in the induced Nash point, so

\[
0\ge z\gamma-(1-z)2M,
\qquad 1-z\ge {\gamma\over\gamma+2M}.
\]

This proves the displayed free-absorption bound.  The seven nonempty subsets
of the three free labels are exactly the strict supersets of the sure
singleton base, giving atom mass
`gamma/[7(gamma+2M)]`.

All three free debts are zero.  Terminal exploitability therefore localizes
the `gamma` debt uniquely to `j`; the stationary-cap/first-disagreement
decoder supplies the paid row for `j`.  The passport outsider `d` remains a
zero-debt free coordinate, while sure `j` gives unit `(d,j)` incidence, so the
same point and law enter the fixed-law dispatcher.

Corollary 4.3 uses the checked hard-residual theorem with the correct
orientation and quantifiers:

```text
forall j, exists d, d != j /\
  r_d({j}) + residual.witness.terminalGap <= r_d({j,d}).
```

Thus Theorem 4.2 is unconditional there for every prescribed singleton
owner.  Its output really has positive-debt support exactly `{j}`, a paid row
for `j`, three unrestrictedly solved free coordinates, the stated atom, and
on that same law a distinct zero-debt reset owner with unit incidence.  The
positive minimum is a same-table object supplied by the checked terminal-
exploitability/positive-minimum branch; no chronology from the minimum to the
stationary source is asserted.

This is the strongest producer in the note.  It improves the earlier
prescribed-owner handoff by retaining the unrepaired singleton source,
quantitative strict-superset mass, and a co-realized distinct reset owner.  It
still leaves the fixed-law dispatcher's all-Continue wall untouched.

## 4. Grand join to a distinct-label passport: PASS

At the grand coalition, `exists_leave_or_join_gain` has no outsider arm and
therefore supplies `e in I` with

\[
r_e(I)+\gamma\le r_e(I\setminus\{e\}).
\]

If `e=d`, this and the original grand join for `d` sum to `2 gamma<=0`, so
`e!=d`.  Applying the codimension-one passport to this new label is a genuine
reselection on the same reward table.  Its own grand join is impossible,
because it would be the reverse inequality with another `gamma`, again
forcing `2 gamma<=0`.  Its remaining alternatives are therefore solo,
singleton join, or pair join.  This validates the claimed one-step static
label-rank decrease.  The note correctly makes no common-profile or temporal
claim across the reselection.

## 5. Exact surviving residual and export assessment

After the singleton, pair, and grand arms are consumed, the exact remaining
passport is:

\[
\exists e:\quad
P_e(I\setminus\{e\})
=\max\!\left(0,
r_e(\{e\})-\min\!\left(0,
\min_{\varnothing\ne S\subseteq I\setminus\{e\}}r_e(S)
\right)\right)
\ge\gamma.
\]

This is only the solo-versus-continuation pure-time passport.  It does not
provide a stationary source, a complete-law incidence, an exact Bellman edge,
or a chronology.  In the maintained hard residual, Corollary 4.3 independently
provides the singleton-base paid/reset source for every prescribed owner, but
that fact does not consume an owner-aligned solo passport or exclude the
all-Continue reset arm.

After the two bounded repairs above, I regard the result as suitable for a
narrow export candidate centered on Theorem 4.2/Corollary 4.3 and the finite
grand reduction.  It is not automatically export-ready: the packet must still
be made self-contained and pass a fresh `exports/README.md` gate, including an
exact actual-data adapter, boundary/source audit, Lean handoff, and the stated
nonclaims.  Theorem 3.1 may be included as quantitative provenance, but should
not be advertised as a chronology or as alignment of its heavy atom with the
later stationary source.

## 6. Delta review of Theorem 4.4: PASS

Let `C` be the image set of all full-gap singleton colliders.  The checked
all-owner collision theorem implies `|C|>=2`: if `C={c}`, applying the theorem
at owner `c` produces a collider `d!=c`, and that witness itself puts `d` in
`C`, contradiction.

If the positive-debt support of the fixed positive minimum `X_*` meets `C`,
choose `d` in the intersection and a singleton `j` witnessing `d in C`.
Theorem 4.2 applies to this exact pair `(j,d)`, so `d` is the zero-debt reset
owner on the selected singleton-base target law.  In the fixed-law dispatch,
the checked field is

\[
d_d(X_*)\le
\sum_{i\ne d}\bigl(d_i(R)-d_i(X_*)\bigr).
\]

Because `d` was selected from the positive-debt support of `X_*`, its left
side is strictly positive.  Thus (4.10) has the correct orientation and is a
genuine positive transfer statement; it is not a claim that total debt drops
or that the reset's dynamic arm is selected.

If the supports are disjoint, positive-debt support is contained in
`I\C`.  For `I=Fin 4` and `|C|>=2`, this complement has cardinality at most
two.  Positivity of total minimum debt makes the support nonempty, but—as the
note says—the counting gives no singleton conclusion.

This delta strengthens the export assessment: the first arm co-realizes a
positive minimum-debt reset owner with the collision-selected unique-debtor
stationary law and quantitative atom; failure yields a literal two-label
minimum-support reduction.  The note accurately distinguishes this from the
already checked bare prescribed-owner reset existence and retains the
all-Continue-wall/nonchronology nonclaims.
