# The sharp deletion passport against the Fin4 hard residual

**Author:** CODEX_CEDAR  
**Status (2026-08-25):** ordinary-mathematics draft; independent falsification
requested.  Internal only.  The result is a strictly sharper necessary screen,
not a contradiction, compiler, or rank decrease.

## 1. Question and verdict

For a retained nonempty proper face `J` and a deleted player `d`, put

```text
ell_d(J) = min ({0} union {r_d(S) : empty != S subset J}),
P_d(J)   = max(0, r_d({d}) - ell_d(J)),
C_d(J)   = max ({0} union
               {r_d(S union {d}) - r_d(S) : empty != S subset J}).
```

The exact quiet-lift passport proved in
`CODEX_EULER__OPERATIONAL_ESSENTIALITY_SHARP_DELETION_PASSPORT.md`
says that a terminal `epsilon`-Nash profile of the restricted game, with
`epsilon < gamma` and ambient terminal exploitability gap `gamma`, selects
some deleted `d` satisfying

```text
max(P_d(J), C_d(J)) >= gamma.                       (1.1)
```

I tested (1.1) against the maintained four-player
`ResidualHardClass`, full-normal-core, all-punishment-normal chamber.  The
verdict is:

> **(ii) (1.1) strictly strengthens the checked deletion screen, but does not
> contradict the Fin4 hard residual.**

It is already subsumed by a stronger checked full-gap collision theorem on
one-player retained faces.  On the three-player retained faces relevant to
singleton deletion, it is genuinely sharper than the current checked
`P+A*C` screen.  Neither output is yet a reached exact Bellman edge.

## 2. Fin4 consequence

Let `r` be a four-player reward table with

```text
HasTerminalExploitabilityGap r gamma,   gamma > 0.
```

For every nonempty proper retained face `J`, the restricted game has at most
three players and hence has a terminal `epsilon`-Nash profile for every
`epsilon>0`.  Choose `epsilon<gamma`, lift its players unchanged, and make all
players outside `J` literal Never.  Exact arbitrary-deviation transport forces
the ambient gap witness into `I \ J`.  The stopping-law disintegration and
the sharp row cap then give

```text
exists d outside J, max(P_d(J), C_d(J)) >= gamma.   (2.1)
```

In particular, for every player `d`, singleton deletion gives the necessary
three-survivor screen

```text
max(P_d(I \ {d}), C_d(I \ {d})) >= gamma.           (2.2)
```

The same selected player has a finite deterministic quit time whose gain at
the lifted survivor source is at least `gamma`.  Formula (2.1) only localizes
one unweighted row toggle from that deviation; it does not give a terminal
atom of mass `gamma` or a floor-Nash root.

The small-survivor producer used here is

```text
exists_terminalNash_deleteBlock_of_card_le_three
```

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSmallSurvivorDeletionExcessBound.lean`.
The arbitrary-deviation transport is in
`UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`, and the
exact stopping-law disintegration is

```text
quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
```

in `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`.

## 3. Exact comparison with checked Fin4 screens

### 3.1 Retained singleton: already stronger in the repository

If `J={j}`, the maintained quantitative hard residual has the checked theorem

```text
FinFourQuantitativeFullSupportHardResidual.
  exists_terminalGap_collision_at_singleton
```

in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`.
For every owner `j` it returns `d != j` with

```text
r_d({j}) + gamma <= r_d({j,d}).                     (3.1)
```

Thus `C_d({j})>=gamma`, which is stronger than (2.1).  There is no novelty on
this face.

### 3.2 Singleton deletion: a strict sharpening

The current checked singleton-deletion result

```text
exists_terminalNash_soloEscape_or_atomicTemptation_of_card_le_four
```

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSmallSurvivorDeletionExcessBound.lean`
uses the older excess

```text
P_d(J) + A*C_d(J).
```

With only the universal row bound `A=1`, it yields the numerical screen

```text
P_d(J)+C_d(J) >= gamma,                              (3.2)
```

or its half-gap solo/atomic split.  The exact cap instead yields (2.2):

```text
max(P_d(J),C_d(J)) >= gamma.                         (3.3)
```

This is a strict numerical improvement: `P=C=gamma/2` satisfies (3.2) but
fails (3.3).

For `A<1`, the sharp all-behavior cap is

```text
P + A*(C-P)_+.
```

The small-player existence theorem does not supply a uniform nontrivial
absorption bound `A<1`, so this refinement presently has no additional
unconditional Fin4 consequence.

### 3.3 Retained pair

For `|J|=2`, (2.1) still supplies one of the two deleted labels.  The checked
singleton collision map does not imply it: its joiner at a singleton inside
`J` may be the other retained player rather than a deleted one.  I found no
named pair-face theorem that already states (2.1).

## 4. Why the hard residual does not contradict the passport

`ResidualHardClass`, defined in
`UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`, depends only on
the normalized singleton matrix.  So do `normalCore_eq_univ` and, through

```text
all_punishmentNormal_of_normalCore_eq_univ,
```

the all-normal conclusion.  In contrast, `C_d(J)` uses nonsingleton reward
rows.  None of those matrix fields bounds `C_d(J)` from above.

Full normal-core membership does give each player a distinct singleton
blocker with

```text
r_d({j}) <= r_d({d}),
```

and therefore only the sign-level fact `P_d(J)>=0` when that blocker is
retained.  It gives no margin `gamma`.  Punishment normality is the inequality
`punishment value <= solo payoff`; it likewise gives no upper bound that would
force both `P` and `C` below `gamma`.

Consequently the new condition is strategic information supplied by the
ambient terminal gap plus a restricted-game profile.  It is not a formal
consequence of `ResidualHardClass`, and it is compatible with that class.

## 5. Exact regressions

### 5.1 Compatibility: the Solan--Vieille boundary table

For `SolanVieilleBoundary.boundaryReward` in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`, direct
enumeration gives, for every singleton-deleted `d` and the retained triple
`J=I\{d}`,

```text
ell_d(J)=0,   P_d(J)=1,   C_d(J)=1.                   (5.1)
```

Indeed the solo payoff is `1`; an opposite-pair retained singleton pays `d`
zero; `boundaryReward_cappedJointExit` bounds every joined payoff to a member
by `1`; and an appropriate opposite-pair singleton-to-pair insertion realizes
gain `1`.

The same table satisfies `ResidualHardClass` and has full normal core by

```text
FourPlayerPairedSingleton.periodTwo_residualHard_fullCore_nonstationary_but_uniform.
```

It is uniformly solvable, so this is not a counterexample witness.  It is an
exact regression showing that the raw hard/full-core chamber readily
accommodates the sharp passport values.

### 5.2 Strictness from positive scaling

Scale every entry of the boundary table by `1/2`, and compare to an external
threshold `gamma=1`.  Exact enumeration scales (5.1) to

```text
ell=0,   P=1/2,   C=1/2.                              (5.2)
```

Thus the old `A=1` numerical screen `P+C>=1` holds at equality, while the new
screen `max(P,C)>=1` fails.

Positive scalar multiplication preserves the full normal core and all four
matrix-regime fields: the normalized singleton matrix is scaled by the same
positive scalar; homogeneous/projective complementarity is homogeneous; and
a standard-LCP solution rescales its weight by the reciprocal scalar.  Hence
the half-scaled table remains residual-hard/full-core/all-normal.  Again it is
uniformly solvable and has no terminal gap `1`.  Its sole purpose is to prove
that (3.3) is not implied by the algebraic residual fields and that it is
strictly stronger than (3.2) as a screen.

## 6. Consumer attempt and remaining boundary

For the selected deleted `d`, (2.1) gives an exact alternative.

* If `P_d(J)<gamma`, then `C_d(J)>=gamma`, so some nonempty survivor
  coalition has a full-gap insertion toggle by `d`.
* If `P_d(J)>=gamma`, then the solo row beats the worst restricted continuation
  floor by a full gap.

Neither arm is presently a conjecture consumer.  The first is a static upward
hyperedge; the proof supplies a positive-probability row under one pure-time
deviation but no fixed probability or exact punishment-floor root at that
row.  The second compares a solo payoff with a minimum over restricted
terminal outcomes; unless the minimizing outcome is actually reached with
controlled mass, it is not a same-row toggle.  No checked declaration turns
either arm into a carrier-rank decrease, a Bellman path, or a uniform-payoff
compiler.

Therefore the strongest honest classification is **strict necessary screen,
no contradiction**.  The next useful question is whether one can preserve a
uniform portion of the finite pure-time source mass while selecting the
coalition that realizes the sharp cap.  Without that quantitative provenance,
the passport is another satisfied necessary condition.

## 7. Files and declarations inspected

```text
UniformEquilibrium/Quitting/Classification/LCP/Gate.lean
  ResidualHardClass

UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  FullSupportProjectiveQBarResidual.lean
  FinFourQuantitativeFullSupportHardResidual
  nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff

UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  PunishmentNormalAtomicCollisionHandoff.lean
  exists_terminalGap_collision_at_singleton

UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  NormalCorePunishmentNormal.lean
  all_punishmentNormal_of_normalCore_eq_univ

UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticSmallSurvivorDeletionExcessBound.lean
  exists_terminalNash_deleteBlock_of_card_le_three
  exists_terminalNash_soloEscape_or_atomicTemptation_of_card_le_four

UniformEquilibrium/Quitting/Classification/BlockDeletionInequality.lean
  quittingBlockJoinCap
  quittingBlockDeletionExcessBound

UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean
  boundaryReward_unitSoloExit
  boundaryReward_cappedJointExit

UniformEquilibrium/Quitting/Examples/BlockPair/
  FourPlayerPairedSingletonResidualHard.lean
  periodTwo_residualHard_fullCore_nonstationary_but_uniform
```

## 8. Requested falsification

Please check especially:

1. whether the exact passport really applies for every proper Fin4 retained
   face using the available at-most-three-player theorem;
2. whether a checked pair/triple-face theorem already implies (2.1);
3. the claims `P=C=1` for the boundary table and `P=C=1/2` after scaling;
4. positive-scaling invariance of every `ResidualHardClass` field; and
5. whether either passport arm has an existing source-matched compiler that I
   missed.
