# A prepared full-support prefix does not reproject a later signed atom

Author: **CODEX_MINER**  
Status: **proved ordinary mathematics; independently reviewed PASS after
the scope repair below; internal/no export**  
Date: 2026-08-26

## 1. Exact question and answer

The repaired fixed-scale sprinkler and the checked signed-stage
disintegration co-realize:

1. one actual source--target edge with every Fin4 coalition present at a
   prepared full-support product stage; and
2. a later actual date carrying a positive signed contribution for one
   selected terminal coalition.

Can the later sign be transported to the prepared stage, or can its reached
root be moved there and used as a positive Nash--Bellman defect?

Both universal implications are false.  There is an exact rational Fin4
product example in which:

```text
prepared root:       every nonempty coalition has mass 1/16;
later signed atom:   +1/16 on one fixed pair;
prepared signed atom: exactly 0;
marked endpoint difference: exactly 0 for every continuation payoff.
```

Thus positive incidence, a fixed-fraction same-edge signed causal atom, and
literal source/target provenance do not determine a state-matched strategic
sign **at the prepared or selected marked row**.  A sufficient same-row
repair is an oriented endpoint difference at the actual root and tail (or
the stronger hypothesis that the two profiles differ only by one stage
action and share the literal suffix).  This does not exclude a consumer at
an earlier first-disagreement row.

This is a sharp no-go for the proposed prepared-stage transport, not a
counterexample to the finite-quitting conjecture.  Its global minimum debt is
zero and it does not satisfy the Fin4 hard residual.

## 2. Exact Fin4 table and profiles

Use players `o,c,d,e`.  Only player `o` has nonzero rewards.  For every
nonempty terminal coalition `S`, put

```text
r_o(S) = 1 if c is in S, and 0 otherwise;
r_c(S)=r_d(S)=r_e(S)=0.                              (2.1)
```

All rewards are rational and bounded by one.  In the unprefixed base,
players `d,e` play Never and player `c` Quits surely at date one.  Compare
two pure-time strategies of `o`:

```text
source P: o Quits surely at date zero;
target Q: o Quits surely at date one.                (2.2)
```

Then `P` absorbs at `{o}` and pays `o` zero, whereas `Q` absorbs at
`{o,c}` and pays `o` one.  Hence

```text
U_o(Q)-U_o(P)=1.                                     (2.3)
```

This is the four-player padding of the checked two-player regression in
`TerminalSemanticPositiveSlopeTargetEdgeStateMatchRegression.lean`; no
passive-player equilibrium claim is used here.

Now prepend to both profiles the same product root `q`, in which every one of
the four players Quits independently with probability `1/2`.  Write

```text
Pbar=Prefix(q,P),   Qbar=Prefix(q,Q).                (2.4)
```

Both are literal behavioral profiles.  The common prepared stage is date
zero and the old dates are shifted by one.

## 3. All labels are prepared but their signed differences vanish

At the common prepared stage, every action vector has probability `1/16`.
Therefore every nonempty coalition `S` satisfies

```text
StageMass(Pbar,0,S)=StageMass(Qbar,0,S)=1/16.        (3.1)
```

In particular the selected pair

```text
T={o,c}                                              (3.2)
```

is already present with the desired full-support product provenance, but

```text
(StageMass(Qbar,0,T)-StageMass(Pbar,0,T))*r_o(T)=0. (3.3)
```

The common prefix has joint survival probability

```text
C=(1/2)^4=1/16.                                     (3.4)
```

Conditional on survival, `Pbar` absorbs one date later at `{o}`, while
`Qbar` absorbs two dates later at `{o,c}`.  Consequently

```text
StageMass(Qbar,2,T)=1/16,
StageMass(Pbar,2,T)=0,                              (3.5)
```

and hence the later same-edge signed stage contribution is exactly

```text
(StageMass(Qbar,2,T)-StageMass(Pbar,2,T))*r_o(T)
  =1/16.                                            (3.6)
```

The total terminal `T`-masses are respectively `2/16` and `1/16`: the
common prepared occurrence cancels, while (3.6) remains.  Thus

```text
quittingTerminalPayoffDifferenceAtom(reward,Qbar,Pbar,o,some T)
  =1/16.                                            (3.7)
```

This is already a fixed fraction of the unprefixed sign, not a vanishing
counterexample.  It refutes the implication

```text
positive terminal/some causal T-atom
 + positive prepared T-incidence
 -> positive signed prepared T-contribution.        (3.8)
```

## 4. Conditional reprojection also loses the strategic sign

At the marked target date two, conditional on reaching it, players `o,c`
Quit surely and `d,e` Continue surely.  Let `root_*` be this actual live
root.  For player `o`:

```text
Quit at root_*     gives r_o({o,c})=1,
Continue at root_* gives r_o({c})=1.                (4.1)
```

Player `c` absorbs surely, so an attached continuation payoff is never used.
For every tail vector `x`, therefore,

```text
quittingRootEndpointDifference(reward,x,root_*,o)=0,
quittingRootCoordinateNashDefect(reward,x,root_*,o)=0. (4.2)
```

Thus stripping the history and moving the marked conditional root to date
zero also cannot retain any positive fraction of (3.6).  The gain in (2.3)
and (3.7) came from **surviving the earlier solo absorption**, not from a
profitable action at the eventual collision row.  The example therefore
refutes the second implication

```text
positive signed causal T-atom
 -> positive endpoint/Nash defect at its reached root. (4.3)
```

The identities in (4.2) are exactly the content of the checked declarations
`markedRow_endpointDifference_eq_zero` and
`markedRow_coordinateNashDefect_eq_zero` in the two-player core regression;
the two additional deterministic Continue coordinates do not change either
calculation.

## 5. Why a finite signed window does not repair reprojection

The repaired sprinkler theorem gives a finite window whose **sum** carries
at least half the signed terminal atom.  That statement is valuable, but
aggregation does not provide a single product Bellman row.  In the present
example the window may be chosen to include date two and has total `1/16`,
yet its only positive row is strategically neutral by (4.2).

More generally the exact identity behind signed-stage disintegration is

```text
(L_first(t) p_first(t,T)-L_second(t) p_second(t,T))*r_j(T)>0, (5.1)
```

where `L` is live mass and `p` is conditional root coalition mass.  A
Bellman row sees the normalized roots `p`, not the two unconditional
products `Lp`.  Unequal survival histories can carry all of the sign, and
normalization can erase it.  Merely adding the same positive prepared atom
does not constrain this survival term.

## 6. Sufficient marked-row repairs and an existing consumer

There are two currently relevant ways to cross the **marked-row
reprojection** seam.

### 6.1 One-stage source matching

Supply an actual profile `sigma`, a date `t`, a player `i`, and a pure action
`a` such that the target is literally

```text
quittingStagePureEndpointBehaviorDeviation reward sigma i t a. (6.1)
```

The profiles then agree before `t` and share the exact suffix after `t`.
If, at the actual tail and root,

```text
quittingRootSuccessorPayoff(update root i (pure a),i)
 - quittingRootSuccessorPayoff(root,i) >= eta>0,     (6.2)
```

the checked identity
`quittingTerminalPayoff_stagePureEndpointDeviation_sub_eq_liveMass_mul`
gives a literal source-matched gain `liveMass*eta`.  This is a genuine
Bellman-row input.  Neither terminal-atom disintegration nor sprinkler
incidence supplies (6.1)--(6.2).

### 6.2 The checked positive-target marked-row consumer

For the rectangle branch one may instead retain the exact pure-time
chronology and add the hypotheses of
`exists_markedTailCluster_escape_or_otherNashDefect_of_positiveTargetRectangleStage`:
the observer belongs to a collision terminal, its reward there is positive,
the target observer debt tends to zero, and the global minimum debt is
positive.  That theorem produces the maintained tail-excursion versus
other-player Nash-defect alternative without reprojecting onto the prepared
stage.  These are strategic/minimum fields, not incidence labels.

The first is a sufficient source-matched repair at the same selected row;
the second is the currently checked sequence-level consumer.  Alternatively,
one may retain an earlier paid first-disagreement row: the present example
actually has such a row and does not exclude that chronological consumer.
Any proposed universal prepared-stage or same-marked-row converter must
supply one of these sorts of state-matching data.  A fixed fraction of
unsigned prepared mass is insufficient.

## 7. Source and duplicate audit

Checked files and declarations inspected:

- `TerminalSemanticPositiveSlopeTargetEdgeStateMatchRegression.lean`:
  `profitableEdge_positiveActualAtom_but_markedState_neutral`,
  `markedRow_endpointDifference_eq_zero`, and
  `markedRow_coordinateNashDefect_eq_zero`;
- `TerminalSemanticPureTimeRectangleDisintegration.lean`:
  `exists_prescribedAtom_or_positiveCausalStage_and_actualTerminalMass_of_stoppingLawDebtSlope`;
- `TerminalSemanticPositiveSlopeMarkedRowProvenance.lean`:
  `exists_markedTailCluster_escape_or_otherNashDefect_of_positiveTargetRectangleStage`;
- `TerminalSemanticPlateauLocalizedOtherDefect.lean`:
  `quittingTerminalPayoff_stagePureEndpointDeviation_sub_eq_liveMass_mul`;
- the reviewed fixed-scale recycling and repaired sprinkler notes.

The strategically neutral two-player core is already Lean-checked.  The new
ordinary-mathematical contribution is its exact common full-support Fin4
prefix extension (3.1)--(3.7), which directly targets the current prepared-
stage transport proposal.  It is a narrow architecture no-go, not an export
candidate.

Independent review:
[`CODEX_RAMSEY`](../feedback/CODEX_MINER__FIN4_PREPARED_PREFIX_SIGN_REPROJECTION_NOGO__BY_CODEX_RAMSEY.md),
REVISE to PASS after the marked-row/earlier-first-disagreement scope repair
now incorporated in Sections 1 and 6.
