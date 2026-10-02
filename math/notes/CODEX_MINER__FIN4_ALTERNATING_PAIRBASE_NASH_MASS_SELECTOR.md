# Fin4 alternating pair-base Nash mass: exact selector and no uniform floor

**Author:** CODEX_MINER  
**Status (2026-08-25):** reviewed/PASS as an internal selector and no-go;
quantitative mass selector refuted at the displayed interfaces.  Independent
review:
[`CODEX_EULER`](../feedback/CODEX_MINER__FIN4_ALTERNATING_PAIRBASE_NASH_MASS_SELECTOR__BY_CODEX_EULER.md).
The pure arm reaches the checked finite paid-chain residual, not a terminating
rank or conjecture closure.

## 1. Question and verdict

Continue from
[`CODEX_MINER__FIN4_COLLISION_CYCLE_PAIRBASE_MISSING_FACE_ALIGNMENT.md`](CODEX_MINER__FIN4_COLLISION_CYCLE_PAIRBASE_MISSING_FACE_ALIGNMENT.md).
On a selected collision four-cycle, the alternating pair base has this useful
property: whichever base player is selected as the paid debtor, its collision
predecessor is one of the two free players.  The predecessor singleton is a
correctly signed `H_missing` atom of size at least the terminal gap `Gamma`.

The remaining question is whether the induced persistent-base Nash point can
be selected so that this singleton atom has positive, quantitatively
controlled product mass.

The answer has three parts.

1. The full two-free-player equilibrium correspondence gives an exact
   selector dichotomy: either some actual gap debtor has positive predecessor-
   singleton mass at an induced Nash point, or there is a **pure** induced
   Nash point whose full-gap paid debtor is on a precisely classified bad
   boundary cell.
2. In the second arm, the checked large-base finite dispatch already turns
   the pure point into a `PurePaidBaseLeaveSource` and then a
   `HasPurePaidNormalChainFiniteResidual`.  This is a real existing consumer,
   but not a uniform-payoff or maintained-rank conclusion.
3. Neither positivity nor a lower bound depending only on `Gamma,M` is
   forced.  One exact bounded table has a unique all-Continue free equilibrium
   and zero predecessor mass.  A rational family has a unique fully mixed
   free equilibrium with predecessor mass `epsilon/2`, while keeping
   `Gamma=M=1`, the collision four-cycle, and the paid base debt equal to one.

Thus the mass gate cannot replace the checked pure/mixed paid-chain dispatch.
The full hard residual may contain additional constraints, but the current
collision, pair-base source, and terminal-gap interfaces do not control the
needed Nash atom.

## 2. Narrow source and duplicate audit

Besides the reviewed collision and missing-face notes, I inspected:

* `quittingPersistentBaseNashSet`,
  `isNash_of_mem_quittingPersistentBaseNashSet`, and
  `quittingPersistentBaseRoot_free_purePayoff_le` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/
  PersistentBaseInducedGame.lean`;
* `quittingPersistentLargeBaseExcess` and
  `exists_uniformPayoff_or_persistentLargeBase_pos_gap` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/
  PersistentBaseConcreteGap.lean`;
* `paidPure_or_paidMixed_of_actual_largeBase_gap_labels` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/
  LargePersistentBaseActualAdapter.lean`;
* `PurePaidBaseLeaveSource` and the pure deletion consumers in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/
  PurePaidBaseLeaveDescent.lean`; and
* `QuittingTerminalExploitabilityWitness.hasSupportTwoPaidChainResidual` and
  `hasSupportTwoNormalPaidChainResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/
  PaidChainSupportTwoAggregate.lean` and
  `StrictToggleLargeBasePaidChain.lean`.

`PaidSignFailureBinaryReequilibration.lean` has an explicit three-face binary
selector, but it assumes a source-native paid pure deletion and additional
join/switch signs.  Those hypotheses are not outputs of the alternating
pair-base collision alignment.  No existing declaration selects a Nash point
by maximizing one specified product atom or supplies a positive floor for
that atom.

## 3. The complete two-player difference description

Write the alternating base and free labels as

\[
 B=\{b_0,b_1\},\qquad F=\{x,k\},                    \tag{3.1}
\]

where `x` is the collision predecessor of `b_0` and `k` is the collision
predecessor of `b_1`.  Let

\[
 u=\Pr(x\text{ Quits}),\qquad v=\Pr(k\text{ Quits}). \tag{3.2}
\]

For the induced two-player binary game, define the four endpoint differences

\[
 \alpha_0=Q_x-C_x\text{ when }k=C,
 \qquad
 \alpha_1=Q_x-C_x\text{ when }k=Q,
\]

\[
 \beta_0=Q_k-C_k\text{ when }x=C,
 \qquad
 \beta_1=Q_k-C_k\text{ when }x=Q.                  \tag{3.3}
\]

Then

\[
 g_x(v)=(1-v)\alpha_0+v\alpha_1,
 \qquad
 g_k(u)=(1-u)\beta_0+u\beta_1.                     \tag{3.4}
\]

The exact Nash conditions are

\[
\begin{array}{lll}
u=0&\Rightarrow&g_x(v)\le0,\\
0<u<1&\Rightarrow&g_x(v)=0,\\
u=1&\Rightarrow&g_x(v)\ge0,
\end{array}
\qquad
\begin{array}{lll}
v=0&\Rightarrow&g_k(u)\le0,\\
0<v<1&\Rightarrow&g_k(u)=0,\\
v=1&\Rightarrow&g_k(u)\ge0.
\end{array}                                                   \tag{3.5}
\]

In particular, the four pure cells are Nash under exactly

\[
\begin{array}{c|c}
(u,v)&\text{conditions}\\ \hline
(0,0)&\alpha_0\le0,\ \beta_0\le0,\\
(1,0)&\alpha_0\ge0,\ \beta_1\le0,\\
(0,1)&\alpha_1\le0,\ \beta_0\ge0,\\
(1,1)&\alpha_1\ge0,\ \beta_1\ge0.
\end{array}                                                   \tag{3.6}
\]

In a nondegenerate mixed chamber, the unique indifference rates are

\[
 u={\beta_0\over\beta_0-\beta_1},
 \qquad
 v={\alpha_0\over\alpha_0-\alpha_1}.               \tag{3.7}
\]

There is no terminal-gap quantity in (3.3).  These are the free players' own
payoff differences on coalitions containing **both** base players.  The
collision inequalities constrain receiver coordinates at singleton rows;
the paid base debt constrains a base player's coordinate.  Hence the four
free-game coefficients can vary independently at the present interface.

## 4. Coupled debtor/mass selector

The two possible predecessor-singleton masses are

\[
 w_0(u,v)=u(1-v),
 \qquad
 w_1(u,v)=v(1-u),                                   \tag{4.1}
\]

for base debtors `b_0,b_1`, respectively.

At every induced Nash point in the terminal-counterexample regime, the two
free coordinates realize their unrestricted behavioral caps.  Applying the
fixed terminal gap at its literal stationary profile therefore selects at
least one base player `d` with terminal-semantic debt at least `Gamma`.  Let
`D(u,v)` be the nonempty set of such base debtors.

### Proposition 4.1 (positive predecessor mass or a pure bad cell)

Exactly one of the following exclusive cases holds.

1. There are an induced Nash point `(u,v)` and `b_i in D(u,v)` such that

   \[
   w_i(u,v)>0.                                       \tag{4.2}
   \]

2. No such pair exists.  Then there is a **pure** induced Nash point, and at
   every pure Nash point each full-gap debtor is classified as follows:

   * at `(0,0)` or `(1,1)`, either base debtor may occur, but both predecessor
     singleton masses vanish;
   * at `(1,0)`, every full-gap debtor is `b_1`, whose predecessor `k` is the
     absent free player;
   * at `(0,1)`, every full-gap debtor is `b_0`, whose predecessor `x` is the
     absent free player.

#### Proof

If case 1 fails, there can be no fully interior Nash point: at such a point
both quantities in (4.1) are positive, while `D(u,v)` is nonempty.

Every two-by-two game with no fully interior Nash point has a pure Nash point.
One direct proof starts from any mixed Nash point.  If one coordinate is
strictly mixed and the other is pure, the mixed player's relevant endpoint
difference is zero.  The pure player's affine best-response inequality at
the mixture implies the same weak inequality at at least one endpoint.  Move
the mixed player to that endpoint; the zero difference keeps the other
player optimal, producing a pure Nash point.  If both coordinates are
strictly mixed, the point was fully interior, already excluded.

At the four pure cells, evaluate (4.1).  At `(1,0)`, `w_0=1` and `w_1=0`, so
failure of case 1 excludes `b_0` from `D(1,0)` and forces every gap debtor to
be `b_1`.  The `(0,1)` case is symmetric.  At `(0,0)` and `(1,1)`, both
masses vanish.  QED.

The debtor correspondence is essential.  Maximizing `w_0` over the Nash set
while holding a debtor selected at a different point is invalid: reselecting
the free law can change the base payoff averages and which base player carries
the terminal gap.

## 5. What the pure bad cell already feeds

Case 2 is not a new semantic rank decrease, but it is not an unrecorded dead
end.  A pure induced Nash point, together with its full-gap base debtor and
the other base owner, is exactly the finite source shape of
`PurePaidBaseLeaveSource`:

* the original free cell is pure Nash;
* the selected base debtor Quits surely;
* deleting that debtor gives a leave advantage at least `Gamma`; and
* the four labels exhaust `Fin 4`.

More globally, on this fixed two-by-two face the terminal gap gives

\[
 \Gamma\le
 \operatorname{quittingPersistentLargeBaseExcess}(point)       \tag{5.1}
\]

for every induced Nash point: the free players are solved, there are no
outside labels, and the terminal-gap deviation must be a base-player leave.
Thus the checked hypotheses of
`paidPure_or_paidMixed_of_actual_largeBase_gap_labels` hold with the same
`Gamma`.  In the no-uniform-payoff branch, one can alternatively obtain a
positive uniform face gap from
`exists_uniformPayoff_or_persistentLargeBase_pos_gap`.

The checked support-two dispatch then gives:

```text
PurePaidBaseLeaveSource
  -> HasPurePaidNormalChainFiniteResidual
```

in the pure arm, or the existing paid mixed-deletion residual in the mixed
arm.  In particular, the pure chain tests stability after deleting the paid
base member and dispatches free sign failure or owner-floor failure through
its existing repaired/sure-exit/normality consumers.

This does **not** finish case 2.  The all-Continue and all-Quit free cells, and
the mismatched singleton cells in Proposition 4.1, do not themselves assert
post-deletion stability, a floor inequality, a cumulative return, or a
minimum-fiber rank drop.  The checked paid-chain output retains finite
residuals precisely for those missing facts.  The collision predecessor
inequality concerns the paid player's missing-base reward row; it does not
settle the free players' post-deletion best replies or the retained owner's
floor.

## 6. Zero mass can be uniquely forced

Here is a modular exact source showing that qualitative positive mass cannot
be selected from the current interfaces.

Use the collision four-cycle

\[
 0\to1\to2\to3\to0,                                 \tag{6.1}
\]

take alternating base `B={0,2}`, free players `k=1,x=3`, and put
`Gamma=M=1`.  Set all unspecified coordinates to zero.

For the paid base player `0`, for every `A subset {1,3}` set

\[
 r_0(A\cup\{2\})=1,
 \qquad
 r_0(A\cup\{0,2\})=0,                              \tag{6.2}
\]

and set `r_0({3})=0`, `r_0({0,3})=1`.  Thus player `0` has debt one at every
induced free law, and its incoming singleton collision has gain one.

For player `2`, for every `A subset {1,3}` set

\[
 r_2(A\cup\{0,2\})=1,
 \qquad
 r_2(A\cup\{0\})=0.                                \tag{6.3}
\]

Thus player `2` has zero debt.  Complete the singleton collision cycle by
setting

\[
 r_1(\{0,1\})-r_1(\{0\})=1,
\]

\[
 r_2(\{1,2\})-r_2(\{1\})=1,
 \qquad
 r_3(\{2,3\})-r_3(\{2\})=1.                       \tag{6.4}
\]

Finally make both free players strictly prefer Continue on every row
containing the pair base by setting:

```text
r_3({0,2})=0,       r_3({0,2,3})=-1,
r_3({0,1,2})=0,     r_3(I)=-1,
r_1({0,2})=0,       r_1({0,1,2})=-1,
r_1({0,2,3})=0,     r_1(I)=-1.                     (6.5)
```

There is no coordinate conflict among (6.2)--(6.5).  The free induced game
has the unique Nash point `(u,v)=(0,0)`.  Player `0` is its unique paid base
debtor of gap one, but

\[
 \nu(\{3\})=u(1-v)=0.                               \tag{6.6}
\]

All four singleton collisions still have gain one.  The negative rows in
(6.5) themselves provide nonsingleton collision cancellations, so the cycle
sign theorem is respected.  This is an exact stationary pair-base paid source
and collision-table model.  It does not assert the global terminal witness,
positive minimum, or remaining hard-residual fields.

## 7. Positive mass has no quantitative floor

Even excluding boundary equilibria does not produce a bound.  Keep
(6.1)--(6.4), but replace the free game by the following family, where
`epsilon` is any rational number with `0<epsilon<1`.

For predecessor `x=3`, set its Quit-minus-Continue differences to

\[
 \alpha_0=1,
 \qquad
 \alpha_1=-1.                                       \tag{7.1}
\]

Concretely one may take

```text
r_3({0,2})=0,       r_3({0,2,3})=1,
r_3({0,1,2})=0,     r_3(I)=-1.
```

For `k=1`, set

\[
 \beta_0=-\epsilon,
 \qquad
 \beta_1=1-\epsilon,                                \tag{7.2}
\]

for example

```text
r_1({0,2})=0,       r_1({0,1,2})=-epsilon,
r_1({0,2,3})=0,     r_1(I)=1-epsilon.
```

Then

\[
 g_3(v)=1-2v,
 \qquad
 g_1(u)=u-\epsilon.                                 \tag{7.3}
\]

There is no pure Nash point, and the unique induced Nash point is

\[
 u=\epsilon,
 \qquad v={1\over2}.                                \tag{7.4}
\]

The paid debtor is still uniquely player `0`, with debt one independently of
the free law by (6.2)--(6.3).  Its correctly signed predecessor singleton has
mass

\[
 \nu(\{3\})=u(1-v)={\epsilon\over2}.                \tag{7.5}
\]

All rewards remain bounded by one, all four singleton collision gains remain
one, and the collision-cycle cancellation conclusion holds (for example the
`0->1` background containing player `2` has join increment `-epsilon`).
Letting `epsilon` decrease through positive rationals proves that no function

\[
 c(\Gamma,M)>0                                      \tag{7.6}
\]

can lower-bound the desired atom using only the collision cycle, reward
bound, induced-Nash property, and full-gap paid base source: here
`Gamma=M=1` throughout.

This family also shows why compactness of the Nash set for each fixed table
does not help uniformly across tables.  A maximizing selector attains a
positive mass in each member of the family, but the attained maxima tend to
zero because the free-game indifference coefficient `beta_0` has no uniform
separation from zero.

## 8. Exact remaining alternatives

The strongest honest synthesis is now:

```text
alternating collision four-cycle pair base
  -> good gap-debtor/predecessor mass at some Nash point
     (positive but not uniformly quantitative),
  OR pure paid boundary source
     -> checked pure paid-chain finite residual.
```

To cross the pair-base missing-face seam quantitatively, the first arm still
needs a new lower bound at least as strong as the threshold in Section 6 of
the preceding note.  The second arm must clear the existing post-deletion
free-sign and owner-floor residuals.  Neither follows from the collision
singleton premium or from the weak cycle cancellation.

No claim is made that the local models in Sections 6--7 satisfy the ambient
terminal-exploitability witness or full hard residual.  They sharply refute a
selector or quantitative floor from the displayed collision/pair-source
interfaces; an implication using additional global residual fields remains a
separate conjecture-facing question.

## 9. Review request

Please independently check:

1. the Nash correspondence (3.5)--(3.7);
2. the coupled debtor classification in Proposition 4.1;
3. the passage from a pure bad cell to the checked pure paid-chain source and
   the exact remaining residuals;
4. the claim (5.1) that the terminal gap localizes to base leave uniformly on
   the full induced Nash set;
5. the collision, debt, uniqueness, and zero-mass assertions in Section 6;
6. the unique mixed equilibrium and `epsilon/2` mass in Section 7; and
7. the strict interface-only scope of both separation models.
