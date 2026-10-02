# Fin4 collision cycles versus the pair-base missing face

**Author:** CODEX_MINER  
**Status (2026-08-25):** independently reviewed `PASS`; partial positive
alignment proved, full consumer refuted at the displayed interfaces.  Review:
[`CODEX_RAMSEY`](../feedback/CODEX_MINER__FIN4_COLLISION_CYCLE_PAIRBASE_MISSING_FACE_ALIGNMENT__BY_CODEX_RAMSEY.md).

## 1. Question and answer

This note combines two independently reviewed results:

1. [`CODEX_EULER__FIN4_COLLISION_CYCLE_FACE_SIGN_CANCELLATION.md`](CODEX_EULER__FIN4_COLLISION_CYCLE_FACE_SIGN_CANCELLATION.md)
   proves that every directed cycle of a selected Fin4 collision map has an
   edge whose positive singleton join premium becomes weakly nonpositive on a
   nonempty background.
2. [`CODEX_RAMSEY__PAIR_BASE_PAID_SOFTENING_MISSING_BASE_DICHOTOMY.md`](CODEX_RAMSEY__PAIR_BASE_PAID_SOFTENING_MISSING_BASE_DICHOTOMY.md)
   shows that an interior softening of an actual pair-base paid source needs a
   quantitatively negative Continue-minus-Quit average `H_missing` on the face
   omitting the other sure base player.

There is one useful positive composition.  If the collision map has a simple
four-cycle, an alternating pair base guarantees that whichever of its two
base players is selected as the actual paid debtor has its collision
predecessor among the two free players.  The **positive singleton collision**
then gives one correctly oriented missing-face atom of magnitude at least
`Gamma`.

The cycle's **nonpositive background cancellation does not supply the needed
atom**.  When it lies on the missing face, its sign is the opposite one:
Continue-minus-Quit is nonnegative, while interior mixing needs a negative
average.  A triple-to-grand cancellation cannot lie on a pair-base missing
face at all.  In addition, the actual pair-base free law need not charge the
useful positive-collision singleton.  There is no checked debtor/receiver
selection for two- or three-cycles and no quantitative negative margin in the
weak cancellation.

An exact rational four-player table below aligns the collision receiver with
the pair-base paid debtor, aligns a pair-to-triple cancellation with a literal
`H_missing` row, and gives a stationary pair-base paid source.  The cancelling
join increment is exactly zero, the correctly signed singleton atom has zero
source weight, and `H_missing=+1`.  Thus the literal softening takes the
debtor-deletion arm.  This is a sharp interface separation, not a finite
quitting-game counterexample.

## 2. Sources and narrow duplicate audit

The checked declarations used by the two reviewed inputs are:

* `FinFourQuantitativeFullSupportHardResidual.
  exists_fixedPointFree_terminalGap_collisionMap` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  PunishmentNormalAtomicCollisionHandoff.lean`;
* `FinFourQuantitativeFullSupportHardResidual.
  nonempty_singletonBaseSameLawResetProducer` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  SingletonBaseSameLawResetProducer.lean`;
* `FinFourPairBasePaidResetTarget`, `debtor_mem_base`, `debtor_gap`, and
  `nonempty_finFourPairBasePaidResetTarget` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  PairBasePaidResetAlignment.lean`; and
* `quittingPersistentBaseRoot_free_purePayoff_le` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/
  PersistentBaseInducedGame.lean`.

A narrow search for collision-cycle background cancellation, pair-base
missing faces, and `H_missing` found the two source notes and
[`CODEX_RAMSEY__REPAIRED_ATOM_MISSING_FACE_SIGN_SEPARATION.md`](CODEX_RAMSEY__REPAIRED_ATOM_MISSING_FACE_SIGN_SEPARATION.md).
That last note proves that a repaired singleton-law atom has the wrong sign
for the same seam.  It does not compare the collision map with an actual
pair-base debtor, prove the four-cycle alternating-base alignment below, or
give the separation table in Section 7.  No checked declaration already
states this composition.

## 3. Exact sign dictionary

Let a pair-base paid target have base

\[
 B=\{d,e\},
\]

where `d` is the selected paid debtor and `e` is the other sure-Quit base
player.  Let `F=I\B` be the two-player free set, and let `nu` be the selected
induced-Nash product law on subsets of `F`.

On the face where `e` Continues, define

\[
 h_A=r_d(A)-r_d(A\cup\{d\}),\qquad
 H_{\rm miss}=\sum_{A\subseteq F}\nu(A)h_A,          \tag{3.1}
\]

with the empty term using the continuation tail as in the reviewed pair-base
note.  Thus `h_A` is **Continue minus Quit** for debtor `d`.

If `0<p,z<1` are the softened Quit probabilities of `d,e`, exact endpoint
mixing requires

\[
 H_{\rm miss}
 =-{zL_d\over1-z}
 \le -{z\Gamma\over1-z}<0.                           \tag{3.2}
\]

For a collision edge `x->d`, put

\[
 \Delta(x,d;T)
 =r_d(T\cup\{x,d\})-r_d(T\cup\{x\}).                \tag{3.3}
\]

The singleton collision is

\[
 \Delta(x,d;\varnothing)\ge\Gamma.                  \tag{3.4}
\]

If `x in F`, then (3.4) is exactly the correctly oriented missing-face atom

\[
 h_{\{x\}}le-\Gamma.                                \tag{3.5}
\]

By contrast, suppose the collision-cycle cancellation has background `T`
and can be placed on the missing face, so
`A=T union {x} subset F`.  Its conclusion is

\[
 \Delta(x,d;T)\le0,
 \qquad h_A=-\Delta(x,d;T)\ge0.                      \tag{3.6}
\]

This is the opposite sign from (3.2).  The cycle theorem is useful here
through its positive singleton endpoint, not through the sign of the forced
nonsingleton cancellation.

## 4. Incidence classification of the cancelling background

Fix the collision receiver `d`.  The complement of `{x,d}` consists of two
labels.  There are two forms of nonempty collision background.

### 4.1 Pair-to-triple background

If `T={k}` is a singleton, choose the other pair-base player `e` to be the
fourth label, outside `{x,d,k}`.  Then the free set is `F={x,k}`, and the
cancellation is literally the full-free missing-face term

\[
 h_F=r_d(F)-r_d(F\cup\{d\})\ge0.                    \tag{4.1}
\]

So label/face incidence can be aligned, but the sign is wrong for the
interior converter.

### 4.2 Triple-to-grand background

If `T` contains both labels outside `{x,d}`, then
`T union {x}=I\{d}`.  Every possible other base player `e!=d` occurs in this
coalition.  The comparison is therefore conditional on `e` Quitting and
belongs to the positive `L_d` side of the pair-base decomposition, never to
`H_missing`.

Accordingly the theorem does not even guarantee that its marked cancellation
is a missing-face row.  When it is, it yields (4.1), not the negative term
required by (3.2).

## 5. A genuine four-cycle alignment theorem

The positive singleton half of the collision theorem does give a new actual
pair-base source statement when the selected functional graph has a
four-cycle.

### Proposition 5.1 (alternating-base paid-debtor alignment)

Let

\[
 e_0\to e_1\to e_2\to e_3\to e_0                 \tag{5.1}
\]

be a simple directed four-cycle of the selected collision map.  Choose the
alternating pair base

\[
 B=\{e_0,e_2\},\qquad F=\{e_1,e_3\},               \tag{5.2}
\]

and use `nonempty_finFourPairBasePaidResetTarget` with either prescribed
owner in `F`.  Let `d in B` be the debtor returned by the actual target, and
let `x` be the predecessor of `d` in (5.1).  Then

\[
 x\in F,qquad
 r_d(\{x,d\})-r_d(\{x\})\ge\Gamma,                 \tag{5.3}
\]

so the actual target's missing-face table contains the term

\[
 h_{\{x\}}\le-\Gamma.                               \tag{5.4}
\]

#### Proof

The target field `debtor_mem_base` gives `d=e_0` or `d=e_2`.  Their cycle
predecessors are respectively `e_3` and `e_1`, both in `F`.  Apply the
selected singleton collision inequality on the corresponding incoming edge
and reverse its sign according to (3.1).  All objects use the same reward
table.  QED.

This repairs the paid-debtor/receiver label mismatch for the positive
singleton row without prescribing which base player is selected as debtor.
This uniform alternating-cycle guarantee is special to the four-cycle.  It is
not the only functional-graph pattern that can admit such a base: for example,
with two disjoint two-cycles, choosing one vertex from each cycle also puts
both possible debtors' predecessors in the free set.  What fails for a general
two-cycle is a guarantee from that cycle alone: the predecessor of either
cycle vertex is the other cycle vertex.  On a three-cycle, every two-element
subset of the cycle contains the predecessor of one of its elements.  Thus no
two-player base made only of those cycle labels has both possible debtors'
incoming colliders outside the base.  An off-cycle fourth label need not have
any incoming collision edge.  The current target does not let us prescribe
which base player becomes the debtor, so general two- and three-cycle cases
retain a genuine label-selection gap.

The marked cancelling edge supplied somewhere on the four-cycle need not be
the incoming edge of this emergent debtor.  Proposition 5.1 therefore aligns
the singleton collision, not the cycle theorem's selected cancellation.

## 6. The exact missing mass threshold

Assume every terminal reward coordinate and the continuation coordinate used
in the empty term have absolute value at most `M`.  In Proposition 5.1 let

\[
 w=\nu(\{x\}).                                       \tag{6.1}
\]

Every `h_A` is at most `2M`, while (5.4) gives
`h_{\{x\}}<=-Gamma`.  Hence

\[
 H_{\rm miss}
 \le -w\Gamma+(1-w)2M
 =2M-w(\Gamma+2M).                                   \tag{6.2}
\]

In particular,

\[
 w>{2M\over\Gamma+2M}
 \quad\Longrightarrow\quad H_{\rm miss}<0.          \tag{6.3}
\]

For a specified other-base softening probability `0<z<1`, the stronger mass
condition

\[
 w\ge
 {2M+z\Gamma/(1-z)\over\Gamma+2M}                   \tag{6.4}
\]

is sufficient for the inequality required in (3.2).

Neither the pair-base target nor the full-support singleton packet bounds
`nu({x})` below.  The latter is a different auxiliary singleton law, while
`nu` is the selected Nash law on the complement of the pair base.  The
collision-cycle cancellation gives no law weight at all.  Thus (6.2) is a
sharp conditional handoff, not a consumer under the current residual fields.

## 7. Exact rational separation model

The following one-table model simultaneously makes the magnitude and source-
law failures literal.  It realizes the collision cycle, an aligned pair-base
stationary paid source, and an aligned missing-face cancellation.  It does
not claim the global terminal-exploitability witness or positive minimum
required for the full hard residual.

Use labels `0,1,2,3`, let `Gamma=M=1`, and select the four-cycle

\[
 0\to1\to2\to3\to0.                                 \tag{7.1}
\]

All unspecified reward coordinates are zero.  Set the following coordinates.

For player `0`:

```text
r_0({3})       = 0,   r_0({0,3})       = 1,
r_0({1,3})     = 0,   r_0({0,1,3})     = 0,
r_0({2,3})     = 0,   r_0({0,2,3})     = 1,
r_0({1,2,3})   = 0,   r_0({0,1,2,3})   = 1,
r_0({1,2})     = 1,   r_0({0,1,2})     = 0,
r_0({1})       = 1,   r_0({0,1})       = 0.
```

For player `1`:

```text
r_1({0})       = 0,   r_1({0,1})       = 1,
r_1({0,2})     = 0,   r_1({0,1,2})     = 1,
r_1({0,3})     = 0,   r_1({0,1,3})     = 1,
r_1({0,2,3})   = 0,   r_1({0,1,2,3})   = 1.
```

For player `2`:

```text
r_2({1})       = 0,   r_2({1,2})       = 1,
r_2({0,1})     = 0,   r_2({0,1,2})     = 1,
r_2({1,3})     = 0,   r_2({1,2,3})     = 1,
r_2({0,1,3})   = 0,   r_2({0,1,2,3})   = 1.
```

For player `3`:

```text
r_3({2})       = 0,   r_3({2,3})       = 1,
r_3({0,2})     = 0,   r_3({0,2,3})     = 1,
r_3({1,2})     = 0,   r_3({1,2,3})     = 1,
r_3({0,1,2})   = 0,   r_3({0,1,2,3})   = 0.
```

All coordinates lie in `[0,1]`.

### Proposition 7.1 (aligned zero cancellation and unused gap atom)

This table has the following properties.

1. Every edge in (7.1) has singleton collision gain exactly one.
2. The edge `3->0` has the exactly zero pair-to-triple cancellation

   \[
   r_0(\{0,1,3\})-r_0(\{1,3\})=0.                  \tag{7.2}
   \]

   The edge `2->3` also has the exactly zero triple-to-grand cancellation

   \[
   r_3(I)-r_3(\{0,1,2\})=0.                         \tag{7.3}
   \]
3. Take pair base `B={0,2}` and the free product law
   `nu=delta_{ {1}}`: players `0,1,2` Quit surely and player `3` Continues
   surely.  This is an exact induced-Nash point for the free players.
4. Player `0` is the unique positive-debt base player at this stationary
   source, with unrestricted debt exactly one.  Its pure Quit payoff is zero
   and its pure Continue/Never payoff is one, so the literal profile carries
   a paid first-disagreement row of gain one.
5. With debtor `d=0`, other base player `e=2`, and free set `F={1,3}`, the
   incoming collision atom, aligned cancellation, and actual missing average
   are

   \[
   h_{\{3\}}=-1,
   \qquad h_{\{1,3\}}=0,
   \qquad H_{\rm miss}=h_{\{1\}}=1.                 \tag{7.4}
   \]

   Thus the correctly signed full-gap atom and the aligned zero cancellation
   both have `nu`-mass zero.
6. The positive conditional-other-base average is also `L_0=1`.  Therefore
   for every `z in [0,1]`, the Continue-minus-Quit advantage of player `0`
   on the two-base softening face is

   \[
   zL_0+(1-z)H_{\rm miss}=1.                         \tag{7.5}
   \]

   Every exact softened root preserving this free law and assigning positive
   Quit probability to `0` is impossible; the exact dichotomy takes the
   debtor-deletion arm `p=0`.

#### Proof

The four singleton equalities are the first displayed pair for each player's
coordinate.  Equations (7.2)--(7.3) are displayed directly.

At the pair-base row, player `1`'s pure-Quit and pure-Continue payoffs are
respectively

\[
 r_1(\{0,1,2\})=1,
 \qquad r_1(\{0,2\})=0,
\]

so prescribed Quit is optimal.  Player `3`'s endpoints are

\[
 r_3(I)=r_3(\{0,1,2\})=0,
\]

so prescribed Continue is optimal.  Hence the free product point is induced
Nash.

For player `0`, the prescribed and Continue endpoints are

\[
 r_0(\{0,1,2\})=0,
 \qquad r_0(\{1,2\})=1,
\]

giving debt and paid pure-time difference one.  For player `2`, they are

\[
 r_2(\{0,1,2\})=1,
 \qquad r_2(\{0,1\})=0,
\]

so its debt is zero.  Both free debts are zero by the induced-Nash
calculations.  Because another player Quits surely at date zero in every one
of these comparisons, arbitrary behavioral deviations reduce to the two root
endpoints; these are unrestricted terminal-semantic debts.

Finally the three values in (7.4) are

\[
 r_0(\{3\})-r_0(\{0,3\})=-1,
\]

\[
 r_0(\{1,3\})-r_0(\{0,1,3\})=0,
\]

and

\[
 r_0(\{1\})-r_0(\{0,1\})=1.
\]

Since `nu` is concentrated on `{1}`, the last value is `H_missing`.  The
conditional-`2` leave advantage is

\[
 L_0=r_0(\{1,2\})-r_0(\{0,1,2\})=1,
\]

which proves (7.5).  QED.

The example rules out any strictly negative quantitative upgrade

\[
 \Delta(x,d;T)\le-\kappa(\Gamma,M),
 \qquad \kappa(\Gamma,M)>0,                         \tag{7.6}
\]

from the collision-cycle inequalities, pair-base induced-Nash source, and
paid-debtor gap alone: here `Gamma=M=1` and the aligned cancellation equals
zero.  It does not rule out an upgrade using additional, presently unused
fields of the full hard residual or the global terminal witness.

## 8. Exact remaining interface

The synthesis leaves three independent requirements.

1. **Label/source selection.**  Outside the four-cycle alternating-base case,
   the pair-base target does not prescribe its debtor to be the receiver of a
   useful collision edge.  Even in the four-cycle case, the cycle theorem's
   marked cancelling edge need not be the incoming edge of that debtor.
2. **Law weight.**  The actual free law `nu` needs quantitative mass on the
   correctly signed singleton predecessor atom, or a direct weighted
   inequality for `H_missing`.  Collision and full singleton-packet support
   do not provide this.
3. **Magnitude/sign.**  A weakly nonpositive collision join is a nonnegative
   `h_A`, the wrong direction for (3.2), and may be exactly zero.  The
   full-gap singleton collision has the correct sign and magnitude but is
   useful only after the law-weight gate.

A conjecture-facing next theorem would therefore need one of:

```text
four-cycle alternating pair-base target
+ nu({predecessor(debtor)}) above the threshold (6.4),
```

or directly

```text
an actual pair-base paid target with
H_missing <= -kappa < 0.
```

The collision-cycle cancellation alone supplies neither.  The present result
does not produce a Bellman root, terminal approximation, payoff return, or
maintained rank descent.

## 9. Review request

Please independently check:

1. the sign conversion (3.4)--(3.6);
2. pair-to-triple versus triple-to-grand incidence in Section 4;
3. the alternating-base debtor alignment in Proposition 5.1 and its failure
   for two- and three-cycles;
4. constants in (6.2)--(6.4);
5. every collision, induced-Nash, unrestricted-debt, paid-row, and
   `H_missing/L` computation in Proposition 7.1; and
6. the strict scope of the separation from the full hard residual.
