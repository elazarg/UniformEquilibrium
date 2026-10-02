# Fin4 collision cycles force a nonsingleton face-sign cancellation

## Status

**Independent review `PASS`; narrow export packet assembled.**  See
[`CODEX_MINER`](../feedback/CODEX_EULER__FIN4_COLLISION_CYCLE_FACE_SIGN_CANCELLATION__BY_CODEX_MINER.md).

Theorem 3.1 below is a direct same-table consequence of the checked Fin4
hard residual.  It uses the full family of singleton collisions together with
one prescribed-owner singleton-base induced Nash source.  It gives a strict
finite reduction: on every directed cycle of the selected collision map, at
least one singleton-positive join edge becomes nonpositive on a nonempty
background coalition.

The result is stronger than the originally sought pointwise
Poincare--Miranda alignment in one direction.  If the selected collision
premiums remained positive on every background, exact induced-Nash
complementarity would propagate sure quitting around the collision cycle and
contradict the prescribed owner's positive debt.  Thus the robust upper-face
signs needed by a stationary box cannot all coexist; a literal pair-to-triple
or triple-to-grand cancellation is forced.

Only Theorem 3.1 and Corollary 3.2 are proposed for export.  The exploratory
stationary-box discussion remains internal.

## 1. Question and narrow source audit

Let $I=\operatorname{Fin}4$, let $r$ be bounded by $M$, and let

```text
residual : FinFourQuantitativeFullSupportHardResidual r M.
```

The checked theorem

```text
FinFourQuantitativeFullSupportHardResidual.
  exists_fixedPointFree_terminalGap_collisionMap
```

in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`
selects a map $f:I\to I$ such that $f(e)\ne e$ and

\[
r_{f(e)}(\{e,f(e)\})-r_{f(e)}(\{e\})\ge\Gamma,       \tag{1.1}
\]

where $\Gamma>0$ is the residual terminal gap.

For every prescribed singleton owner $e$, the checked theorem

```text
FinFourQuantitativeFullSupportHardResidual.
  nonempty_singletonBaseSameLawResetProducer
```

in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/SingletonBaseSameLawResetProducer.lean`
selects an actual stationary source in which:

* $e$ Quits surely;
* the other three players form a Nash point of the finite binary game induced
  by the persistent base $\{e\}$;
* the unrestricted terminal-semantic debt of $e$ is at least $\Gamma$.

The induced-game Nash property is exposed by
`isNash_of_mem_quittingPersistentBaseNashSet` and
`quittingPersistentBaseRoot_free_purePayoff_le` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`.

The face-numerator identities used for interpretation are in
`UniformEquilibrium/Quitting/Stationary/FaceNumerator.lean`.  A narrow search
found no existing theorem asserting the cycle cancellation below.

## 2. Robust collision premiums

For an edge $e\to j$, with $j\ne e$, and a background

\[
T\subseteq I\setminus\{e,j\},
\]

define the join increment

\[
\Delta(e,j;T)
 =r_j(T\cup\{e,j\})-r_j(T\cup\{e\}).                \tag{2.1}
\]

If player $e$ Quits surely in a product row, the pure-Quit minus
pure-Continue endpoint difference of $j$ is exactly a Bernoulli average of
these increments over the other two players:

\[
Q_j-C_j
 =\sum_{T\subseteq I\setminus\{e,j\}}
      w(T)\Delta(e,j;T),                             \tag{2.2}
\]

where the nonnegative weights $w(T)$ sum to one.  This is just conditioning
the product opponent row on the sure quitter $e$.  In division-free terms,
the opponents' Continue mass is zero, so (2.2) is also the face numerator
$F_j$.

Consequently, if every $\Delta(e,j;T)>0$, then $j$ strictly prefers Quit
at every product row having $e$ sure.  At an induced persistent-base Nash
point, this forces $j$'s own Quit probability to equal one: otherwise the
pure-Quit payoff would strictly exceed the prescribed convex mixture,
contradicting the exact Nash inequality.

This implication uses arbitrary background hazards and is precisely the
uniform upper-face sign missing from the singleton collision (1.1).

## 3. Main finite reduction

### Theorem 3.1 (collision-cycle background cancellation)

Assume $0\le M$, $|r_i(S)|\le M$, and let `residual` be as above.
Choose any fixed-point-free terminal-gap collision map $f$ satisfying
(1.1).  Let

\[
e_0\to e_1\to\cdots\to e_{m-1}\to e_0,
\qquad 2\le m\le4,                                  \tag{3.1}
\]

be any simple directed cycle of $f$, so
$f(e_t)=e_{t+1\bmod m}$.

Then there are an edge $e_t\to e_{t+1}$ of this cycle and a **nonempty**
background

\[
\varnothing\ne T\subseteq
 I\setminus\{e_t,e_{t+1}}
\]

such that

\[
r_{e_{t+1}}(T\cup\{e_t,e_{t+1}})
 \le r_{e_{t+1}}(T\cup\{e_t}).                     \tag{3.2}
\]

Thus the same receiver has a join gain at least $\Gamma$ at the singleton
background $\{e_t\}$, but a weakly nonpositive join gain after adding one
or both of the remaining Fin4 labels.

#### Proof

Suppose instead that every cycle edge is robustly positive:

\[
\Delta(e_t,e_{t+1};T)>0
\quad\text{for every }t\text{ and every }
T\subseteq I\setminus\{e_t,e_{t+1}}.               \tag{3.3}
\]

Apply `nonempty_singletonBaseSameLawResetProducer` with prescribed owner
$e_0$.  Let `root` be its stationary root and write

\[
p_i=\Pr_{\operatorname{root}_i}(\mathrm{Quit}).
\]

Then $p_{e_0}=1$, and the
restriction to $I\setminus\{e_0\}$ is an exact induced binary-game Nash
point.

We propagate sure quitting forward around (3.1).  Assume $p_{e_t}=1$.
For $t<m-1$, player $e_{t+1}$ is a free player of the singleton-base
game.  Formula (2.2) and (3.3) give

\[
Q_{e_{t+1}}-C_{e_{t+1}}>0.
\]

The free induced-Nash inequality therefore forces
$p_{e_{t+1}}=1$.  Starting from $p_{e_0}=1$, induction gives

\[
p_{e_1}=\cdots=p_{e_{m-1}}=1.                       \tag{3.4}
\]

Now apply the robust premium on the final edge
$e_{m-1}\to e_0$.  Since $e_{m-1}$ Quits surely, (2.2) gives

\[
Q_{e_0}-C_{e_0}>0.                                  \tag{3.5}
\]

The source prescribes $e_0$ to Quit surely.  Moreover an opponent Quits
surely by (3.4), so play ends at date zero regardless of $e_0$'s action.
Every unrestricted behavioral deviation by $e_0$ therefore reduces to its
date-zero Quit/Continue mixture.  By (3.5), Quit is the unique best response,
and the source payoff already equals its unrestricted cap.  Hence the
terminal-semantic debt of $e_0$ is zero.

This contradicts the producer field

\[
\Gamma\le d_{e_0}(\text{source}),
\]

with $\Gamma>0$.  Therefore (3.3) fails on some cycle edge and background,
giving (3.2).  The failing background cannot be empty, because (1.1) makes

\[
\Delta(e_t,e_{t+1};\varnothing)\ge\Gamma>0.
\]

This proves the theorem. □

### Corollary 3.2 (finite Fin4 sign-reversal screen)

Every selected collision-map cycle in a maintained Fin4 hard residual
contains one of the following literal nonsingleton reversals.

1. **Pair-to-triple cancellation:** for the third label (k),

   \[
   r_j(\{e,j,k\})-r_j(\{e,k\})\le0;
   \]

2. **Triple-to-grand cancellation:** for the two remaining labels (k,l),

   \[
   r_j(I)-r_j(\{e,k,l\})\le0.
   \]

The edge simultaneously satisfies

\[
r_j(\{e,j\})-r_j(\{e\})\ge\Gamma.                  \tag{3.6}
\]

The alternatives are inclusive: a cycle may have several cancelling edges
or both types of cancelling background.

## 4. Relation to the stationary sign-box route

For player (j=f(e)), the singleton collision gives one positive corner of
the face (q_e=1).  A Poincare--Miranda construction would need a sign valid
on the entire assigned face, not merely at that corner.  Theorem 3.1 proves
that the most direct attempted extension is impossible in the hard residual:
on every collision-map cycle, at least one assigned upper face contains both

* the positive singleton corner (3.6), and
* a pure nonsingleton corner with the nonpositive sign (3.2).

Relabeling does not repair this.  The collision map is already allowed to be
any finite choice of the checked singleton colliders, and the conclusion is
asserted on every directed cycle of that chosen map.

Boxes not anchored at zero or one remain logically possible.  The theorem
does not rule out an interior face-sign box or a common face-numerator zero.
It says that the checked singleton collisions plus the full family of
prescribed-owner stationary handoffs do not assemble the obvious
singleton-corner box.  Any successful stationary producer must use the
forced cancellation quantitatively, choose different blocker labels, or work
on a genuinely interior box.

## 5. Why this is a strict maintained-residual reduction

The checked residual previously supplied four positive singleton collision
edges but no nonsingleton sign attached to their functional graph.  Theorem
3.1 adds a finite same-table constraint using no chronology or source
identification:

> every directed cycle of any selected collision map has a marked edge and a
> nonempty background on which its collision premium reverses weakly.

For Fin4 there are only two possible background cardinalities, so the output
is literally a pair-to-triple or triple-to-grand inequality.  It is not
another classification of the normalized singleton matrix.

Equivalently, the subclass in which one selected collision cycle has strict
positive join premium on every background is empty inside the maintained
hard residual.  Outside the residual, that robust-cycle subclass is consumed
by the same proof: the prescribed singleton-base positive-debt source cannot
exist.  The conclusion is therefore a producer-facing exclusion, not merely
a supplied common-zero verifier.

## 6. Exact scope and nonclaims

The theorem uses:

* the actual terminal-gap collision map;
* one actual prescribed-owner singleton-base induced Nash point;
* the owner's full-gap unrestricted terminal-semantic debt; and
* literal coalition rewards on the same table.

It does **not** claim:

* a Poincare--Miranda box or a fully mixed stationary equilibrium;
* that the cancelling background has positive probability at a separately
  selected pair-base or repaired source;
* a Bellman edge, chronology, payoff return, or debt descent;
* that the cancelling edge aligns with the hard principal or marked lasso;
* a quantitative negative margin in (3.2); or
* closure of the Fin4 conjecture.

The next finite question is whether the positive singleton/weakly negative
nonsingleton sign reversal on one collision-cycle edge can be re-equilibrated
with the two remaining labels into an existing singleton- or pair-base
all-behavior compiler.

## 7. Requested independent review

Please check:

1. the Bernoulli-average identity (2.2), including terminal-set labels;
2. propagation of sure quitting from strict endpoint advantage at the induced
   persistent-base Nash point;
3. the final reduction of the owner's unrestricted cap to the date-zero
   endpoints after an opponent is forced sure;
4. the cycle indexing and the claim that the failing background is nonempty;
5. novelty against existing atomic-collision and Möbius-incidence
   declarations; and
6. whether this finite nonsingleton cancellation changes the maintained
   residual enough for a later export packet.
