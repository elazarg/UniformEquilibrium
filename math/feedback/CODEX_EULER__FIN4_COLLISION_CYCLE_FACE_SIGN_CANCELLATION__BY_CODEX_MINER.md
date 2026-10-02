# Review of Fin4 collision-cycle face-sign cancellation

**Reviewer:** CODEX_MINER  
**Date:** 2026-08-25  
**Verdict:** `PASS`

I independently checked Theorem 3.1 and Corollary 3.2 in
[`CODEX_EULER__FIN4_COLLISION_CYCLE_FACE_SIGN_CANCELLATION.md`](../notes/CODEX_EULER__FIN4_COLLISION_CYCLE_FACE_SIGN_CANCELLATION.md)
against the current collision-map, persistent-base Nash, and
singleton-base producer declarations.  I found no mathematical objection.

## 1. Exact claim checked

Fix a terminal-gap collision selector `f : Fin 4 -> Fin 4`, and fix any
simple directed cycle

\[
 e_0\to e_1\to\cdots\to e_{m-1}\to e_0,qquad 2\le m\le4.
\]

For an edge `e->j` and
`T subset I\{e,j}`, write

\[
 \Delta(e,j;T)=r_j(T\cup\{e,j\})-r_j(T\cup\{e\}).
\]

The reviewed conclusion is that some cycle edge has a nonempty background
with `Delta<=0`, while its empty-background collision gain is at least the
positive terminal gap.

## 2. Bernoulli-average identity and robust positivity

If `e` Quits surely, then conditional on the independent actions of the two
labels outside `{e,j}`, pure Quit by `j` produces `T union {e,j}` and pure
Continue produces `T union {e}`.  Hence

\[
 Q_j-C_j=\sum_{T\subseteq I\setminus\{e,j\}}w(T)\Delta(e,j;T),
\]

where the Bernoulli product weights are nonnegative and sum to one.  This
also remains correct later in the propagation when other already-propagated
players Quit surely: the weights are then supported only on backgrounds
containing those players.  Strict positivity on **every** background still
makes the average strictly positive.

Because an opponent Quits surely, the opponents' all-Continue mass for `j`
is zero.  Thus the division-free face numerator is indeed the same endpoint
difference in this row.  No conditional quotient or boundary division is
being used.

The negation of the robust hypothesis is also handled with the right sign:
failure of `Delta>0` gives `Delta<=0`, not a claimed strict negative margin.

## 3. Sure-quitting propagation at the induced Nash point

Apply
`FinFourQuantitativeFullSupportHardResidual.nonempty_singletonBaseSameLawResetProducer`
only once, with prescribed owner `e_0`.  Definitionally its persistent base
root makes `e_0` Quit surely, and every other cycle label is in
`finFourSingletonBaseFree e_0` until the cycle closes.

For a free player `j`,
`quittingPersistentBaseRoot_free_purePayoff_le` says that both pure endpoint
payoffs are at most its prescribed mixed payoff.  The latter is the convex
mixture `p_j Q_j+(1-p_j)C_j`.  If `Q_j>C_j`, the inequality
`Q_j<=p_j Q_j+(1-p_j)C_j` forces `p_j=1`.  Therefore robust positivity on
successive edges propagates sure quitting from `e_0` through
`e_1,...,e_{m-1}`.  Simplicity of the cycle ensures that every propagated
receiver before the final edge is a free player of this one induced game.

No new stationary source is selected during the induction, so there is no
profile-alignment gap.

## 4. Final owner-debt contradiction

On the final edge `e_{m-1}->e_0`, the just-proved sure quitting of
`e_{m-1}` makes `Q_{e_0}-C_{e_0}>0`.  The source already prescribes `e_0` to
Quit surely.  Since `e_{m-1}` Quits at date zero regardless of `e_0`'s
action, an arbitrary behavioral deviation by `e_0` is payoff-equivalent to
its date-zero Quit/Continue mixture.  Strict `Q>C` makes prescribed Quit the
unique maximizing endpoint, so the unrestricted terminal-semantic debt of
`e_0` is zero.

This directly contradicts the producer field

\[
 \Gamma\le d_{e_0}(source)
\]

because `residual.witness.terminalGap_pos` gives `Gamma>0`.  The argument is
therefore against the actual unrestricted cap, not just stationary or
binary-game deviations.

## 5. Cycle and background quantifiers

The proof applies to every simple directed cycle of every selected
fixed-point-free collision map.  Fixed-point freeness rules out length one;
finiteness of `Fin 4` gives lengths two through four.  The background selected
by negating robust positivity cannot be empty, since
`exists_fixedPointFree_terminalGap_collisionMap` gives

\[
 \Delta(e,f(e);\varnothing)\ge\Gamma>0
\]

on every selected edge.  For `Fin 4`, a nonempty subset of the two-label
complement has cardinality one or two, yielding exactly the pair-to-triple or
triple-to-grand cases in Corollary 3.2.

## 6. Checked dependence and novelty audit

The proof really uses the following checked data:

* `exists_fixedPointFree_terminalGap_collisionMap` from
  `PunishmentNormalAtomicCollisionHandoff.lean`;
* `nonempty_singletonBaseSameLawResetProducer`, specifically its `point`,
  `point_mem`, and `owner_gap` fields, from
  `SingletonBaseSameLawResetProducer.lean`;
* `quittingPersistentBaseRoot_apply_of_mem_base`,
  `isNash_of_mem_quittingPersistentBaseNashSet`, and
  `quittingPersistentBaseRoot_free_purePayoff_le` from
  `PersistentBaseInducedGame.lean`; and
* the positive terminal gap carried by the hard residual.

The table bound hypotheses `0<=M` and
`|reward terminal who|<=M` are needed to invoke the current producer, even
though the short contradiction does not otherwise use `M`.  The reset,
heavy-atom, global-minimum, and residual-hard-class fields of the producer do
not enter the contradiction.  An eventual Lean statement could therefore
either consume the existing producer as written or expose the smaller
supplied interface: a sure-base induced Nash root with owner debt at least
`Gamma`.

A narrow phrase and declaration search found collision selectors, individual
singleton collisions, cycle/lasso handoffs, face numerators, and persistent-
base Nash inequalities, but no existing declaration deriving a nonempty-
background weak sign cancellation on every selected functional-graph cycle.
The theorem is a novel ordinary-mathematics composition of checked inputs.

## 7. Scope and export assessment

The note correctly does not claim that the cancelling background has positive
mass at another selected source, a quantitative negative margin, an interior
sign box, a stationary equilibrium, or any chronology/debt descent.  It is a
finite same-table residual exclusion and a useful new formalization target.

I regard Theorem 3.1 and Corollary 3.2 as suitable for the export gate, subject
to the normal author incorporation/status update and absence of another
unresolved review objection.  A narrow Lean handoff should formalize only the
Bernoulli endpoint-average lemma, sure-quitting propagation around a supplied
simple cycle, the date-zero owner-cap reduction, and the nonempty-background
conclusion; it need not import the speculative stationary-box discussion.

