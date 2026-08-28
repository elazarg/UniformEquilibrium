# Constrained-root normal work and minimum-leakage no-go

Authors: `CODEX_GIBBS`, with gate repairs by `CODEX_ROOT`

Independent review:
[`CODEX_CARNOT`](../feedback/CODEX_GIBBS__CONSTRAINED_ROOT_NORMAL_WORK_AND_LEAKAGE_LEDGER__BY_CODEX_CARNOT.md)

## Exact statement

Let `I` be finite and let `r` be a bounded quitting reward table.  Let
`tau` be an actual behavioral tail with terminal semantic pair

\[
 z=(u,b),\qquad d_i=b_i-u_i,\qquad D=\sum_i d_i.
\]

Here `b_i` is the unrestricted behavioral best-response cap, including
Never, unbounded pure quitting dates, randomized hazards, and arbitrary
behavioral stopping rules.

Choose lower bounds `0 <= ell_i < 1`.  In the one-row game whose
all-Continue continuation payoff is `u`, let `q` be an exact Nash root when
player `i` is restricted to Quit probabilities in `[ell_i,1]`.  Write

\[
 Q_i=\text{pure-Quit value},\qquad
 C_i=\text{pure-Continue value},\qquad
 g_i=Q_i-C_i,
\]

and

\[
 H_i=\Pr_q(\text{every opponent of }i\text{ Continues}).
\]

Define lower-face normal work and the inherited-cap shield by

\[
 W_i=\ell_i(-g_i)_+,
 \qquad
 R_i=\min\{H_i d_i,(g_i)_+\}.
\]

Then the literal prefixed profile `q*tau` satisfies, coordinatewise,

\[
 \boxed{d_i(q*z)=W_i+H_i d_i-R_i.}\tag{1}
\]

Let

\[
 D_*:=\inf\{D(x):x\text{ is the semantic pair of an actual profile}\}>0,
\]

and put `E=D-D_*` and `E'=D(q*z)-D_*`.  Summing (1) gives

\[
 \boxed{
 W=E'-E+\sum_i(1-H_i)d_i+\sum_iR_i,
 }
 \qquad W=\sum_iW_i.\tag{2}
\]

For

\[
 \kappa(\ell)=\min_i\max_{j\ne i}\ell_j,
\]

if at least two lower floors are positive, then

\[
 \boxed{W\ge \kappa(\ell)D_*-E.}\tag{3}
\]

In particular, if at least two coordinates have floor at least `ell>0`,
then `W >= ell D_*-E`.  A near-minimum constrained repair with
`E=o(ell)` therefore cannot have total normal work `o(ell)`.

If `g_p<0`, exact constrained optimality forces `q_p=ell_p`.  Let `q^-`
replace only player `p`'s root action by pure Continue, and put `y=q^-*z`.
Then

\[
 U_p(y)-U_p(q*z)=W_p,
 \qquad
 \boxed{d_p(y)=d_p(q*z)-W_p.}\tag{4}
\]

Nevertheless global minimality forces the exact repayment account

\[
 \boxed{
 \sum_{j\ne p}\bigl(d_j(y)-d_j(q*z)\bigr)
 =D(y)-D(q*z)+W_p
 \ge W_p-E'.}\tag{5}
\]

Thus on the minimum fibre, or whenever `E'=o(W_p)`, removing binding normal
work creates first-order aggregate debt in the other coordinates.  In the
unique-debtor case some new coordinate has debt at least

\[
 \frac{W_p-E'}{|I|-1}.
\]

Consequently the proposed implication

```text
exact constrained lower-face work
    -> negligible cross-coordinate leakage / renewable support descent
```

is false at the stated local interface.  A valid consumer must add a
source-attached cancellation, fixed response chart, no-entry theorem, or
another orientation of the repayment flow.  Sources appreciably above the
minimum and genuinely hierarchical one-owner constructions are not
classified by this result.

## Conjecture-facing change

This closes one proposed route in
[`FIN4_RENEWABLE_ORIENTATION_OR_COUNTEREXAMPLE.md`](../questions/FIN4_RENEWABLE_ORIENTATION_OR_COUNTEREXAMPLE.md):
exact normal-cone complementarity does not manufacture the second-order
cap-leakage bounds required for the advertised repeated support drain.  The
full cap ledger forces the opposite first-order account near a positive
minimum.

The remaining producer must control the repayment in (5), carry it as
chronological charge, or use a hierarchy in which the other floors and their
work are genuinely lower order.  This packet is a boundary/no-go theorem,
not a terminal approximation or a uniform-equilibrium consumer.

## Definitions, agency, and existence of the constrained root

The root `q` exists by ordinary finite-game mathematics.  Give player `i`
the compact convex action interval `[ell_i,1]`, and define its payoff at a
product point by the one-row quitting payoff with continuation value `u_i`
on the all-Continue outcome.  The payoff is continuous in the product and
affine in the player's own coordinate.  The compact convex-game Nash theorem
therefore supplies an exact constrained root.

This is an arbitrary-prescribed-continuation theorem.  It is not an
application of the repository's stationary face-numerator existence theorem.
Prefixing `q` to `tau` is literal, so every semantic pair used above belongs
to an actual behavioral profile.

## Proof

The one-row literal root defect against `u` is

\[
 \delta_i^u=(1-q_i)(g_i)_++q_i(-g_i)_+.
\]

Constrained optimality has three cases: `q_i=ell_i` when `g_i<0`,
`q_i=1` when `g_i>0`, and arbitrary `q_i` when `g_i=0`.  Hence

\[
 \delta_i^u=W_i.\tag{6}
\]

The unrestricted continuation option contributes the exact surcharge

\[
\begin{aligned}
 S_i
 &=\max\{Q_i,C_i+H_id_i\}-\max\{Q_i,C_i\}\\
 &=H_id_i-\min\{H_id_i,(g_i)_+\}.
\end{aligned}\tag{7}
\]

Adding (6) and (7) proves (1).  Rearranging its sum proves (2).  Since
`q_j>=ell_j`,

\[
 1-H_i\ge\max_{j\ne i}q_j
           \ge\max_{j\ne i}\ell_j
           \ge\kappa(\ell).
\]

Using `E'>=0`, `R_i>=0`, and `sum_i d_i>=D_*` in (2) proves (3).

For (4), removing player `p`'s binding Quit probability changes only that
player's complete prescribed strategy and raises its payoff by
`ell_p(C_p-Q_p)=W_p`.  Its unrestricted cap depends only on its opponents and
is unchanged.  Equation (4) follows.  Summing all coordinate changes and
using `D(y)>=D_*` proves (5).

For a finite backward block `z_t=q_t*z_(t+1)`, equation (2) telescopes to

\[
 \boxed{
 \sum_{t<H}W_t
 =E_0-E_H
 +\sum_{t<H}\sum_i(1-H_{t,i})d_i(z_{t+1})
 +\sum_{t<H}\sum_iR_{t,i}.}\tag{8}
\]

This is conditional row work, not reach-weighted chronological charge.

For any finite sequence of own-strategy removals `x_m -> x_(m+1)`, with
mover `p_m` and gain `w_m`, fixed-opponent cap invariance gives

\[
 \sum_{j\ne p_m}
   \bigl(d_j(x_{m+1})-d_j(x_m)\bigr)
 =w_m+E_{m+1}-E_m.\tag{9}
\]

For each label set `A`, the exact cut balance is

\[
\begin{aligned}
 D_A(x_K)-D_A(x_0)
 ={}&-\sum_{m:p_m\in A}w_m\\
 &+\sum_m\sum_{\substack{j\in A\\j\ne p_m}}
   \bigl(d_j(x_{m+1})-d_j(x_m)\bigr).
\end{aligned}\tag{10}
\]

A closed debt-vector chain can therefore carry positive work: each label's
outgoing work is exactly replenished by signed leakage from other movers.
Neither support cardinality nor mover/recipient labels orient (10).

## Fin4 boundary regression

Take players `h,k,i,j`.  Give `h` and `k` payoff zero on every nonempty
coalition, and put

\[
 r_i(S)=\mathbf 1_{\{\mathbf 1_{i\in S}\ne\mathbf 1_{j\in S}\}},
 \qquad
 r_j(S)=\mathbf 1_{\{\mathbf 1_{i\in S}=\mathbf 1_{j\in S}\}}.
\]

At the pure sure-exit roots

\[
 hk,\quad hki,\quad hkij,\quad hkj
\]

there is the strict endpoint cycle

\[
 hk\xrightarrow{i}hki\xrightarrow{j}hkij
   \xrightarrow{i}hkj\xrightarrow{j}hk.
\]

Every edge gains one, annihilates the mover's unit debt, and creates unit
debt at the next mover.  Total debt and support cardinality remain one.
Because two sure quitters remain after every unilateral deviation, these are
full behavioral terminal debts and the tail is inaccessible.

The half--half mixed root of `i,j`, with `h,k` surely quitting, is an exact
matching-pennies equilibrium.  Hence this table has global minimum zero.  It
is not a Fin4 counterexample and does not refute a theorem using complete
positive-minimum provenance.  It exactly falsifies a local rank inferred
only from work, mover/recipient labels, debt support, and minimum-style
coordinate bookkeeping.

## Hard-residual boundary

On the Fin4 positive minimum fibre, checked singleton separation supplies a
uniform `Delta>0` with

\[
 u_i-r_i(\{i\})\ge\Delta.
\]

At all Continue, `g_i<=-Delta`.  Uniform continuity over the compact
prescribed-payoff projection of the minimum fibre gives a neighborhood in
which every constrained small clock is at its lower face and

\[
 W_i\ge\ell_i\Delta/2.
\]

This makes normal work quantitative, but gives no sign to the repayment in
(5).  Positive finite floors can even create temporary full debt support in
the prefixed profile; that support is not the limiting minimum-source
support.

## Source correspondence and Lean handoff

The exact algebra is supported by these checked declarations:

- `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart`;
- `quittingRootContinuationOptionSurcharge_eq_max_increment`;
- `quittingTerminalSemanticDebt_prefix_eq_literalDefect_add_surcharge`;
- `quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain`; and
- `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal`.

The generic repayment identity overlaps
`notes/ATLAS_GATEKEEPER__SOURCE_ATTACHED_SINGLETON_ENDPOINT.md`.  The new
content is the constrained normal-work decomposition, its positive-minimum
lower bound, the finite backward-block telescope, and the exact demonstration
that near-minimum binding removal requires first-order leakage.

Suggested declarations are:

```text
exists_constrainedRoot_against_continuation
constrainedRootCoordinateNashDefect_eq_normalWork
constrainedRoot_terminalDebt_eq_normalWork_add_inherited_sub_shield
nearMinimum_totalNormalWork_ge_floor_mul_minimum_sub_excess
lowerFaceRemoval_otherDebtChange_sum_eq
lowerFaceRemoval_exists_supportEntry_of_uniqueDebtor
finiteConstrainedBlock_normalWork_telescope
```

The first declaration is the elementary arbitrary-`u` compact-game adapter.
The remaining local results are finite max/algebra consequences of the named
checked identities.

## Scope and nonclaims

- No positive-minimum reward table is constructed.
- No best response is assumed attained.
- Conditional row work is not called prescribed-payoff chronological charge.
- Forced repayment requires `E'=o(W_p)` or minimum-fibre membership; positive
  minimum plus binding alone is insufficient.
- A source appreciably above the minimum is unclassified.
- A hierarchical repair with all nonowner floors genuinely lower order is
  not excluded.
- No terminal approximation, admissible return, support descent, or uniform
  equilibrium payoff is proved.

## Formalization status

The packet's normal-work/no-leakage core is proved in Lean and integrated at
its exact corrected scope.

- `Math.affineBinaryDefect_eq_lowerFaceNormalWork`,
  `Math.lowerBoundComplementarity_of_endpoint_bounds`,
  `Math.sum_range_work_eq_excess_telescope`, and
  `Math.finiteDebtCutBalance`
  (`MathUE/ConstrainedAffineNormalWork.lean`) provide the game-independent
  affine, telescope, and signed cut identities.
- `constrainedRootCoordinateNashDefect_eq_normalWork`,
  `constrainedRoot_terminalDebt_eq_normalWork_add_inherited_sub_shield`, and
  `constrainedRoot_totalNormalWork_eq_excessChange_add_killed_add_shield`
  (`Research/Quitting/ConstrainedRootNormalWork.lean`) prove formulas (1),
  (2), (6), and (7) with the unrestricted behavioral terminal cap.
- `nearMinimum_totalNormalWork_ge_floor_mul_minimum_sub_excess`,
  `nearMinimum_totalNormalWork_ge_kappa_mul_minimum_sub_excess`, and
  `floor_le_quittingLowerFloorKappa_of_two` prove the heterogeneous and
  two-floor forms of (3).
- `constrainedRoot_quitProbability_eq_lower_of_gap_neg`,
  `lowerFaceRemoval_payoffGain_eq_normalWork`,
  `lowerFaceRemoval_moverDebt_eq_sub_normalWork`, and
  `lowerFaceRemoval_otherDebtChange_sum_eq` prove (4) and the exact identity
  underlying (5).
- `lowerFaceRemoval_work_sub_excess_le_otherDebtChange_sum` and
  `exists_other_lowerFaceRemoval_averageRepayment` prove the sharp
  near-minimum repayment bound.  The positive-debt conclusion
  `lowerFaceRemoval_exists_supportEntry_of_uniqueDebtor` explicitly assumes
  that the mover is the source's unique debtor and that work strictly exceeds
  the source excess; it does not infer support entry from the signed account
  alone.
- `constrainedRoot_finiteBackwardBlock_telescope` and
  `actualOwnStrategyRemoval_finiteDebtCutBalance` prove (8)--(10).  The former
  is an unweighted finite row telescope; the latter concerns literal finite
  sequences of behavioral own-strategy replacements.
- `exists_quittingLowerBoundConstrainedRoot` and
  `exists_actual_quittingLowerBoundConstrainedPrefix`
  (`Research/Quitting/ConstrainedRootExistence.lean`) supply the compact
  constrained root against an arbitrary prescribed continuation and attach
  it literally to a supplied actual behavioral tail.
- `FinFourConstrainedRootNormalWorkRegression.finite_boundaryRegression`
  (`Research/Quitting/FinFourConstrainedRootNormalWorkRegression.lean`) proves
  the same-table Fin4 boundary example: the displayed unilateral cycle moves
  one unit of full behavioral semantic debt, while an actual stationary mixed
  profile realizes global carrier minimum zero.

For this checked core the evidence seals are `M`, `L`, and `A`, where `A` is
only the arbitrary-tail prefix adapter from a supplied actual behavioral
profile.  There is no positive-minimum atlas source `A` and no downstream
`C`.  In particular, no theorem or prose here supplies repayment orientation
or cancellation, chronological charge, a renewable source or rank,
terminal approximation, or a uniform-equilibrium payoff.

This packet remains in `revisit` because the separate hard-residual paragraph
still lacks its literal Lean capstone.  The existing declarations
`exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal` and
`exists_open_exactAllContinueTube_minimumFiber` prove the uniform singleton
gap and an open exact-all-Continue root tube on the positive minimum fibre.
They do not yet prove the advertised uniform statement that every sufficiently
small lower-bound constrained root in the relevant prescribed-payoff
neighborhood binds all its floors and satisfies
`W_i >= ell_i * Delta / 2`.  That is the sole remaining positive claim from
this packet; it must not be inferred from the exact-root tube without a
separate constrained-root argument.
