# Renewed owner cycles require linear horizontal capacity recharge

Author: `CODEX_HAHN`

## Status

**Exact ordinary mathematics; aggregate obstruction, not a consumer.**  A
renewable sequence of late reset children gives one uniformly charged exact
predecessor path in every phase.  Under bounded exact-prefix capacity, the
canonical capacity potential shows that the intervening horizontal cap-child
operations must restore a linear amount of capacity.  The same conclusion
holds for terminal semantic debt.

This does not turn a finite cycle of owner labels into an admissible return.
The cap-child operation is not an exact Nash--Bellman edge, and the source
state need not recur when its owner label recurs.  Thus the renewed packet
remains in the same nonterminal source-reprojection component.

## Question

Suppose the late-reset renewal theorem is iterated indefinitely.  Does
finiteness of the owner set, together with the fixed exact absorption/debt
expenditure in every phase, force a positive admissible return?

## 1. Alternating data

Let `S_m` be the actual cap-clock source at phase `m`.  Decorate its payoff
with the all-Continue simplex root to obtain one state `s_m` in the full
canonical boxed Nash--Bellman state space.  Let `P_m` be the literal
exact-prefix descendant selected before the next horizontal cap child is
installed, with boxed endpoint `p_m` carrying the last actual prefix root.
Let `S_(m+1)` be that cap child and decorate its payoff by all Continue to
obtain `s_(m+1)`.  The next vertical phase starts at this **same** decorated
state `s_(m+1)`.  Thus there is a finite exact predecessor path

\[
 s_m\longrightarrow p_m
\tag{1}
\]

in the full boxed Nash--Bellman relation, while

\[
 P_m\dashrightarrow S_{m+1}
\tag{2}
\]

is a one-player complete cap-response replacement.  The dashed arrow is not
an edge of the charged relation.

The late-reset source theorem supplies constants `a_0,c_0>0`, independent of
`m`, such that the path in (1) has charge

\[
 A_m\ge a_0
\tag{3}
\]

and its first exact prefix spends at least `c_0` of total terminal-semantic
debt.  Write

\[
 Q_m:=D(S_m)-D(P_m)\ge c_0,
\qquad
 H_m:=D(S_{m+1})-D(P_m).
\tag{4}
\]

No sign is assumed on `H_m`.

## 2. Exact debt-recharge ledger

The definitions give

\[
 D(S_{m+1})-D(S_m)=H_m-Q_m.
\tag{5}
\]

Therefore for every `N`,

\[
 \boxed{
 \sum_{m<N}H_m
 =\sum_{m<N}Q_m+D(S_N)-D(S_0).}
\tag{6}
\]

All terminal-semantic debts lie in a fixed bounded interval.  Consequently,

\[
 \sum_{m<N}H_m\ge Nc_0-O(1).
\tag{7}
\]

Thus indefinite renewal is possible only if the horizontal cap-child seams
inject total debt at a positive asymptotic rate.

More specifically, suppose `S_(m+1)` is obtained from `P_m` by replacing
only player `b_m` with a complete cap response of gain `g_m>=0`.  The mover's
unrestricted cap is unchanged, so its debt falls by exactly `g_m`.  Hence

\[
 H_m=-g_m+
 \sum_{i\ne b_m}\bigl(d_i(S_{m+1})-d_i(P_m)\bigr).
\tag{8}
\]

Combining (6) and (8) shows

\[
 \sum_{m<N}\sum_{i\ne b_m}
 \bigl(d_i(S_{m+1})-d_i(P_m)\bigr)
 \ge Nc_0+\sum_{m<N}g_m-O(1).
\tag{9}
\]

Every fixed vertical expenditure, and every payoff gain of the cap owner,
must be financed by cross-player debt creation at the horizontal seams.

## 3. The stronger global boxed-capacity ledger

Let `R_box` be the charged relation on the **full** canonical boxed
Nash--Bellman state space.  Its edges are exact predecessor edges and its
charge is joint root absorption.  No punishment-floor certificate is part of
its state.

Under no Fin4 uniform payoff, the checked bounded exact-block hazard-capacity
theorem gives one constant bounding the sum of all marginal root hazards in
every finite exact Nash--Bellman block.  At every root, joint absorption is at
most the sum of the marginal hazards.  Every finite `R_box` path decodes to
such a block.  Hence all finite `R_box` path charges have one common bound.

Apply the generic charged-relation construction and define

\[
 \Phi(s):=\sup\{\operatorname{charge}(p):p\text{ is a finite }R_{box}
                 \text{ path starting at }s\}.
\tag{10}
\]

The common path bound makes `Phi` a bounded real-valued potential on every
boxed state.  Every phase path (1) therefore satisfies

\[
 \Phi(p_m)+A_m\le\Phi(s_m).
\tag{11}
\]

Define the horizontal capacity displacement using the fixed decorations

\[
 K_m:=\Phi(s_{m+1})-\Phi(p_m).
\tag{12}
\]

Summing (11) and inserting (12) gives

\[
 \sum_{m<N}A_m
 \le \Phi(s_0)-\Phi(s_N)+\sum_{m<N}K_m.
\tag{13}
\]

Since `Phi` is bounded and `A_m>=a_0`,

\[
 \sum_{m<N}K_m\ge Na_0-O(1).
\tag{14}
\]

This conclusion is stronger than the debt ledger: even if a horizontal
replacement hides its recharge from total debt, it must restore the global
exact-prefix capacity spent during the preceding phase.

Equation (14) does not itself yield a contradiction.  The capacity potential
is a potential only on exact predecessor edges.  No monotonicity or
continuity theorem controls it across a complete-strategy cap replacement.
The explicit decorations close the typing seam: the target of the horizontal
replacement is evaluated at `s_(m+1)`, and that identical boxed state is the
source of the next vertical path.  No root-independence assertion for `Phi`
is needed.

## 4. Why owner-label recurrence is insufficient

There are four possible owners and successive renewed owners are distinct.
An infinite construction therefore contains a finite cycle of owner labels.
It does not follow that it contains a cycle of semantic states:

\[
 b_m=b_{m+L}
 \quad\not\Longrightarrow\quad
 S_m=S_{m+L}
 \text{ or } U(S_m)=U(S_{m+L}).
\tag{15}
\]

Even compact recurrence of the source payoffs does not remove (2).  A
positive exact near-return requires one path made entirely of exact
predecessor edges whose endpoint payoff returns near its
starting payoff.  Here each charged path stops at `P_m`, and its putative
next source is separated by the non-admissible horizontal seam
`P_m --> S_(m+1)`.

Strict best-response cycles show that finite mover labels and bounded payoff
vectors do not prohibit the linear cross-player transfers in (9).  The
positive global-minimum provenance supplies the renewable source and the
uniform constants; it does not presently orient the horizontal seams.

## 5. Exact residual

Indefinite renewed reset motion therefore has the following necessary form:

1. every phase begins at an actual uniformly pinned cap-clock source;
2. an exact predecessor path spends at least `a_0` of global boxed capacity
   and at least `c_0` of total debt;
3. a one-player cap-child replacement restores, cumulatively, at least the
   same capacity and debt at linear rate; and
4. the restored source changes before the next exact path is selected.

To consume the component one still needs one of:

- a theorem bounding `K_m` or the cross-player term in (9) by a telescoping
  source functional;
- a source-compatible exact predecessor path across the horizontal seam;
- a finite rank which the cap-child replacement cannot restore; or
- a quitting-specific contradiction to linear cap-response recharge under
  positive global minimum debt.

Without such an input, the renewal theorem closes the source packet under
iteration but does not close the uniform-equilibrium proof.

## Source correspondence

The renewable phase input is
`CODEX_HAHN__LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE`.  The full boxed
charged relation is `quittingPunishmentFloorBoxChargedRelation` in
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorChargedRelation.lean`.
The generic bounded budget-to-go potential is `ChargedRelation.value`, with
decrement theorem `ChargedRelation.value_tgt_add_charge_le_value_src`, in
`MathUE/ChargedPathBudget.lean`.  The common path bound comes from
`finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`;
joint absorption is bounded by the sum of the marginal hazards.
The debt-coordinate and re-entry accounting is the reviewed theorem in
`FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE`.

## Next exact question

Does a late reset cap-child replacement admit a bound on its canonical
capacity displacement in terms of the signed outsider holonomy, with a
remainder summable along one renewed owner cycle?  A merely local bound by
the cap-response gain cannot suffice: horizontal best-response cycles can
rotate cross-player debt exactly.
