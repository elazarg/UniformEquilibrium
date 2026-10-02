# Maximal target-cap re-rooting: exact charge ledger and inert-tube no-go

Identity: `CODEX_GATE`  
Date: 2026-08-31  
Status: **ordinary mathematics composed with checked and scratch
declarations; exact trichotomy proved; sharp maintained-regime no-go proved;
no full-debt chamber consumer.**  Recomputing an exact root at the fork target
does preserve the reached suffix quantitatively.  It does not force positive
absorption.  A sufficiently small radial version of the common-prefix fork
has a fixed positive spectator debt rise while its target cap lies in the
checked open unique-all-Continue tube.  The all-Continue outcome therefore is
not ruled out by positive minimum, full debt, or the global moat, and it does
not by itself enter reset-rigid.

## 1. Exact question

The previous note
[`CODEX_GATE__FULL_DEBT_FORK_CAP_TRANSPORT_AND_REBASE.md`](CODEX_GATE__FULL_DEBT_FORK_CAP_TRANSPORT_AND_REBASE.md)
proved the following ordinary-mathematics reduction from the current scratch
fork.

For one actual near-minimum full-debt source `X`, a complete unilateral fork
`X -> Y` has:

- a fixed mover payoff gain `G>0`;
- literal equality before a uniformly reached paid cut;
- a fixed outsider `j` with debt rise
  
  \[
  d_j(Y)-d_j(X)\geq c>0;                             \tag{1.1}
  \]

- and, after the checked endpoint-rise decoder, a prescribed terminal atom
  or a common-response rectangle attached behind that same cut.

The old exact prefix generally stops being Nash because the target cap has
changed.  The present question is whether one can discard those roots,
compute a fresh exact product root against the target cap, and force a
charged rebase.

There are two answers.

1. Every fresh exact root has a precise debt/charge ledger and retains a
   uniformly positive fraction of the localized atom.
2. Even the maximum-absorption exact root can be all Continue.  The maintained
   strict-minimum tube makes this outcome compatible with a positive outsider
   rise, rather than excluding it.

## 2. Maximum-absorption exact root

Let

\[
 y=(U,B,\mu)
\]

be a joint terminal-semantic/law carrier point in a finite quitting game.
Write

\[
 D_y=\sum_i(B_i-U_i),
 \qquad
 D_*:=\min_{x\in\mathcal C_{\rm sem}}D(x)>0.          \tag{2.1}
\]

Let `N(B)` be the set of exact product-root Nash equilibria against tail `B`.
It is a nonempty compact subset of the finite product of Boolean probability
simplices: nonemptiness is `exists_isZeroQuittingRootNash`, and the root-Nash
inequalities are closed.  The absorption function

\[
 a(p)=1-\prod_i p_i(\mathrm{Continue})
\]

is continuous.  Hence there is an exact root `p*` maximizing `a`.  Put

\[
 a_*=a(p_*),\qquad s_*=1-a_*,                       \tag{2.2}
\]

and let

\[
 y^+=\operatorname{Prefix}(p_*,y)                   \tag{2.3}
\]

include both the semantic prefix and the corresponding terminal-law prefix.

This maximum selection is ordinary mathematics here.  No existing
production declaration was found which packages the argmax itself.

## 3. Exact debt, charge, and atom ledger

### Theorem 3.1 (maximal target-cap re-root ledger)

With the data of Section 2,

\[
 d_i(y^+)=s_*d_i(y)\qquad(i\in I),                  \tag{3.1}
\]

and therefore

\[
 D(y^+)=s_*D_y.                                      \tag{3.2}
\]

Define the re-root charge and the target excess by

\[
 \kappa_*=a_*D_y,
 \qquad E_y=D_y-D_*.
\]

Then

\[
 \boxed{0\leq\kappa_*\leq E_y},                    \tag{3.3}
\]

\[
 D(y^+)-D_*=E_y-\kappa_*,                           \tag{3.4}
\]

and

\[
 \boxed{s_*\geq D_*/D_y>0}.                        \tag{3.5}
\]

For Fin4 rewards bounded by `M`, every debt coordinate is at most `2M`, so

\[
 s_*\geq D_*/(8M).                                  \tag{3.6}
\]

If two terminal profiles `y` and `x` carry a signed payoff atom `A_S` at one
absorbing outcome and the same fresh root `p*` is prefixed to both, then

\[
 A_S^+=s_*A_S.                                       \tag{3.7}
\]

Consequently every localized atom inequality

\[
 \alpha\leq |\Omega|A_S,qquad \alpha>0,             \tag{3.8}
\]

survives fresh maximal re-rooting with

\[
 \frac{D_*}{8M}\alpha
    \leq |\Omega|A_S^+                              \tag{3.9}
\]

in Fin4.

#### Proof

Equation (3.1) is the checked exact cap-prefix debt identity
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`.
Summing proves (3.2).  The prefixed point remains in the carrier, so global
minimality gives

\[
 D_*\leq s_*D_y.
\]

Rearranging gives (3.3)--(3.5), and the reward bound gives (3.6).  Equation
(3.7) is
`quittingTerminalPayoffDifferenceAtom_literalRootStack` for a one-root word.
Combining it with (3.6) proves (3.9).  `QED`

Thus a newly absorbing exact root cannot screen the paid suffix completely.
Positive global debt forces a quantitative amount of Continue mass through
every exact cap root, independently of which root maximizes absorption.

## 4. Exact three-way re-root alternative

Order the following alternatives as written.

### Alternative M: minimum-fibre handoff

If

\[
 D(y^+)=D_*,                                         \tag{4.1}
\]

then `kappa_*=E_y` and the literal prefixed endpoint is on the global minimum
fibre.  Every zero debt coordinate of `y` remains zero by (3.1).  More
generally, if a sequence has

\[
 d_j(y_n)\longrightarrow0,qquad
 D(y_n^+)\longrightarrow D_*,                       \tag{4.2}
\]

then every compact cluster point `z` of `y_n^+` satisfies

\[
 D(z)=D_*,\qquad d_j(z)=0.                           \tag{4.3}
\]

This is the minimum-fibre support handoff relevant to the vanishing-debt
rectangle arm.

### Alternative C: positively charged off-minimum rebase

If (4.1) fails and `a_*>0`, then

\[
 0<\kappa_*<E_y,                                     \tag{4.4}
\]

and `p*` is a literal positive-absorption exact root whose tail retains the
localized atom by (3.9).  The residual excess is exactly

\[
 E_y-\kappa_*=D(y^+)-D_*>0.                          \tag{4.5}
\]

This is a genuine charged outward rebase, although it is not yet a return.

### Alternative I: all-Continue inert entry

If (4.1) fails and `a_*=0`, maximality implies that every exact root has zero
absorption.  A Boolean product root has zero absorption only when every player
Continues surely.  Therefore all Continue is the unique exact root, and

\[
 y^+=y.                                               \tag{4.6}
\]

The target, its law, and the localized suffix atom are fixed literally.

These alternatives are exhaustive.  They are quantitative through
(3.3)--(3.9), but Alternative C has no positive lower bound on `a_*` in terms
of the spectator rise (1.1).  Section 6 shows that no such bound follows even
in the maintained positive-minimum regime.

## 5. How the root charge is paid by the fork transfer

Let the fork source have excess

\[
 e_X=D(X)-D_*,
\]

let its mover gain be `G`, and define the aggregate outsider debt transfer

\[
 \Lambda=\sum_{k\ne i}\bigl(d_k(Y)-d_k(X)\bigr).
\]

Own-cap invariance gives the exact ledger

\[
 E_Y=e_X+\Lambda-G.                                  \tag{5.1}
\]

After maximal exact re-rooting,

\[
 \boxed{
 D(Y^+)-D_*=e_X+\Lambda-G-\kappa_*\geq0.}           \tag{5.2}
\]

Thus any positive root charge is paid by source excess plus the **net**
outsider transfer after the mover gain.  The selected spectator rise `c` is
one positive summand in `Lambda`; it is not by itself an upper or lower bound
for `kappa_*`.  This is the sharp meaning of “absorption charged to the rise.”
Replacing `Lambda` by only the selected coordinate would silently discard the
other two unrestricted cap/payoff changes.

## 6. Maintained-regime no-go: a positive rise inside the all-Continue tube

The all-Continue branch is not excluded by the positive minimum or global
singleton moat.  In fact the current strict-minimum infrastructure lets one
put the fork target deliberately inside that branch.

### Theorem 6.1 (small common-prefix forks have positive transfer but inert exact re-roots)

Assume the no-uniform-payoff regime and use the strict Fin4 minimum plateau
and open exact-all-Continue tube supplied by
`exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff`.
Let its cap be `B_*`, and let `T` be the open neighborhood in which every exact
root is all Continue.

Let `X_n` be one source-attached sequence of actual near-minimum full-debt
profiles such that

\[
 B(X_n)\to B_*,\qquad D(X_n)\to D_*,qquad
 d_k(X_n)\geq\delta>0                               \tag{6.1}
\]

for all four labels.  Suppose the common-prefix scratch producer supplies a
full stopping-law fork `F_n` of one fixed mover with gain

\[
 U_i(F_n)-U_i(X_n)\geq g_0>0.                        \tag{6.2}
\]

For `lambda in (0,1)`, mix only the mover's complete stopping law:

\[
 Y_n^\lambda=(1-\lambda)X_n+_i\lambda F_n.          \tag{6.3}
\]

Then one can choose one fixed sufficiently small `lambda>0` such that, for
all large `n`:

1. every coordinate of `Y_n^lambda` still has debt at least `delta/2`;
2. the mover gain is at least `lambda g_0`;
3. some fixed outsider `j`, after a subsequence, has

   \[
   d_j(Y_n^\lambda)-d_j(X_n)
      \geq \lambda g_0/4;                            \tag{6.4}
   \]

4. the mover behaviors remain literally equal before the same paid cut; and
5. `B(Y_n^lambda)` belongs to `T`, so the maximum-absorption exact root is
   uniquely all Continue and has absorption zero.

#### Proof

Payoff is affine in the mover's stopping law, so the gain in (6.3) is exactly
`lambda` times the full-fork gain.  Total variation from the source mover law
is at most `lambda`.  Proposition 4.1 of the preceding note gives, for every
outsider,

\[
 |B_k(Y_n^\lambda)-B_k(X_n)|\leq2M\lambda,
 \qquad
 |d_k(Y_n^\lambda)-d_k(X_n)|\leq4M\lambda.           \tag{6.5}
\]

The mover cap is invariant and its debt falls by at most `2M lambda`.
Choose `lambda` small enough that `4M lambda<delta/2`.  This proves item 1.

Because `T` is open at `B_*`, choose the same `lambda` so that the cap modulus
`2M lambda` fits inside a fixed neighborhood contained in `T`.  Since
`B(X_n)->B_*`, item 5 holds eventually.

Write `epsilon_n=D(X_n)-D_*`.  Global minimality at the actual mixed target
and own-cap invariance give

\[
 \sum_{k\ne i}
  \bigl(d_k(Y_n^\lambda)-d_k(X_n)\bigr)
 \geq\lambda g_0-\varepsilon_n.                     \tag{6.6}
\]

Eventually `epsilon_n<=lambda g_0/4`; one of the three outsiders then has
rise at least `lambda g_0/4`.  Pass to a subsequence to fix its label.  The
stopping-law mixture preserves every finite mass and reconstructed hazard
strictly before the common cut, proving item 4.  Finally, membership in `T`
gives the unique all-Continue conclusion by
`eventually_exactRoot_eq_allContinue_of_unique_of_singletonGap`, equivalently
the tube's stored uniqueness field.  `QED`

Applying `hasVanishingDebtAtomAlternative_of_endpointDebtRise` to (6.4)
still gives a fixed positive atom/rectangle charge.  Hence the following data
coexist in the maintained positive-minimum source architecture:

```text
positive full debt at source and target;
literal common-prefix paid fork;
fixed outsider unrestricted-debt rise;
fixed localized terminal atom or response rectangle;
unique all-Continue fresh exact cap root.
```

This proves that the atom does not force exact root absorption.  It also
shows why shrinking the fork to control cap transport cannot solve the
problem: shrinking is precisely what places the target cap in the inert tube.

## 7. Exact Fin4 stress regression with unique all-Continue target

The following elementary table independently verifies every local sign in
Theorem 6.1, while honestly having global minimum zero.

Let the players be `i,j,k,l`.  For every nonempty coalition `S`, define

\[
 r_i(S)=\begin{cases}0&i\in S,\\1&i\notin S,\end{cases}
\]

and define `r_k,r_l` analogously.  For `j`, put

\[
 r_j(S)=
 \begin{cases}
 0,&j\in S,\\
 1,&j\notin S\text{ and }i\in S,\\
 2,&j\notin S\text{ and }i\notin S.
 \end{cases}                                         \tag{7.1}
\]

At the source profile `sigma`, everybody Continues at date zero and all four
players Quit at date one.  The terminal coalition is the full set, so

\[
 U(\sigma)=(0,0,0,0),\qquad B(\sigma)=(1,1,1,1),
 \qquad d(\sigma)=(1,1,1,1).                         \tag{7.2}
\]

Indeed, each player obtains one by unilaterally Continuing at date one while
the other three Quit.

Now replace only `i` by Never.  The target terminal coalition is `{j,k,l}`.
Thus

\[
 U(\tau)=(1,0,0,0),\qquad B(\tau)=(1,2,1,1),
 \qquad d(\tau)=(0,2,1,1).                           \tag{7.3}
\]

The mover gains one and the spectator `j`'s unrestricted cap and debt rise by
one.  Source and target behavior agree before date one, and source joint reach
to that date is one.

Against the target cap `V'=(1,2,1,1)`, Continue strictly dominates Quit for
every player at every product root:

- for `i,k,l`, Continue always pays one, while every coalition containing the
  player pays zero;
- for `j`, Continue pays at least one when opponents absorb and pays two at
  all Continue, while Quit always pays zero.

Therefore all Continue is the **unique** exact root against `V'`.  Its maximal
absorption is zero despite the unit outsider cap rise and unit actual reach.

The table is not a positive-minimum counterexample.  At the all-Never profile,
every singleton reward and every cap is zero, so `D_*=0`.  It proves the exact
local implication false and agrees with the maintained-regime tube theorem,
which is the genuinely positive-minimum obstruction.

## 8. When minimum-fibre handoff becomes reset-rigid

The fork target in Theorem 6.1 remains full debt by construction.  Its unique
all-Continue root fixes the same off-minimum or full-support minimum point and
does **not** create a reset coordinate.  Thus Alternative I does not simply
mean “transition to reset-rigid.”

The vanishing-debt response endpoint is different.  Let `R_n` be the target
response profile in the rectangle arm, with

\[
 d_j(R_n)\leq e_n\to0,
\]

and let `R_n^+` be its fresh maximal exact re-root.  By (3.1),

\[
 d_j(R_n^+)\leq e_n.                                 \tag{8.1}
\]

If `D(R_n^+)->D_*`, compactness gives the minimum-fibre support handoff
(4.3).  If the same limiting law retains positive opponent incidence for
`j`, the checked
`exists_quittingLawTightResetRigidChamber` supplies the reset-rigid chamber
after packaging the point as the minimum of its new law-tight saturation
hull.  If the only positive atom is the binding owner's singleton/Never law,
the reviewed global singleton moat excludes that chamber.

Without both minimum-fibre return and the required positive law/incidence
provenance, no reset-rigid conclusion follows.  A positive signed difference
atom between two response endpoints guarantees positive mass in at least one
of their laws, not automatically in the small-debt target law.  This is a
remaining source-attachment condition, not a cosmetic detail.

## 9. Source audit and nonduplication

Declarations and files inspected narrowly:

- `positiveDebt_exists_commonPrefix_profitableStoppingLawFork` in
  `fable/lean/FableCommonPrefixFork.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` and
  carrier prefix closure through the imports of
  `Diagnostics/Quitting/LawTightCapNashSaturationHull.lean`;
- `quittingLawTightCapNashSaturationHull_rootAbsorptionMass_le_debtExcess_div`
  and the finite-chain charge telescopes in
  `Diagnostics/Quitting/LawTightCapNashMinimumFace.lean`;
- `quittingTerminalPayoffDifferenceAtom_literalRootStack` in
  `Diagnostics/Quitting/StoppingLaw/ContinuePrefixAtomAccess.lean`;
- `eventually_exactRoot_eq_allContinue_of_unique_of_singletonGap`,
  `exists_open_exactAllContinueTube_debtHomotopy`, and
  `exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff`
  in
  `Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`;
- `hasVanishingDebtAtomAlternative_of_endpointDebtRise` in
  `Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`; and
- `QuittingLawTightResetRigidChamber` and
  `exists_quittingLawTightResetRigidChamber` in
  `Diagnostics/Quitting/LawTightCapNashStrictMinimum.lean`.

The hull-minimum absorption bound already contains the inequality underlying
(3.3) for hull points.  The new content here is the explicit maximal-root
trichotomy, quantitative atom survival under fresh re-rooting, its exact
composition with the fork transfer ledger, and Theorem 6.1 showing that the
maintained common-prefix fork can carry a positive outsider rise inside the
unique-all-Continue tube.

No Lean, fable, feedback, question, or export file was edited.

## 10. One next question

The precise remaining question is now on the vanishing-debt response endpoint,
not on the fork target root:

> For the source-attached rectangle endpoints `R_n`, must either the maximal
> fresh-root absorption stay uniformly positive outside the exact
> all-Continue tube, or must `D(R_n^+)-D_*` tend to zero while the small-debt
> target law retains a positive opponent-incidence atom?

The first answer would provide a renewable charged rebase.  The second would
enter reset-rigid through Section 8.  Theorem 6.1 proves that no statement of
this form can use only the fork target's spectator rise, actual reach, full
debt, or singleton moat: those fields already coexist with unique
all-Continue exact re-rooting.
