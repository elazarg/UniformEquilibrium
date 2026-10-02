# Impure Fin4 screening: the payer-cap compensation branch

**Identity:** CODEX_STRENGTHEN  
**Date:** 2026-08-31  
**Status:** exact ordinary-mathematics regression, with checked declaration
boundaries recorded below.  The one-round max-branch system suggested in
Revision 6 of
[`NONLOCAL_RECENTERING_ATTACK.md`](../fable/NONLOCAL_RECENTERING_ATTACK.md)
is feasible.  More basically, the presently checked minimum-return packet
does not put near-minimum **whole debt** on the profile carrying the pair,
gain, and zero marked-owner defect.  Thus route (b) is not presently a
source consequence.  Even if that missing co-indexing is granted by hand,
there is a rational branch in which deleting the row raises three caps but
lowers the payer's cap by exactly the balancing amount.

This is not a quitting-game counterexample and does not establish that the
rational table below has positive global minimum.  In fact it has explicit
pure-pair terminal Nash profiles.  Its purpose is narrower and exact: all
listed one-round algebraic consequences, including both displayed debt
levels and both singleton moats, admit a rational solution.  Universal
global minimality or another perturbation inequality is still doing
essential work not present in the proposed system.

## 1. Checked source boundary

I inspected the following declarations and no broader Lean subtree.

* `FinFourSourcePreservingForcedPairPacket.pairProfile_eq_purePair`,
  `forcedOwnerDefect_eq_zero`, `payerGain_floor`, and
  `payerTargetDebt_eq_sourceDebt_sub_gain` in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingForcedPair.lean`.
  The pair, zero defect, and gain live on purified endpoint profiles.
* `FinFourOwnerCompressedMinimumReturnForcedPairPacket.normalizedDecoratedFamily`,
  `FinFourNormalizedReturnSelection.markedOwnerDefect_eq_zero`,
  `postDateSpine_eq_reference`, and `limit_tailDebt_eq_minimum` in
  `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`.
* `QuittingMarkedPairMinimumTailSource` and
  `QuittingMarkedPairMinimumTailSelection.limit_wholeDebt_pos` in
  `Research/Quitting/FixedPairMinimumTailNormalizedReturn.lean`.
  The source requires `tailDebt_tendsto` to the global minimum.  Its only
  generic conclusion about the whole decorated profile is strictly positive
  whole debt (and the global lower bound implicit in `minimum_global`), not
  convergence or equality of whole debt with the minimum.
* `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.
* The hard singleton matrix and its checked regime-5 properties are the
  matrix `M_W` recorded in Section 8 of
  [`FIN4_COUNTEREXAMPLE_DOSSIER.md`](../fable/FIN4_COUNTEREXAMPLE_DOSSIER.md).

Consequently the exact checked packet provides

\[
 D(T_n)\longrightarrow D_*,\qquad
 \text{pair mass}>\lambda,\qquad
 \text{paid gain}>g,\qquad \delta_o=0,
\]

but does **not** provide

\[
 D(\sigma_n)\longrightarrow D_*                         \tag{1.1}
\]

for the whole pair-decorated profiles `sigma_n`.  Moreover those profiles
are literal pure pair rows, not impure rows.  The unpurified reference
profile does not inherit, by any inspected declaration, the same pair event,
paid gain, and zero selected defect.  Applying the general deletion identity
to a whole decorated profile is legal, but its error

\[
 \varepsilon_n=D(\sigma_n)-D_*                            \tag{1.2}
\]

is uncontrolled.  It may pay the entire screening inequality.  This is a
quantifier/provenance gap in the claim that route (b) “needs no new facts.”

The calculation below grants (1.1), an impure pair row, and common-witness
data anyway.  Feasibility survives that strengthening.

## 2. The exact one-row system, with every max branch visible

Let `I={0,1,2,3}`.  Write a profile as

\[
 \sigma=\pi\star q\star T,                               \tag{2.1}
\]

where `q=(q_i)` is one product row and `T` has semantic pair `(u,b)`.
For a coalition `S`, put

\[
 P_q(S)=\prod_{i\in S}q_i\prod_{i\notin S}(1-q_i),
 \quad \rho=P_q(\varnothing),
 \quad \rho_i=\prod_{k\ne i}(1-q_k).                    \tag{2.2}
\]

The three row quantities for coordinate `i` are

\[
 A_i=\sum_{\varnothing\ne S}P_q(S)r_i(S),                \tag{2.3}
\]

\[
 Q_i=\sum_{S\subseteq I\setminus\{i\}}
       P_{q,-i}(S)r_i(S\cup\{i\}),                       \tag{2.4}
\]

\[
 W_i=\sum_{\varnothing\ne S\subseteq I\setminus\{i\}}
       P_{q,-i}(S)r_i(S).                                 \tag{2.5}
\]

Thus the prescribed Continue endpoint is

\[
 \widetilde C_i=W_i+\rho_i u_i,                          \tag{2.6}
\]

whereas the cap Continue channel is

\[
 C_i=W_i+\rho_i b_i.                                     \tag{2.7}
\]

Let `s_i=r_i({i})`.  The old and deleted inner caps are

\[
 c_i^- =\max(Q_i,C_i),\qquad c_i^+=\max(s_i,b_i).         \tag{2.8}
\]

For the prefix data of Revision 6, write `m_i,w_i,theta,theta_i` for
`M_i^pi,W_i^pi,rho_pi,rho_pi^{-i}`.  Then all outer maxima are

\[
 B_i^- =\max(m_i,w_i+\theta_i c_i^-),\qquad
 B_i^+ =\max(m_i,w_i+\theta_i c_i^+).                    \tag{2.9}
\]

There are four independent branch labels per coordinate:

1. `oldInner_i in {Q,C}`, selecting `Q_i` or `C_i` in `c_i^-`;
2. `deletedInner_i in {S,T}`, selecting `s_i` or `b_i` in `c_i^+`;
3. `oldOuter_i in {P,V}`, selecting `m_i` or the old window channel;
4. `deletedOuter_i in {P,V}`, selecting `m_i` or the deleted channel.

For example `oldInner_i=C` means both the equality `c_i^-=C_i` and
the branch inequality `C_i>=Q_i`; `oldOuter_i=V` means
`B_i^-=w_i+theta_i*c_i^-` and that quantity is at least `m_i`.
After the row `q` is fixed, each branch is a finite system of affine
equalities and inequalities in the rewards, tail coordinates, and prefix
aggregates.  Before fixing `q`, only the product probabilities make it
multilinear.

The exact deletion screen is

\[
 \sum_i(B_i^+-B_i^-)
 \ge
 \theta\left((1-\rho)\sum_i u_i-\sum_i A_i\right)
 -\varepsilon.                                           \tag{2.10}
\]

The other requested one-round constraints can be stated without conflating
prescribed and cap continuations:

* tail minimum/full debt:
  `d_i=b_i-u_i>0` and `sum_i d_i=D_*`;
* global singleton moat at a minimum point:
  `b_i-s_i>=D_*`;
* pair mass:
  `P_q({j,o})>=lambda`;
* zero selected defect, when `0<q_o<1`:
  `Q_o=tilde C_o`;
* a Continue-playing payer `p` with actual one-row paid gain:
  `Q_p-tilde C_p>=g>0`;
* the pure-pair hard signs:
  `r_o({j,o})-r_o({j})>=gamma` and
  `r_p({j,o,p})-r_p({j,o})>=D_*/3`.

For an actual minimum-limit whole profile one should additionally impose
full debt and the singleton moat on `(U^-,B^-)`, not only on the tail.
The certificate below satisfies these stronger local conditions too.

## 3. An exact rational feasible branch

Take roles

\[
 j=0,\qquad o=1,\qquad p=2,\qquad k=3,                   \tag{3.1}
\]

and constants

\[
 D_0={1\over4},\qquad \lambda={1\over5},
 \qquad\gamma={1\over100}.                              \tag{3.2}
\]

The notation `D_0`, rather than `D_*`, is deliberate until universal global
minimality is discussed in Section 5.

Here is a complete rational reward table.  It is given coordinatewise to
avoid a fifteen-row vector table.

For player `0`:

* `r_0({0})=1`, `r_0({0,1})=7`;
* every other nonsingleton containing `0` has reward `49/12`;
* `r_0({1})=4`, `r_0({2})=r_0({3})=0`;
* every remaining nonempty coalition not containing `0` has reward `55/8`.

Player `1` is obtained by swapping labels `0` and `1` in that list.

For player `2`:

* `r_2({2})=1`;
* `r_2({0,2})=r_2({1,2})=173/96`,
  `r_2({0,1,2})=145/12`, and `r_2({2,3})=5`;
* the other three nonsingleton coalitions containing `2` have reward
  `173/48`;
* `r_2({0})=r_2({1})=0`, `r_2({3})=4`, `r_2({0,1})=12`;
* the other three nonempty coalitions not containing `2` have reward `31/6`.

For player `3`:

* `r_3({3})=1`;
* `r_3({0,3})=r_3({1,3})=0`,
  `r_3({0,1,3})=49/4`, and `r_3({2,3})=5`;
* the other three nonsingleton coalitions containing `3` have reward `19/4`;
* `r_3({0})=r_3({1})=0`, `r_3({2})=4`, `r_3({0,1})=12`;
* the other three nonempty coalitions not containing `3` have reward `31/6`.

All rewards have absolute value below `13`.

### 3.1 An actual returned tail

Let `T` play independent Quit probability `1/2` for every player at its
first date and all Continue forever afterward.  For every coordinate, the
sum of its rewards over the seven nonsingleton coalitions containing it is
`63/2`, and the sum over the seven nonempty coalitions not containing it is
also `63/2`.  Since every singleton reward is one,

\[
 Q_i^T={1+63/2\over8}={65\over16},\qquad
 C_i^T={63/2\over8}={63\over16}.                          \tag{3.3}
\]

The prescribed payoff is their half-half average,

\[
 u_i=4,                                                   \tag{3.4}
\]

and the unrestricted cap is

\[
 b_i={65\over16}.                                        \tag{3.5}
\]

Indeed Quit at the first date attains `65/16`; Continue there and Quit at
the next date also attains `63/16+1/8=65/16`.  Hence

\[
 d_i(T)={1\over16}>0,qquad D(T)={1\over4}=D_0,           \tag{3.6}
\]

and the full-debt global-moat inequality is satisfied with large slack:

\[
 b_i-r_i(\{i\})={49\over16}\ge D_0.                     \tag{3.7}
\]

### 3.2 The impure row and its four max branches

Take no earlier prefix and put

\[
 q_0=q_1={1\over2},\qquad q_2=q_3=0.                    \tag{3.8}
\]

Then `rho=1/4`, and the exact pair `{0,1}` has conditional and unconditional
mass `1/4>lambda`.  Direct substitution gives the following branch table.

| player | `A_i` | `Q_i` | `W_i` | `rho_i` | `tilde C_i` | `C_i` | old branch | `B_i^-` |
|---|---:|---:|---:|---:|---:|---:|---|---:|
| `0` | `3` | `4` | `2` | `1/2` | `4` | `129/32` | `C` | `129/32` |
| `1` | `3` | `4` | `2` | `1/2` | `4` | `129/32` | `C` | `129/32` |
| `2` | `3` | `267/64` | `3` | `1/4` | `4` | `257/64` | `Q` | `267/64` |
| `3` | `3` | `53/16` | `3` | `1/4` | `4` | `257/64` | `C` | `257/64` |

All four deleted inner maxima choose the tail branch `T`, since
`b_i=65/16>1=s_i`.  With the empty prefix both outer maxima choose their
window channels.  The complete max word is therefore

\[
 (C,C,Q,C)\longrightarrow(T,T,T,T).                     \tag{3.9}
\]

The whole prescribed payoff is unchanged:

\[
 U_i(q\star T)=A_i+\rho u_i=3+1=4.                      \tag{3.10}
\]

Its debts are

\[
 \left({1\over32},{1\over32},{11\over64},{1\over64}\right),
 \qquad \sum_i d_i(q\star T)={1\over4}=D_0.             \tag{3.11}
\]

They have full support.  The whole-profile singleton moat also holds:

\[
 B_i^- -1\in
 \left\{{97\over32},{97\over32},{203\over64},{193\over64}\right\}
 \subseteq[D_0,\infty).                                  \tag{3.12}
\]

Player `o=1` is exactly indifferent in the **prescribed** row:

\[
 Q_1=\widetilde C_1=4,                                   \tag{3.13}
\]

so its selected local defect is zero.  The unplayed Quit endpoint of
`p=2` has the actual gain

\[
 Q_2-\widetilde C_2={11\over64}>{1\over8}>0.             \tag{3.14}
\]

At the purified pair itself,

\[
 r_1(\{0,1\})-r_1(\{0\})=3,                             \tag{3.15}
\]

and

\[
 r_2(\{0,1,2\})-r_2(\{0,1\})
 ={145\over12}-12={1\over12}={D_0\over3}.               \tag{3.16}
\]

Thus both the forced-owner and payer floors hold, including the weaker
scaled floors `lambda*gamma` and `lambda*D_0/3`.

Finally, deletion changes the four caps by

\[
 \left({1\over32},{1\over32},-{7\over64},{3\over64}\right),
 \qquad \sum_i(B_i^+-B_i^-)=0.                           \tag{3.17}
\]

The payoff side of the screening identity is also exactly zero:

\[
 (1-\rho)\sum_i u_i-\sum_iA_i
 ={3\over4}\cdot16-12=0.                                \tag{3.18}
\]

Hence the deletion screen holds at equality with `epsilon=0`.  The positive
cap openings for players `0,1,3` are financed exactly by the payer cap drop
`-7/64`.  This is the advertised compensation branch.

### 3.3 Hard table signs

The singleton comparison matrix of this table is exactly

\[
 M_W=
 \begin{pmatrix}
 0&3&-1&-1\\
 3&0&-1&-1\\
 -1&-1&0&3\\
 -1&-1&3&0
 \end{pmatrix}.                                         \tag{3.19}
\]

Thus it inherits the dossier's checked full normal core, Q/no-homogeneous,
and regime-5 `bar Q` failure.  All singleton self-rewards are one, so every
player is punishment-normal by the standard ceiling.  A fixed-point-free
collider map is

\[
 0\mapsto1,\quad1\mapsto0,\quad2\mapsto3,\quad3\mapsto2, \tag{3.20}
\]

with respective join gaps `3,3,1,1`, all above `gamma`.  Thus the feasible
branch is not caused by dropping the hard singleton signs.

## 4. What the feasible point proves

### Theorem 4.1 (one-round screening nonconsumption)

The following finite collection of constraints is rationally feasible:

1. an actual product-profile tail and an actual impure one-row extension;
2. equal positive displayed debt levels `D(T)=D(q*T)=D_0`;
3. full debt support and the singleton moat at both displayed pairs;
4. fixed positive pair mass;
5. zero selected-owner defect;
6. a fixed paid-gain floor for a distinct payer;
7. the pure forced-pair gap and payer-defect floor;
8. the hard Fin4 regime-5 singleton matrix and collider signs; and
9. the exact window-deletion identity and screening inequality with every
   max branch fixed.

The proof is the rational certificate in Section 3.  No numerical tolerance
or floating-point inference is used.

Therefore those consequences alone cannot yield a contradiction, chamber
consumer, or support-rank drop.  In particular the outsider estimate
`rho_i<=1-c` does not determine the sign of cap change: it controls the tail
coefficient, while the old quit-now candidate `Q_p` can still exceed the
returned tail cap.

## 5. Why this is a regression, not a counterexample

The notation `D_0` cannot honestly be upgraded to the actual global `D_*`
for this table.  For example the pure pair profiles on

\[
 \{0,2\},\ \{0,3\},\ \{1,2\},\ \{1,3\},\ \{2,3\}
\]

are exact terminal Nash profiles under the displayed rewards, so the true
global infimum is zero.  This was checked by the exact rule that, at a pure
coalition, each member compares leaving the coalition and each outsider
compares joining it.  The marked pair `{0,1}` is not the culprit: its total
debt is `1/3`, with player `2` carrying `1/12` and player `3` carrying
`1/4`.

For one explicit check, at `{0,2}` the two members receive `49/12` and
`173/96`, while leaving gives them `0` and `0`.  Outsider `1` receives
`55/8` and would receive only `49/12` by joining; outsider `3` receives
`31/6` and would receive only `19/4` by joining.  Hence every coordinate
debt is exactly zero at that profile.

This failure identifies rather than weakens the conclusion.  Equal debt
values plus the global singleton moat are only finitely many necessary
conditions for minimality; they do not assert

\[
 D(\tau)\ge D_0\quad\text{for every behavioral profile }\tau. \tag{5.1}
\]

The one-window deletion test checks one such competitor.  The certificate
makes that test an equality while failing other competitor tests.  Calling
the displayed scalar `D_*` would silently insert the universal condition
(5.1), which is essentially the unavailable global information.

There are consequently two separate missing fields in route (b).

1. **Source co-indexing.**  The checked minimum-return family has a minimum
   post-mark tail, but not a near-minimum whole impure profile carrying the
   same pair, gain, and zero defect.  Equivalently, (1.2) is not known to
   vanish.
2. **A constraint killing cap compensation.**  Even after granting the
   co-indexing and all local minimum consequences, the payer's active
   quit-now branch may satisfy
   `Q_p>b_p`; here `267/64>260/64`.  Deletion then lowers the payer cap and
   pays for all other cap openings.  Neither the full-debt moat nor zero
   defect for `o` upper-bounds this overshoot.

A sufficient new inequality for this particular branch would be
`Q_p<=b_p`, or more generally a second source-faithful perturbation charging
the positive part `(Q_p-b_p)_+`.  No inspected declaration supplies it.
Near-minimality of the purified/paid endpoint would also add global
competitor inequalities, but that is route (a), the original N3 rather than
a consequence of route (b).

## 6. Strongest surviving conclusion and next obligation

Revision 6's deletion identity and outsider screen remain correct and useful.
The proposed one-round “screening system,” however, is neither presently
produced on one impure witness nor algebraically infeasible after the missing
co-indexing is granted.  Its sharp surviving output is a necessary-condition
generator with a distinguished compensation chamber `(C,C,Q,C)`.

The next concrete obligation is one of the following equivalent-strength
source advances:

* prove whole-debt convergence for an impure profile carrying the exact
  pair/gain/zero-defect fields; or
* prove a source-attached upper bound on the payer overshoot
  `(Q_p-b_p)_+`, or a second finite perturbation inequality that charges it.

Without one of these, adding more copies of the same deletion inequality
does not eliminate the rational compensation mechanism above.
