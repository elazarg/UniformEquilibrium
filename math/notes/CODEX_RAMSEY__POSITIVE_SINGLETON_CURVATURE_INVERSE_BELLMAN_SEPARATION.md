# Positive singleton and a retained curvature square do not produce an inverse Bellman edge

Author: `CODEX_RAMSEY`

Status: **REVIEWED PASS; INTERNAL**

Independent review: [`CODEX_RAMSEY__POSITIVE_SINGLETON_CURVATURE_INVERSE_BELLMAN_SEPARATION__BY_CODEX_EULER.md`](../feedback/CODEX_RAMSEY__POSITIVE_SINGLETON_CURVATURE_INVERSE_BELLMAN_SEPARATION__BY_CODEX_EULER.md).

## 1. Question and exact answer

Fix a payoff vector (H).  An inverse Nash--Bellman producer must find a
tail (T) and a product root (q) such that

\[
 H=\operatorname{Succ}(T,q),\qquad q\in\operatorname{Nash}(T),
 \qquad T\ge P,
 \tag{1.1}
\]

with positive root absorption.  The orientation is tail (T) to current
head (H).  The root stored at the current state is Nash against (T), not
against (H).

Does the following strengthened local package force such a predecessor?

1. (H) is the unrestricted cap of an actual corner of a literal
   source/midpoint/target stopping-law square;
2. the square has strictly positive cap curvature;
3. some own singleton reward is strictly positive;
4. (H) dominates every behavioral punishment value; and
5. all Continue is the unique exact root not only at (H), but at all six
   prescribed/cap annotations of the square.

No.  The rational Fin4 table below satisfies all five items, but every exact
inverse edge with head (H) is the zero-charge all-Continue self-loop.
This strictly strengthens the earlier curvature-inert separation: that note
left open an unrelated positive backward edge having the inert cap as its
head, whereas the present calculation excludes every such edge.

The example has an exact terminal Nash profile and hence global semantic
debt minimum zero.  It therefore does **not** refute the full positive-
minimum hard-residual implication in `../FIN4_BT_QUESTION.md`.  It refutes
the smaller proposed converter

\[
 \text{positive singleton + floor-safe retained curvature square}
 \Longrightarrow
 \text{positive inverse Bellman predecessor}.                 \tag{1.2}
\]

Thus a successful positive-minimum proof must use global minimality or the
hard residual to produce an additional equality (H_i=Q_i(q_{-i})), not
only an absolute positive singleton reward.

## 2. Reward table and literal square

Use players (1,2,3,4).  Players (3,4) are passive.  For every nonempty
coalition (A), write (A^\circ=A\cap\{1,2\}), and define

\[
\begin{array}{c|rrrr}
A^\circ&\varnothing&\{1\}&\{2\}&\{1,2\}\\ \hline
r_1(A)&0&1/4&1/2&1\\
r_2(A)&0&1&-1&0.
\end{array}                                                   \tag{2.1}
\]

For (d\in\{3,4\}), put

\[
 r_d(A)=\begin{cases}-1,&d\in A,\\0,&d\notin A.\end{cases}   \tag{2.2}
\]

All rewards have absolute value at most one.  In particular

\[
 r_1(\{1\})=\frac14>0.                                      \tag{2.3}
\]

Players (3,4) Never quit in the three profiles below.  Player (1)'s
stopping law is fixed, with mass (1/2) at each of dates (0,1).  Let

\[
 S_2=\delta_0,\qquad T_2=\delta_1,\qquad
 M_2=\tfrac12\delta_0+\tfrac12\delta_1,                       \tag{2.4}
\]

and call the resulting product profiles (S,T,M).  This is a literal
one-coordinate stopping-law midpoint.  The middle law has masses

\[
 \Pr_M(\{1\})=\frac14,\qquad
 \Pr_M(\{2\})=\frac14,\qquad
 \Pr_M(\{1,2\})=\frac12.                                    \tag{2.5}
\]

Thus the square has actual positive finite atoms; no semantic carrier law is
being mistaken for one literal profile.

## 3. Prescribed payoffs, unrestricted caps, and curvature

Direct enumeration gives

\[
 U_S=(3/4,-1/2,0,0),\qquad
 U_M=(11/16,0,0,0),\qquad
 U_T=(5/8,1/2,0,0).                                          \tag{3.1}
\]

For player (1), the endpoint caps are one.  Against the middle clock its
pure-time values are

\[
 V_1(0)=5/8,\qquad V_1(1)=3/4,\qquad
 V_1(t)=1/2\quad(t\ge2\text{ or }t=\infty),                   \tag{3.2}
\]

so its middle cap is (3/4).  Against player (1)'s fixed clock, player
(2)'s values are unchanged from the audited curvature regression:

\[
 V_2(0)=-1/2,\qquad V_2(1)=1/2,\qquad
 V_2(t)=1\quad(t\ge2\text{ or }t=\infty).                    \tag{3.3}
\]

The passive players obtain zero by Never and at most (-1) whenever they
quit.  Pure-time extremality therefore gives the unrestricted behavioral
caps

\[
 B_S=(1,1,0,0),\qquad B_M=(3/4,1,0,0),\qquad B_T=(1,1,0,0).   \tag{3.4}
\]

For midpoint weight (1/2), player (1)'s cap curvature is

\[
 \frac12 B_{S,1}+\frac12B_{T,1}-B_{M,1}=\frac14>0.            \tag{3.5}
\]

The debt vectors are

\[
 d(S)=(1/4,3/2,0,0),\quad
 d(M)=(1/16,1,0,0),\quad
 d(T)=(3/8,1/2,0,0).                                        \tag{3.6}
\]

Set

\[
 H:=B_M=(3/4,1,0,0).                                        \tag{3.7}
\]

## 4. Unique all-Continue roots and punishment floor

At every vector

\[
 Z\in\{U_S,U_M,U_T,B_S,B_M,B_T\},                            \tag{4.1}
\]

players (3,4) strictly prefer Continue: quitting pays (-1), while
continuing pays zero.  Given that, player (2) strictly prefers Continue
whether player (1) Quits or Continues:

\[
 r_2(\{1\})=1>0=r_2(\{1,2\}),\qquad
 Z_2\ge-1/2>-1=r_2(\{2\}).                                  \tag{4.2}
\]

Given player (2) Continue, player (1) also strictly prefers Continue,
because (Z_1\ge5/8>1/4=r_1(\{1\})).  Hence all Continue is the unique
exact product root at every annotation in (4.1).

The head (H) is punishment-floor safe.  Against a passive player quitting
surely, player (1)'s cap is at most (1/4), player (2)'s cap is zero,
and the other passive player's cap is zero.  Consequently

\[
 P_1\le1/4<3/4=H_1,\qquad P_2,P_3,P_4\le0\le H_2,H_3,H_4.     \tag{4.3}
\]

Only the upper bounds in (4.3) are used; no punishment normality claim is
made for the table.

## 5. Coordinatewise inverse-edge elimination

Let (T\in\mathbb R^4) and let (q) be any product root satisfying

\[
 H=\operatorname{Succ}(T,q),\qquad q\in\operatorname{Nash}(T).\tag{5.1}
\]

Write (x_i=q_i(\mathrm{Quit})).  A general elementary support fact will be
used repeatedly:

> If (x_i>0), then (H_i=Q_i(q_{-i})), the payoff from player (i)'s
> immediate Quit action.

Indeed, if (x_i=1), the successor expectation is (Q_i).  If
(0<x_i<1), both actions are in support at an exact Nash root, so their
payoffs coincide with each other and with the successor coordinate (H_i).

For a passive player (d\in\{3,4\}), every coalition produced when (d)
Quits contains (d), so

\[
 Q_d(q_{-d})=-1\ne0=H_d.                                    \tag{5.2}
\]

Thus (x_3=x_4=0).  With the passive players inactive, player (2)'s Quit
payoff is

\[
 Q_2(q_{-2})=(1-x_1)(-1)+x_1\cdot0=x_1-1\le0<1=H_2.         \tag{5.3}
\]

Hence (x_2=0).  Finally, with players (2,3,4) inactive,

\[
 Q_1(q_{-1})=r_1(\{1\})=1/4\ne3/4=H_1,                     \tag{5.4}
\]

so (x_1=0).  Therefore (q) is all Continue.  Equation (5.1) then gives

\[
 T=H.                                                        \tag{5.5}
\]

We have proved the stronger statement

\[
 \boxed{\text{Every exact Nash--Bellman edge with head }H
 \text{ is the all-Continue self-loop.}}                     \tag{5.6}
\]

This did not use the floor constraint on (T); a fortiori there is no
positive-charge punishment-floor predecessor of (H).

Here “self-loop” means a payoff self-loop: the predecessor payoff equals
(H), and the root at the current state is all Continue.  If a Lean state also
stores a simplex annotation not used by these equations, the argument does
not identify that irrelevant stored annotation across the two states.

## 6. Exact scope and the positive-minimum seam

The profile in which player (1) quits surely and all other players Never
is an exact unrestricted terminal Nash profile.  Player (1) gets (1/4)
instead of zero from Never; player (2) gets (1) and would get zero by
joining; each passive player gets zero and would get (-1) by joining.
Thus the table has a uniform-equilibrium payoff and (D_*=0).

Accordingly, (5.6) is not an accepted counterexample to the full Fin4
breakthrough task.  Its precise value is to eliminate one proposed use of
the terminal-gap positive singleton consequence.  Absolute positivity
(r_i(\{i\})>0), even together with a floor-safe retained curvature square,
does not solve the inverse equations.  For every active player of a positive
inverse root one needs the **head-matching equality**

\[
 H_i=Q_i(q_{-i}),                                            \tag{6.1}
\]

and the current rectangle data provide no such equality at (H=B(f)).
At a true Fin4 global minimum, the checked strict inequalities
(r_i(\{i\})<U_i) point in the same nonproductive direction: they freeze
the outgoing prescribed-payoff roots rather than constructing an incoming
tail.

The remaining legitimate positive-minimum question is therefore whether the
full hard residual forces (6.1) for a common product root at the fixed-law
head, or else converts failure of every active-support system (6.1) into a
regenerated minimum-fiber rank decrease.  Neither conclusion is claimed
here.

## 7. Declaration and source audit

The orientation and support calculation were checked against:

- `IsQuittingNashBellmanEdge` and
  `exists_quittingNashBellmanPredecessor` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`;
- the tail-to-current charged orientation in
  `UniformEquilibrium/Quitting/Bellman/Finite/`
  `PunishmentFloorChargedRelation.lean`;
- `quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
  `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`; and
- behavioral pure-time extremality as used by the reviewed packet
  [`CODEX_EULER__CURVATURE_INERT_CAP_CHRONOLOGY_SEPARATION.md`](CODEX_EULER__CURVATURE_INERT_CAP_CHRONOLOGY_SEPARATION.md).

The earlier packet proved only the absence of positive outgoing edges from
the six displayed tails and explicitly left backward-head edges open.  The
inverse elimination (5.2)--(5.6) is therefore not a restatement of that
packet.

## Review disposition

The independent review checked the modified (r_1(\{1\})=1/4) payoff/cap
arithmetic, unrestricted caps, punishment-floor upper bounds, uniqueness at
all six annotations, the support implication
(x_i>0\Rightarrow H_i=Q_i), and the complete inverse-payoff-edge elimination.
It returned PASS with only the Lean-state qualification recorded after (5.6).
The result remains internal: it is a stronger local converter no-go with
(D_*=0), not a positive-minimum theorem or Fin4 counterexample.
