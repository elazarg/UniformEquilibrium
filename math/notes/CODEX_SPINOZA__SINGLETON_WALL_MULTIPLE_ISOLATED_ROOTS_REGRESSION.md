# A singleton cap wall can have only isolated nonsure multiple roots

Author: CODEX_SPINOZA

## Status

**Exact rational regression in ordinary mathematics; not Lean-checked.** A
literal Fin4 terminal semantic pair has one singleton-pinned positive debtor,
but its one-stage exact-root set consists of three isolated roots, including
two distinct fully mixed roots. No root is pure and no player Quits surely at
any root.

Thus the local data “singleton cap pin + positive debt + multiple positive
exact roots” do not force a two-sure terminal screen, a pure pinned-owner
screen, a connected root component, or a vertical root fiber. This is a
local implication counterexample, not a positive-global-minimum quitting
game and not a counterexample to uniform equilibrium.

## 1. Rational quitting table

Let the players be \(0,1,2,3\), and let the continuation payoff be
\(u=0\). For root Quit probabilities

\[
 x=q_0,\qquad y=q_1,\qquad z=q_2,
\]

define the four pure-Quit-minus-pure-Continue endpoint differences by

\[
\begin{aligned}
 D_0(y,z)&=y-z-20(y-1/4)(z-3/4),\\
 D_1(x,z)&=x-z,\\
 D_2(x,y)&=(x-1/4)(y-3/4),\\
 D_3&=-1.
\end{aligned}                                             \tag{1}
\]

These multi-affine differences come from one rational quitting table. For a
nonempty coalition \(S\), define coordinate \(i\)'s reward by

\[
 r_i(S)=
 \begin{cases}
  0,&i\notin S,\\
  D_i(\mathbf 1_{S\setminus\{i\}}),&i\in S,
 \end{cases}                                               \tag{2}
\]

where in the second line \(D_i\) is evaluated on the displayed opponent
coordinates and unused player-3 coordinates are ignored. For \(i=3\), the
second line means \(-1\). Since every Continue payoff is zero against
\(u=0\), multilinear interpolation of the vertex values in (2) gives
exactly (1).

## 2. The actual singleton wall

Take the literal all-Never behavioral tail. Its prescribed payoff is zero.
Against opponents who Never, player \(i\)'s complete cap is the better of
Never, which pays zero, and quitting alone, which pays \(r_i(\{i\})\).
Equation (1) gives

\[
 (r_0(\{0\}),r_1(\{1\}),r_2(\{2\}),r_3(\{3\}))
 =(-15/4,0,3/16,-1).
\tag{3}
\]

Hence the complete semantic pair of this actual tail is

\[
 (u,B)=\bigl(0,(0,0,3/16,0)\bigr).
\tag{4}
\]

Player \(2\) is a singleton-pinned debtor:

\[
 B_2=r_2(\{2\})=3/16,
 \qquad d_2=B_2-u_2=3/16>0.
\tag{5}
\]

## 3. Exact root enumeration

At an exact product root, each coordinate obeys the binary complementarity
rule

\[
 q_i=0\Rightarrow D_i\le0,\qquad
 0<q_i<1\Rightarrow D_i=0,\qquad
 q_i=1\Rightarrow D_i\ge0.
\tag{6}
\]

Since \(D_3=-1\), every root has \(q_3=0\). We now exhaust the three cases
for \(y=q_1\).

### Case \(y=0\)

Player 1's condition gives \(x\le z\). Moreover

\[
 D_2={3\over4}(1/4-x),
 \qquad D_0=4z-15/4.
\tag{7}
\]

If \(z=0\), player 2 requires \(x\ge1/4\), contradicting \(x\le z\).
If \(0<z<1\), player 2 requires \(x=1/4\); then player 0 mixes and requires
\(D_0=0\), so \(z=15/16\). If \(z=1\), player 2 requires
\(x\le1/4\), but \(D_0=1/4>0\), which is incompatible with either
\(x=0\) or \(0<x<1\). Thus this case gives exactly

\[
 (x,y,z)=(1/4,0,15/16).
\tag{8}
\]

### Case \(y=1\)

Player 1 gives \(x\ge z\), and

\[
 D_2={1\over4}(x-1/4),
 \qquad D_0=49/4-16z.
\tag{9}
\]

If \(z=0\), player 2 requires \(x\le1/4\), while player 0's condition
cannot hold because \(D_0=49/4\). If \(0<z<1\), player 2 requires
\(x=1/4\), and \(x\ge z\); player 0 mixing would instead require
\(z=49/64>1/4\). If \(z=1\), the two inequalities force \(x=1\), but
then \(D_0=-15/4<0\), contradicting pure Quit by player 0. There is no root
in this case.

### Case \(0<y<1\)

Player 1 mixes, so \(x=z\). If \(x=0\), player 0 requires
\(y\le15/64\), while player 2 requires \(y\ge3/4\). If \(x=1\), player
0 requires \(y\le1/16\), while player 2 again requires \(y\ge3/4\).
Thus \(0<x=z<1\), and both players 0 and 2 mix. The equation

\[
 (x-1/4)(y-3/4)=0
\tag{10}
\]

has two branches. If \(x=1/4\), then
\(D_0=11(y-1/4)\), so \(y=1/4\). If \(y=3/4\), then
\(D_0=11(3/4-x)\), so \(x=3/4\). Hence the two roots are

\[
 (x,y,z)=(1/4,1/4,1/4),qquad(3/4,3/4,3/4).
\tag{11}
\]

Combining the cases, the full Fin4 exact-root set is exactly

\[
 \boxed{
 (1/4,0,15/16,0),\quad
 (1/4,1/4,1/4,0),\quad
 (3/4,3/4,3/4,0).}
\tag{12}
\]

It is finite, so every root is isolated. Every root has positive absorption,
but every coordinate is strictly below one. Thus there is no sure quitter,
no pure root, and no connected root path between the two fully mixed roots.

## 4. Consequence for the renewed-wall route

The reviewed two-sided-wall theorem reaches a common off-minimum payoff with
two distinct positive exact roots when exact root matching fails. Regression
(2)--(12) shows that the wall and finite-dimensional complementarity alone
cannot upgrade that output to any of the currently terminal cases. A valid
Fin4 classification must additionally use genuinely global data such as:

- which root is selected by the canonical capacity path;
- literal high/low source ancestry and the capacity gap;
- punishment-floor admissibility; or
- the positive global minimum over the complete terminal-semantic carrier.

Merely interpolating between the roots is invalid: the exact-root set in
(12) is disconnected.

## Sources inspected

- `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`, for the
  endpoint difference and exact binary complementarity semantics;
- `UniformEquilibrium/Quitting/Root/NashBellmanSpine.lean`, for closedness of
  the exact-root graph;
- `notes/CODEX_SPINOZA__TWO_SIDED_SINGLETON_WALL_UNIQUE_ROOT_CAPACITY_SHIFT.md`;
- `notes/CODEX_SPINOZA__CAPACITY_GAP_ROOT_MATCHING_OR_PERSISTENT_INNER_MARK.md`;
  and
- `formalized/POSITIVE_MINIMUM_EXACT_PREFIX_CLOCK_ESCAPE.md`.

## Boundary and nonclaims

- The table is rational and the all-Never semantic pair is literal, not an
  abstract cap assignment.
- The pair (4) is not asserted to minimize debt over the terminal-semantic
  carrier. In particular, this is not a positive-\(D_*\) counterexample.
- No statement is made about the table's uniform-equilibrium payoff set.
- The regression refutes only a local multi-root implication. It does not
  refute a theorem using canonical capacity selection or full source
  chronology.

## Next exact question

Can the capacity-selected root and its separated low-side root be ordered by
one global source functional that is absent from (1)--(12), or does the
capacity gap again shift into the all-summable outward predecessor object?
