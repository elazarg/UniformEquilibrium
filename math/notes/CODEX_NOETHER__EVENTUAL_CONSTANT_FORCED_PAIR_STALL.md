# Eventual-constant forced-pair stalls are actual finite-clock fixed points

Author: `CODEX_NOETHER`

## Current status

The eventual-constant branch of the canonical maximal-prefix ray does not
hide a compactness bubble.  It is an attained finite-clock semantic point,
with a unique all-Continue exact cap root.  This strengthens the normal form
but does not consume it.

More sharply, the precise Fin4 owner/payer pattern at an *immediate* constant
forced pair is compatible with all of the maintained table-level hard data:
full normal core, `ResidualHardClass`, punishment normality, and a
full-support normalized singleton packet.  An exact rational completion is
given below.  It has an exact all-Never equilibrium, so its global debt
minimum is zero and it is not a counterexample.  The regression proves that
the missing positive-minimum/terminal-gap hypothesis must be used through a
genuinely global behavioral argument; the forced-pair labels and hard
singleton matrix cannot by themselves contradict eventual constancy.

The exact remaining scalar after spending the paid endpoint is the
cross-coordinate horizontal compensation.  Unique all-Continue at the
source cap gives no sign for it.

Everything below is ordinary mathematics.  No Lean file and no export claim
is made.

## 1. Question and inspected interface

Let (C=\{j,o\}) be the pure forced pair and let (Z_C) be its
tail-independent terminal-semantic pair.  Starting from (Z_C), the checked
canonical selector recursively prefixes a maximum-absorption exact cap--Nash
root.  Write

\[
 Z_{k+1}=T_{q_k}Z_k,
 \qquad q_k=q^{\max}(B(Z_k)).                 \tag{1}
\]

The source-facing result
`FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_maximalPrefixRayMinimumReturn_or_stall`
in
`Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`
leaves a strict arm with

\[
 D(Z_k)\downarrow L>D_*>0.                    \tag{2}
\]

The task here is the subcase in which (q_N) is literally all Continue for
some finite (N), especially (N=0).

The exact source declarations inspected were:

* `quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`
  in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`;
* the autonomous maximal selector and semantic orbit in
  `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`;
* `QuittingMaximalCapSemanticPrefixRayStall` and its debt/absorption account
  in `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`;
* the forced owner, fixed payer, and literal pure-pair adapter in
  `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean` and
  `MaximalPrefixRayDichotomy.lean`; and
* `FinFourQuantitativeFullSupportHardResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.

## 2. Finite stopping of the autonomous ray is exact fixation

### Proposition 2.1

If (q_N) is all Continue, then

\[
 Z_k=Z_N,qquad q_k=\mathbf C
 \quad(k\ge N),                               \tag{3}
\]

and all Continue is the **unique** exact product-root Nash equilibrium
against (B(Z_N)).

### Proof

All Continue has zero absorption.  The selected root maximizes absorption
among all exact roots.  Hence maximality of (q_N=\mathbf C) says that every
exact root has absorption zero.  A product quitting root has absorption zero
only when every player Continues surely, proving uniqueness.

Prefixing by all Continue fixes the complete terminal-semantic pair.  The
selector depends only on the current cap, so the same unique root is selected
again.  Induction gives (3).  ∎

### Proposition 2.2

The fixed point (Z_N) is realized by one literal finite-clock profile.  Its
terminal law has finite support and absorption occurs by its displayed pure
pair date under prescribed play and under every unilateral behavioral
replacement.  In particular, every unrestricted cap coordinate at (Z_N)
is attained by one of finitely many pure stopping-time endpoints.

### Proof

The realizing profile is the finite word

\[
 q_{N-1}*\cdots*q_0*(\text{pure }C)*\tau .     \tag{4}
\]

The tail \(\tau\) is screened by the pure nonsingleton row.  Under a
unilateral replacement, at least one of the two members of (C) is still
prescribed to Quit surely at that date.  Thus no unilateral deviation can
reach the counterfactual tail.  Only the finitely many decisions before and
at the pair date matter.  Randomized and history-dependent stopping rules are
convex combinations of these finitely many pure endpoints.  ∎

Consequently, in the strict ray arm the limit is not a nonattained bubble:

\[
 \boxed{D(Z_N)=L>D_*} .                        \tag{5}
\]

Neither attainment nor finite cap attainment is enough to lower (5).

## 3. The exact missing horizontal quantity

Let (p) be the retained paid mover at the shifted pure pair and let (Y_N)
be the literal profile obtained by taking its best endpoint there.  On the
canonical pure-pair ray the paid gain is the mover's entire whole-profile
debt:

\[
 g=d_p(Z_N)>0,qquad d_p(Y_N)=0.               \tag{6}
\]

Define the horizontal compensation

\[
 K_p:=\sum_{i\ne p}\bigl(d_i(Y_N)-d_i(Z_N)\bigr). \tag{7}
\]

Then the total-debt identity is exactly

\[
 D(Y_N)=L-g+K_p.                               \tag{8}
\]

Global minimality supplies only

\[
 K_p\ge g-(L-D_*).                             \tag{9}
\]

The unique-all-Continue statement is a Nash condition at the *outer source
cap* (B(Z_N)).  The number (K_p) measures the other three unrestricted
caps after changing (p)'s complete prescribed strategy at the buried
pair.  There is no implication in either direction between these facts.

Thus a genuine consumer needs new data of one of the following kinds:

* an upper bound on (K_p) strong enough to put (Y_N) on or below the
  minimum fibre;
* no-new-debtor control together with minimum-fibre return, turning (6) into
  a support drop; or
* a source-matched chronology which pays the compensation in (7) and returns
  to one fixed target.

For (N>0), recomputing a canonical ray after the horizontal update also
changes the outer word.  This is the known restart seam.  For (N=0), if the
best endpoint remains nonsingleton, there is no such seam: (Y_0) is exactly
the next pure coalition.  Even that stronger immediate case is not locally
contradictory, as the following regression shows.

## 4. A residual-hard immediate-stall regression

Let (I=\operatorname{Fin}4).  Start with the paired singleton matrix

\[
 M=
 \begin{pmatrix}
 0&3&-1&-1\\
 3&0&-1&-1\\
 -1&-1&0&3\\
 -1&-1&3&0
 \end{pmatrix}.                                \tag{10}
\]

For every singleton ({a}), set

\[
 r_i(\{a\})=M_{ia}.                            \tag{11}
\]

The diagonal singleton rewards are therefore zero.

It remains to define nonsingleton coordinates.  For each player (i), write
any coalition containing (i) uniquely as (T\cup\{i\}), with
(T\subseteq I\setminus\{i\}).  Choose arbitrary passive values (f_i(T))
for (i\notin T), subject to

\[
 f_i(\{a\})=M_{ia}.                            \tag{12}
\]

Take all other passive values to be zero except

\[
 f_2(\{0,1\})=1,qquad f_3(\{0,1\})=2.        \tag{13}
\]

Define the membership gains

\[
\begin{aligned}
 g_0(T)&=\mathbf1_{3\in T}-2\mathbf1_{1\in T},\\
 g_1(T)&=\mathbf1_{0\in T}-2\mathbf1_{3\in T},\\
 g_2(T)&=\mathbf1_{0\in T}-2\mathbf1_{3\in T},\\
 g_3(T)&=\mathbf1_{1\in T}-2\mathbf1_{0\in T},
\end{aligned}                                  \tag{14}
\]

and put

\[
 r_i(T\cup\{i\})=f_i(T)+g_i(T).               \tag{15}
\]

Equations (11)--(15) define one rational reward table coordinatewise on all
nonempty coalitions.

### Proposition 4.1: exact forced-pair data

At the pure pair (C=\{0,1\}),

\[
 U(C)=(1,4,1,2),qquad B(C)=(3,4,2,2),         \tag{16}
\]

so

\[
 d(C)=(2,0,1,0).                               \tag{17}
\]

The strict singleton-to-pair owner can be chosen as (o=1): its payoff
rises from (r_1(\{0\})=3) to (r_1(C)=4), and its pair defect is zero.
The distinct outside player (p=2) has the strict pair-to-triple gain

\[
 r_2(\{0,1,2\})-r_2(\{0,1\})=1.               \tag{18}
\]

Thus the exact owner-zero/payer-positive forced-pair labels coexist at the
same literal row.

### Proposition 4.2: the maximal ray is immediately constant

All Continue is the unique exact product-root Nash equilibrium against

\[
 b=B(C)=(3,4,2,2).                             \tag{19}
\]

### Proof

Write the four Quit probabilities as (x_0,x_1,x_2,x_3).  By (14), the
Quit-minus-Continue endpoint differences are

\[
\begin{aligned}
 G_0&=x_3-2x_1-3(1-x_1)(1-x_2)(1-x_3),\\
 G_1&=x_0-2x_3-4(1-x_0)(1-x_2)(1-x_3),\\
 G_2&=x_0-2x_3-2(1-x_0)(1-x_1)(1-x_3),\\
 G_3&=x_1-2x_0-2(1-x_0)(1-x_1)(1-x_2).
\end{aligned}                                  \tag{20}
\]

At a Nash root, (x_i>0) implies (G_i\ge0), while (x_i=0) implies
(G_i\le0).

If (x_0>0), the first inequality gives (x_3\ge2x_1).  If (x_3=0), it
forces (x_1=0,x_2=1), after which (G_1=x_0>0), contradicting
(x_1=0).  Hence (x_3>0); then (G_3\ge0) gives
(x_1\ge2x_0>0), and (G_1\ge0) gives (x_0\ge2x_3).  Chaining with the
first inequality gives (x_3\ge2x_1\ge4x_0\ge8x_3), impossible.

Thus (x_0=0).  If (x_1>0), (G_1\ge0) forces (x_3=0,x_2=1); then
(G_3=x_1>0), contradicting (x_3=0).  Hence (x_1=0).  If (x_3>0),
(G_3\ge0) forces (x_2=1); then (G_0=x_3>0), contradicting (x_0=0).
Hence (x_3=0).  Finally, if (x_2>0), then (G_2=-2<0), a
contradiction.  Therefore every coordinate is zero.  ∎

Since the maximum absorption among exact roots is zero, the canonical
maximal-prefix selector chooses all Continue at depth zero and forever.

### Proposition 4.3: every non-witness table-level hard field survives

The table has:

1. normalized singleton matrix exactly (M);
2. full normal core and `ResidualHardClass`;
3. punishment normality for every player; and
4. a full-support normalized singleton packet with mass (1/4) on every
   owner and target zero.

### Proof

Item 1 is immediate from (11) and the zero diagonal.  The checked declaration
`pairedSingletonMatrix_normalCore_eq_univ`, the public matrix theorems proving
standard-Q and no-homogeneous behavior, and
`pairedSingletonMatrix_not_projectiveQBar` in the paired-singleton example
give item 2 by exactly the same four-field construction used there.  This is
a theorem about the singleton matrix, so changing the nonsingleton completion
does not affect it.

For item 3, let every opponent play Never.  A player's best response is worth
zero: Quit alone pays its diagonal singleton reward zero, and Never pays
zero.  Hence its punishment value is at most its singleton reward.

For item 4, the average of every row of (M) under the uniform owner law is
\(1/4\ge0\).  The target and every own singleton payoff are zero, and the
same all-Never punishment test gives the punishment inequality.  Every owner
has positive mass (1/4).  ∎

### Proposition 4.4: why this is not a counterexample

The all-Never behavioral profile is an exact terminal Nash profile.  Every
finite unilateral Quit pays the deviator its own singleton reward zero, and
Never pays zero.  Consequently

\[
 D_*=0.                                        \tag{21}
\]

Thus the regression deliberately omits exactly the global terminal-gap field
of `FinFourQuantitativeFullSupportHardResidual`.  It proves that adding the
other fields, even together with the exact forced-pair owner/payer provenance
and immediate unique-all-Continue fixation, does not orient the stall.

More precisely, the regression proves analogues of
`normalCore_eq_univ`, `all_punishmentNormal`, `packet`,
`packet_support_eq_univ`, positive packet mass, and `residualHardClass`.  It
does **not** construct `witness`; consequently it also makes no claim about
the witness-dependent numerical `massFloor_pos` and `massFloor_le` fields.

## 5. Verdict

For the eventual-constant branch, positive global minimum plus the retained
labels has not yielded a contradiction.  What is proved is a sharp boundary:

\[
\boxed{
\begin{array}{c}
\text{eventual constant canonical ray}\\
\Longrightarrow\\
\text{actual finite-clock off-minimum fixed point with attained caps,}\\
\text{unique all-Continue cap root, and exact horizontal compensation (8).}
\end{array}}
\]

The residual-hard regression shows that no static singleton-matrix or
same-row label argument can control that compensation.  A conjecture-facing
consumer must use the terminal exploitability witness on an actual modified
profile, or produce a source-matched return/no-entry theorem controlling
(K_p).  Merely restarting the maximal selector, invoking hard-principal
algebra, or observing cap attainment repeats the same fixed point.

## 6. Two separate formalization targets

The source theorem and the regression should be kept separate.

### Target A: autonomous finite fixation

For the generic maximal-prefix orbit, formalize:

```text
maximalCapSemanticPrefixOrbit_eventually_constant_of_root_eq_allContinue
maximalCapSemanticPrefixOrbit_unique_exactRoot_of_selected_allContinue
maximalCapSemanticPrefixOrbit_finitePureTimeCapAttainment_of_eventualConstant
eventualConstantForcedPair_horizontalCompensation_eq
```

The conclusion must retain the literal finite profile, finite terminal law,
full behavioral cap attainment, the strict equality `D = L > D_*` in the
stall arm, and the spectator leakage identity (8).

### Target B: rational immediate-stall regression

Package (11)--(15) as a concrete reward table and prove:

```text
normalizedSoloMatrix = pairedSingletonMatrix
normalCore = univ
ResidualHardClass
forall player, IsQuittingNormalPlayer
full-support normalized singleton packet with mass 1/4
pure {0,1} semantic pair = ((1,4,1,2),(3,4,2,2))
owner 1 defect = 0
outside payer 2 join gain = 1
unique exact cap root at (3,4,2,2) = allContinue
allNever is exact terminal Nash
terminal semantic minimum debt = 0
```

The last two declarations are essential: they make explicit that this is a
sharp regression and not a positive-gap counterexample.  Neither Target A
nor Target B by itself consumes the strict ray, and this note is not proposed
for export before independent review.
