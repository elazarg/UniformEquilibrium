# Positive welfare separation: the common-normal screen

**Owner:** `CODEX_EULER`  
**Status (2026-08-26):** new ordinary mathematics and exact rational
regression; internal pending independent review.  No export claim.

## 1. Question

Can robust failure of finitely many local quitting-game repair systems be
converted, by finite separation, into one strictly positive player weight and
a global Bellman welfare bias?

The short answer is:

* for a quitting game, existence of the bias is already equivalent to one
  finite **terminal-row common-normal LP**;
* separately positive local normals do not imply a common normal, even with
  rational data, strict local margins on every nonsaturated row, and exact
  one-sided security floors; and
* the precise missing hypothesis is finite common-normal compatibility.  A
  Helly test reduces it to subfamilies of at most `|I|` local cells, provided
  those cells cover every global recurrent row.

Thus ordinary cellwise Farkas separation cannot prove WS3 in
`ideas/PositiveWelfareSeparator`.  A valid producer must establish the
common-normal compatibility from additional repair geometry.

## 2. Checked interfaces inspected

The downstream consumer and bias are:

```text
UniformEquilibrium/Certificates/Adaptive/WeightedWelfareBias.lean
  HasWeightedWelfareBias
  hasUniformWeightedWelfareCap_of_hasWeightedWelfareBias
  isUniformEquilibriumPayoff_of_oneSidedGuarantees_of_positiveWeightedWelfareBias

UniformEquilibrium/Certificates/Adaptive/WeightedSecurityWelfareAssembly.lean
  HasUniformWeightedWelfareCap
  isUniformEquilibriumPayoff_of_oneSidedGuarantees_of_positiveWeightedWelfareCap

UniformEquilibrium/Quitting/Classification/EquivariantSecurityWelfareAssembly.lean
  weighted_terminalPayoff_le_of_hasUniformWeightedWelfareCap
  not_hasUniformWeightedWelfareCap_of_terminal_welfare_gt

MathUE/Probability/PhaseOccupationDuality.lean
  phaseAverageReward_le_bias
  exists_optimal_phaseOccupation_and_phaseBias_of_feasible
```

The general LP duality is correct and useful.  The simplification below uses
the exact absorbing-state definition of `quittingGame` in
`ProofView/Concepts/Stochastic/Models/Quitting/Game.lean`.

A narrow search of the maintained literature summaries and transcriptions
found no paper theorem asserting the missing local-repair-to-positive-normal
implication.  The arguments below use only finite polyhedral separation,
Helly's theorem, and the checked project interfaces; no literature producer is
being imported.

## 3. Exact quitting-game bias equivalence

Let `I` be a nonempty finite player set, let `r` be a quitting reward table,
let `v in R^I`, and let `alpha in R^I` be arbitrary.  Write

\[
 \langle\alpha,x\rangle=\sum_{i\in I}\alpha_i x_i.
\]

### Theorem 3.1 (a quitting welfare bias is exactly a terminal-row normal)

The following are equivalent.

1. `HasWeightedWelfareBias (quittingGame r) alpha v`.
2. The finite inequalities

   \[
     0\leq\langle\alpha,v\rangle,                       \tag{3.1}
   \]

   \[
     \langle\alpha,r(S)\rangle
       \leq\langle\alpha,v\rangle
       \quad\text{for every nonempty }S\subseteq I      \tag{3.2}
   \]

   hold.

When (3.1)--(3.2) hold, the identically zero state bias and bound zero witness
the checked definition.

#### Proof

Assume a bias `B` satisfies the universal Bellman inequality.  At an absorbed
state `some S`, every joint action has stage payoff `r(S)` and returns to the
same state.  The two copies of `B(some S)` cancel, leaving (3.2).  At the live
state under the all-Continue action, stage payoff is zero and the next state
is again live.  The two copies of `B(none)` cancel, leaving (3.1).

Conversely take `B=0`.  At a live state every current stage payoff is zero.
The required inequality is (3.1), independently of whether the next state is
live or absorbed.  At `some S` it is exactly (3.2).  The bias bound is zero.
QED.

### Consequence 3.2

For quitting games the occupation-polytope producer does not need to search
for a nonzero bias.  The recurrent extreme classes already include the live
all-Continue self-loop with reward zero and each absorbed terminal self-loop
with reward `r(S)`.  Their inequalities are necessary, and zero bias makes
them sufficient.

Hence the genuinely open producer is precisely a strictly positive common
normal for these finitely many reward rows at a target already carrying
one-sided security certificates.

## 4. Exact rational LP

Assume `r` and `v` are rational.  Normalize the weight by
`sum_i alpha_i=1`.  The exact finite program is

\[
\begin{array}{ll}
\text{maximize}&\tau\\[1mm]
\text{subject to}
 &\sum_i\alpha_i=1,\\
 &\alpha_i\geq0,\quad \alpha_i\geq\tau\quad(i\in I),\\
 &-\langle\alpha,v\rangle\leq0,\\
 &\langle\alpha,r(S)-v\rangle\leq0
      \quad(\varnothing\ne S\subseteq I).
\end{array}                                                   \tag{4.1}
\]

If the feasible set is nonempty, its optimum is attained and rational.  It is
strictly positive exactly when a strictly positive welfare weight exists.
Together with one-sided security certificates at `v`, `tau_*>0` feeds the
checked positive-weight bias consumer and yields a uniform-equilibrium payoff.

For a cleaner alternative, define the finite residual family

\[
 Z=\{-v\}\cup\{r(S)-v:\varnothing\ne S\subseteq I\}.
\]

The Gordan--Stiemke/Motzkin alternative gives

\[
 \exists\alpha\gg0\ \forall z\in Z,\ \alpha\cdot z\leq0
 \quad\Longleftrightarrow\quad
 \operatorname{cone}(Z)\cap\mathbb R_+^I=\{0\}.          \tag{4.2}
\]

Thus failure of the positive separator has an exact rational certificate:
there are nonnegative coefficients, not all zero, whose conic combination of
the residual rows is a nonzero coordinatewise-nonnegative vector.  Normalize
that vector to have coordinate sum one to obtain a bounded rational
feasibility LP.

The right side of (4.2), not local repair infeasibility, is the precise global
condition which WS3 must produce.

## 5. Minimal rational failure of local-to-global separation

Take two players, target `v=(0,0)`, and terminal rewards

\[
 r(\{1\})=(1,-1/2),\qquad
 r(\{2\})=(-1/2,1),\qquad
 r(\{1,2\})=(0,0).                                      \tag{5.1}
\]

Consider two local cells, each also containing the saturated joint row:

\[
 E_1=\{r(\{1\}),0\},\qquad E_2=\{r(\{2\}),0\}.
\]

Each cell has a strictly positive normal with a strict margin on its
nonsaturated generator:

\[
 (1,3)\cdot r(\{1\})=-1/2,qquad
 (3,1)\cdot r(\{2\})=-1/2.                              \tag{5.2}
\]

But a common positive normal would have to satisfy

\[
 \alpha_1\leq\alpha_2/2,qquad
 \alpha_2\leq\alpha_1/2,                               \tag{5.3}
\]

which is impossible for `alpha_1,alpha_2>0`.  Equivalently,

\[
 r(\{1\})+r(\{2\})=(1/2,1/2)>0                         \tag{5.4}
\]

is the conic obstruction in (4.2).

This is a literal quitting table, not only an abstract convex example.  Each
player has an exact one-sided security floor zero: Quit at date zero.  If the
opponent Continues, the player receives `1`; if the opponent also Quits, the
player receives `0`.  Nevertheless no positive weight has a global welfare
cap at target zero, since the two pure singleton exit profiles force the
incompatible inequalities (5.3).

The game is not a conjecture counterexample.  Both players quitting at date
zero is itself an exact terminal Nash profile with payoff zero.  The table is
a source-level regression proving only that robust rowwise/local positive
separation, even beside exact security floors, does not glue into the common
welfare normal required by the checked consumer.

## 6. The precise additional condition: finite common-normal compatibility

Let a finite family of local cells `E_c` cover every global residual row in
`Z`.  For `delta>0`, put

\[
 W_c(\delta)=\left\{\alpha:
   \sum_i\alpha_i=1,\ \alpha_i\geq\delta,\
   \alpha\cdot z\leq0\ (z\in E_c)\right\}.              \tag{6.1}
\]

These are rational compact convex sets in an affine space of dimension
`|I|-1`.

### Theorem 6.1 (Helly common-normal producer)

Suppose that for every subfamily of at most `|I|` cells there is a strictly
positive normalized weight satisfying all rows in that subfamily.  Then there
is one strictly positive normalized weight satisfying every cell, hence every
global residual row.

#### Proof

There are finitely many subfamilies of size at most `|I|`.  Take a positive
rational `delta` smaller than the minimum coordinate of every supplied
subfamily weight.  Every at-most-`|I|` subfamily of the convex sets
`W_c(delta)` has nonempty intersection.  Their ambient affine dimension is
`|I|-1`, so Helly's theorem gives nonempty intersection of all of them.  Since
the defining data are rational, the nonempty rational polyhedron contains a
rational point.  Coverage then gives all constraints in (4.1).  QED.

The two-player table (5.1) shows the Helly order is sharp: each single cell
has a robust positive normal, while the two-cell family does not.

This theorem identifies the missing repair statement exactly.  A successful
WS3 proof must show at least one of the following equivalent kinds of global
compatibility:

1. the terminal-row LP (4.1) has `tau_*>0`;
2. no nonzero nonnegative conic combination obstruction (4.2) exists; or
3. every at-most-`|I|` family of repair cells admits a common positive normal,
   with the cells covering all recurrent residual rows.

Producing a different Farkas multiplier for each cell is insufficient.

## 7. Frontier consequence and nonclaims

The PositiveWelfareSeparator route is now an exact finite alternative for
quitting games rather than an unspecified occupation-separation hope:

```text
positive common terminal-row normal (LP tau_* > 0)
    + supplied one-sided security floors
    -> zero weighted Bellman bias
    -> checked uniform welfare cap
    -> checked uniform-equilibrium payoff;

nonzero nonnegative conic residual combination
    -> exact obstruction to this welfare route at the selected target.
```

What remains unproved is the game-facing producer: current local repair
failure data have not been shown to exclude the conic obstruction or to give
the `|I|`-wise common-normal property.  The rational table (5.1) shows that no
proof using only separate local positive multipliers can work.

This note does not claim that absence of a positive welfare normal implies
absence of a uniform equilibrium, nor that (5.1) is a terminal-gap table.  It
does not identify the presently maintained Fin4 repair cells with a cover
satisfying Theorem 6.1.  That exact adapter is the next question.

## 8. Requested check

Please independently verify Theorem 3.1 against the literal quitting-game
state/action timing, the strict-cone alternative (4.2), the security claim and
no-common-normal calculation in (5.1), and the Helly number `|I|` in Theorem
6.1.
