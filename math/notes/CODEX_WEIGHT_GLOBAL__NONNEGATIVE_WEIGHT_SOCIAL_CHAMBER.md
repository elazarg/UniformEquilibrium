# Nonnegative-weight social chamber at the ordinary global minimum

Author: CODEX_WEIGHT_GLOBAL

Status: PROOF_DRAFT

This note proves ordinary finite-dimensional consequences of named checked
terminal-semantic declarations.  The new weighted aggregation, its
positive-mass outcome selection, and the supportwise cone alternative have
not been checked as Lean declarations.

## Question

Let $I$ be a finite player set and let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting-game reward table.  Put

\[
s_i=r_i(\{i\}).
\]

For a point $z=(U,B)$ in the closed terminal-semantic carrier, let

\[
d_i(z)=B_i-U_i\geq0,
\qquad
D(z)=\sum_i d_i(z).
\]

Let $z_*=(U,B)$ minimize $D$ on the carrier and write

\[
D_*=D(z_*).
\]

Given a nonnegative vector \(\theta\in\mathbb R^I_{\geq0}\), define

\[
T_\theta=\sum_i\theta_i,
\qquad
M_\theta=\max_i\theta_i,
\qquad
A_\theta=\sum_i\theta_i s_i,
\]

and

\[
R_\theta=
\max\left(0,\max_{S\ne\varnothing}
  \sum_i\theta_i r_i(S)\right).
\]

Assume that at least two coordinates of \(\theta\) are positive.  Does

\[
R_\theta\leq A_\theta                                      \tag{C}
\]

force $D_*=0$, and hence a uniform-equilibrium payoff?  Can the resulting
finite reward-table certificate be selected at one common terminal outcome?

## Result

### The global-minimum costate inequality

If $D_*>0$, then

\[
\boxed{
A_\theta+(T_\theta-M_\theta)D_*
\leq \sum_i\theta_iU_i
\leq R_\theta.}                                           \tag{1}
\]

Because at least two coordinates of \(\theta\) are positive,

\[
T_\theta-M_\theta>0.                                     \tag{2}
\]

Consequently a positive minimum obeys

\[
R_\theta>A_\theta,
\qquad
D_*\leq
\frac{R_\theta-A_\theta}{T_\theta-M_\theta}.             \tag{3}
\]

The unconditional bound is

\[
\boxed{
D_*\leq
\max\left(0,
  \frac{R_\theta-A_\theta}{T_\theta-M_\theta}
\right).}                                                 \tag{4}
\]

In particular, (C) forces $D_*=0$.  The checked zero-minimum consumer then
gives a uniform-equilibrium payoff.

Condition (C) is the finite homogeneous system

\[
\theta_i\geq0,
\qquad
|\{i:\theta_i>0\}|\geq2,
\qquad
\theta\mathbin\cdot s\geq0,
\qquad
\theta\mathbin\cdot(r(S)-s)\leq0
\quad(S\ne\varnothing).                                  \tag{5}
\]

The costate may be normalized by $T_\theta=1$.

### Positive-mass common-outcome certificate

Let

\[
\overline r(\omega)=
\begin{cases}
0,&\omega=\mathrm{Never},\\
r(S),&\omega=S\ne\varnothing.
\end{cases}
\]

At every positive ordinary global minimum there is a terminal reward-moment
representation \(\mu\) of $U$ and an outcome in its positive support such
that

\[
\boxed{
0<\mu(\omega),
\qquad
(T_\theta-M_\theta)D_*
\leq
\theta\mathbin\cdot(\overline r(\omega)-s).}              \tag{6}
\]

Thus failure of the chamber is witnessed by one common terminal outcome,
not by choosing a different outcome for each payoff coordinate.  The outcome
may be Never; its surplus is $-A_\theta$.

### Joint-law mass-times-surplus certificate

The preceding outcome can be selected quantitatively on a supplied literal
law coordinate.  Suppose

\[
(z_*,\mu)=((U,B),\mu)
\]

belongs to the joint terminal-semantic/law carrier and that its law coordinate
has reward moment $U$.  Put

\[
c_\theta=T_\theta-M_\theta>0,
\qquad
K=|\Omega|,
\]

where \(\Omega\) consists of Never and all nonempty coalitions.  Then some
literal outcome satisfies

\[
\boxed{
\mu(\omega)\,
\theta\mathbin\cdot(\overline r(\omega)-s)
\geq\frac{c_\theta D_*}{K}.}                              \tag{6a}
\]

The product is positive, so this one outcome simultaneously has positive
mass in the retained limiting law and positive weighted singleton surplus.

Assume additionally that every reward coordinate has absolute value at most
$R>0$.  If

\[
A_\theta=\theta\mathbin\cdot s\geq0,
\]

then Never has nonpositive surplus and the selected outcome is a finite
coalition.  Since

\[
\theta\mathbin\cdot(\overline r(\omega)-s)
\leq2RT_\theta,
\]

the same outcome satisfies the separate floors

\[
\boxed{
\theta\mathbin\cdot(\overline r(\omega)-s)
\geq\frac{c_\theta D_*}{K},
\qquad
\mu(\omega)
\geq\frac{c_\theta D_*}{2KRT_\theta}.}                   \tag{6b}
\]

For Fin4, $K=16$.  With the normalization $T_\theta=1$, the floors in
(6b) become $c_\theta D_*/16$ and $c_\theta D_*/(32R)$.

Unlike an arbitrary Carathéodory reweighting, this conclusion retains the
displayed joint-carrier law exactly.  It does not say that \(\mu\) itself is
the terminal law of one profile; joint-carrier membership gives a limiting
law along an actual realizing subsequence.

## Proof

The checked theorem `minimumTerminalSemantic_singletonMargin` states that at
a positive ordinary global minimum,

\[
D_*\leq B_i-s_i                                             \tag{7}
\]

for every player $i$.  Multiply (7) by \(\theta_i\geq0\) and sum:

\[
T_\theta D_*
\leq \sum_i\theta_i(B_i-s_i).
\]

Since $B_i=U_i+d_i$,

\[
\sum_i\theta_i(B_i-s_i)
=\theta\mathbin\cdot(U-s)+\sum_i\theta_i d_i.
\]

All debts are nonnegative and \(\theta_i\leq M_\theta\), so

\[
\sum_i\theta_i d_i
\leq M_\theta\sum_i d_i
=M_\theta D_*.
\]

Subtracting gives

\[
(T_\theta-M_\theta)D_*
\leq\theta\mathbin\cdot(U-s),                             \tag{8}
\]

which is the left side of (1).

Carrier reward-moment membership supplies a probability mass \(\mu\) on
Never and the finitely many nonempty coalitions such that

\[
U=\sum_\omega\mu(\omega)\overline r(\omega).
\]

Every weighted outcome reward is bounded above by $R_\theta$, so

\[
\theta\mathbin\cdot U\leq R_\theta.
\]

This proves (1).  If every positive-mass outcome had weighted surplus
strictly below the left side of (6), averaging would contradict (8).  Hence
one positive-mass outcome satisfies (6).

For the joint-law form, define

\[
a_\omega=
\mu(\omega)\,
\theta\mathbin\cdot(\overline r(\omega)-s).
\]

The reward-moment identity and (8) give

\[
\sum_{\omega\in\Omega}a_\omega
=\theta\mathbin\cdot(U-s)
\geq c_\theta D_*.
\]

There are $K$ summands, so one is at least $c_\theta D_*/K$, proving
(6a).  For a finite coalition, the reward bound and \(\theta\geq0\) give

\[
\theta\mathbin\cdot(\overline r(\omega)-s)
\leq
\sum_i\theta_i
  |\overline r_i(\omega)-s_i|
\leq2RT_\theta.
\]

The positive product in (6a), together with \(\mu(\omega)\leq1\), gives the
surplus floor in (6b); division by $2RT_\theta>0$ gives the mass floor.
If $A_\theta\geq0$, the Never surplus is $-A_\theta\leq0$, so it cannot
be the selected positive-product outcome.

If two coordinates are positive, deleting the largest one from their sum
still leaves a positive summand, proving (2).  Equations (3)--(4) follow.
Under (C), (1) is incompatible with $D_*>0$.  Thus $D_*=0$, and
`exists_uniformEquilibriumPayoff_of_hasZeroMinimumTerminalSemanticDebt`
applies.

No behavioral profile attaining $z_*$ is used.  The minimum and its reward
moment may exist only in the closed carrier.

## Unification of the checked subset chambers

The coefficient $T_\theta-M_\theta$ contains the checked indicator cases.

If \(\theta_i=1\) for every player, then

\[
T_\theta-M_\theta=|I|-1,
\]

which is the all-player aggregate-surplus inequality.

If $J\subseteq I$, $|J|\geq2$, and

\[
\theta=\mathbf1_J,
\]

then

\[
T_\theta-M_\theta=|J|-1,
\]

and (1), (6) are exactly the coarse checked subset inequalities in
`TerminalSemanticMinimumAggregateSurplus.lean`.

This proof does not insert zero coordinates into
`minimumTerminalSemantic_weightedSingletonMargin`, whose hypotheses require
a strictly positive costate and whose objective is a weighted debt minimum.
It instead combines the checked unweighted singleton margin at the ordinary
global minimum with a nonnegative costate.  The two results should therefore
remain distinct:

* the weighted-minimum theorem bounds the minimum of
  \(\sum_i\theta_i d_i\) by a coefficient $n-1$;
* the theorem here bounds the ordinary total-debt minimum $D_*$ by the
  coefficient $T_\theta-M_\theta$, and permits zero weights.

They yield the same sign-chamber closure when \(\theta\) is strictly
positive, but they are not the same quantitative assertion.

## Exact supportwise finite-dimensional alternative

The zero-allowing costate class is a finite union of fixed-support classes.
It therefore should not be assigned the single cone alternative for an
everywhere strictly positive costate without keeping track of the support.

Fix $J\subseteq I$, $|J|\geq2$, and restrict vectors to their $J$
coordinates.  Define

\[
C_J=\operatorname{cone}\left(
\{-s|_J\}\cup
\{(r(S)-s)|_J:S\ne\varnothing\}
\right)
\subseteq\mathbb R^J,
\]

and let $P_J=\mathbb R^J_{\geq0}$.  Exactly one of the following holds:

1. there is a vector \(\theta_J\in\mathbb R^J_{>0}\) such that

   \[
   \theta_J\mathbin\cdot s|_J\geq0,
   \qquad
   \theta_J\mathbin\cdot(r(S)-s)|_J\leq0
   \quad(S\ne\varnothing);                               \tag{9}
   \]

2. $C_J\cap(P_J\setminus\{0\})\ne\varnothing$.

This is the same strict separation argument as the everywhere-positive
costate alternative, now applied in \(\mathbb R^J\).  Explicitly, if arm 2
fails, the finitely generated and therefore closed cone $C_J$ is disjoint
from the compact simplex

\[
\Delta_J=\{p\in P_J:\sum_{i\in J}p_i=1\}.
\]

Strong separation gives a functional nonpositive on $C_J$ and strictly
positive on \(\Delta_J\).  Conicity forces the first bound to be zero, and
testing the vertices of \(\Delta_J\) makes every coordinate of the functional
strictly positive, giving arm 1.  Conversely, an arm-1 functional is positive
on every nonzero vector of $P_J$ and nonpositive on $C_J$, so arm 2 is
impossible.

Arm 2 has an equivalent probabilistic-looking but purely algebraic form:
there is a probability law
\(\nu_J\) on Never and the nonempty coalitions such that

\[
\mathbb E_{\nu_J}[\overline r_i]\geq s_i
\quad(i\in J),                                            \tag{10}
\]

with strict inequality for at least one coordinate in $J$.

To see this, write a nonzero vector in arm 2 as

\[
v=-\lambda_0s|_J+
\sum_{S\ne\varnothing}\lambda_S(r(S)-s)|_J
\in P_J\setminus\{0\},                                  \tag{11}
\]

where all coefficients are nonnegative.  Normalize by

\[
L=\lambda_0+\sum_S\lambda_S>0.
\]

Putting mass \(\lambda_0/L\) on Never and \(\lambda_S/L\) on $S$ gives

\[
v/L=
\mathbb E_{\nu_J}[\overline r|_J]-s|_J.
\]

Conversely every law satisfying (10) gives (11).  Conic Carathéodory in
\(\mathbb R^J\) allows the law to be chosen with support of cardinality at
most $|J|$.

Consequently, failure of every nonnegative costate certificate with at least
two positive coordinates is equivalent to the following finite family of
obstructions:

> For every $J\subseteq I$ with $|J|\geq2$, there is a law supported on at
> most $|J|$ terminal outcomes whose expected payoff weakly dominates
> $(s_i)_{i\in J}$ on $J$, and strictly dominates it in at least one
> $J$-coordinate.

In Fin4, every player pair therefore has a two-outcome law with this Pareto
property if all social costate chambers fail.

These laws are conic separation certificates.  They are not asserted to be
terminal laws of behavioral profiles.  In particular, a mixture of two
nonsingleton coalitions can require correlation that the quitting game's
independent current actions do not supply.  No Nash, chronology, or
uniform-equilibrium construction follows from (10) alone.

The Gordan alternative for the everywhere strictly positive chamber is the
case $J=I$ of this table-level feasibility statement.  That alternative is
only a dual of the finite reward-table inequalities.  It may be paired with
the weighted-minimum theorem, but it does not mention or dualize a debt
objective.  The weighted-minimum theorem and the ordinary-global-minimum
inequality proved here remain different pieces of mathematics.

## Exact Fin4 separation from every subset indicator

Let $I=\{1,2,3,4\}$ and take

\[
\theta=(1,2,3,4).
\]

Put

\[
s=(1,-1/2,0,0),
\]

so \(\theta\mathbin\cdot s=0\), and give every singleton coalition the
reward vector \(s\).  This is consistent with
\(s_i=r_i(\{i\})\).  For each nonsingleton coalition $S$, let
\(\ell(S)\) and $h(S)$ be respectively the members of $S$ having least and
greatest \(\theta\)-weight.  Define \(x(S)\) by

\[
x_{\ell(S)}(S)=\theta_{h(S)},
\qquad
x_{h(S)}(S)=-\theta_{\ell(S)},
\qquad
x_k(S)=0
\quad(k\notin\{\ell(S),h(S)\}).                          \tag{12}
\]

Set \(r(S)=s+x(S)\) on nonsingleton coalitions.  Then for every terminal
coalition,

\[
\theta\mathbin\cdot r(S)=0.
\]

Thus $A_\theta=R_\theta=0$, and the nonnegative-weight chamber proves
$D_*=0$ and a uniform-equilibrium payoff.

On the other hand, take any player subset $J$ with $|J|\geq2$, and use
the terminal coalition $S=J$.  Its $J$-social reward is

\[
\sum_{i\in J}r_i(J)
=\sum_{i\in J}s_i+
  \theta_{h(J)}-\theta_{\ell(J)}
>\sum_{i\in J}s_i.                                       \tag{13}
\]

Therefore the unweighted subset chamber fails for every eligible $J$.
The example separates the arbitrary-costate theorem from the complete family
of subset-indicator tests, not merely from the all-player equal-weight test.
It also has mixed, nonzero own-singleton rewards, so its closure is not the
zero-solo disjunct.

It is an existence example, not a counterexample candidate: the theorem
itself proves that its minimum debt is zero.

## Boundaries

1. If \(\theta\) has only one positive coordinate, then
   $T_\theta-M_\theta=0$, so the argument supplies no positive debt cost.
2. Never must be included in $R_\theta$ and in the common-outcome law.
3. The selected reward-moment law need not be executable by one behavioral
   profile.
4. The theorem is a special-case existence chamber, not a proof for an
   arbitrary reward table.
5. The common-outcome inequality is a finite reward-table obstruction.  It
   does not locate a reached chronological row carrying that outcome.

## Named checked inputs inspected

- `minimumTerminalSemantic_singletonMargin`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`);
- `quittingTerminalSemanticCarrier_prescribed_mem_rewardMomentSet`,
  `quittingTerminalOutcomeReward`, and `quittingTerminalRewardMoment`
  (`UniformEquilibrium/Quitting/Root/TerminalSemanticMoment.lean`);
- `exists_terminalSemanticLawCarrier_lift` and
  `terminalSemanticLawCarrier_rewardMoment`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`);
- `quittingTerminalSemanticDebt_nonneg_of_mem_carrier` and
  `exists_minimum_quittingTerminalSemanticDebtSum`
  (`UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`);
- `exists_uniformEquilibriumPayoff_of_hasZeroMinimumTerminalSemanticDebt`
  (`UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean`);
- `minimumTerminalSemantic_subset_singletonSurplus` and
  `exists_terminalOutcome_subset_singletonSurplus_ge_minimumDebt`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumAggregateSurplus.lean`);
- `minimumTerminalSemantic_weightedSingletonMargin`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticWeightedAuxiliaryNashBudget.lean`).

## Status boundary

Proved here as ordinary mathematics:

- the nonnegative-costate global-minimum inequality (1);
- the quantitative and zero-debt consequences (3)--(5);
- the positive-support common-outcome certificate (6);
- the source-attached joint-law mass-times-surplus certificate (6a)--(6b);
- the exact fixed-support cone/law alternative (9)--(11), including the
  Carathéodory support bound; and
- the Fin4 strict-separation example (12)--(13).

Not proved or claimed:

- a new Lean declaration packaging these consequences;
- executability of the dual laws;
- attainment of the minimum pair by one behavioral profile; or
- uniform-equilibrium existence outside the displayed finite reward-table
  chamber.
