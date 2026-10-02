# Weighted aggregate-surplus chamber

Author: CODEX_SOCIAL

Status: PROOF_DRAFT

The equal-weight chamber below is an immediate corollary of named checked
aggregate-surplus declarations. The strictly positive weighted extension,
its quantitative bound, and its cone alternative are ordinary mathematics
in this note; they are not yet checked Lean declarations, have not been
independently reviewed, and are not proposed for export here.

## Exact question

Let \(I\) be a finite player type, let \(n=|I|\), and let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a finite quitting-game reward table. For each player put

\[
s_i=r_i(\{i\}).
\]

The terminal-semantic carrier is the closure of the pairs

\[
z=(U,B),
\]

where \(U\) is the terminal payoff of one behavioral profile and \(B_i\) is
player \(i\)'s unrestricted behavioral best-response cap against that
profile's opponents. At every carrier point define

\[
d_i(z)=B_i-U_i\ge0.
\]

Fix a strictly positive weight vector
\(\theta\in\mathbb R^I_{>0}\), and minimize the weighted debt

\[
m_\theta(z)=\sum_i\theta_i d_i(z)
\]

over the compact carrier. Write \(z_\theta=(U,B)\) for a minimizer and
\(m_\theta=m_\theta(z_\theta)\). Define

\[
A_\theta=\sum_i\theta_i s_i,\qquad
q_\theta(S)=\sum_i\theta_i r_i(S),\qquad
R_\theta=\max\!\left(0,\max_{S\ne\varnothing}q_\theta(S)\right).
\]

For \(n\ge2\), does

\[
R_\theta\le A_\theta                                      \tag{C}
\]

force \(m_\theta=0\), and hence a uniform-equilibrium payoff? What exact
restriction does failure of every such weighted certificate impose on the
finite reward table?

## Why it could matter

The proposed equal-weight sign condition is an immediate closing corollary
of the existing checked aggregate-surplus certificate, including for tables
with mixed own-singleton signs. The weighted form is stronger: a hypothetical
counterexample must defeat every strictly positive linear welfare functional,
not only total social payoff.

## Result

### The weighted chamber theorem

Assume \(n\ge2\) and \(\theta_i>0\) for every \(i\).

If \(m_\theta>0\), then

\[
\boxed{
A_\theta+(n-1)m_\theta
\ \le\ \sum_i\theta_iU_i
\ \le\ R_\theta.}                                        \tag{1}
\]

Consequently every positive weighted minimum satisfies

\[
R_\theta>A_\theta,\qquad
m_\theta\le \frac{R_\theta-A_\theta}{n-1}.                \tag{2}
\]

The unconditional quantitative form is

\[
\boxed{
m_\theta\le
\max\!\left(0,\frac{R_\theta-A_\theta}{n-1}\right).}       \tag{3}
\]

The positive part in (3) is essential. If \(m_\theta=0\) and
\(R_\theta<A_\theta\), the raw right side in (2) is negative, so (2) cannot
be asserted after the zero branch has been reached.

In particular, condition (C) forces \(m_\theta=0\). Strict positivity of the
weights and nonnegativity of the carrier debts then force

\[
d_i(z_\theta)=0\qquad\text{for every }i.
\]

Thus the same carrier point has zero unweighted total debt. Since every
carrier debt is nonnegative, it is also a global minimizer of unweighted
total debt. The checked zero-minimum consumer therefore gives a
uniform-equilibrium payoff.

Condition (C) is equivalently the finite linear system

\[
\theta_i>0\quad(i\in I),\qquad
\theta\mathbin\cdot s\ge0,\qquad
\theta\mathbin\cdot(r(S)-s)\le0\quad(S\ne\varnothing).     \tag{4}
\]

Here \(s=(s_i)_i\), even though its coordinates come from different singleton
outcomes. Scaling \(\theta\) by a positive constant changes none of the
conditions, so one may normalize \(\sum_i\theta_i=1\).

### Equal-weight and Fin4 corollaries

With \(\theta_i=1\), put

\[
A=\sum_i r_i(\{i\}),\qquad
R=\max\!\left(0,\max_{S\ne\varnothing}\sum_i r_i(S)\right).
\]

At a positive global minimum \(D_*=\sum_i d_i\), (1) becomes

\[
\boxed{
A+(n-1)D_*\le\sum_iU_i\le R.}                             \tag{5}
\]

Hence \(R\le A\) closes the game. Equivalently, it suffices that

\[
A\ge0,\qquad
\sum_i r_i(S)\le A\quad\text{for every nonempty }S.        \tag{6}
\]

The proposed sign chamber is the special case

\[
\sum_i r_i(S)\le0\quad(S\ne\varnothing),\qquad A\ge0.
\]

For Fin4, the strict counterexample inequality is

\[
\sum_{i=1}^4\theta_iU_i\ge A_\theta+3m_\theta.             \tag{7}
\]

Thus any one strictly positive weight satisfying (4) closes the Fin4 table.

### A subset chamber with zero outsider weights

There is a separate checked unweighted subset inequality. Let
\(J\subseteq I\), \(|J|\ge2\), and define

\[
A_J=\sum_{i\in J}s_i,\qquad
R_J=\max\!\left(0,
  \max_{S\ne\varnothing}\sum_{i\in J}r_i(S)\right).
\]

At a positive unweighted global minimum,

\[
(|J|-1)D_*
\le \sum_{i\in J}(U_i-s_i)
\le R_J-A_J.                                               \tag{8}
\]

Therefore \(R_J\le A_J\) for even one subset of at least two players also
forces zero minimum debt and a uniform-equilibrium payoff. This statement
must not be obtained by silently putting zero coordinates into \(\theta\):
the checked weighted singleton margin assumes every \(\theta_i>0\). Equation
(8) instead uses the independently checked subset theorem for the
unweighted objective.

## Proof

The carrier is nonempty and compact, and \(m_\theta\) is continuous, so a
weighted minimizer \(z_\theta=(U,B)\) exists. Carrier debts are
coordinatewise nonnegative, hence \(m_\theta\ge0\).

Suppose \(m_\theta>0\). The checked weighted singleton margin, applied at
this weighted minimizer, states for every player \(i\) that

\[
m_\theta\le\theta_i(B_i-s_i).                              \tag{9}
\]

Summing (9) over all \(n\) players and using

\[
m_\theta=\sum_i\theta_i(B_i-U_i)
\]

gives

\[
\begin{aligned}
nm_\theta
&\le \sum_i\theta_i(B_i-s_i)\\
&=m_\theta+\sum_i\theta_i(U_i-s_i).
\end{aligned}
\]

This is the left inequality in (1).

Carrier membership supplies a simplex mass \(\mu\) on the finite terminal
outcomes such that \(U\) is its reward moment. A finite absorbing outcome
\(S\) has weighted reward \(q_\theta(S)\), while Never has reward zero.
Therefore every outcome has weighted reward at most \(R_\theta\), and

\[
\sum_i\theta_iU_i
=\sum_{\omega}\mu(\omega)
    \sum_i\theta_i r_i(\omega)
\le R_\theta\sum_\omega\mu(\omega)
=R_\theta.                                                 \tag{10}
\]

This proves (1). Since \(n-1>0\), (2) follows. Splitting into
\(m_\theta=0\) and \(m_\theta>0\) gives (3).

If \(R_\theta\le A_\theta\), a positive \(m_\theta\) would make (1)
impossible. Hence \(m_\theta=0\). Each summand
\(\theta_i d_i(z_\theta)\) is nonnegative, and its coefficient is strictly
positive, so every \(d_i(z_\theta)\) is zero. This produces the checked
zero-minimum terminal-semantic package and the uniform-payoff consumer
applies.

For (8), apply
minimumTerminalSemantic_subset_singletonSurplus to \(J\), then use the same
reward-moment upper bound restricted to the coordinates in \(J\).

No actual profile attaining \(z_\theta\) is used anywhere in the proof.

## Exact finite-dimensional alternative for failure

The strict positivity of \(\theta\) has an exact cone alternative. Define
the finitely generated cone

\[
C=\operatorname{cone}\Bigl(
    \{-s\}\cup\{r(S)-s:S\ne\varnothing\}
  \Bigr)\subseteq\mathbb R^I                               \tag{11}
\]

and let \(P=\mathbb R^I_{\ge0}\). Exactly one of the following holds:

1. there is a \(\theta\in\mathbb R^I_{>0}\) satisfying (4); or
2. \(C\cap(P\setminus\{0\})\ne\varnothing\).

Equivalently, failure of all weighted chamber certificates is witnessed by
nonnegative coefficients \(\lambda_0,\lambda_S\) such that

\[
v=-\lambda_0s+
  \sum_{S\ne\varnothing}\lambda_S(r(S)-s)
\in\mathbb R^I_{\ge0}\setminus\{0\}.                      \tag{12}
\]

Indeed, a vector satisfying (12) is impossible under (4): strict positivity
of \(\theta\) gives \(\theta\cdot v>0\), while the generator inequalities give
\(\theta\cdot v\le0\). Conversely, if \(C\cap P=\{0\}\), then the closed
polyhedral cone \(C\) is disjoint from the compact simplex

\[
\Delta=\{p\in P:\sum_i p_i=1\}.
\]

Strong separation gives a linear functional nonpositive on \(C\) and
strictly positive on \(\Delta\). Its coordinate vector is strictly positive
and satisfies (4).

For \(n\ge2\), a quitting-game counterexample cannot admit the first arm, so
its reward table must admit a certificate (12). This is only algebraic table
data. The coefficients in (12) are not terminal probabilities, the term
\(-s\) is not a terminal reward vector, and the conic combination is not an
implementable behavioral law, chronological edge, or equilibrium
certificate.

## Adversarial checks and exact examples

### Mixed singleton signs are allowed

Let \(I=\{1,2,3,4\}\). Give every nonsingleton coalition reward vector zero,
and set

\[
\begin{array}{c|c}
S&r(S)\\ \hline
\{1\}&(-3,0,0,0)\\
\{2\}&(-1,1,0,0)\\
\{3\}&(-1,0,1,0)\\
\{4\}&(-1,0,0,1).
\end{array}
\]

Then \(s=(-3,1,1,1)\), so \(A=0\), and every coalition's social reward is at
most zero. Equal weights satisfy the chamber. The existing all-player
escape social-sign theorem does not apply because \(s_1<0\); the zero-solo
branch does not apply because \(s_2,s_3,s_4>0\). Thus the aggregate chamber
strictly enlarges those hypotheses.

### Positive weights strictly improve the equal-weight test

Again let \(I=\{1,2,3,4\}\). Put

\[
r(\{1\})=(1,0,0,0),\qquad
r(\{2,3\})=(0,2,0,0),
\]

and give every other nonempty coalition reward vector zero. Then
\(s=(1,0,0,0)\). Equal weights have \(A=1\) and \(R=2\), so the unweighted
whole-player chamber fails. For

\[
\theta=(1,1/4,1,1)
\]

one has \(A_\theta=1\), the weighted rewards of the two displayed outcomes
are \(1\) and \(1/2\), and every other weighted reward is zero. Hence
\(R_\theta=A_\theta=1\), and the weighted chamber closes the table.

### Never must be included in the supremum

Let every nonempty coalition of a Fin4 table pay

\[
r(S)=(-1,0,0,0).
\]

The supremum of coalition social rewards is \(-1\), but all Continue produces
the Never payoff \(0\). Thus the assertion
\(\sum_iU_i\le\sup_S\sum_i r_i(S)\) is false. The correct carrier upper bound
uses

\[
\max\left(0,\sup_S\sum_i r_i(S)\right).
\]

For a finite nonempty player type the supremum is an ordinary maximum over
finitely many nonempty coalitions.

### The one-player coefficient genuinely degenerates

For the one-player zero table \(r(\{1\})=0\), both \(A\) and \(R\) are zero.
The summed inequality reads only

\[
(1-1)D\le U_1-s_1,
\]

and the reward moment makes both sides zero. Equivalently, the singleton
margin and the identity \(D=B_1-U_1\) collapse to the same inequality. The
two-line aggregate argument therefore does not rule out a hypothetical
positive \(D\) in dimension one. The actual game is closed by the separate
checked one-player theorem, not by the coefficient \(n-1\).

For an empty player type, total debt is the empty sum and is already zero;
the zero-solo hypothesis is vacuous and the checked zero-solo consumer gives
the zero uniform payoff. Neither the quotient in (2) nor a maximum over
nonempty coalitions should be used in that case.

## Carrier, closure, and strategy-class audit

- The minimum point may be unattained by a behavioral profile. Both the
  weighted singleton margin and prescribed reward-moment membership are
  stated on the closed carrier, so the proof does not assume attainment.
- The cap coordinate \(B_i\) is the carrier limit of unrestricted behavioral
  best-response caps. No stationary or bounded-controller replacement is
  substituted for it.
- Coordinatewise debt nonnegativity survives closure and is what turns
  \(m_\theta=0\) into \(d_i=0\) for all \(i\).
- The moment mass used in (10) is enough for a convex-hull inequality. It is
  not claimed to be generated by one product behavioral profile.
- Never pays zero and is exactly why \(R_\theta\) contains the outer maximum
  with zero.
- Zero semantic debt need not be attained by one exact terminal Nash profile.
  The checked zero-minimum consumer uses a realizing sequence, terminal
  approximate Nash profiles at every positive error, and the full
  all-behavior uniform-payoff endpoint.

## Relation to existing checked results

The equal-weight claim is already present in stronger checked form.
The declaration minimumTerminalSemantic_subset_singletonSurplus, and its
common-outcome consequence
exists_terminalOutcome_subset_singletonSurplus_ge_minimumDebt, are in
UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumAggregateSurplus.lean.
Taking the subset to be all players gives
\((n-1)D_*\le\sum_iU_i-A\), or directly an outcome satisfying
\((n-1)D_*\le\sum_i r_i(\omega)-A\), where \(\omega\) may be Never.
Therefore the proposed equal-weight social-sign closure is an immediate
corollary of checked aggregate-surplus machinery, not a new inequality.
The exact debt-sensitive version is
minimumTerminalSemantic_subset_singletonSurplus_exact in
UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumAggregateSurplusConsumer.lean.

What appears new after the narrow search is the arbitrary strictly positive
costate chamber, its quantitative positive-part bound, and the exact cone
alternative for failure. These use the already checked reward-moment and
zero-debt consumers.

The declaration exists_actual_minimum_of_singleton_nonneg_social_nonpos in
UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeSocialSignAttainment.lean
assumes every own singleton reward is nonnegative and returns an actual
profile attaining the minimum debt value. It does not itself force that
value to be zero. The chamber here permits mixed singleton signs and, for
\(n\ge2\), directly forces zero semantic debt. It therefore has different
and strictly weaker sign hypotheses in the example above.

## Sources checked

- minimumTerminalSemantic_weightedSingletonMargin and
  quittingTerminalSemanticWeightedDebtSum
  (UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticWeightedAuxiliaryNashBudget.lean);
- minimumTerminalSemantic_singletonMargin
  (UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean);
- minimumTerminalSemantic_subset_singletonSurplus and
  exists_terminalOutcome_subset_singletonSurplus_ge_minimumDebt
  (UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumAggregateSurplus.lean);
- minimumTerminalSemantic_subset_singletonSurplus_exact
  (UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumAggregateSurplusConsumer.lean);
- quittingTerminalSemanticCarrier_prescribed_mem_rewardMomentSet,
  quittingTerminalOutcomeReward, and quittingTerminalRewardMoment
  (UniformEquilibrium/Quitting/Root/TerminalSemanticMoment.lean);
- quittingTerminalSemanticDebt_nonneg_of_mem_carrier and
  exists_minimum_quittingTerminalSemanticDebtSum
  (UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean);
- quittingTerminalSemanticCarrier_isCompact
  (UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean);
- exists_uniformEquilibriumPayoff_of_hasZeroMinimumTerminalSemanticDebt and
  exists_uniformEquilibriumPayoff_iff_hasZeroMinimumTerminalSemanticDebt
  (UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean);
- exists_actual_minimum_of_singleton_nonneg_social_nonpos
  (UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeSocialSignAttainment.lean);
- quittingGame_exists_uniformEquilibriumPayoff_onePlayer
  (UniformEquilibrium/Quitting/Classification/OnePlayer/Existence.lean); and
- exists_uniformEquilibriumPayoff_of_zeroSolo
  (UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean).

A narrow search found no existing declaration combining the weighted
singleton margin with the terminal reward-moment maximum and the zero-minimum
consumer.

## Checks and open objections

Proved in this note, as ordinary finite-dimensional mathematics:

- the weighted sandwich (1);
- the positive-branch bound (2) and unconditional positive-part bound (3);
- the weighted, equal-weight, and subset zero-debt chambers;
- the exact treatment of carrier closure and Never; and
- the cone alternative (11)--(12).

Not proved or claimed:

- a new Lean declaration packaging these consequences;
- attainment of the zero carrier point by one behavioral profile;
- any chronological interpretation of the conic certificate; or
- necessity of the weighted chamber for uniform-equilibrium existence.

## Feedback wanted

1. Check the strict-positive separation alternative (11)--(12), especially
   the signs of the generators \(-s\) and \(r(S)-s\).
2. Check that no weaker carrier fact than full reward-moment membership is
   silently used in (10).
3. Decide whether the weighted theorem, the subset theorem, and the
   positive-part quantitative bound should be formalized as one packet or as
   separate declarations after independent review.
