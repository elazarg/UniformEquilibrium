# Social-costate slack decomposes into law, margin, and debt-face slack

Identity: CODEX_ROOT

Status: ordinary mathematics proved below. This is a structural sharpening of
the nonnegative-weight social chamber, not a new terminal consumer.

## Question

Let \(z_*=(U,B)\) be a positive ordinary global minimum of terminal-semantic
total debt in a finite quitting game. Put

\[
s_i=r_i(\{i\}),\qquad
d_i=B_i-U_i,\qquad
D_*=\sum_i d_i>0.
\]

For \(\theta\ge0\) with at least two positive coordinates, define

\[
T=\sum_i\theta_i,\qquad
M=\max_i\theta_i,\qquad
A=\theta\cdot s,
\]

and

\[
R_\theta=\max\left(0,\max_{S\ne\varnothing}\theta\cdot r(S)\right).
\]

The social chamber proves

\[
A+(T-M)D_*\le R_\theta.
\]

What exact information is contained in the slack of this inequality?

## Exact slack identity

Define the coordinate singleton-margin slack

\[
m_i=B_i-s_i-D_*\ge0
\]

and the reward-moment slack

\[
e_\theta=R_\theta-\theta\cdot U\ge0.
\]

Then

\[
\boxed{
R_\theta-A-(T-M)D_*
=e_\theta
+\sum_i\theta_i m_i
+\sum_i(M-\theta_i)d_i.}
\tag{1}
\]

All three terms on the right are nonnegative.

### Proof

The checked singleton margin at a positive ordinary minimum gives \(m_i\ge0\).
Reward-moment membership gives \(e_\theta\ge0\). Moreover,

\[
\begin{aligned}
\sum_i\theta_i m_i
&=\theta\cdot(B-s)-TD_*\\
&=\theta\cdot(U-s)+\sum_i\theta_i d_i-TD_*.
\end{aligned}
\]

Adding

\[
\sum_i(M-\theta_i)d_i
=MD_*-\sum_i\theta_i d_i
\]

gives

\[
\sum_i\theta_i m_i+\sum_i(M-\theta_i)d_i
=\theta\cdot(U-s)-(T-M)D_*.
\]

Adding \(e_\theta=R_\theta-\theta\cdot U\) proves (1).

## Equality classification

Equality in the social bound holds if and only if all of the following hold.

1. The prescribed reward moment is weighted-maximal:

   \[
   \theta\cdot U=R_\theta.
   \]

2. Every positively weighted coordinate is singleton-margin tight:

   \[
   \theta_i>0
   \quad\Longrightarrow\quad
   B_i-s_i=D_*.
   \]

3. Every positive-debt coordinate has maximum weight:

   \[
   d_i>0
   \quad\Longrightarrow\quad
   \theta_i=M.
   \]

For a supplied joint-carrier lift \((z_*,\mu)\), condition 1 is equivalent to

\[
\mu\bigl(\{\omega:\theta\cdot\bar r(\omega)=R_\theta\}\bigr)=1.
\tag{2}
\]

Indeed,

\[
e_\theta
=\sum_\omega\mu(\omega)
  \bigl(R_\theta-\theta\cdot\bar r(\omega)\bigr),
\]

and every summand is nonnegative.

Thus sharpness aligns three faces at once: a face of the reward-moment
polytope, the singleton-margin face, and the maximum-weight face of the debt
simplex.

## Quantitative concentration

Let

\[
\varepsilon_\theta=
R_\theta-A-(T-M)D_*\ge0.
\]

Equation (1) gives the following bounds.

For every \(\delta>0\),

\[
\sum_{\{i:M-\theta_i\ge\delta\}}d_i
\le\frac{\varepsilon_\theta}{\delta}.
\tag{3}
\]

For a joint-carrier law \(\mu\),

\[
\mu\bigl(
 \{\omega:R_\theta-\theta\cdot\bar r(\omega)\ge\delta\}
\bigr)
\le\frac{\varepsilon_\theta}{\delta}.
\tag{4}
\]

For every coordinate with \(\theta_i>0\),

\[
0\le B_i-s_i-D_*
\le\frac{\varepsilon_\theta}{\theta_i}.
\tag{5}
\]

These are immediate because each selected nonnegative contribution is bounded
by the total slack.

## Fin4 chamber consequences

At a full-debt minimum, \(d_i>0\) for all four players. Equality in the social
bound therefore forces

\[
\theta_0=\theta_1=\theta_2=\theta_3=M.
\tag{6}
\]

Hence every genuinely nonuniform costate has strict social slack in the
full-debt chamber. Quantitatively,

\[
\varepsilon_\theta
\ge\sum_i(M-\theta_i)d_i.
\tag{7}
\]

At a reset-rigid minimum with zero set

\[
Z=\{i:d_i=0\},
\]

equality forces every player outside \(Z\) to have maximum weight. Only the
zero-debt coordinates may carry lower weights. Thus a sharp costate identifies
a debt face without using chronology.

These conclusions are exact but do not orient a reset or construct a return.
When the social upper bound has substantial slack, (1) supplies no small
parameter. When it is nearly sharp, (3)--(5) provide a finite-dimensional
concentration packet that may be compared with the full-debt and reset-rigid
chamber consumers.

## Boundary and nonclaims

- The identity requires \(D_*>0\), because the checked singleton margin used
  to define \(m_i\ge0\) has that hypothesis.
- It does not prove that any useful costate is sharp or nearly sharp.
- Reward-law concentration is a statement about a limiting joint-carrier law,
  not a reached chronological row.
- Debt-face concentration does not preserve caps under a strategy
  replacement.
- No terminal approximate equilibrium, return, or renewable rank is claimed.

## Sources inspected

- minimumTerminalSemantic_singletonMargin in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean;
- quittingTerminalSemanticCarrier_prescribed_mem_rewardMomentSet in
  UniformEquilibrium/Quitting/Root/TerminalSemanticMoment.lean;
- exists_terminalSemanticLawCarrier_lift and
  terminalSemanticLawCarrier_rewardMoment in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean;
- minimumTerminalSemantic_subset_singletonSurplus in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumAggregateSurplus.lean;
  and
- formalized/NONNEGATIVE_WEIGHT_SOCIAL_CHAMBER_AND_SPARSE_REWARD_BOUNDARY.md.
