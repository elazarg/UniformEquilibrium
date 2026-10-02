# Independent review: nonnegative-weight social chamber

Reviewer: `CODEX_DESCENDANT`

Date: 2026-08-31

Verdict: **PASS.**

I found no mathematical or strategy-class defect in the current note.  This
review covers the current version, including the joint-law mass-times-surplus
certificate (6a)--(6b) and the mixed, nonzero-singleton Fin4 example.  I found
no export-blocking issue.

## Claim reviewed

At a positive ordinary global minimum \(z_*=(U,B)\) of total terminal
semantic debt, put

\[
d_i=B_i-U_i,
\qquad
D_*=\sum_i d_i>0.
\]

For a nonnegative vector \(\theta\) with at least two positive coordinates,
write

\[
T=\sum_i\theta_i,
\qquad
M=\max_i\theta_i,
\qquad
A=\theta\mathbin\cdot s,
\]

and

\[
R_\theta=\max\left(0,\max_{S\ne\varnothing}
  \theta\mathbin\cdot r(S)\right).
\]

The note proves

\[
A+(T-M)D_*
\leq\theta\mathbin\cdot U
\leq R_\theta.                                            \tag{1}
\]

It then derives a finite reward-table chamber implying \(D_*=0\), a
positive-support outcome certificate, a quantitative version on a supplied
joint-carrier law, a supportwise cone alternative, and a Fin4 example not
detected by any subset-indicator chamber.

## 1. Weighted ordinary-minimum inequality

The checked singleton margin at a positive ordinary global minimum is

\[
D_*\leq B_i-s_i
\quad\text{for every }i.                                  \tag{2}
\]

Multiplying by \(\theta_i\geq0\), summing, and using
\(B_i=U_i+d_i\) gives

\[
TD_*\leq\theta\mathbin\cdot(U-s)+\sum_i\theta_i d_i.
\]

Since \(d_i\geq0\) and \(\theta_i\leq M\),

\[
\sum_i\theta_i d_i\leq M\sum_i d_i=MD_*.
\]

This proves the left side of (1).  Reward-moment membership of \(U\), with
Never represented by the zero reward vector, proves the right side.  Because
at least two weights are positive, \(T-M>0\), so all divisions and strict
consequences in the note are valid.

In particular,

\[
\theta\mathbin\cdot s\geq0,
\qquad
\theta\mathbin\cdot(r(S)-s)\leq0
\quad(S\ne\varnothing)
\]

is incompatible with \(D_*>0\).  The cited checked zero-minimum theorem then
produces a uniform-equilibrium payoff for the unrestricted behavioral
strategy class.  The note does not silently assume that one profile attains
the carrier minimum.

## 2. Positive-support and joint-law certificates

For a reward-moment law \(\mu\), equation (1) gives

\[
\sum_\omega\mu(\omega)
  \theta\mathbin\cdot(\overline r(\omega)-s)
\geq (T-M)D_*.
\]

The positive-support outcome conclusion follows by finite averaging.

For the stronger joint-law statement, define

\[
a_\omega=
\mu(\omega)\,
\theta\mathbin\cdot(\overline r(\omega)-s).
\]

The checked joint-carrier moment identity makes

\[
\sum_{\omega\in\Omega}a_\omega
=\theta\mathbin\cdot(U-s)
\geq (T-M)D_*.
\]

With \(K=|\Omega|\), at least one literal outcome therefore satisfies

\[
a_\omega\geq\frac{(T-M)D_*}{K}.                          \tag{3}
\]

The right side is positive, so both its mass and its surplus are positive.
This establishes (6a) on the displayed joint-carrier law itself; it is not a
Caratheodory replacement law.

Under the coordinate reward bound \(|r_i(S)|\leq R\), nonnegative weights
give

\[
\theta\mathbin\cdot(\overline r(\omega)-s)\leq2RT.
\]

Since \(\mu(\omega)\leq1\), equation (3) gives the two separate floors

\[
\theta\mathbin\cdot(\overline r(\omega)-s)
\geq\frac{(T-M)D_*}{K},
\qquad
\mu(\omega)\geq\frac{(T-M)D_*}{2KRT}.
\]

If \(A=\theta\mathbin\cdot s\geq0\), Never has surplus \(-A\leq0\), so
the positive-product outcome must be a finite coalition.  For Fin4,
\(K=1+(2^4-1)=16\), and the constants stated in the note follow.  The note
also correctly warns that a joint-carrier law is a limiting law and need not
be realized by one profile.

## 3. Supportwise alternative

For fixed \(J\), the cone

\[
C_J=\operatorname{cone}\bigl(
  \{-s|_J\}\cup\{(r(S)-s)|_J:S\ne\varnothing\}
\bigr)
\]

is finitely generated and closed.  Its disjointness from the nonnegative
simplex gives a functional nonpositive on \(C_J\) and strictly positive on
every simplex vertex.  This is exactly the claimed strictly positive costate
on \(J\).  Conversely, such a costate excludes every nonzero point of
\(C_J\cap\mathbb R^J_{\geq0}\).

Normalizing a nonzero conic representation gives the stated law on Never and
nonempty coalitions.  Conic Caratheodory uses at most \(|J|\) generators;
there is no missing affine \(+1\) in this support bound.  The note correctly
labels these laws as algebraic certificates rather than executable terminal
laws.

## 4. Mixed-singleton Fin4 separation example

For

\[
\theta=(1,2,3,4),
\qquad
s=(1,-1/2,0,0),
\]

one has \(\theta\mathbin\cdot s=0\).  Giving each singleton coalition the
whole reward vector \(s\) is consistent with \(s_i=r_i(\{i\})\).  For a
nonsingleton \(S\), let \(\ell\) and \(h\) be its least- and greatest-weight
members and set

\[
x_\ell=\theta_h,
\qquad
x_h=-\theta_\ell,
\qquad
x_k=0\text{ otherwise}.
\]

Then

\[
\theta\mathbin\cdot x
=\theta_\ell\theta_h-\theta_h\theta_\ell=0,
\]

so every terminal reward has weighted value zero and the new chamber closes
the table.  For any \(J\) with \(|J|\geq2\), choosing \(S=J\) increases the
unweighted \(J\)-sum by

\[
\theta_{h(J)}-\theta_{\ell(J)}>0.
\]

Thus every eligible subset-indicator chamber fails.  The example genuinely
uses mixed, nonzero singleton rewards and separates the arbitrary
nonnegative-costate theorem from all indicator tests.

## 5. Formalization and export boundary

The following checked declarations support the semantic inputs and the
unrestricted-UE conclusion:

- `minimumTerminalSemantic_singletonMargin`;
- `quittingTerminalSemanticCarrier_prescribed_mem_rewardMomentSet`;
- `terminalSemanticLawCarrier_rewardMoment`; and
- `exists_uniformEquilibriumPayoff_of_hasZeroMinimumTerminalSemanticDebt`.

The weighted aggregation, quantitative outcome selection, supportwise cone
alternative, and explicit Fin4 example remain ordinary mathematics requiring
new Lean packaging.  This is accurately stated in the note and is not an
export blocker under the conference criteria.

I also checked the displayed-formula delimiters and equation tags in the
current file.  They are balanced and unique.

## Sources inspected

- `notes/CODEX_WEIGHT_GLOBAL__NONNEGATIVE_WEIGHT_SOCIAL_CHAMBER.md`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`;
- `UniformEquilibrium/Quitting/Root/TerminalSemanticMoment.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`; and
- `UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean`.
