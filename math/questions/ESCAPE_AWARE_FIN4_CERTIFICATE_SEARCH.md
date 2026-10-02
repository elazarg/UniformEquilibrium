# Exact certificate search or complete decision for four-player quitting games

## Game and input

Let \(I=\{0,1,2,3\}\). The input is a rational reward table
\(r(S)\in\mathbb Q^4\) for every nonempty coalition \(S\subseteq I\),
given by sixty exact rational numbers satisfying \(|r_i(S)|\le1\).

At every date, players independently choose Continue or Quit. The first
nonempty quitting coalition \(S\) ends the game and pays \(r(S)\).
Infinite all-Continue pays zero. A behavioral strategy is an arbitrary
sequence of live-date Quit probabilities, equivalently a law on
\(\mathbb N\cup\{\mathrm{Never}\}\). Each player's law is independent
of the others. A unilateral deviation may replace one complete law.

For a product law \(p\), let \(U_i^r(p)\) be its expected terminal payoff
and define

\[
B_i^r(p)=\sup_{\tau_i}U_i^r(\tau_i,p_{-i}),\qquad
E_r(p)=\max_i(B_i^r(p)-U_i^r(p)),\qquad
\eta(r)=\inf_p E_r(p).
\]

Both the infimum and every response supremum range over unrestricted
behavioral laws, including Never and laws with unbounded support on finite
dates.

The equality \(\eta(r)=0\) is equivalent to existence of a fixed uniform-
equilibrium payoff: one vector \(v\) such that, for every \(\varepsilon>0\),
some profile and horizon threshold work at every larger finite-average
horizon, with prescribed payoff within \(\varepsilon\) of \(v\) in every
coordinate and no unilateral behavioral gain exceeding \(\varepsilon\).
Here stage payoffs are zero before absorption and equal the terminal reward
from the absorption date onward.

## Question

Give either of the following.

1. A normalized rational table \(r\), a rational \(\gamma>0\), and a
   finite exact certificate, with a sound independently checkable verifier,
   proving

   \[
   E_r(p)\ge\gamma\qquad\text{for every behavioral product law }p.
   \]

2. An algorithm that terminates on every normalized rational input table
   and returns either such a positive-gap certificate or a finite exact
   certificate proving \(\eta(r)=0\). Specify the certificate language,
   verifier, and mathematical soundness in both branches. In the zero branch,
   it is enough to certify a procedure that, for every positive rational
   \(\varepsilon\), returns four rational laws on some finite menu
   \(\{0,\ldots,N-1,\mathrm{Never}\}\), with \(N\ge1\), and full error
   \(E_r(p)\le\varepsilon\). Its correctness and termination at every
   requested error must be proved. The laws and deadlines need not be nested.

A direct proof that \(\eta(r)=0\) for every input, or a counterexample
satisfying item 1, also settles the question. A finite-scale approximation
algorithm alone is not a complete decision of zero versus positive infimum.

## Sound finite-dimensional lower bounds

A lower-bound search may use sets
\(R_M(r)\subseteq\mathbb R^{d_M}\) described by finitely many rational
polynomial equalities and inequalities, together with an objective
\(\Phi_M\). These are finite-dimensional real semialgebraic sets, not
sets of finite cardinality.

Soundness requires a lift of every actual behavioral profile,

\[
\mathcal E_M(p)\in R_M(r),\qquad
\Phi_M(\mathcal E_M(p))\le E_r(p).
\]

Then a certified lower bound on \(\inf_{x\in R_M(r)}\Phi_M(x)\) is a
lower bound on \(\eta(r)\). An exact semantic lift may retain the actual
coordinates \((U,B)\) and impose
\(\Phi_M=\max(0,\max_i(B_i-U_i))\), giving equality on actual-profile
lifts. This does not assert that every relaxed feasible point is realized
by a behavioral profile, or that a compressed finite-clock profile has
exactly the original error.

The lift and its proof must cover all boundary cases: positive Never mass,
finite stopping mass escaping to later dates, simultaneous quitting,
singleton preemption, and every unrestricted unilateral response. Relaxed
outcome masses cannot be used as actual profiles without proving their
independent-product realization or supplying an approximation argument.

Even if lower values converge to \(\eta(r)\), failure to find a positive
lower certificate at finitely many stages proves no zero-gap conclusion.
Likewise a positive-gap semidecision procedure need not terminate on a
zero-gap table. A zero-branch certificate must instead establish actual
approximation at every accuracy. It may use any sound existence or
realization argument; a common chronology or one exact equilibrium profile
is not required.

## Why rational inputs suffice for counterexample search

For real reward tables the same value satisfies

\[
|\eta(r)-\eta(r')|\le2\lVert r-r'\rVert_\infty.
\]

Consequently any normalized real table with positive gap has a normalized
rational neighbor with positive gap. Rationality is an exact input model,
not a restriction to rational behavioral strategies in the negative
certificate. Floating-point evidence, a restricted-profile lower bound, or
the absence of a certificate after a finite search does not settle either
branch.
