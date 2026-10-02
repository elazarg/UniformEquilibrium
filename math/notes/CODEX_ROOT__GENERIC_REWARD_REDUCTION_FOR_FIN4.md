# Generic-reward reduction for the Fin4 conjecture

Author: `CODEX_ROOT`

Status: **PROVED REDUCTION / INTERNAL NOTE.**  The reduction is ordinary
mathematics from a named checked Lipschitz theorem.  No generic Fin4 existence
theorem is claimed.

## Result

Let \(\mathcal R_4\cong\mathbb R^{60}\) be the space of four-player quitting
reward tables, with the uniform norm, and put

\[
 \eta(r)=\inf_\sigma\max_i\bigl(B_i^r(\sigma)-U_i^r(\sigma)\bigr).
\]

The checked theorem
`abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close` in
`Research/Quitting/TerminalExploitabilityRewardRobustness.lean` gives

\[
 |\eta(r)-\eta(r')|\le 2\lVert r-r'\rVert_\infty. \tag{1}
\]

The checked terminal selection results identify \(\eta(r)=0\) with existence
of a uniform-equilibrium payoff.  Consequently:

### Theorem 1 (dense-class sufficiency)

If \(G\subseteq\mathcal R_4\) is dense and every table in \(G\) has a
uniform-equilibrium payoff, then every four-player quitting table has a
uniform-equilibrium payoff.

**Proof.**  Given \(r\), choose \(r_n\in G\) with \(r_n\to r\).  Then
\(\eta(r_n)=0\).  Equation (1) gives \(\eta(r)=0\).  Apply terminal
selection.  \(\square\)

### Theorem 2 (counterexamples are robust)

If \(\eta(r)=\gamma>0\), then every table \(r'\) satisfying

\[
 \lVert r-r'\rVert_\infty<\gamma/2
\]

also satisfies \(\eta(r')>0\).  Thus the set of Fin4 counterexamples is open.
In particular, a Fin4 counterexample cannot exist only on a measure-zero,
meagre, isolated, or purely degenerate parameter set.

### Corollary 3 (generic counterexample reduction)

Let \(G\) be any dense subset of reward space.  If a Fin4 counterexample
exists, one exists in \(G\).  More generally, this holds for any residual
set, since every nonempty open ball meets a residual dense set.

Examples of admissible dense classes include:

1. rational reward tables;
2. tables avoiding any prescribed finite collection of nontrivial polynomial
   equalities;
3. tables whose sixty reward coordinates are algebraically independent over
   \(\mathbb Q\); and
4. a countable intersection of open dense finite-program transversality
   conditions, provided each condition is independently proved dense.

The rational specialization is already used by the checked Fin4
counterexample semidecision.  The point here is the positive route: it is
enough to prove existence on a dense general-position class.

## What genericity may legitimately remove

Generic perturbation can eliminate degeneracies that are expressed by
nonzero polynomial equations in the reward coordinates.  Plausible targets
include:

- accidental equalities between distinct pure-coalition rewards;
- singularity of a fixed finite complementarity or KKT system;
- nontransverse intersection for one fixed finite-clock/program skeleton;
- ties between finitely many explicitly displayed selector candidates.

For a countable collection of finite skeletons, a Baire argument can impose
all proved open-dense regularity conditions simultaneously.  Since a
counterexample set would be open, it would contain a table satisfying them
all.

## What genericity does not remove automatically

1. Nash complementarity itself forces endogenous equalities; those are not
   accidental reward degeneracies.
2. A cap or minimum point ranges over a continuum.  Regularity for each fixed
   rational cap does not imply uniform regularity over all caps.
3. Finite hazard capacity does not bound chronological word length: arbitrarily
   many arbitrarily small hazards remain possible.
4. Generic reward coordinates do not restore chronology forgotten by a
   semantic quotient.
5. A unique root or locally continuous selector is not by itself a terminal
   consumer.

Thus Theorem 1 is a real reduction, not a claim that the conjecture is now a
routine genericity argument.

## Concrete next test

For each fixed finite executable program skeleton \(P\), define a bad set
\(D_P\subseteq\mathcal R_4\) where its finite complementarity/KKT system has
an unrecorded tie, a singular isolated solution, or a non-trace-safe selected
branch.  Prove one of:

1. \(D_P\) is contained in a proper semialgebraic discriminant, and the
   complement admits a closed local executable selector; or
2. \(D_P=\mathcal R_4\) for a concrete skeleton, identifying an equality
   forced by game semantics rather than degeneracy.

If the first alternative holds for every skeleton in a countable executable
grammar, intersect the resulting open dense sets and rerun the Fin4 source
atlas on a generic alleged counterexample.  The remaining essential question
will be whether local trace-safe selectors plus bounded hazard capacity yield
one global controller.  A failure there is evidence that nonlocal chronology,
not reward degeneracy, is the real obstruction.

## Scope

This note proves neither density of any already-solvable Fin4 class nor a
generic uniform-equilibrium theorem.  Its exact contribution is that a
hypothetical counterexample is robust, and therefore a proof may freely
restrict to any independently established dense general-position class.
