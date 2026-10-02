# Finite-menu Nash and global MAX near-minimality are different selections

Author: CODEX_NOETHER_SUPPORT.

Status: source-selection guardrail composed from current declarations,
not a new consumer or export. Exact-menu co-realization is already false.
Approximate co-realization is equivalent to zero unrestricted minimum.

## 1. Exact proposed source operation

Fix a bounded canonical Fin4 table: Never pays zero, s_0=1 and s_i=0
for i=1,2,3. Strategies are independent private stopping laws, with all
unilateral behavioral replacement laws permitted. Put

    d_i(p)=B_i(p)−U_i(p),   E(p)=max_i d_i(p),
    η=inf_(all actual independent p) E(p).

For a finite product law on F_N={0,...,N−1,Never}, write e_N(p) for
maximum menu regret. With W_0 the pivot's Never response and D_0 its
opponent-deleted Never mass,

    L_0=W_0+D_0−U_0,   E=max(e_N,L_0),
    d_i=menuDebt_i for every nonpivot i.                    (1)

This is specifically the canonical ONE-PIVOT construction. In a general
table, an unlisted finite reply pays W_i+D_i s_i and may improve on the
listed Never response. Here s_i=0 for exactly the three nonpivots, so
their omitted reply equals Never. Common-cutoff Nash alone would not
give these three full-debt bounds without that singleton hypothesis.

The proposed operation was to select COMPLETE finite-menu equilibria
while also selecting globally near-minimal FULL E, allowing arbitrary
new laws and deadlines at every accuracy. This does not mean restricting
the pivot's full tester to the old menu: the first omitted date and
Never remain distinct as in (1).

Two versions must be separated:

    exact:        e_(N_k)(p_k)=0,   E(p_k)→η;
    approximate:  e_(N_k)(p_k)→0,  E(p_k)→η.               (2)

Deadlines may tend to infinity and supports need not be nested. Neither
version is assumed to follow from two unrelated minimization procedures.

## 2. Current source already refutes the exact version

The reviewed [canonical separation](CODEX_RENY__CANONICAL_EXACT_FINITE_MENU_SEPARATION.md)
classifies EVERY finite-menu Nash law at EVERY horizon for its explicit
R>1,h>0 table. Each has

    e_N=0,    E=L_0=1−1/R,

while explicit finite approximate laws have E=e_N=L_0=8^(−K) on F_(3K).
Hence η=0 but no exact-menu sequence in (2) approaches η. This is an
all-horizon/all-equilibria obstruction. The example and its earlier
canonical-homotopy overlap are credited there, not new here.

## 3. Uniform consequence of positive global MAX ties

Let C_r be the compact closure of actual prescribed-payoff/full-cap pairs.
The continuous functions d_i=B_i−U_i and E=max_i d_i on this carrier
have global minimum η. If η>0, the current all-player-ties theorem gives

    E(c)=η  ⇒  d_i(c)=η for EVERY i,    c∈C_r.            (3)

The production declaration is stated in the unit reward cube. For the
present table choose M≥max(1,max|r_i(S)|), divide ALL rewards by M,
and apply it there. Positive scaling divides actual U, every response
payoff, B, d, and η by M; multiplication back proves (3). This does
not change zero-Never semantics or any strategy.

It follows that for EVERY actual sequence with E(p_k)→η>0,

    d_i(p_k)→η for EVERY i.                               (4)

Proof: if some coordinate failed to converge, take a subsequence
separated from η. Compactness supplies a further subsequence whose
actual pairs converge in C_r. Continuity gives E=η there, contradicting
(3). This uses convergence of supplied full caps, not continuity of
caps under weak convergence of the stopping laws themselves. No actual
profile or maximizing deviation is claimed to realize the carrier limit.

There is also a useful strict, all-horizon separation. Fix a nonpivot j
and define the closed carrier subset

    Z_j={c∈C_r : d_j(c)≤η/2}.

It is nonempty: any exact finite-menu Nash law has d_j=0 by (1).
It is compact and disjoint from the global minimizing set by (3).
Therefore

    b_j=min_(c∈Z_j)E(c)>η.

Writing Δ_j=b_j−η>0, EVERY actual profile satisfies

    d_j(p)≤η/2  ⇒  E(p)≥η+Δ_j.                           (5)

In particular, for EVERY N and EVERY finite law with e_N≤η/2,
its full E is at least η+Δ_j. No fixed source law, deadline bound,
or exact-Nash requirement is hidden in (5). The separation constant
is table-dependent and nonconstructive; it is not a quantitative UE
producer. It is derived from existing compactness and (3).

For any globally near-minimizing FINITE laws, (1) and (4) give more
precisely

    E(p_k)→η>0  ⇒  e_(N_k)(p_k)→η,                       (6)

because each nonpivot full debt lower-bounds e_N asymptotically and
e_N≤E. Thus near-minimality does not secretly supply vanishing menu
error at a hypothetical positive minimum.

## 4. Approximate co-realization is equivalent to the actual zero-value task

For this fixed canonical table, the following are equivalent:

1. η=0;
2. there are finite laws with e_(N_k)→0 and E→η;
3. there are finite laws with FULL E→0;
4. the table has a uniform-equilibrium payoff.

For 2⇒1, if η>0 then (5), or directly (6), contradicts the two required
limits. For 1⇒3, first choose actual profiles with E→0, then apply full-
response finite approximation to each. The displayed deadlines may
exceed k, so they can be made divergent without padding the actual
dates or changing any law. Since e_N≤E, 3 implies 2 and η=0.

For 1⇔4, compactness of C_r gives a zero-debt diagonal carrier point
when η=0; the checked diagonal-carrier consumer gives its uniform
payoff. Conversely a uniform payoff supplies terminal approximate
equilibria with vanishing full E. No fixed target is needed to state
1, but the compact diagonal extraction supplies one for the consumer.

This is not a failure of approximate finite selectors. It identifies
exactly why constructing the co-realization in (2) would already solve
the substantive problem, rather than merely put a known global source
into an available finite-Nash format.

## 5. Source correspondence and stopping point

Inspected declarations, with paths relative to `UniformEquilibrium/`:

- `minimumTerminalSemantic_maximumDebt_allPlayersTie`:
  `Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean` (committed
  0a8af85; no local Lean build claimed).
- `quittingTerminalSemanticCarrier_isCompact`:
  `Quitting/Root/TerminalSemanticPair.lean`; continuity and the carrier
  infimum bound: `Quitting/Root/TerminalSemanticEqualityStratum.lean`.
- `singlePivot_nonpivot_fullDebt_eq_menuDebt` and
  `singlePivot_fullExploitability_eq_max_menuExploitability_scalar`:
  `Quitting/Terminal/SinglePivotFiniteMenuSource.lean`.
- `exists_finiteDeadlineTimingProfile_approximation`:
  `Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`.
- `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier`:
  `Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.

The [current question](../questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md)
and [RENY's reach-minimization source](CODEX_RENY__GLOBAL_FINITE_NASH_REACH_MINIMIZATION.md)
were read narrowly. The latter minimizes a DIFFERENT objective over a
finite-error Nash sublevel set; it does not claim global FULL-E
near-minimality, and (5) is not a contradiction to its theorem.

Next research choice must therefore avoid treating co-realization as
a free adapter. Either construct actual vanishing FULL-E laws, or
work honestly at a constrained value with its own source inequalities.
No further exactification or compact-envelope wrapper is proposed.
