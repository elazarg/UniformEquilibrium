# The full-objective joint active-response move: exact scope and stopping point

Author: CODEX_RENY.

The simultaneous first-order information proposed for this mechanism is
already present in HAHN's finite-clock KKT theorem. The exact independent
joint move below is legitimate, but neither that theorem nor common-clock
compression gives its required pointwise descent inequality. This note
records the algebra and the precise unproved implication; it is not a new
producer, a new residual class, or a counterexample to global selection.
All calculations below are ordinary mathematics, not new Lean results.

## 1. Actual finite source and the tested operation

There are four players. For each nonempty quitting coalition S there is a
real reward vector r(S), with all coordinates bounded in absolute value by
M. All Never pays zero. The own-singleton vector is (1,0,0,0). Players use
independent stopping laws on the nonnegative integers together with Never;
no common random label or observation of an unobserved deviation is used.
Every full behavioral replacement is represented by a stopping law, and
its terminal payoff is an average of pure-time payoffs.

For N≥1 put F_N={0,…,N−1,Never}. Write U_i(p) for prescribed payoff,
V_i,t(p) for the payoff after replacing player i by pure time t, and

    g_i,t(p)=V_i,t(p)−U_i(p),
    F(p)=max_i sup_t g_i,t(p).

For p supported on F_N, the complete tester set is
T_N={0,…,N,Never}. Thus F is a finite maximum of multiaffine polynomials
on X_N=∏_i Δ(F_N). In canonical notation it is exactly

    F(p)=max(E_N(p),L₀(p)),
    L₀(p)=V₀,Never(p)+∏_(j≠0) p_j(Never)−U₀(p).

Let p be a GLOBAL minimizer of F on X_N, and m=F(p)>0. This is not a
finite-menu Nash assumption. The minimum exists by compactness and full
finite-tester continuity. It need not equal the unrestricted infimum.

The existing simultaneous KKT theorem supplies nonnegative weights
λ_i,t, summing to one, supported on tied full tests g_i,t(p)=m. Set
θ_i=Σ_t λ_i,t. For θ_i>0 define the actual law
ρ_i(t)=λ_i,t/θ_i; if θ_i=0 put ρ_i=p_i. All these laws are supported
on F_(N+1). Positive θ_i implies that every response in ρ_i attains
player i's full cap at p and that this player's full debt is m.

The proposed additional operation is a simultaneous PRIVATE mixture:

    p_i(ε)=(1−εh_i)p_i+εh_iρ_i,
    h_i≥0,    0≤εh_i≤1.                                  (1)

The selectors h_i may differ; no player symmetry is imposed. The desired
useful conclusion would be some common ε>0 and h with

    F(p(ε))<m.                                             (2)

This would strictly improve the actual enlarged-menu minimum. To prove
the canonical selection question, isolated strict inequalities without a
uniform comparison or a separate zero-limit argument would still be
insufficient. No such iteration or zero-limit claim is made here.

## 2. What all tied testers actually require

Because (1) is supported on F_(N+1), recompute the FULL tester set as
T_(N+1)={0,…,N+1,Never}. For a tester a=(i,t) in this set and a subset
S of the players, let p^S replace exactly coordinates in S by ρ_j. Then
multiaffinity gives the exact identity

    g_a(p(ε))=Σ_S w_S(ε)g_a(p^S),
    w_S(ε)=∏_(j∈S)(εh_j)∏_(j∉S)(1−εh_j).                 (3)

These are independent-coordinate corner weights. The prescribed law is
not a correlated random choice of one corner. Equation (3) follows by
expanding each marginal in the product expectation, both for prescribed
payoff and for the pure-response payoff.

Put C_a,j=g_a(p^{ {j} })−g_a(p). The coefficient of ε is

    A_a(h)=Σ_j h_j C_a,j.                                  (4)

Let A⁺(p)={(i,t): t∈T_(N+1), g_i,t(p)=m}. This includes every newly
duplicated late test, even one assigned zero multiplier weight. Finiteness
of the tester set gives

    (d/dε)₊ F(p(ε)) at ε=0 = max_(a∈A⁺(p)) A_a(h).         (5)

Consequently a negative maximum in (5) proves (2) for sufficiently small
ε. A negative λ-weighted average is not that condition. Source-inactive
tests have a strict finite gap and can be kept below m for small ε, but
source-active tests with zero λ-weight cannot be discarded. If the
maximum is zero, no sign conclusion follows here. These claims follow
directly from the finite polynomial expansions; no convexity of F is
assumed. No higher-order descent claim is developed.

For θ_j>0, every source-active test owned by j has

    C_(j,t),j=−m,                                          (6)

because its deviation payoff does not depend on p_j, whereas the actual
replacement ρ_j raises U_j by m. The cross-coordinate C_a,j have no sign
specified by own-response optimality.

The existing KKT conclusion is already simultaneous:

    Σ_a λ_a Dg_a(p)[v−p]≥0    for EVERY v∈X_N.              (7)

If ρ_j is supported in the OLD menu, substituting the one-coordinate
direction in (7) gives Σ_a λ_a C_a,j≥0. Hence for any joint combination
of such old-menu directions, the weighted sum of (4) is nonnegative.
In fact its entire path stays in X_N and global minimality rules out (2)
for every ε, not just to first order. This uses the actual global
minimum and is not a local-Nash argument.

If some ρ_j uses the newly allowed date N, (7) no longer controls that
external direction. This is a possible enlarged-calendar move, but (6)
does not control its cross terms and (7) supplies no negative sign for
them. The genuinely missing assertion for this mechanism is a choice of
the SAME λ, h, and ε for which all complete inequalities in (3) are
strictly below m. The source theorem does not assert it. We have neither
proved it nor produced an actual positive global minimizer refuting it.

## 3. The new late test is literal, not an old label

At the original source p, pure dates N and N+1 have equal payoffs. After
(1), an opponent may stop at N, so this equality can disappear. For the
pivot, let P_S be the probability that no opponent quits before N and
the nonempty set of opponents quitting at N is precisely S. Directly
conditioning on those events gives

    V₀,N+1(p(ε))−V₀,N(p(ε))
      =Σ_(∅≠S⊆{1,2,3}) P_S [r₀(S)−r₀(S∪{0})].           (8)

If an opponent quits earlier the two replies coincide. If none quits by
N the pivot receives its singleton one under either reply. This proves
(8) for all atoms and Never masses. The bracket has no imposed sign for
an arbitrary canonical reward table. Therefore an old cap label does
not justify omitting the newly exposed cap inequality in (3) or (5).

The new late finite payoff of every nonpivot equals its Never payoff,
because its own singleton is zero. Thus the enlarged objective still has
exactly the canonical form max(E_(N+1),L₀). Both its menu part and its
updated pivot scalar have been included above.

One may alternatively force every nonpivot ρ_j to use Never in place of
date N. The two choices have equal OWN payoff at p, and then the pivot's
two late tests remain equal along the modified path. But they need not
have equal effects on OTHER players. This alters the joint direction
and its cross coefficients; it is not a consequence of unchanged KKT
data and supplies no descent sign by itself.

## 4. What common-clock independent recombination adds

The reviewed QUANTILE result applies to the fixed two-source family
(p,ρ) and uniformly to all independent coordinate mixtures between them.
For quantile level K, it puts their recombination box on a common clock
of length at most 16K and changes the FULL objective by at most 14M/K,
uniformly over the four mixture weights. These bounds include all late
and Never tests. For an already finite family the common gap-preserving
shortening also preserves its full cap geometry exactly before any
probability rounding is introduced.

Therefore the infimum over this fixed recombination box and the infimum
over its compressed box differ by at most 14M/K. This is a useful finite
representation statement. It supplies neither a sign for (4) or (8), nor
a good mixture parameter, nor a new source family. In particular, an
arbitrarily accurate representation of a box whose minimum is m does
not turn that minimum into zero. Convex combinations of marginal laws
do not make the full objective convex or produce a minimax interchange.

## 5. Bounded source comparison and precise conclusion

The starting sources named in
`CODEX_RENY__GLOBAL_FINITE_NASH_REACH_MINIMIZATION.md` were read in full:

- `CODEX_HAHN__FINITE_CLOCK_EXPLOITABILITY_KKT_BOUNDARY_OR_CROSS_AMPLIFICATION.md`,
  Theorem 2.1, already states (7) with all active pure-time multipliers
  at one full-objective global minimizer. Theorem 3.1 derives its
  boundary-or-cross-amplification alternative. It does not lose the
  simultaneous subgradient by initially selecting one debtor.
- `CODEX_HAHN__FINITE_CLOCK_KKT_FIXED_FACE_OR_FULL_TIMING_BUBBLE.md`
  retains marked pure-time witnesses in the subsequent compactification.
  Its fixed/escaping calendar alternatives do not prove a sign for (3).
- QUANTILE's common-coordinate mixture theorem and its independent review
  `feedback/QUANTILE__BY_CODEX_RENY.md`, Section 3, supply precisely the
  uniform finite-family representation used in Section 4.

The selected `docs/TOOLKIT.md` route was followed to:

- `singlePivot_fullExploitability_eq_max_menuExploitability_scalar` and
  the accompanying nonpivot/pivot cap identities in
  `UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`;
- `exists_minimum_quittingControllerFiniteWordLoss`,
  `antitone_quittingControllerFiniteWordValue`, and
  `tendsto_quittingControllerFiniteWordValue` in
  `UniformEquilibrium/Quitting/ControllerTester/FiniteWordValue.lean`.

The latter are checked finite-word existence, monotonicity, and convergence
to the unrestricted semantic value, not a proof that that value is zero.

The narrow mechanism is stopped at (3)–(8): retaining simultaneous
multipliers was already done; independent joint mixing produces actual
laws but no established pointwise descent. This does not disprove joint
global optimization, exclude a nonsymmetric branch, or refute the canonical
approximate-selection question. No new conditional interface is proposed.
