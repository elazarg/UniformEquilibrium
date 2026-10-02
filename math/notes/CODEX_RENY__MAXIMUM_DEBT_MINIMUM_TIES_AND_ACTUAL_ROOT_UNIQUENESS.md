# Maximum-debt minimum ties and uniqueness of the actual-payoff root

Author: CODEX_RENY.

Status: ordinary-mathematics proof, independently checked
[by CODEX_HILBERT](../feedback/CODEX_RENY__MAXIMUM_DEBT_MINIMUM_TIES_AND_ACTUAL_ROOT_UNIQUENESS__BY_CODEX_HILBERT.md),
not Lean-checked. The statements concern the compact minimum of **maximum**
terminal regret. They neither produce early absorption nor exclude a new
reward-table class. The source comparison below distinguishes this objective
from the already stronger isolation theorems for minimum **total** regret.

The maximal-debtor tie lemma, including nonattainment, was already proved
in Section 11 of
[CODEX_HILBERT__EXTREMAL_REWARD_TABLE_VARIATIONAL_TEST.md](CODEX_HILBERT__EXTREMAL_REWARD_TABLE_VARIATIONAL_TEST.md).
Section 3 below is an independent derivation. The additional consequence
is uniqueness of every exact root at the actual payoff U in Section 4.

## 1. Exact setting and claims

Let I be a nonempty finite player set. For every nonempty S⊆I fix a reward
vector r(S), with |r_i(S)|≤M and M>0. Independent stopping laws on
ℕ∪{Never} implement the quitting game: the first finite stopping date yields
the coalition stopping there; all-Never pays zero. All unilateral behavioral
deviations are allowed. Equivalently, on the unique live history they are
arbitrary stopping laws, so their expected payoffs are mixtures of pure-date
and Never payoffs. Put

```text
U_i(p)=prescribed payoff,
B_i(p)=supremum of all unilateral deviation payoffs,
d_i(p)=B_i(p)−U_i(p),          E(p)=max_i d_i(p).

C=closure{(U(p),B(p)):p an actual product stopping-law profile},
E(U,B)=max_i(B_i−U_i),        m=min_{(U,B)∈C} E(U,B).
```

The carrier C is compact in the finite reward box; its debts are nonnegative.
Continuity of E implies m=inf_p E(p), without asserting that an actual p
attains m. Write s_i=r_i({i}).

For q∈[0,1]^I, its finite root game gives r(S) to nonempty root Quit
coalitions and U if everyone Continues. Its exact Nash equilibria are
independent mixed roots. Let c_i(q)=∏_{j≠i}(1−q_j).

**Theorem.** Suppose m>0. Every pair (U,B)∈C with E(U,B)=m has:

1. At least two distinct coordinates with B_i−U_i=m.
2. All-Continue as its **only** exact Nash root against U.

The theorem holds for arbitrary signed rewards and arbitrary finite I. It
uses no punishment-normal hypothesis, no canonical singleton normalization,
and no attainment by an actual profile. The one-player case of assertion 1
simply rules out m>0.

## 2. One-coordinate repair on actual laws

Fix an actual profile p and player k. Choose a complete response law τ_k
whose payoff is B_k(p)−ε, with 0≤ε tending to zero as accurately as desired.
Replace only player k's stopping law by

```text
p'_k=(1−θ)p_k+θτ_k,      0≤θ≤1.
```

This is private randomization by k, not correlation between players and not
a punishment conditioned on detecting a deviation. Opponents remain fixed.
Their unchanged laws imply B_k(p')=B_k(p), while linearity gives

```text
d_k(p')=(1−θ)d_k(p)+θε.                                  (1)
```

For every j≠k, one changed opponent law has total variation at most θ.
Couple the original and replacement law by using the original law with
probability 1−θ. Conditional on disagreement, every payoff difference is at
most 2M. This gives |U_j(p')−U_j(p)|≤2Mθ. The same estimate holds uniformly
for **every** fixed response of j; taking suprema therefore gives
|B_j(p')−B_j(p)|≤2Mθ. Hence

```text
d_j(p')≤d_j(p)+4Mθ               (j≠k).                 (2)
```

No response maximizer or finite response support is assumed here. An
arbitrarily accurate response is enough, even when the full cap is not
attained. The bounded payoff estimate is independent of all clock horizons.

## 3. A positive compact maximum minimum cannot have one maximal debtor

Suppose a minimizing pair (U,B) has unique maximal debtor k. Put d=B−U and
choose g>0 with d_j≤m−g for all j≠k. If there is no other player, omit
these inequalities and the corresponding terms below.

Choose a fixed θ with 0<θ<1 and 4Mθ<g. Take actual profiles pⁿ whose
semantic pairs converge to (U,B). For each n use a response τ_kⁿ with
error ε_n→0 and apply the **same** θ in (1)–(2). Then

```text
limsup_n d_k(p'ⁿ) ≤ (1−θ)m < m,
limsup_n d_j(p'ⁿ) ≤ m−g+4Mθ < m          (j≠k).
```

There are finitely many coordinates, so limsup_n E(p'ⁿ)<m. This contradicts
the defining actual-profile infimum m. In the one-player case the first
inequality alone is the contradiction. This proves assertion 1.

In particular, no map assigning a repaired semantic pair to (U,B) was
needed: different approximating profiles may use different responses, and
the repaired pairs need not converge. The strict finite-dimensional upper
bound is already enough. This is the needed nonattainment repair.

## 4. An absorbing root would create a uniquely maximal debtor

For any fixed root q, the literal prefix operation is a continuous map
C→C. Its exact cap recursion is

```text
U'_i=q_i Q_i+(1−q_i)C_i(U),
B'_i=max(Q_i,C_i(U)+c_i(q)d_i),
```

where Q_i is the pure Quit endpoint and C_i(U) is the pure Continue
endpoint. The cap allows each deviator its own optimal continuation law;
it does not require one continuation serving all deviations.

If q is exact Nash against U, then U'_i=max(Q_i,C_i(U)). Therefore

```text
0≤d'_i≤c_i(q)d_i≤m.                                    (3)
```

These are statements about the continuous semantic prefix itself, so they
hold for a nonattained pair in C. They also follow directly from the checked
auxiliary-prefix inequality by setting the auxiliary shift to d=B−U.

Suppose q is nontrivial. If two different coordinates of q are positive,
every c_i(q)<1. Equation (3) gives E(U',B')<m, a contradiction. Otherwise
q has one active owner k, with q_k>0. Then

```text
d'_j≤(1−q_k)m<m   (j≠k),             d'_k≤m.
```

Carrier minimality forces d'_k=m. Thus (U',B') is itself a global
max-debt minimizer with k as its unique maximal debtor, contradicting
Section 3. There can be no nontrivial exact root.

Finite mixed Nash existence supplies at least one exact root, so the sole
remaining root is all-Continue. This proves assertion 2. It also gives
U_i≥s_i, although that last consequence is already checked independently.

## 5. Relation to global finite geometric-repair minima

Consider the canonical Fin4 setting and m_N of FRECHET's
[global repair contraction](CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_PAYOFF_FLOOR_ESCAPE.md):
three opponent laws range over all dates below N and Never; the pivot has
an arbitrary finite head and a geometrically distributed finite tail plus
Never. The relaxed zero-first-atom boundary is included in the finite
optimization.

Every relaxed optimizer's pair belongs to C: positive first-atom
implementations have the **same** U and their caps converge to the
relaxed caps. Conversely, given any actual product law p, censor each
nonpivot's finite mass at dates at least N to Never. The total mass changed
is ε_N→0, so every prescribed payoff and every response cap changes by at
most 2Mε_N, uniformly over deviators. Thus the resulting full regret is at
most E(p)+4Mε_N. The geometric compression theorem then replaces the
pivot without increasing any cap or changing U. Consequently

```text
m_N↓m=inf_p E(p).
```

It follows that every cluster of the **full semantic pairs** of global
relaxed optimizers is a global maximum-debt minimizer in C. If m>0,
Sections 3–4 apply to every such cluster: at least two debts tie at m,
and every exact root at its U is all-Continue.

This avoids lower hemicontinuity of the exact-root correspondence. One
cannot infer the same conclusion merely from vanishing absorption of roots
at U_N; instead the cluster is proved to be a global semantic minimizer and
the actual-response argument is applied anew there. A payoff-only cluster
also admits a semantic cluster subsequence because the cap vectors are
bounded; the same conclusion then holds at that payoff.

FRECHET's quantitatively stronger finite-calendar statement is

```text
m_{N+2} ≤ m_N−a(q)m_N²/(32M)
```

for every exact root q against an optimizer's actual payoff, with
a(q)=1−∏_i(1−q_i). The novel finite aspect is the N+2 support incidence,
including the relaxed boundary and complete responses. This note does not
independently review those constants or that calendar proof. Its additional
compact-minimum consequence uses only Section 2 and the existing prefix
formula. Neither result forces m=0 in the all-Continue region.

## 6. Narrow source comparison

The route was the controller–tester and minimum-plateau entries in
`docs/TOOLKIT.md` and `docs/FRONTIER.md`, followed by the declarations below
and their directly used definitions. No literature-priority claim is made.

- `quittingControllerTesterValue_eq_minimum_rawMaximumDebt` and
  `quittingControllerTesterValue_eq_zero_iff_exists_uniformEquilibriumPayoff`
  in `UniformEquilibrium/Quitting/ControllerTester/ControllerValue.lean`
  already identify the compact maximum objective and its zero test.
- `quittingControllerCanonicalBarrier` and
  `nonempty_closedInvariantBarrier_iff_le_controllerTesterValue` in
  `UniformEquilibrium/Quitting/ControllerTester/BarrierDuality.lean` provide
  the existing invariant max-debt barrier. They do not supply the response
  mixture used in Section 3.
- `minimumTerminalSemantic_exploitabilitySingletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`
  already gives B_i−s_i≥m, and hence U_i−s_i≥m−d_i≥0, at every positive
  maximum-debt minimum.
- In that same file,
  `minimumTerminalSemantic_exploitabilityAuxiliaryNash_eq_allContinue`
  gives uniqueness against B−h when 0≤h_i<m for **every** i. It does not
  apply to h=d: at least one d_i=m, and Section 3 now forces at least two.
  `minimumTerminalSemantic_exploitabilityIs_allContinuePlateau` states
  that all-Continue is an exact root against U; it does not state uniqueness
  of that root. These are the exact boundaries strengthened here.
- `quittingTerminalSemanticDebt_prefix_le_auxiliaryNash` in
  `UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`, together
  with `quittingTerminalSemanticPrefix` and carrier preservation in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, already
  gives (3). The actual-profile version is
  `quittingTerminalDeviationDebt_rootThenContinuation_le` in
  `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
- `minimumTerminalSemantic_exactNash_allContinue_or_debtGateSolo` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumDebtSimplex.lean`
  and `quittingTerminalSemantic_minimum_twoPositiveDebt_root_eq_allContinue`
  in `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`
  assume a minimum of the **sum** of debts. They are not maximum-minimum
  statements. The latter says two positive debts, not two maximal debts.
- `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal` and
  `exists_open_exactAllContinueTube_minimumFiber` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`
  supply stronger singleton separation and open exact-root isolation, but
  for the minimum **total**-debt fiber and with all-player punishment
  normality. Their proofs use the singleton-tight unique-debtor iteration
  in `TerminalSemanticSingletonTightMinimumFaceIteration.lean`. Those
  hypotheses cannot be silently replaced by a maximum-debt minimum.
- `fixedCapPin_exactRoot_absorptionMass_lowerBound` in
  `UniformEquilibrium/Diagnostics/Quitting/FirstExactRootDebtDescent.lean`
  supplies a quantitative root absorption estimate from a positive owner
  debt and a cap-to-singleton pin. It is not a global all-coordinate repair
  or a finite geometric-calendar producer.

No matching two-maximal-debt or actual-U uniqueness theorem was found in
these concrete maximum-minimum source files and adjacent declarations.
The preceding statement concerns the checked declarations, not conference
notebooks: HILBERT's earlier Section 11 already proves the two-tie lemma.
This is a bounded repository comparison, not a global novelty theorem.

## 7. Exact limitation

The new statements rule out an absorbing root **at** a positive maximum
minimum. They do not prove a strict singleton gap U_i>s_i, an open
neighborhood with unique exact root, or any uniformly positive absorption
choice near the minimum. The inspected total-debt isolation theorem has
those stronger conclusions under different hypotheses.

The remaining mathematical issue is still to construct a coordinated
product-law move in the actual-U all-Continue region that lowers the
positive maximum floor. Rephrasing the uniqueness theorem as another
plateau condition does not construct that move. The current proof stops
at this boundary.
