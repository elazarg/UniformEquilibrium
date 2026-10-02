# Independent review of the strengthened global maximum-minimum package

Reviewer: CODEX_RENY. Ordinary mathematical review, not a Lean check.
Read the complete frozen proof surface before other reviews of the stronger
claims; no author file or export was changed.

## Reviewed bytes and verdict

The complete dependency surface consists of these four files under `notes/`:

| File | SHA-256 |
| --- | --- |
| CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_PAYOFF_FLOOR_ESCAPE.md | 5a719508f3970be8e5e33721c29d44e049e83ad32d069cafba4afe743e762335 |
| CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_APPROXIMATE_ROOT_CLUSTER_ADDENDUM.md | 10cd17c43b8d2620efae3faa80e11516e7afc045849964ab97c243df595dd9b7 |
| CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_LOWERED_ROOT_MARGIN_TEST.md | e98d2be429759903c7a760b04d6a26718f58d05573856f6424604f643d8e5efc |
| CODEX_HILBERT__GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES.md | 42cf56a4a354823a3a17e379715dac61bd6c1ccd62aeb277bb32b99844a06166 |

**Verdict: PASS.** No unresolved mathematical objection to the all-player
tie theorem, the strict actual-payoff singleton margin, the displayed
one-date/two-date finite inequalities, their relaxed-boundary arguments,
or their consequences for every compact-carrier minimum. The older two
files were checked as proof dependencies, not as separate export targets.

The strict-interior, all-tied case remains open. This review does not
certify a uniform-equilibrium producer or authorize export placement.

## 1. Strongest mathematical statements covered

Let a four-player quitting game have arbitrary signed rewards bounded by
M>0, independent stopping laws on ℕ∪{Never}, and Never payoff zero. Let
U(p), B(p) be its prescribed payoff and unrestricted behavioral response
caps, C the closure of all actual pairs, d=B−U, and

```text
m=min_{(U,B)∈C} max_i d_i=inf_p max_i d_i(p).
```

If m>0, **every** minimizing pair satisfies

```text
d_i=m                 for every player i,
U_i−r_i({i})≥m²/(64M)  for every player i.               (1)
```

The all-player tie assertion holds for any nonempty finite player set;
the explicit constant 64 in the margin proof is checked here for four
players. Neither assertion assumes punishment normality, canonical
singletons, nor realization of a minimum by one actual profile.

For canonical singleton vector (1,0,0,0), let m_N be the joint relaxed
geometric-repair minimum with all three nonpivots supported before N or
at Never and the pivot allowed its finite head, geometric finite tail,
and Never mass. Here M≥1. Every optimizer with m=m_N>0 satisfies the
following source comparisons:

```text
m_{N+2}≤m−a(q)m²/(32M)+e(q;U)               (all roots q),

m_{N+2}≤m−(m²/(64M)−g)_+ m²/(320M²),
    where g=min_i(U_i−s_i),

m_{N+1}≤m−m min((m−d_k)/(4M),m/(16M)),
    if U≥s and d_k<m.                                  (2)
```

All minima are over the **whole** finite-domain probability set, not over
one coordinate, exact timing Nash profiles, or a chosen equilibrium
component. All displayed regrets are full behavioral regrets.

## 2. Finite optimization and exact cap incidence

The first frozen file supplies the complete finite polynomial head data
and two-endpoint canonical tail formulas. They extend continuously to
α=0<λ, where α is the first geometric atom and λ is the finite tail
mass. Positive-α implementations preserve U exactly and their caps
converge to the relaxed caps. Thus the boundary point is legitimate
finite optimization data, but is not itself an actual clock law.

After any root prefix, all nonpivots lie before L=N+1 or at Never. The
pivot remains finite-head/geometric-tail/Never. For the pivot, every pure
date at least L has the same payoff, no smaller than Never because its
own singleton is one. For a nonpivot, every late response value lies
between Quit L and Never; its own singleton is zero. This remains true
when spectator or collision rewards are negative, the finite tail is
empty, the geometric hazard is one, or deleted survival is zero.

Hence every player has a complete pure response in {0,…,L,Never}.
Mixing one player toward such a response changes at most one head atom
or the Never atom. All pivot atoms strictly after L remain a uniformly
scaled geometric tail. This proves literal membership in the N+2 family
without a cutoff depending on α or on response accuracy. The extra
date cannot be silently omitted for a nonpivot reply at L.

The one-date solo-prefix construction needs no new complete reply. All
old clocks simply shift by one and the selected player gains an initial
atom, so its output lies in the N+1 family. N=0 and a selected pivot
cause no exception.

## 3. Prefix and response estimates; explicit branch checks

For a root q, write c_i=∏_{j≠i}(1−q_j), Q_i for Quit, C_i(U) for
Continue, V_i for the prescribed mixture, and
e_i=max(Q_i,C_i(U))−V_i. The exact prefix formulas give

```text
B'_i=max(Q_i,C_i(U)+c_i d_i),
d'_i=[c_i d_i−(Q_i−C_i(U))_+]_++e_i≤c_i d_i+e_i.        (3)
```

These formulas include all complete responses in the continuation,
separately for each deviator; no common best-response tail is needed.
If a=1−∏_i(1−q_i)>0 and q_k is largest, then q_k≥a/4 and
c_j≤1−a/4 for every j≠k. Only k can remain unscreened.

Mix its complete best response into its whole law with fixed weight
θ=am/(32M)≤1/16. Its own cap is unchanged and its debt is multiplied
by 1−θ. A change of one opponent law of total variation at most θ
changes every prescribed payoff and every fixed-response payoff by at
most 2Mθ. Taking suprema retains that uniform cap bound, so all other
debts increase by at most 4Mθ. This proves the first line of (2).

The argument survives a sure root owner: the repair changes that owner's
**whole stopping law**, not only the old tail hidden behind a sure Quit.
It also survives an approximate root; its literal defect is added once,
not once per date. No chronological sum or public correlation is used.

At α=0<λ, choose implementing sources with debts at most the relaxed
debts plus ε, keeping U, q, k and θ fixed. All estimates add at most ε
and remain in the same enlarged calendar. Passing to the numerical
infimum is valid; weak continuity of complete caps is not asserted.

## 4. Lowered roots and the strict margin

Choose q exact Nash against W=U−h·1. If q_i=0, raising continuation
from W to U preserves Continue as a best action, giving e_i(q;U)=0.
If 0<q_i<1, both actions were indifferent at W, so the exact new
defect is q_i c_i h. If q_i=1, any Continue advantage created by the
raise is at most c_i h. Hence in every boundary case

```text
e_i(q;U)≤q_i c_i h≤a h.                               (4)
```

The absorption factor is essential. A mere additive h bound would not
give the desired strict result as a→0.

Set h=m²/(64M)≤M/16. If g<h, all-Continue is not Nash at W. Every
exact root there has positive absorption. The explicit bound follows
from η_h=(h−g)_+≤2M+h:

```text
Q_i−C_i(W)≥η_h−5M(1−c_i),
a≥η_h/(5M).
```

This uses finite root Nash existence at W even if W lies outside the
original reward box. It does not treat W as an actual continuation.
Together with (3)–(4) it yields the strict-margin finite inequality in
(2). The inequalities η_h<5M and 4M+h<5M justify the sure-Quit branch
of this absorption estimate.

For a compact minimum, fix q at the limiting U−h rather than selecting
roots at approximating U_n. The defect changes by at most
2‖U_n−U‖∞. Choose actual p_n→(U,B), approximate complete responses
with error ε_n→0, and the same θ throughout. Then

```text
limsup_n E(p'_n)≤m−am²/(32M)+ah=m−ah<m
```

if a>0, contradicting the actual-profile infimum. No repaired sequence
needs to converge. Thus all-Continue must be Nash at U−h, proving the
second line of (1). This explicitly avoids lower hemicontinuity of the
Nash correspondence and cap attainment.

## 5. Slack-aware solo prefix and every player's tied debt

For a new solo owner k with Quit probability h, the complete formulas are

```text
d'_k=d_k+h(U_k−s_k),
d'_j=max((1−h)(s_j−U_j)+h(r_j({k,j})−r_j({k})),
          (1−h)d_j)                       (j≠k),       (5)
```

provided U≥s. All immediate joining deviations are present in the first
branch; this branch may not be dropped merely because it was inactive
at the old source.

With ζ=m−d_k>0 and h=min(ζ/(4M),m/(16M)), the owner rises by at most
2Mh≤ζ/2. Also hm≤ζ/2. Each outsider's first branch is at most
2Mh≤m/8≤(1−h)m, and its second branch is at most (1−h)m. Thus every
debt is at most m−hm<m. The operation is not Nash at the new root;
its owner's particular defect is paid by that owner's old slack.

At a compact MAX minimum, the checked singleton-margin theorem already
gives U≥s. If any d_k<m, the continuous fixed-root semantic prefix
maps C into C and (5) yields a contradiction. Equivalently, its actual
approximants give literal strict competitors. This proves all-player
ties without punishment normality or actual attainment. The finite
relaxed-boundary argument keeps the same h and adds only ε, as claimed.

## 6. Global finite limits and exact scope of the remaining region

Every relaxed optimizer is in C via positive-α approximation. Conversely,
TV censoring of only the nonpivots of an arbitrary actual source followed
by geometric pivot compression gives m_N↓m. Therefore every full
semantic cluster of global optimizers satisfies (1) when m>0.

The finite strict-margin inequality makes U≥s hold uniformly for all
sufficiently large-domain optimizers if m>0. The slack inequality then
also makes every debt approach m uniformly over optimizer choices.
This is an immediate consequence of the two consecutive-value drops
tending to zero, not a claim that each finite optimizer already satisfies
the exact limiting equalities.

The frozen proper-subset-change test was also checked directly. At its
global m₀=1/2 example, an unchanged half-finite pivot leaves pivot debt
at least 1/2; an unchanged Never follower instead leaves debts at least
A and 1−A. Thus changing even three whole laws cannot improve there,
whereas all four quitting surely is Nash. That example is below the
payoff floor and does not falsify the all-four root move. It is not a
counterexample in the surviving strict-interior region.

Neither inequality provides descent when all d_i=m and all
U_i−s_i≥m²/(64M). In that region a solo prefix spends nonexistent
owner slack, and the selected lowering may leave all-Continue exact.
No positive absorption floor or universal progress there is proved.

## 7. Exact source novelty and the export relevance boundary

I rechecked the named MAX declarations in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`:

- `minimumTerminalSemantic_exploitabilitySingletonMargin` gives
  B_i−s_i≥m, hence only U_i−s_i≥m−d_i≥0.
- `minimumTerminalSemantic_exploitabilityIs_allContinuePlateau` gives
  all-Continue existence at U.
- `minimumTerminalSemantic_exploitabilityAuxiliaryNash_eq_allContinue`
  assumes every auxiliary shift is strictly below m. It does not allow
  the full debt vector, still less the full debt plus a positive lowering.

The new package strengthens these to **every coordinate tied at m** and
the uniform quantitative actual-payoff margin in (1), with actual
new-date comparisons (2). These are not mere finite packaging of the
already checked non-strict MAX margin.

The checked SUM isolation declaration
`exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`
assumes minimum **total** debt and all-player punishment normality. Its
open unique-root tube concerns that different fiber. It cannot supply
(1) on arbitrary maximum-minimum points. The package's previous
two-maximal-debtor lemma was already ordinary mathematics in HILBERT's
EXTREMAL Section 11 and is not itself a new result here.

I read `exports/README.md` and the live
`questions/QUITTING_CONTROLLER_TESTER_DUALITY.md` and
`questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md`. The current
theorems do **not** constitute a complete answer to either sign/selection
question. A gate-compliant assembly must state the precise strict
reduction instead of describing a local lemma as a producer.

One exact reduced obligation supported by the proofs is the following.
For fixed r and M, define the restricted positive carrier region

```text
T_r={(U,B)∈C : e=max_i(B_i−U_i)>0,
       B_i−U_i=e for every i,
       U_i−s_i≥e²/(64M) for every i}.
```

Then the controller sign assertion m=0 is equivalent to:

```text
For every (U,B)∈T_r, there exists an actual product-law profile p
with E(p)<max_i(B_i−U_i).                               (R)
```

If m=0, the actual-profile infimum immediately supplies the competitor
for every positive e. Conversely if m>0, a compact minimum lies in T_r
by (1), and (R) contradicts that minimum. The two moves also explicitly
improve every positive actual source outside this region: use the lowered
root when its singleton margin is too small, and otherwise use a slack
owner when debts are not all tied. For unrestricted sources the complete
reply may be approximate; choosing its accuracy sufficiently small retains
the strict decrease. At nonattained carrier points the same fixed-root,
actual-approximation arguments provide strict competitors.

The region in (R) must include **carrier** points, not just actual laws:
a positive minimum need not be actually attained. Replacing it by a
consumer only for exact actual members of T_r would introduce a gap.

This is a genuine named narrowing of the controller-sign obligation and
is the appropriate relevance claim for a possible combined export. The
frozen note collection by itself still lacks the final self-contained
assembly and its reviewed handoff. The remaining consumer (R) is not
proved. No new special-case UE coverage, counterexample, or strict-interior
descent should be attributed to this PASS.
