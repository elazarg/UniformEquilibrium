# Lowered-continuation roots force a strict margin at positive maximum minima

Author: `CODEX_FRECHET_CYCLE`.

Status: ordinary-mathematics proof draft, not independently reviewed or
Lean-checked. The all-four-law candidate below improves the earlier
non-strict payoff-floor reduction to a uniform strict singleton margin.
It gives both a literal two-date finite-repair inequality and a statement
for every positive minimum of unrestricted maximum regret. No punishment
normality is assumed. The all-tied, strictly above-singletons region remains
unconsumed. Earlier frozen proof packets are unchanged; no export is made.

## 1. Exact setting and the useful root estimate

The finite-repair setting is exactly that of the frozen
[`GLOBAL_REPAIR_PAYOFF_FLOOR_ESCAPE`](CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_PAYOFF_FLOOR_ESCAPE.md),
SHA `5a719508f3970be8e5e33721c29d44e049e83ad32d069cafba4afe743e762335`,
and its separate
[`APPROXIMATE_ROOT_CLUSTER_ADDENDUM`](CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_APPROXIMATE_ROOT_CLUSTER_ADDENDUM.md),
SHA `10cd17c43b8d2620efae3faa80e11516e7afc045849964ab97c243df595dd9b7`.

There are four independent stopping laws on `ℕ∪{Never}`; the first finite
stoppers receive their nonempty coalition's reward, and all-Never pays
zero. All unilateral behavioral stopping-law deviations are permitted.
Rewards satisfy `|r_i(S)|≤M`, with `M≥1` in the canonical finite-repair
setting. Own singletons are `s=(1,0,0,0)`. Write U for prescribed payoffs,
B for full unilateral caps, `d=B−U≥0`, and `E=max_i d_i`.

The global relaxed geometric-repair minimum m_N optimizes all three
nonpivot laws on `F_N={0,…,N−1,Never}` and all pivot head/geometric-tail
coordinates, including `α=0<λ`. It is not coordinatewise or exact-Nash
minimization. For any selected global optimizer, its actual-payoff vector
U is preserved by positive-α boundary implementation, and
`0≤m_N≤2M`.

For an independent root q let

```text
c_i=∏_(j≠i)(1−q_j),             a=1−∏_i(1−q_i),
Q_i=pure Quit endpoint,
C_i(U)=A_i+c_i U_i=pure Continue endpoint,
V_i(U)=q_iQ_i+(1−q_i)C_i(U),
e_i(q;U)=max(Q_i,C_i(U))−V_i(U),      e(q;U)=max_i e_i.
```

The addendum proves, for every such q and every global optimizer with
`m=m_N>0`,

```text
m_(N+2)≤m−a m²/(32M)+e(q;U).                            (AR)
```

Its mechanism is literal: prefix the joint root q, then privately mix
the largest-hazard owner toward one complete pure reply with weight
`am/(32M)`. All four root coins are independent. The complete reply lies
in `{0,…,N+1,Never}`, so the resulting profile lies in the N+2 geometric
family. The relaxed boundary adds a vanishing numerical error at the same
N+2, not an increasing cutoff.

## 2. Lowering continuation pays absorption-relative error

Fix `h>0`, put `W=U−h·1`, and choose any exact mixed Nash root q in the
finite one-stage game with continuation W. Finite mixed Nash existence
applies even if W lies slightly outside the reward box. The root is then
prefixed onto the actual continuation U, not W.

**Lemma.** For every i,

```text
e_i(q;U)≤q_i c_i h,            hence e(q;U)≤a h.          (L)
```

If `q_i=0`, exact Nash at W says `C_i(W)≥Q_i`. As
`C_i(U)=C_i(W)+c_i h`, Continue remains best and the actual-U defect is
zero. If `q_i>0`, Quit is supported at W, so `Q_i≥C_i(W)`.
Consequently `(C_i(U)−Q_i)_+≤c_i h`. If `q_i<1`, Continue is also
supported at W, which gives `Q_i=C_i(W)`; in particular actual U cannot
make Quit strictly better. If `q_i=1`, the prescribed root action is
Quit. In both cases the actual-U root defect is
`q_i(C_i(U)−Q_i)_+`, proving the first inequality. Finally
`q_i c_i≤q_i≤a`.

Thus the cost is a h, not a horizon-independent additive h. Combining
(L) and (AR) gives

```text
m_(N+2)≤m−a[m²/(32M)−h].                                (D_h)
```

For any `h<m²/(32M)`, every absorbing exact root against the lowered
continuation produces a strict decrease. This root selection uses only
the optimizer's U and a finite game constructed from the raw table. It
supplies no equilibrium tail or known periodic schedule.

## 3. Quantitative finite-menu strict-margin escape

Set

```text
h=m²/(64M),             g=min_i(U_i−s_i),
η_h=(h−g)_+=max_i(s_i−W_i)_+.
```

Since `m≤2M`, we have `h≤M/16`. The same elementary forced-absorption
estimate as in the frozen proof, now at W, gives

```text
a≥η_h/(5M).                                              (A_h)
```

For completeness, if `s_i−W_i=η_h>0`, its Quit-minus-Continue root gap
against no quitting opponent is η_h. Against a nonempty opponent
coalition its gap is between −2M and 2M. Since
`η_h≤2M+h` and `4M+h<5M`,

```text
Q_i−C_i(W)≥η_h−5M(1−c_i).
```

If `1−c_i<η_h/(5M)`, exact Nash at W forces `q_i=1`, giving a=1.
Otherwise `a≥1−c_i≥η_h/(5M)`. Also `η_h/(5M)<1`, so both cases give
(A_h). When η_h=0 the assertion is immediate.

As the bracket in (D_h) is exactly h, this proves

```text
m_(N+2)≤m_N−(m_N²/(64M)−g)_+ · m_N²/(320M²).            (SM)
```

This holds for **every** global relaxed optimizer, including α=0<λ.
No step treats the lowered W as its actual continuation payoff.

If `m_N↓m_∞>0`, rearranging (SM) shows uniformly over all global
optimizers that

```text
(m_N²/(64M)−min_i(U_i−s_i))_+
    ≤320M² (m_N−m_(N+2))/m_N² →0.
```

Every payoff cluster therefore has the explicit strict margins

```text
U_(∞,i)−s_i ≥ m_∞²/(64M)>0        for every i.             (F)
```

The result improves the earlier non-strict floor, but does not force
m_∞=0: (SM) becomes inert when every margin is at least h.

## 4. Stronger formulation at every unrestricted maximum minimum

This section does not require canonical singletons, geometric compression,
or attainment by an actual stopping law. Keep four players and arbitrary
signed rewards with `|r_i(S)|≤M`, `M>0`. Define

```text
C=closure{(U(p),B(p)):p an actual independent stopping-law profile},
m=min_(U,B)∈C max_i(B_i−U_i)=inf_p E(p).
```

The carrier is compact in the finite reward box and its debts are
nonnegative. Let `(U,B)∈C` be **any** minimum with m>0.

**Theorem.** Every coordinate satisfies

```text
U_i−r_i({i})≥m²/(64M).                                   (CM)
```

Choose `h=m²/(64M)`, let `W=U−h·1`, and let q be any exact root against
W. Suppose its absorption a is positive. Choose actual profiles p_n
whose full semantic pairs converge to `(U,B)`. Thus `E(p_n)→m` and
`U(p_n)→U`. At the actual source payoffs U(p_n), the fixed q has root
defect at most

```text
e(q;U(p_n))≤a h+2‖U(p_n)−U‖∞.
```

Prefix q and select its largest-hazard owner k. Mix k toward a complete
response with response error ε_n→0, using the **fixed** weight
`θ=am/(32M)`. Such approximate responses always exist; no pure cap
attainer or finite response-support theorem is assumed here. The prefix
and one-coordinate estimates from the frozen proof and addendum give

```text
limsup_n E(p′_n)≤m−am²/(32M)+a h=m−a h<m.
```

Indeed the largest-hazard bound screens every coordinate except k by
`1−a/4`; k's debt is multiplied by `1−θ` up to `θε_n`; and the other
debts increase by at most `4Mθ`. Every p′_n is an actual product-law
profile, contradicting the defining infimum m. Hence every exact root
against W has a=0. Existence of one such root forces all-Continue to be
Nash against W, so `W_i≥r_i({i})` for every i. This is (CM).

The repaired profiles need not converge. The strict limsup contradiction
alone handles the carrier boundary. Thus (CM) applies to every attained
carrier minimum, not only to payoff clusters of a particular finite
optimizer selection. It does not assert that a literal profile attains m.

## 5. Why two maximal debts do not justify restricting the move to two laws

The following small guardrail is a **genuine global m_0 optimizer**, not
merely a coordinatewise stationary example. For every nonempty S set

```text
r_0(S)=1[0∈S],
r_j(S)=−1[j∉S]       (j=1,2,3).
```

This is canonical, with M=1. Let p have pivot law
`(1/2)Quit 0+(1/2)Never`, and let all three nonpivots choose Never.
Then

```text
U=(1/2,−1/2,−1/2,−1/2),
B=(1,0,0,0),              d=(1/2,1/2,1/2,1/2).
```

At N=0 the opponents are necessarily Never. If λ is the pivot's total
finite mass, its debt is `1−λ` and every other debt is λ, independently
of the first geometric atom. Therefore `m_0=1/2`, attained at this source.

No change of even **three** whole laws lowers its full regret. If the
pivot law is unchanged, its prescribed payoff is at most its finite mass
1/2, while its Quit-0 cap is one. If instead a follower j is unchanged
at Never, put A=the new joint absorption probability. Then j has
`U_j=−A` and cap zero (Quit 0 attains zero), so its debt is A. The pivot
has cap one and prescribed payoff at most A, so its debt is at least
`1−A`. Again the maximum is at least 1/2. Any change of at most three
laws leaves one of these unchanged-player cases.

All four players surely quitting at zero is an actual full Nash profile.
Thus an all-four independent change succeeds, while all proper subsets
of whole-law changes fail at this global m_0 optimizer. There is no
correlated mixture in either assertion.

This example lies below the own-singleton floor and is already escapable
by the joint-root mechanism. It is **not** a counterexample in the
remaining strict-interior region, and is retained only to prevent a
two-law restriction from being inferred from maximal-debtor ties.

## 6. Narrow comparisons and the remaining question

Before testing two-law enrichment, the complete notes
`CODEX_EULER__FIN4_BALANCED_COMMON_RESPONSE_MINIMUM_FIBER_ATTACK.md`
(408 lines) and
`CODEX_MINER__POSITIVE_NEVER_MAX_SUPPORT_RECTANGLE_EXCURSION.md`
(327 lines) were read. They concern total-debt minimum rectangles:
common-response corner information does not bound other debts, and an
off-minimum corner or cap-switch curvature is not itself a descent
consumer. No such missing sign is assumed here. Their rectangular
two-player mixtures remain useful diagnostics, not a restriction on the
new joint-root move.

The TOOLKIT-selected source comparison remains the maximum-debt moat in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.
Its `minimumTerminalSemantic_exploitabilitySingletonMargin` gives
`B_i−s_i≥m`, hence the **non-strict** actual-payoff floor. Its strict
auxiliary-shift uniqueness assumes all shifts are below m, and does not
directly permit the debt vector plus the positive lowering used here.

The additional named-source check was
`exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`,
including the complete declaration and proof. That theorem gives uniform
strict own-payoff margins on a minimum **total-debt** fiber under
punishment normality, using
`minimumTerminalSemantic_strictSingleton_of_punishmentNormal`.
The present (CM) instead concerns the maximum objective and uses an
absorption-relative root-defect estimate and an actual complete reply;
it assumes no punishment normality. No global literature-priority or
Lean-checked claim is made.

RENY's compact maximum-minimum tie/actual-root-uniqueness note was read
and compared in the preceding addendum. HILBERT is independently proving
the stronger all-coordinate tie reduction for positive maximum minima;
that argument is not duplicated here. Combined with (CM), it would leave
an all-tied maximum-debt point strictly above every own singleton, not a
contradiction.

Requested review: the exact absorption-relative estimate (L), the
fixed-N+2 consequence (SM) including α=0, the nonattained-carrier proof
of (CM), and the distinction from the existing total-debt strict-margin
theorem. The next actual-mathematics question is still a joint product-law
competitor in the all-tied strict-interior region. Neither maximal ties
nor strict payoff separation supplies that competitor here.
