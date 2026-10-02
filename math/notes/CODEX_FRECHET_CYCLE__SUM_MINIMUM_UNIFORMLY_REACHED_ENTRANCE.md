# Uniformly reached prescribed entrance at a positive SUM minimum

Author/reconstructor: `CODEX_FRECHET_CYCLE`.

Status: ordinary-mathematics reconstruction of the second response in
`gpt/APPROX.md`, after an independent audit. The user submission supplies
the argument; this record makes its assumptions and carrier boundary
explicit. No independent review of this rewritten surface or Lean check is
claimed. No export. This is a source theorem for an incoming prescribed
row, not a support-Nash or unbounded-charge producer.

The source file has SHA
`3a7e5b844186f587a454b9a7437aef72dd1a365acea3ccda36f92c0fa6b0258d`;
its second response, beginning “The cap-tight branch can be consumed
explicitly,” has SHA
`d18f8a88bc1928d6e3ae4c11bd5333741aa7e43e356fe662fab5254756698f73`.

## 1. Exact data and the independent capacity input

Fix four players and a reward vector r(S) for every nonempty coalition,
with `|r_i(S)|≤M`, M>0. Players independently choose stopping laws on
`ℕ∪{Never}`. The first finite stopping coalition receives its reward;
all-Never pays zero. All unilateral behavioral deviations are allowed,
equivalently all own stopping laws on the unique live history.

Let U(p) be prescribed terminal payoff, B(p) the unrestricted response
cap, `d_i=B_i−U_i≥0`, and `D=Σ_i d_i`. Let

```text
S=closure{(U(p),B(p)):p is an actual product-law profile},
D_*=min_(u,b)∈S Σ_i(b_i−u_i)=inf_p D(p)>0,
K={z∈S:D(z)=D_*},              s_i=r_i({i}).
```

S and K are compact and nonempty; `|u_i|,|b_i|≤M` on S. These are
minimum **SUM-debt** data. They cannot be replaced by the minimum of the
maximum debt, or by a finite-menu minimum.

The capacity route below uses this precise independent input:

**CAP.** There is a finite common bound on `Σ_(t<H) a(q_t)` for all
finite sequences in the reward box with exact root Nash at v_t and
`v_(t+1)=F(q_t,v_t)`, where F is the actual one-stage payoff map and
`a(q)=1−∏_i(1−q_i)`. No source-anchor reachability is required.

CAP is not the unbounded approximate-packet producer under investigation.
In the project's Fin4 contrary case it follows from
`finFour_quittingFullBoxExactPredecessor_hasFiniteBudget_of_no_uniformPayoff`,
with D_*>0 implying no uniform payoff by
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`.
Section 7 records the exact sources. Equivalently, the equality arm below
can be excluded using already-established strict actual-payoff singleton
isolation under punishment normality; that route is stated separately.

## 2. Prefix identity and the weak minimum cap margin

For a product root q write `c=∏_i(1−q_i)`, `a=1−c`, and
`α_i=∏_(j≠i)(1−q_j)`. Let Q_i(q) be the Quit endpoint and
`C_i(q,v)=A_i^opp(q)+α_i v_i` the Continue endpoint. Put

```text
F_i(q,v)=q_i Q_i(q)+(1−q_i)C_i(q,v),
A_i(q,v)=max(Q_i(q),C_i(q,v)),
g_i(q,v)=A_i(q,v)−F_i(q,v)≥0,
T_q(u,b)=(F(q,u),A(q,b)).
```

T_q is a continuous carrier-preserving map. It is the literal one-root
prefix on actual profiles, extended to S by continuity. Since the
coefficient of v_i in F_i is the joint survival c,

```text
d_i(T_q z)=c d_i(z)+g_i(q,b).                            (1)
```

At every z=(u,b)∈K,

```text
b_i≥s_i+D_* for every i.                                (2)
```

Indeed choose an exact Nash root against `b−t·1`, `0≤t<D_*`.
Its ordinary defect against b satisfies `g_i(q,b)≤t q_i α_i`:
lowering continuation cannot make a supported Continue action less
optimal when the continuation is raised back, and a supported Quit
action then loses at most `tα_i`. Summing (1) gives

```text
D(T_qz)≤cD_*+tΣ_i q_iα_i≤D_*−(D_*−t)a.
```

Minimality forces a=0. All-Continue being Nash against `b−t·1` gives
`b_i−t≥s_i`; let t increase to D_*.

## 3. The equality orbit, exact packet, and uniform strict cap surplus

Suppose `b_k=s_k+D_*` at one z⁰∈K. Set

```text
λ=D_*/[2(D_*+2M)]∈(0,1),
q_k=λ,               q_j=0 for j≠k,
z^(n+1)=T_q z^n.
```

If z^n∈K and its owner cap is unchanged, (2) implies for j≠k

```text
C_j(q,b^n)−Q_j(q)
 =(1−λ)(b_j^n−s_j)+λ[r_j({k})−r_j({k,j})]
 ≥(1−λ)D_*−2Mλ=D_*/2>0.
```

Thus outsiders have zero cap-root defect, while the owner's is λD_*.
Equation (1) gives `D(z^(n+1))=D_*`; the owner's next cap remains b_k.
Induction therefore supplies this orbit for every n, entirely in K.

Define separate packet annotations

```text
v_k^n=s_k,                v_j^n=b_j^n for j≠k.
```

They need not be the prescribed coordinates of z^n. They lie in the
reward box, q is exact Nash against every v^n, and
`v^(n+1)=F(q,v^n)`. For any Q>0, a word of length
`H=ceil(Q/λ)` has zero support error and charge Hλ≥Q. If a punishment
floor P with `P_i≤s_i` is part of the packet contract, then v^n≥P as
well, by (2). Reversing the value chronology gives the usual finite
exact Nash–Bellman block; the root and its charge are unchanged.

CAP excludes this unbounded exact family. Equality in (2) is impossible.
Compactness of K and the finite player set therefore give ρ>0 with

```text
b_i≥s_i+D_*+ρ       for all (u,b)∈K and all i.             (3)
```

There is also an independent isolation-based exclusion, using no CAP:
if every positive SUM minimum already satisfies `u_i>s_i`, the same
equality orbit has
`u_k^n=s_k+(1−λ)^n(u_k^0−s_k)→s_k`. Compactness gives a minimum cluster
with u_k=s_k, contradicting that strict isolation. The checked theorem
`minimumTerminalSemantic_strictSingleton_of_punishmentNormal` supplies
this hypothesis under same-table punishment normality. Thus the strict
cap conclusion also follows from that existing result and the displayed
orbit; it is not logically dependent on the sought approximate producer.

## 4. Deleting a small prescribed row lowers SUM debt

Compactness and (3) give ε₀>0, decreased so `ε₀≤ρ/32`, such that

```text
D(z)≤D_*+ε₀  ⇒  b_i≥s_i+D_*+ρ/2 for every i.             (4)
```

Set `h=min(1/2,ρ/(8M))>0` and `κ=ρ/8`. Suppose an actual profile has
first root q and subsequent actual continuation p⁺, with
`z=T_q z⁺`, `D(z)≤D_*+ε₀`, and `a(q)≤h`. Since
`Q_i(q)≤s_i+2Ma(q)`,

```text
b_i−Q_i(q)≥D_*+ρ/4>0.
```

Hence the front cap's maximizing branch is Continue:
`b_i=C_i(q,b⁺)`. Its cap-root defect is then
`g_i(q,b⁺)=q_i(b_i−Q_i(q))`. Using (1) and Σ_iq_i≥a,

```text
D(z)≥(1−a)D(z⁺)+a(D_*+ρ/4).
```

Consequently

```text
(1−a)(D(z)−D(z⁺))≥a(D_*+ρ/4−D(z))≥(ρ/8)a,
D(z⁺)≤D(z)−κa.                                         (5)
```

Here `1−a≥1/2`, so the continuation is reached with positive probability.
Deletion keeps it in the same near-minimum region. This deletes the
profile's prescribed row; it does not Nashify or otherwise replace it.

The same branch calculation also gives

```text
‖U(z)−U(z⁺)‖∞≤2Ma,
|b_i−b_i⁺|≤2M(1−α_i)≤2Ma.                              (6)
```

Thus both prescribed payoffs and unrestricted caps are controlled.

## 5. A first large row exists, with almost full entry reach

Take any actual p with `D(p)≤D_*+ε`, `0<ε≤ε₀`. Let q_t be its live
root at date t, and let p^[t] be the all-Continue conditional continuation
with time reset. Let T be the first date with a(q_T)>h.

While t<T, (5) applies repeatedly and gives

```text
κΣ_(t<T) a(q_t)≤D(p)−D(p^[T])≤ε.                        (7)
```

To see T is finite, suppose every row were small. The same bound at
every cutoff would make Σ_ta(q_t) finite. The conditional probability
of any absorption after date t is then at most Σ_(s≥t)a(q_s)→0, so
`U_i(p^[t])→0`. But (4), nonnegative debts, and
`d_i≤D(p^[t])≤D_*+ε₀` give

```text
U_i(p^[t])≥s_i+ρ/2−ε₀.
```

Some s_i is positive: otherwise all-Never is an exact terminal Nash
profile and D_*=0. The two conclusions contradict one another for that
player. Therefore T<∞.

All prior roots have survival at least 1/2, so these conditional sources
are genuine reached actual continuations. From (6)–(7) and the product
survival estimate,

```text
Σ_(t<T)a(q_t)≤8ε/ρ,
D(p^[T])≤D(p),
Pr_p(reach T)≥1−8ε/ρ,
‖(U(p),B(p))−(U(p^[T]),B(p^[T]))‖∞≤16Mε/ρ.               (8)
```

The sup norm in the last line is on both complete vectors. No uniform
bound on the date T is asserted.

There are fifteen nonempty coalitions. Some S has root probability
greater than h/15 at T. Since ε≤ρ/32 gives entry reach at least 3/4,

```text
Pr_p(first stopping coalition S occurs at date T)>h/20.   (9)
```

This is an unconditional stage-atom floor in the original profile, not
only a conditional atom in a rare suffix.

## 6. Same-source carrier representation, without Nash or attainment

Let actual semantic pairs of p_n converge to any z_*∈K. Choose ε_n↓0
dominating their nonnegative excess debt, and take the T_n above. Then
the shifted pairs still converge to z_* by (8), their original entry
reaches tend to one, and their first roots have absorption greater than h.

Compactness permits one common subsequence with `q_(n,T_n)→q_*` and
the post-row continuation pairs converging to `z⁺∈S`. If the large row
has zero joint survival, use the continuation specified by the complete
behavioral profile; no positive-reach conditional assertion is made for
that post-row tail. Its semantic pair is still an actual carrier member.
Continuity of T gives

```text
z_*=T_(q_*) z⁺,                a(q_*)≥h>0.               (10)
```

A further subsequence fixes the coalition S in (9). All approximating
objects retain the same original profile and cutoff ancestry.

The limit z⁺ is a **carrier point** and need not be realized by any
actual law. Neither q_* nor its approximating prescribed rows are
asserted Nash against their continuation payoffs. The exact relation is

```text
D_*=c(q_*)D(z⁺)+Σ_i g_i(q_*,b⁺).
```

It allows an off-minimum continuation, positive cap-root regret, or
both. No support-error control against u⁺ follows. Substituting a Nash
root would change the front semantic point and its source identity.

## 7. Source comparison and precise remaining step

The narrow route was TOOLKIT's literal minimum/cap moat, minimum-fiber
isolation, and finite exact-capacity entries. Inspected declarations:

- `nearMinimumTerminalSemantic_auxiliaryNash_budget`,
  `nearMinimumTerminalSemantic_constantShiftNash_absorption`, and
  `nearMinimumTerminalSemantic_cap_sub_singleton_ge` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCapNashNearMinimum.lean`:
  the weak cap margin and its near-minimum auxiliary-root budget are old.
- `minimumTerminalSemantic_strictSingleton_of_punishmentNormal` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumLawFiniteAtom.lean`,
  and `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal`
  in `TerminalSemanticFinFourMinimumFiberIsolation.lean`: strict and
  uniform actual-payoff isolation already hold for SUM minima under
  normality. The fixed-row method is also present on the singleton-tight
  unique-debtor face in `TerminalSemanticSingletonTightMinimumFaceIteration.lean`.
- `lawTightCapNashMinimumFace_globalMinimumOriginDebtMoat` in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashGlobalMinimumMoat.lean`:
  its supplied hull minimum retains the weak cap margin; it does not
  supply the same-source deletion/entry estimates (8).
- `quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum` and
  `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
  in `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`.
- `finFour_quittingFullBoxExactPredecessor_hasFiniteBudget_of_no_uniformPayoff`
  in `UniformEquilibrium/Diagnostics/Quitting/FinFourFullBoxExactPredecessorCapacity.lean`,
  through `finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
  and `quittingFullBoxExactPredecessor_hasFiniteBudget_of_boundedHazardCapacity`.
  The full-box edge definitions and reversed finite-block adapter were
  inspected. This capacity does not require reachability from a chosen
  anchor and does not assume the approximate-packet producer.
- `exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff`
  in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect.lean`:
  this existing theorem concerns approximate roots at prescribed minimum
  payoffs, not incoming prescribed rows from possibly off-minimum tails.

The prospective additional source result is (8)–(10), uniform over every
near-minimizing actual profile / every realizing sequence. No matching
statement was found in this bounded source set. The strict cap surplus
is a useful consequence of existing isolation plus the displayed orbit,
not a replacement for the earlier SUM isolation work. The recent owned
MAX results have a different objective and cannot be substituted here.

Remaining step: turn the incoming prescribed row into a source-matched
support-Nash charged packet or an actual strict debt improvement. This
record does not attempt that step and does not assert a uniform payoff,
positive counterexample, or full producer.
