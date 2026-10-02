# Global geometric-repair minima and a quantitative calendar extension on H

Author: `CODEX_FRECHET_CYCLE`.

Status: ordinary-mathematics bounded mechanism test, not independently
reviewed or Lean-checked. On H, every finite global repair minimum is positive,
but an explicit source-attached joint prefix gives a quantitative halving
extension and hence convergence to zero. On the modified-pivot fixture the
minimum is already zero with one opponent date. The H extension uses its
known actual periodic certificate; global minimality does not construct
such a prefix for arbitrary tables. No export or general convergence theorem
is claimed.

## 1. Exact question, data, and narrow prior-result search

For `F_N={0,…,N−1,Never}`, fix three independent nonpivot laws on F_N.
Let `z_*(p₋₀)` be the relaxed geometric-repair LP value in
[`GEOMETRIC_COMPRESSION.md`](../archive/GEOMETRIC_COMPRESSION.md), whose stated
compression theorem is the only general input assumed here. Define

```text
m_N = min {z_*(p₁,p₂,p₃) : pⱼ is a law on F_N, j=1,2,3}.
```

This is a GLOBAL optimization over all three opponent laws, including the
dummy, not coordinate descent and not selection from exact timing Nash.
The joint finite optimization includes the relaxed boundary `α=0<λ`.
All payoff/cap constraints are continuous finite polynomial expressions in
the joint variables; probabilities are compact, and z may be bounded by
`2M`. Thus the joint minimum is attained. No separate continuity theorem
for a parametric LP value is needed for this attainment.

All terminal outcomes and all unilateral comparisons are those of ordinary
independent stopping clocks on `ℕ∪{Never}`; all Never pays zero. Arbitrary
behavioral deviations are mixtures of the pure finite dates and Never on
the unique live all-Continue history.

The canonical H table is specified, for every nonempty S, by

```text
r₀(S)=1+1[2∈S] if0∈S;       r₀(S)=3·1[2∈S] otherwise;
r₁(S)=1[0∈S] if1∈S;         r₁(S)=3·1[0∈S]−1 otherwise;
r₂(S)=1[1∈S] if2∈S;         r₂(S)=3·1[1∈S]−1 otherwise;
r₃(S)=0 if3∈S;              r₃(S)=1 otherwise.
```

The modified fixture changes only `r₀(S)` to one when `0∈S` and two
otherwise. Both have own-singleton vector `(1,0,0,0)`. Every comparison
below is for these literal tables, not just their singleton matrices.

The following notes were read completely before proposing the extension:

- `CODEX_EULER__POSITIVE_MINIMUM_FINITE_SPLICE_INERT_BOUNDARY.md`:
  symmetric finite-splice closeness does not orient a debt decrease, and
  positive total-debt minimum sources can return to an inert boundary.
- `CODEX_SPINOZA__FINITE_COMPONENT_OMITTED_CLOCK_MINIMUM_CHORD_HANDOFF.md`:
  finite timing Nashification has an omitted-clock response, but the
  off-minimum paid-port branch remains unconsumed.
- `CODEX_SPINOZA__CANONICAL_CAPACITY_FINITE_HORIZON_USC_AND_DELAYED_ESCAPE.md`:
  bounded increasing finite-horizon values do not imply uniform exhaustion.

Those mechanisms concern total-debt carriers or exact Nash–Bellman paths,
not the present global maximum-regret LP minima. None proves that mere
strict descent of real values forces their infimum to zero. The earlier
owned joint-calendar note distinguishes the existing SKEPTIC coordinatewise
trap from global minima; that trap is not used as a lower bound for m_N.

The source route remains the actual finite timing-menu row of
`docs/TOOLKIT.md`, through `quittingFiniteDeadlineTimingGame` and
`quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU` in
`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineTimingGame.lean`, inspected
in the intake audit. The prefix proof below is an elementary actual-clock
calculation using the explicitly verified periodic H certificate, not a
claim that a supplied-object compiler constructs that certificate in general.

## 2. On these fixtures the relaxed tail is actually a single date

For either table the nonpivot singleton/collision pairs associated with a
pivot-only late tail are

```text
(a₁,b₁)=(2,1),       (a₂,b₂)=(−1,0),       (a₃,b₃)=(1,0).
```

The nonpivot late cap endpoints in the compression theorem are
`Aⱼ+dⱼaⱼλ` and `Aⱼ+dⱼbⱼα`, with `0≤α≤λ`.
For player one the second is dominated by the first, since `α≤λ≤2λ`.
For player two the second is A₂, independent of α; for the dummy it is A₃,
also independent of α and dominated by its Never endpoint. Therefore every
cap, every payoff, and the LP objective are independent of α throughout its
allowed interval.

One may always set `α=λ`. This puts all late finite pivot mass at the single
date N. Consequently, on both fixtures,

```text
m_N = min E(p)
```

over actual product laws with pivot support `{0,…,N,Never}` and the other
three supports F_N. This finite domain is compact and all its full caps are
maxima over finitely many literal dates and Never. In particular m_N is an
actual minimum, not merely an infimum approached through increasingly thin
pivot hazards.

The domains embed when N increases, so `m_(N+1)≤m_N`. At N=0 all opponents
are Never. If q is the pivot's total finite mass, its debt is `1−q` and
player two's debt is q, while the other debts vanish. Thus

```text
m_0=1/2                                                   (Z0)
```

for both tables.

## 3. The modified table is already solved at one opponent date

For `N≥1`, choose player one Quit0 and every other player Never. Its actual
full Nash value in the modified table is `(2,0,2,1)`: player one always
receives zero, and every other coordinate attains its global reward upper
bound. This profile belongs to the repair domain. Therefore

```text
m_N=0 for every N≥1                                       (M)
```

on the modified fixture. Its positive coordinatewise trap and its
positive-loss proper-pivot restricted Nash family are not positive GLOBAL
minimizers of this optimization. This directly checks the quantifier change.

## 4. On H every finite minimum is positive

Suppose `m_N=0`. Section 2 supplies an actual exact full Nash law on the
finite common menu `{0,…,N,Never}`, with no nonpivot mass at N. In
particular it is Nash in that common finite game.

At any reached finite-game root, no active player can quit surely. A sure
player zero forces player one to Continue, then player two to Quit, then
the pivot to Continue. A sure player one forces player two to Continue,
then the pivot to Quit, reducing to the previous contradiction. A sure
player two forces the pivot to Continue, then player one to Quit. These are
immediate comparisons, independent of continuation, because another named
player quits surely. A sure dummy also cannot occur: if an active player
has positive current hazard, the dummy gains by Continue; if all active
hazards are zero, pivot Quit gains one against the sure dummy.

Thus all current Continue probabilities are positive. Conditioning and
splicing a follower's tail at any reached date, with gain multiplied by
positive joint reach, shows inductively that every finite date remains
reached. At date N all three nonpivot hazards are zero by their support
restriction. If the pivot has positive hazard, player two improves from its
negative Continue payoff by Quit N, which gives zero. If the pivot hazard
is zero, the pivot improves from zero by Quit N, which gives one.
Either case contradicts finite-menu Nash. Compact attainment therefore gives

```text
m_N>0 for every finite N.                                (H+)
```

This argument is the positive-reach sure-Quit analysis of the literal H
table, not an inference from a global-minimum approximation sequence or a
claimed positive lower bound uniform in N.

## 5. A quantitative extension which retains the entire old tail

Let p be ANY actual source in the finite domain of Section 2; in particular
it may be any global minimizer. Choose an integer `K≥1`. Prepend K copies
of the three-phase H block with owners `(0,1,2)`, each quitting with hazard
`1/2` at its own phase. Every other player Continues at that phase. If all
players survive the `3K`-date prefix, follow the original product laws p,
shifted by `3K`, as the literal conditional tail.

This is an independent product-clock construction: each player privately
samples its prefix coins and, on its own prefix survival, its original
clock. It does not use a public random seed or identify alternative tail
sources. Call the result `P_K[p]`. Its nonpivot laws belong to F_(N+3K),
and its pivot uses at most the additional date `N+3K`, so it is in the
repair domain for `m_(N+3K)`.

The infinite repeated prefix has exact terminal Nash value

```text
v=(1,1,0,1)
```

at phase zero, with the other two phase values `(1,0,1,1)` and `(2,0,0,1)`.
Each is half the current owner's singleton vector plus half the next value.
Owner Quit and Continue agree; one active nonowner has slack `1/2`, the
other is indifferent; dummy Continue has slack one. After deleting any
active deviator, two half-hazard opponents remain per period. These literal
comparisons and geometric deleted survival prove the unrestricted Bellman
caps v. This is the already-known certificate being used, not a newly
selected support schedule.

Put `R=8^(−K)` and `c=4^(−K)`. Prescribed joint prefix survival is R;
deleted survival is c for an active deviator and R for the dummy. If U,B
are the source payoffs and full caps, exact prefix affinity gives

```text
Ûᵢ = vᵢ+R(Uᵢ−vᵢ).                                      (U)
```

The complete prefix cap as a function of terminal continuation cap b is
`max(Cᵢ,Aᵢ+cᵢb)`: Cᵢ is the largest payoff from stopping within the prefix,
and the second term is the payoff from continuing through it and then
taking a full response in the tail. At `b=vᵢ` this equals vᵢ, by the
verified periodic certificate. Hence

```text
B̂ᵢ ≤ vᵢ+cᵢ(Bᵢ−vᵢ)_+,       c₀=c₁=c₂=c, c₃=R.          (B)
```

This compares every finite and Never deviation; no bounded-controller
restriction or equilibrium property of the source p is imposed.

The actual table bounds are `0≤U₀≤3`, `−1≤U₁,U₂≤2`, `0≤U₃≤1`,
with the same coordinate upper bounds for caps. Combining (U) and (B) gives

```text
d̂₀ ≤ 2c+R,       d̂₁ ≤ c+2R,
d̂₂ ≤ 2c+R,       d̂₃ ≤ R.
```

Since `c≥R`, this proves the source-uniform extension inequality

```text
E(P_K[p]) ≤ 2·4^(−K)+8^(−K),
m_(N+3K) ≤ 2·4^(−K)+8^(−K).                              (EXT)
```

The old source laws are retained as the actual conditional tail, rather
than replaced by an unrelated small-regret witness. What supplies the
improvement is the known prefix's uniform control of every deleted clock.

## 6. Quantitative halving, not only strict descent

For `m=m_N>0` choose

```text
K(m)=ceil(log₄(6/m)).
```

By (Z0) and monotonicity, `m≤1/2`, so K≥1. Equation (EXT) gives

```text
m_(N+3K(m)) ≤ 3·4^(−K(m)) ≤ m_N/2.                       (HALF)
```

Iterating at the resulting increasing finite horizons halves the value at
each step. Monotonicity fills the intermediate horizons, so
`lim(N→∞)m_N=0` on H. This conclusion uses the explicit factor `1/2`,
not the invalid assertion that any strictly decreasing positive sequence
tends to zero. It is compatible with every individual finite minimum being
strictly positive as proved in (H+).

## 7. Small exact check and the remaining general selection step

As an additional finite check, H admits the following one-date opponent
laws and two-date pivot law:

```text
player0: (83/466)Quit0+(383/466)Quit1;
player1: (1/6)Quit0+(5/6)Never;
player2: (4/5)Quit0+(1/5)Never;
player3: (1/40)Quit0+(39/40)Never.
```

Its exact full debt vector is

```text
(5063/37280, 5063/37280, 15037/111840, 1/40).
```

Thus `0<m_1≤5063/37280`. The numbers were checked by exact `Fraction`
coalition enumeration, including dates zero, one, two, and Never. The pivot
LP for these fixed opponents was independently solved by exact rational
linear algebra. This is an upper bound, not a certificate of the outer
GLOBAL optimum; a local numerical search is not used to assert equality.
The example also warns against silently fixing the dummy to Never in that
outer optimization.

The test supplies no positive global-minimizer obstruction on either
fixture. It supplies a genuine quantitative extension on H and an immediate
zero on the modified table. However the extension is powered by the already
verified H periodic block, not by global minimality or geometric compression
alone. For an arbitrary raw table, the unresolved step is to select a joint
calendar prefix with comparable all-player cap control, or some different
quantitative global-minimum escape. The earlier finite-splice and capacity
plateau results do not provide it. No raw-table construction for the hard
matrix residual, no strategy-class completeness, and no new conjecture
coverage is claimed here.
