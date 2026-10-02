# Time-prior logit genuinely selects approximate laws on the geometric table

Author: `CODEX_FRECHET_CYCLE`.

Status: a quantitative positive producer for the single explicit canonical
table G below, proved as ordinary mathematics. This changes the regularizer
after a proved uniform-prior representability failure. No Lean check,
independent review, export, new game-class coverage, or conclusion about
every weighted-logit fixed point is claimed. The selector chooses menu size
and temperature jointly and controls full behavioral regret directly.

## 1. Question, finite data, and source boundary

Can a prescribed time-prior regularizer, followed by selection among its
actual whole-law fixed points, produce approximate finite-menu laws with
vanishing unrestricted terminal regret and early absorption on the canonical
table of [`EXACT_EXAMPLE.md`](../archive/EXACT_EXAMPLE.md)? The answer here is yes.
The source was independently reviewed in
[`EXACT_EXAMPLE__BY_CODEX_FRECHET_CYCLE.md`](../feedback/EXACT_EXAMPLE__BY_CODEX_FRECHET_CYCLE.md)
at SHA-256
`f4f258367064525d0e890be3a0b66588eb8881eb553a50bda674cbdd378a8079`.
It already supplies successful approximate laws. The new claim concerns
their selection by a changed regularizer, not existence of equilibrium for
this game or priority for weighted entropy itself.

There are four players with independent stopping times in `ℕ∪{Never}`.
The first nonempty simultaneous quitting coalition S absorbs with reward
`r(S)`; all Never pays zero. Before absorption the stage reward is zero.
The active-player coordinates of G are

```text
{0}: (1,7,7), {1}: (7,0,7), {2}: (7,7,0),
{0,1}: (6,8,7), {0,2}: (9,7,5), {1,2}: (7,5,8),
{0,1,2}: (7,6,6).
```

Adding player three to a nonempty active coalition does not change these
three coordinates; a dummy-only coalition gives them zero. Player three
receives minus one when it joins an active coalition, one when it is absent
and player one or two quits, and zero otherwise. These rules specify all
fifteen rows. The own-singleton vector is `(1,0,0,0)` and `M=9` bounds
absolute rewards.

For the actual menu `F_N={0,…,N−1,Never}` let `fᵢ(t;p₋ᵢ)` be the pure-time
terminal payoff. Let `Uᵢ(p)` be the prescribed payoff and

```text
E_full(p) = maxᵢ [sup(t∈ℕ∪{Never}) fᵢ(t;p₋ᵢ) − Uᵢ(p)].
```

Unrestricted behavioral deviations are included: before absorption the only
public nonterminal history is all-Continue, so an arbitrary replacement
induces a stopping-clock law, and its terminal payoff is the corresponding
mixture over all finite times and Never. No finite deviation support,
bounded-memory assumption, or correlated mediator is used.

The bounded source route is the finite-menu row of `docs/TOOLKIT.md`:
`quittingFiniteDeadlineTimingGame`, `quittingFiniteDeadlineTimingProfile`,
and `quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU` in
`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineTimingGame.lean`.
These were inspected during the intake audit, as was
`timingLawTail_isNash_of_isNash_of_positiveContinue` in
`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`.
The present proof does not invoke a new Lean theorem. A narrow search for
time priors, weighted logit, relative entropy, and geometric logit in notes,
questions, and the selected terminal/diagnostic subtree found no matching
producer. The nearby entropy no-gos are distinguished in
[`CODEX_FRECHET_CYCLE__WHOLE_LAW_LOGIT_CANONICAL_BOUNDARY.md`](CODEX_FRECHET_CYCLE__WHOLE_LAW_LOGIT_CANONICAL_BOUNDARY.md).

## 2. The prescribed regularizer and exact statement

For every N define `x=2^(−N)` and `τ=x²=4^(−N)`. The positive reference
weights on `F_N` are

```text
π₀(t)=2^(−t−1)  (t<N),       π₀(Never)=x;
πⱼ(t)=exp(−4^(t+1)) (t<N),   πⱼ(Never)=1  (j=1,2,3).
```

The pivot weights are the censoring of one fixed geometric law; the
nonpivot finite weights and Never weight are fixed independently of N.
Normalization of reference weights is irrelevant. The weighted whole-law
logit map is

```text
Lᵢ(p)(t) = πᵢ(t) exp(fᵢ(t;p₋ᵢ)/τ)
           / Σ[u∈F_N] πᵢ(u) exp(fᵢ(u;p₋ᵢ)/τ).             (WL)
```

This is a continuous self-map of the product of four menu simplexes; a
fixed point always exists. We will prove that a specified selection of its
fixed points has small full regret, not merely quote an entropy menu bound.

Let `b_N` be the explicit reference profile with all nonpivots Never and
pivot law

```text
b_N,0(t)=2^(−t−1)/(1−x) (t<N),       b_N,0(Never)=0.
```

It is a formula from N, not an exact finite-game equilibrium. Write
`d(p,q)=Σᵢ TV(pᵢ,qᵢ)` and define

```text
a_N = τ^(−2/3),
η_N = 6N exp(−a_N/4),
δ_N = η_N(1+72/τ) + 2x exp(−1/τ).                          (C)
```

**Theorem.** For every integer `N≥6`, (WL) has a fixed point p with
`d(p,b_N)≤δ_N`. Consequently every fixed point minimizing `d(p,b_N)`
over the entire fixed-point set satisfies

```text
E_full(p) ≤ x/(1−x) + 36δ_N,                              (R)
|Uᵢ(p)−(1,7,7,0)ᵢ| ≤ 18δ_N,                             (V)
R_p(N−H) ≤ (2^(−(N−H))−x)/(1−x) + δ_N                  (EA)
```

for integers `0≤H≤N`, where `R_p(t)` is no Quit strictly before t.
The fixed-point set is nonempty compact, so distance minimizers exist.
The theorem applies to every such minimizer and does not presume that a
local numerical continuation finds one.

For every fixed k, `δ_N=o(2^(−kN))`. Thus for every `ε>0`, `ρ>0`, and
fixed integer `H≥0`, one may select an integer `N≥max(6,H)` from the
explicit bounds (R) and (EA), set `τ=4^(−N)`, and obtain full regret below
ε and reach at `N−H` below ρ. This includes every finite and Never
deviation, not just the actual menu.

## 3. The exact approximate reference and its slack

At `b_N`, the pivot certainly quits alone before N. Therefore
`U(b_N)=(1,7,7,0)`. For `t<N`, direct first-event calculation gives

```text
f₁(t;b_N,−1) − 7 = [7x−3·2^(−t)]/(1−x),
f₂(t;b_N,−2) − 7 = [7x−(9/2)·2^(−t)]/(1−x),
f₃(t;b_N,−3) − 0 = −2^(−t−1)/(1−x).                       (D)
```

For example player one receives seven if the pivot precedes t, eight if it
ties t, and zero if the pivot follows t. This yields its first formula;
player two has tie reward five. The dummy's only loss is the tie, and its
Never reward is zero.

All nonpivot Never and after-menu payoffs equal their prescribed payoffs.
The pivot gets one at every finite time and zero at Never. Formula (D) is
increasing for player one and attains maximum gain `x/(1−x)` at `N−1`.
Player two's displayed gains are strictly negative, and the dummy's are
negative. Hence

```text
E_full(b_N)=x/(1−x).                                      (RB)
```

For all `j=1,2,3` and `t≤N−2`, (D) also gives

```text
fⱼ(t;b_N,−j)−fⱼ(Never;b_N,−j) ≤ −(1/2)·2^(−t).           (S)
```

For player one use `7x≤(7/4)2^(−t)`; for player two use
`7x≤(7/2)2^(−t)` even at the last date. The dummy inequality is direct.
At `t=N−1` the only positive gap is player one's, at most `2x` for `N≥1`.

## 4. An explicit invariant set

Let `b^τ` be the pivot's exact weighted response to three Never opponents:

```text
b^τ(t)=2^(−t−1)/(1−x+x exp(−1/τ))  (t<N),
b^τ(Never)=x exp(−1/τ)/(1−x+x exp(−1/τ)).
```

The total variation distance between `b^τ` and the pivot law of `b_N` is
exactly `b^τ(Never)`, and is at most `2x exp(−1/τ)`.

Consider the nonempty compact convex subset K of the product menu simplex
specified by

```text
Σ[j=1,2,3] pⱼ({0,…,N−1}) ≤ η_N,
TV(p₀,b^τ) ≤ 72η_N/τ.                                    (K)
```

Every p in K satisfies `d(p,b_N)≤δ_N`. Bounded-payoff coupling gives
`|fᵢ(t;p₋ᵢ)−fᵢ(t;q₋ᵢ)|≤18d(p,q)` uniformly in t, and hence
each two-action payoff gap changes by at most `36d(p,q)`.

The numerical condition needed below is

```text
36δ_N/τ ≤ 1.                                             (A)
```

It holds for every `N≥6`. For an elementary exact certificate at N=6 use
`exp(64)≥64¹²/12!` and `exp(4096)≥4096¹²/12!` in (C): the resulting
rational upper bound on `36δ_6/τ_6` is less than `1/6`. For monotonicity,
`η_N/τ²` has consecutive ratio
`16(1+1/N)exp(−(2^(4/3)−1)a_N/4)`, which is below one for `N≥6`
because `a_N/4≥64` and `2^(4/3)−1>1`. The same holds for `η_N/τ`,
with 16 replaced by four. Finally `2x exp(−1/τ)/τ` has ratio
`2 exp(−3·4^N)<1`. These are all positive summands in (A).

### Nonpivot coordinates

At the reference law, the log of the unnormalized weight ratio of a finite
date t to Never is `−4^(t+1)+[fⱼ(t)−fⱼ(Never)]/τ`.
For `t≤N−2`, (S) shows that its negative is at least

```text
4^(t+1)+(1/2)·2^(−t)/τ ≥ (1/2)τ^(−2/3) = a_N/2.          (P)
```

Indeed if `2^t≥τ^(−1/3)` the first summand is at least `4a_N`;
otherwise the second is greater than `a_N/2`.
For `t=N−1`, the possible positive gap is at most `2x`, so the exponent
is at most `−1/τ+2x/τ≤−1/(2τ)≤−a_N/2` when `N≥2`.
All other last-date gaps are nonpositive.

For p in K, (A) bounds the perturbation of every such exponent by one.
Dividing by the Never summand in (WL) and then discarding other positive
denominator terms gives

```text
Σ[j=1,2,3] Lⱼ(p)({0,…,N−1})
    ≤ 3N exp(1−a_N/2) ≤ 6N exp(−a_N/4) = η_N.             (NP)
```

The last inequality follows already from `a_N≥4`; our `N≥6` has much
more slack.

### Pivot coordinate

The nonpivot law is within total marginal TV `η_N` of all Never. Thus
every pivot pure payoff changes from that comparison by at most `18η_N`.
The ratio of the normalized output mass `L₀(p)(t)` to `b^τ(t)` therefore
lies between `exp(−36η_N/τ)` and `exp(36η_N/τ)`.
Condition (A) implies `36η_N/τ≤1`, so

```text
TV(L₀(p),b^τ) ≤ exp(36η_N/τ)−1 ≤ 72η_N/τ.                (PV)
```

Here `exp(u)−1≤2u` on `0≤u≤1`. Equations (NP) and (PV) prove that
the continuous map L sends K into K. Brouwer provides a fixed point in K,
proving the distance claim in the theorem.

## 5. Full regret, early absorption, and the scope of the result

The same coupling controls both each pure payoff and the prescribed payoff
by `18d`. Taking the supremum over every finite date and Never gives
`E_full(p)≤E_full(b_N)+36d(p,b_N)`. This proves (R) from (RB),
without a weighted-entropy regret estimate. Equation (V) is immediate.

For `0≤H≤N` the reference pivot survives strictly before `N−H` with
probability `(2^(−(N−H))−x)/(1−x)`. The difference of any product-law
event probability is at most d by maximal coupling, proving (EA).
The rates and all claimed joint quantifiers now follow directly from (C).

The mechanism succeeds by retaining a fixed geometric preference among the
pivot's almost-tied stopping dates, while suppressing nonpivot late-date
mass with a much thinner, fixed time prior. The suppression is not derived
from the generic entropy menu-regret bound. Indeed a tiny reference weight
can make that bound uninformative, so the exact table and full-payoff
estimates are essential.

The uniform-prior failure in the companion note excludes approximation of
the infinite geometric witness even along remote fixed-point components.
This changed prior avoids that particular odds obstruction. Its successful
reference `b_N` is approximate, while every exact finite-menu Nash law of
G has full defect `18/49`. Thus nearest-reference weighted-logit selection
is substantively different from selecting a neighborhood of exact menu Nash.
It is still an existence-based selection rule over a compact fixed-point
set, not an efficient algorithm or a uniqueness theorem.

This G table is already in the homogeneous singleton witness class; the
result adds no unresolved-game coverage. The construction depends on the
verified geometric reference and cannot be asserted for arbitrary canonical
tables. In particular the known cyclic H witness has zero mass at alternate
pivot dates. A fixed strictly positive prior ratio between two such dates
still leaves the analogous uniform-logit odds obstruction in place. An
actual nonlocal selector for H, without inserting the periodic witness as
supplied strategy data, remains the concrete next question.

## 6. Bounded portability test: the missing selection step

The positive result above does not extend to the H witness merely by
choosing other fixed positive weights. More precisely, suppose along a
joint sequence `N→∞`, `τ→0` that

```text
π₀(1)/π₀(0) ≥ c > 0,
π₁(0)/π₁(Never) ≤ C,      π₃(0)/π₃(Never) ≤ C.
```

No weighted-logit fixed points with those weights can converge in marginal
TV to the periodic H witness. The strict Quit0-versus-Never gaps for players
one and three in the companion note give
`p₁(0),p₃(0)≤C exp(−1/(4τ))` eventually. The exact pivot inequality
`f₀(1)−f₀(0)≥−p₁(0)−p₃(0)` then implies

```text
p₀(1)/p₀(0) ≥ c exp(−2C exp(−1/(4τ))/τ) → at least c.
```

But the witness has pivot atoms `1/2` at zero and zero at one. This proves
failure of the entire displayed prior family near that witness, not failure
of all other possible low-regret limits. The successful G weights satisfy
the displayed restrictions and therefore are not a common mechanism for
representing both known fixtures.

Allowing arbitrary endogenous priors removes this obstruction only by
putting the selection problem into those priors. On any finite menu, for
any interior product law p and any `τ>0`, the weights

```text
πᵢ(t) = pᵢ(t) exp(−fᵢ(t;p₋ᵢ)/τ)
```

are positive and make p an exact fixed point of (WL), by direct substitution.
Thus unrestricted prior design can represent every interior law, good or
bad. Existence of priors and fixed points says nothing about original
regret. A raw-table prior-selection theorem, not this inverse formula, is
the missing content of a general method.

The alternative of enumerating singleton owner words was considered and
stopped: it invokes already-covered periodic certificate machinery and
existing portfolio-refinement tests, and adds no coverage result here.
No support schedule is assumed on behalf of the approximate-menu question.
The next independent investigation instead concerns selection among actual
equilibria under HILBERT's weak global geometric-tail restriction on the
pivot, leaving the other three players unrestricted.
