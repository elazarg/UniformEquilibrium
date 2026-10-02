# Normal-floor elimination and a fixed reset exit from the summable waist

Author: CODEX_GROMOV

Independent reviews:
[CODEX_HAHN](../feedback/CODEX_GROMOV__SUMMABLE_WAIST_NORMAL_FLOOR_AND_RESET_EXIT__BY_CODEX_HAHN.md),
[CODEX_SPINOZA](../feedback/CODEX_GROMOV__SUMMABLE_WAIST_NORMAL_FLOOR_AND_RESET_EXIT__BY_CODEX_SPINOZA.md)

The reviewed source note is frozen at SHA-256
`b1425eead9f69f695bef8a1e1b69d02327bc010de7cd06760aba66c0047948ab`.
Both reviews record a PASS on that exact revision.

## Exact statement

Consider a finite quitting game. For a product root `x`, write `A(x)` for
its probability of absorption, and for player `i` write `s_i(x)` for the
probability that every opponent of `i` Continues. Let `F_x(v)` be the root
Bellman action on a continuation vector `v`. A root is exact Nash against
`v` when no player can improve at that root by changing its Boolean marginal.

Let `chi_i` be player `i`'s behavioral punishment value and let `r_i({i})`
be its singleton reward. Call `i` normal when

```
chi_i <= r_i({i}).
```

The packet proves the following three claims.

### Theorem A: normal-floor elimination

Let `(v_t,x_t)`, for `t >= 0`, be a bounded exact Nash--Bellman tail:

```
v_t = F_{x_t}(v_{t+1}),
x_t is exact Nash against v_{t+1}.
```

If

```
sum_t A(x_t) < infinity,
```

then every normal player is above its punishment floor at every date:

```
chi_i <= v_t(i)  for all t.
```

Consequently, in the four-player all-normal hard residual, the checked
alternative "eventual punishment-floor violation with summable absorption"
is impossible.

### Theorem B: singleton-wall exact exit

Let `y=(W,B)` be an actual terminal-semantic carrier point. Suppose all
terminal reward coordinates and all coordinates of `W` have absolute value
at most `M`, where `M>0`. Put

```
d_i(y) = B_i - W_i,
D(y)   = sum_i d_i(y).
```

Suppose, for one player `j` and positive numbers `d0, epsilon`, that

```
d_j(y) >= d0,
W_j <= r_j({j}) - epsilon.
```

For every exact product root `x` against `W`, the actual carrier prefix
`y' = T_x(y)` satisfies

```
D(y) - D(y') >= c(d0,epsilon,M),
A(x) >= a(epsilon,M),
```

where

```
c(d0,epsilon,M)
  = min { d0, epsilon/2, epsilon*d0/(8*M) } > 0,

a(epsilon,M)
  = min { 1, epsilon/(8*M) } > 0.
```

This statement quantifies over every exact root against the displayed actual
payoff. It is not a selected-root or stationary-deviation statement.

### Theorem C: infinite cap resets give a fixed-capacity exact exit

Let `zeta^n` be actual terminal profiles satisfying the literal nesting

```
zeta^(n+1) = bar_q^n :: zeta^n.
```

Assume the sum of all marginal Quit hazards in the roots `bar_q^n` is finite.
Fix a player `j` and `delta>0` such that, eventually,

```
d_j(zeta^n) >= delta.
```

Assume that at infinitely many transitions, called resets, Quit immediately
is an attained complete behavioral cap for `j` at `zeta^(n+1)`.

Then, at every sufficiently late reset child,

```
U_j(zeta^n) <= r_j({j}) - delta/2.
```

Every exact product root against that child's actual prescribed payoff
therefore gives a literal exact Nash--Bellman prefix with

```
total debt drop >= c_delta,
joint absorption >= a_delta,
```

where

```
c_delta = min { delta, delta/4, delta^2/(16*M) } > 0,
a_delta = min { 1, delta/(16*M) } > 0.
```

If `D_*` is the global minimum of total terminal-semantic debt on the actual
carrier, every sufficiently late reset child satisfies

```
D(zeta^n) >= D_* + c_delta.
```

Thus the infinite-reset branch is a uniformly absorbing, fixed-debt-spending
exact temporal exit. The theorem does not assert that its prefixed descendant
retains the nested cap-child genealogy.

## Conjecture-facing change

This packet strictly narrows two live obligations:

- `FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION`: in the all-normal hard
  residual, the under-punishment side of the checked summable-tail
  alternative is eliminated. Only the floor-safe summable tail remains.
- `FIN4_QUANTITATIVE_PAID_PORT_CONSUMER`: in the reviewed nested cap-child
  reduction, the infinite-reset arm is no longer a static cap toggle. It has
  a literal exact root edge with fixed positive absorption and fixed positive
  total-debt expenditure.

The remaining branches are the floor-safe all-summable port and the eventual
shifted-cap packet. To close the reset branch recursively one must also prove
that the exact-prefix descendant regenerates the source passport; this packet
does not supply that renewal.

## Definitions and assumptions

All root laws are independent products of Boolean Quit/Continue marginals.
The Bellman root game observes only the public all-Continue history and uses
the supplied continuation payoff after joint Continue. Exact root Nash
allows arbitrary changes of one player's root marginal.

The terminal-semantic cap `B_i` is the supremum over all behavioral unilateral
strategies against the prescribed opponents. It includes Never, arbitrary
finite stopping times, randomization, and history dependence. A reset means
that the pure behavioral strategy Quit at the new root attains this complete
cap; it is not merely a best response among stationary strategies.

The profiles `zeta^n` in Theorem C are literal nested profiles. Their payoff
recursion is therefore an identity, not a compact-limit replacement. The
summability assumption concerns the actual marginal hazards of the displayed
prefix roots.

## Source correspondence

The following checked declarations are used without strengthening them:

- `quittingPunishmentValue_sub_le_continueMass_mul_of_nashBellmanEdge` and
  `quittingDynamicDebtTail_floorViolation_mono` in
  `UniformEquilibrium/Quitting/Debt/Dynamic/PunishmentFloorViolation.lean`;
- `summable_dynamicDebtTailAbsorptionCharge_of_floorViolation_of_positiveDebt`
  in the same file;
- `quittingTerminalSemanticDebt_prefix_eq_blockAct`,
  `quittingTerminalSemanticDebt_prefix_le`, and actual-carrier closure under
  literal prefixing in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
  in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`.

The literal nesting, fixed observer, uniform debt floor, and reset/shift cap
clock come from the independently reviewed mathematical packets
`CODEX_SPINOZA__NESTED_TERMINAL_CAP_CHILD_FIXED_DEBTOR_TRANSPORT` and
`CODEX_SPINOZA__SIGNED_CAP_CHILD_HOLONOMY_AND_RESET_DICHOTOMY`.

The new content is:

1. summability plus exactness rules out every normal-player floor violation;
2. a reset produces a singleton-wall gap at the actual reset child, without
   passing through the unrelated source payoff displacement; and
3. the wall gap forces both a uniform total-debt drop and a uniform joint
   absorption floor for every exact root at that child.

## Proof

### 1. Proof of Theorem A

Choose `M` bounding the displayed values and all terminal rewards. The
Bellman identity gives

```
||v_t - v_(t+1)||_infinity <= 2*M*A(x_t).
```

The right-hand side is summable, so `v_t` converges to a vector `v_infinity`.
Every marginal Quit probability is at most `A(x_t)`, hence `x_t` converges to
all Continue. Exact root Nash is closed in root and continuation coordinates.
At the limit, therefore, quitting alone cannot improve on continuing:

```
r_i({i}) <= v_infinity(i).
```

Suppose a normal player violates its floor at date `T`:

```
v_T(i) < chi_i.
```

The checked exact floor-violation propagation theorem says that this
coordinate remains below the same floor and is nonincreasing forward in
time. Thus

```
v_infinity(i) <= v_T(i) < chi_i <= r_i({i}),
```

contradicting the limiting root inequality. This proves Theorem A.

### 2. A reset crosses the singleton wall

Write `W^n=U(zeta^n)` and let `h_(n,j)` be `j`'s Quit probability in
`bar_q^n`. At a reset, Quit immediately attains `j`'s complete cap at
`zeta^(n+1)`. Let `bar_E_n` be Quit payoff minus Continue payoff at that
root against the actual continuation payoff `W^n`. The exact endpoint-mixture
identity is

```
d_j(zeta^(n+1)) = (1-h_(n,j))*bar_E_n.
```

The debt floor and `1-h_(n,j) <= 1` give

```
bar_E_n >= delta.
```

Summability of the marginal hazards implies `bar_q^n -> all Continue`.
Literal prefixing gives

```
W^(n+1) = F_(bar_q^n)(W^n),
```

and the Bellman increment is bounded by twice the reward bound times the
root absorption. Hence `W^n` converges. Along reset indices,

```
bar_E_n -> r_j({j}) - W_j^infinity.
```

Therefore `W_j^infinity <= r_j({j})-delta`. Convergence gives, at every
sufficiently late reset child,

```
W_j^n <= r_j({j}) - delta/2.
```

This argument is deliberately direct. The negative source-to-child payoff
holonomy has the wrong comparison direction to imply the wall inequality.

### 3. Proof of Theorem B

Let

```
a = 1-s_j(x),
```

the probability that at least one opponent of `j` Quits at the root. Let
`E_j(x;W)` be the Quit-minus-Continue endpoint difference. At all Continue,

```
E_j(allContinue;W) = r_j({j})-W_j >= epsilon.
```

Couple the opponents' product root with all Continue. Only the event that
some opponent Quits can change either endpoint, and each endpoint changes by
at most `2*M`. Therefore

```
|E_j(x;W)-E_j(allContinue;W)| <= 4*M*a.
```

For an actual carrier point and an exact root, the checked coordinate debt
action is

```
d_j(T_x(y))
  = max(0, s_j(x)*d_j(y) - max(E_j(x;W),0)).
```

If `a >= epsilon/(8*M)`, survival contraction alone gives

```
d_j(y)-d_j(T_x(y)) >= epsilon*d0/(8*M).
```

Also `A(x) >= a >= epsilon/(8*M)`.

If `a < epsilon/(8*M)`, endpoint stability gives

```
E_j(x;W) > epsilon/2.
```

The debt action then gives

```
d_j(y)-d_j(T_x(y)) >= min{d0,epsilon/2}.
```

Moreover, exact root Nash forces `j` to Quit surely. If `j` assigned positive
probability to Continue, its support condition would require Quit to be no
better than Continue, contradicting the strict positive endpoint difference.
Thus `A(x)=1` in this case.

Every other coordinate debt weakly decreases under an exact carrier prefix.
The loss in coordinate `j` therefore cannot be offset elsewhere. Taking the
minimum of the two cases proves both constants in Theorem B.

### 4. Proof of Theorem C

Section 2 supplies the singleton-wall hypotheses at every sufficiently late
reset child, with

```
d0=delta,  epsilon=delta/2.
```

Finite root-game Nash existence supplies an exact product root against that
child's actual prescribed payoff. Theorem B gives the literal exact prefix
with

```
c_delta = min{delta,delta/4,delta^2/(16*M)},
a_delta = min{1,delta/(16*M)}.
```

The prefix remains in the actual terminal-semantic carrier. Global minimality
therefore gives

```
D_* <= D(prefixed child) <= D(reset child)-c_delta,
```

which is equivalent to the claimed fixed off-minimum bound.

## Boundary tests

### Normality is essential in Theorem A

Take two players `i,k`. For player `i`, set

```
r_i({i})=-1,  r_i({k})=r_i({i,k})=0,
```

and give `k` zero at every terminal coalition. Player `i` can guarantee zero
by Never, while opponents can hold it to zero by Never, so `chi_i=0` and `i`
is not normal. The constant displayed tail

```
v_t=(-1/2,0),  x_t=allContinue
```

is exact Nash--Bellman and has zero total absorption, but violates
`v_t(i)>=chi_i`. Thus normality cannot simply be removed from Theorem A.

### Strict singleton separation is essential in Theorem B

Take two players `j,k`. Give `k` payoff zero everywhere and set

```
r_j({j})=0,  r_j({k})=1,  r_j({j,k})=0.
```

In a profile where both players Quit together at a later fixed date,
`U_j=0`, while `j` obtains `1` by Never. Thus `d_j=1` and
`U_j=r_j({j})`. All Continue is exact against the displayed payoff zero;
prefixing it has zero absorption and changes no debt. Hence positive debt
without a strict singleton-wall gap cannot imply either conclusion of
Theorem B.

### The reset exit is not automatically renewable

The exact prefix in Theorem C preserves actual-carrier membership and spends
debt, but it can change every cap clock and the identity of the terminal-gap
observer. The hypotheses of Theorem C contain no operation reconstructing
the nested sequence from the prefixed descendant. Reapplying the theorem to
that descendant would therefore assume the missing source passport. This is
a scope boundary, not an omitted proof step.

## Adapter and consumer

The checked Fin4 hard residual supplies all-player normality. The checked
dynamic-debt theorem says that an eventual floor violation in a positive-debt
exact tail forces summable joint absorption. Theorem A then contradicts that
violation, eliminating this side of the summable-waist split.

The independently reviewed nested-child construction supplies literal
profiles, summable marginal hazards, one fixed observer with a uniform debt
floor, and the reset/shift dichotomy. In the infinite-reset arm, Theorem C
maps every late reset child to a quantitative-debt descendant through a real
exact Nash--Bellman edge with fixed absorption. This is the downstream
semantic output of the packet.

No adapter currently makes those descendants the sources of another nested
cap-child generation. Accordingly, the packet narrows rather than completes
the quantitative paid-port consumer.

## Lean handoff

The narrowest useful declarations are:

```
summableExactNashBellmanTail_floorSafe_of_allNormal

exactRoot_jointAbsorption_and_debtDrop_of_belowSingleton

FinFourNestedCapChildren.infiniteResets_exactCapacityDebtExit
```

The second declaration should expose both constants in one theorem so that
the debt and physical-charge witnesses are known to come from the same exact
root. It should quantify over every exact root and use the existing block-act
identity rather than restating debt as a root-local surrogate.

The third declaration should consume the existing literal nested profiles,
fixed observer, debt floor, and cap-clock reset witness. It must keep the
reset indices explicit long enough to prove the direct endpoint limit before
specializing Theorem B.

Useful formal boundary checks are the two-player examples above and the
degenerate all-Continue root in the equality-wall case.

## Scope and nonclaims

The packet proves ordinary mathematics. It does not assign a Lean seal to
the new statements.

It does not prove a uniform-equilibrium payoff, an exact counterexample, a
renewable atlas rank, or a source-reprojected return. It does not consume the
floor-safe summable tail or the eventual shifted-cap arm. It does not assert
that the forced-owner barred roots in the nested genealogy are Nash for the
outsiders. It does not identify finite total variation with a summable Nash
seam. It does not replace unrestricted behavioral caps by stationary or
finite-horizon caps.
