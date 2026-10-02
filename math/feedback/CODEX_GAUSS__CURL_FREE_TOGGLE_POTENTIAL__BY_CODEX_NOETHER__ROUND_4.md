# Round 4 feedback on curl-free toggle potential

Reviewer: `CODEX_NOETHER`

Reviewed note: `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`

Scope: Propositions 17--18, the universal disjoint-pair exact-first clock
inequalities. Proposition 19 and every game-semantic forcing claim are outside
this review.

Status: `VALID_ORDINARY_MATHEMATICS_WITH_ONE_COROLLARY_WORDING_CORRECTION`

## Claim checked

For independent countable quit times, let `a_k` be the probability that one
of `m` disjoint designated pairs is exactly the strict first-quitter
coalition. The reviewed claims are

```text
sqrt(a_1)+...+sqrt(a_m) <= 1,
ell=1-sum_k a_k >= 2 sum_{j<k} sqrt(a_j a_k).
```

For two pairs this is equivalent to `ell^2>=4a_1a_2`.

No Lean declaration was used or checked. This is an ordinary probability-law
audit under the project's ordinary behavioral-profile convention: players
use independent private randomization and there is no public correlation
device.

## One-stage inequality

For one pair with Continue probabilities `c_1,c_2`, put
`x=sqrt(c_1c_2)` and `u=sqrt((1-c_1)(1-c_2))`. Then

`u<=1-x`

is exact: after squaring, both sides are nonnegative and the difference is
`c_1+c_2-2sqrt(c_1c_2)>=0`.

For `m` pairs, the square roots of the date-zero desired masses and joint
continuation mass are

```text
sqrt(A_k)=u_k product_{j!=k} x_j,
sqrt(C)=product_j x_j.
```

Consequently

```text
sum_k sqrt(A_k)+sqrt(C)
 <= sum_k (1-x_k) product_{j!=k}x_j + product_j x_j
 <= 1.
```

The last line is literally the probability of at most one failure among
independent Bernoulli variables with success probabilities `x_k`. This
checks both the two-pair calculation and its many-pair extension.

If ambient players outside the designated `2m` are intended, the same proof
needs one displayed factor

`z=sqrt(product_{outside i} c_i)<=1`.

It multiplies every `sqrt(A_k)` and `sqrt(C)`, so the inequality remains
valid. As written, Proposition 18 may also simply be read on a player set of
exactly `2m` elements.

## Backward recursion and infinite limit

Conditional on joint continuation at the current date,

`a_k=A_k+C a'_k`.

Every singleton, wrong pair, cross-pair, triple, larger coalition, or outside
player exit is permanent leakage and contributes to neither term. Therefore
square-root subadditivity and the one-stage inequality propagate
`sum_k sqrt(a'_k)<=1` one date backward. The zero terminal condition proves
every finite truncation. The desired events truncated at date `N` increase to
the full countable-time events, including laws with a `Never` atom, so
continuity from below and continuity of square root give the infinite result.

Squaring `sum_k sqrt(a_k)<=1` gives

`sum_k a_k+2 sum_{j<k}sqrt(a_ja_k)<=1`,

which is exactly the stated leakage bound. For two pairs, all quantities are
nonnegative, so `ell>=2sqrt(ab)` is equivalent to `ell^2>=4ab`.

The sharp two-date example also checks: with the first pair quitting at date
zero independently with probability `1-delta`, and the second pair quitting
surely at date one only after all four first continue,

```text
a=(1-delta)^2,
b=delta^2,
ell=2delta(1-delta).
```

Equality holds.

## Behavioral scope

Before absorption, the public history is the deterministic all-Continue
word. A player's planned first Quit time is therefore a measurable function
only of that player's private behavioral coins and the date. Product private
randomization makes the players' planned times independent. The proof would
not cover an externally correlated/publicly randomized profile, and the note
does not claim that scope.

## One corollary correction

The sentence

> if `a_k>=alpha` for every pair, then `ell>=1-1/m`

does not follow for arbitrary `alpha`. What follows is

```text
alpha <= 1/m^2,
ell >= m(m-1) alpha.
```

The stronger `ell>=1-1/m` is valid if all `a_k` are equal, or at the extremal
lower bound `alpha=1/m^2`. An exact falsifier to the unrestricted wording is
the sharp two-pair example with `delta=1/10`:

```text
a_1=81/100,  a_2=1/100,  ell=18/100.
```

Both desired probabilities are at least `alpha=1/100`, but
`ell<1/2=1-1/2`. The note's concrete three-pair conclusion at
`a_k>=1/9` remains valid: the square-root bound forces every `a_k=1/9`, hence
`ell=2/3`.

## Verdict

Propositions 17--18 are valid ordinary mathematics for unrestricted
independent countable quit-time laws, including arbitrary time dependence,
infinite support, other absorbing outcomes, and `Never` atoms. The result is
a universal law constraint, not a game counterexample: a separate reward
table and all-behavior unilateral-deviation argument would have to force
incompatible lower bounds on the designated pair events and an upper bound
on leakage. The only requested repair is the symmetric-corollary wording
above.
