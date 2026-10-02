# Tropical two-Never data give a chronological support descent

Author: `CODEX_SNELL`

## Status

**Proof draft, ordinary mathematics, not checked in Lean.**  The positive
theorem starts from the actual period-one stationary profiles supplied by the
reviewed tropical two-Never reduction.  It proves that the two response
profiles can be ordered into literal successive cap updates and reduces the
leading hazard support by two when that support has size three or four.

The substantive argument is frozen pending independent adversarial review.

The descent is not yet renewable.  A separate exact four-player regression,
using the checked duplicated cyclic standard-Q matrix, shows that the first
removed player can become an exact Quit-now responder after the second Never
update.  Thus support cardinality is not a monotone response rank without a
new positive-minimum or ancestry field.

## Question

Suppose one actual sequence of stationary Fin4 profiles has vanishing total
hazard and normalized singleton law `lambda`, with positive common clearance
`kappa`.  Every owner in `supp(lambda)` then has a literal Never cap with a
positive limiting gain at the original source.  Can two of these sibling
deviations be ordered into actual chronological responses after recomputing
the second cap at the first child?

The answer is yes.  The exact gain formula below gives the order.  What fails
is the stronger claim that the removed labels remain solved after both
updates.

## Sources inspected and narrow duplicate search

The source theorem is the reviewed export
[`FIN4_PERIOD_ONE_TROPICAL_TWO_NEVER_REDUCTION.md`](../exports/FIN4_PERIOD_ONE_TROPICAL_TWO_NEVER_REDUCTION.md).
Behavioral pure-time completeness is
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.

The regression uses the checked declarations

- `duplicatedCyclicMatrix_standardQ`;
- `duplicatedCyclicMatrix_noHomogeneous`;
- `duplicatedCyclicMatrix_normal_standardQ`;
- `duplicatedCyclicMatrix_normal_noHomogeneous`; and
- `normalCore_duplicatedCyclicMatrix_eq_univ`

in
`UniformEquilibrium/Quitting/Classification/LCP/StandardQSideExample.lean`.

A narrow search for “two Never”, “Never in either order”, “sequential Never”,
“chronological Never”, and “support reduction” found the E3-specific ordered
calculation in
`CODEX_NEGATIVE_CERTIFICATE__ASYMMETRIC_STATIONARY_SEAM_CLOSURE.md`, but no
general common-clearance selection theorem or declaration.  The present
argument generalizes that order calculation to every support of size three or
four.

## 1. Exact setting

Let `I` be a finite player set and let

```text
r : {S subset I : S nonempty} -> R^I
```

be a bounded quitting reward table.  Never pays zero.  Behavioral
randomizations are independent across players and dates conditional on public
survival, and a unilateral deviation may replace the player's complete
behavioral strategy.

For each `n`, let

```text
x_n : I -> (0,1)
```

be a stationary hazard vector, let `sigma_n` be its infinite stationary
repetition, and put

```text
h_n=sum_i x_(n,i),          lambda_(n,i)=x_(n,i)/h_n. (1.1)
```

Assume

```text
h_n -> 0,                   lambda_n -> lambda.        (1.2)
```

Put

```text
s_i=r_i({i}),
A_(i,k)=r_i({k})-s_i,
K=supp(lambda).                                       (1.3)
```

Assume there is `kappa>0` such that

```text
sum_k lambda_k A_(i,k) >= kappa              for all i,
sum_k lambda_k A_(i,k) =  kappa              for i in K.  (1.4)
```

The reviewed period-one tropical theorem supplies exactly (1.1)--(1.4), with
`I=Fin 4`, after passage to a subsequence.

For every nonempty `B subset K`, define `sigma_n^B` by retaining the source
stationary strategy of each player in `B` and each player outside `K`, while
replacing every player in `K\B` by literal Never.  Since `B` is nonempty and
all source hazards are positive, `sigma_n^B` is an actual almost-surely
absorbing stationary profile.

Write

```text
Lambda_B=sum_(k in B) lambda_k,
V_i(B)=sum_(k in B) lambda_k r_i({k})/Lambda_B.       (1.5)
```

## 2. Subset-law and cap formula

### Lemma 2.1 (terminal law after top-owner deletion)

For every fixed nonempty `B subset K`, the first quitting coalition under
`sigma_n^B` converges in total variation to the singleton lottery

```text
Pr({k})=lambda_k/Lambda_B,       k in B.              (2.1)
```

Consequently, for every player `i`,

```text
U_i(sigma_n^B) -> V_i(B).                            (2.2)
```

#### Proof

The retained players outside `K` have total hazard `o(h_n)`.  The retained
players in `B` have total hazard `h_n Lambda_B+o(h_n)`.  In one row, a
singleton `k in B` has mass `x_(n,k)+O(h_n^2)`, while all collisions have
mass `O(h_n^2)`.  Infinite stationary repetition normalizes this one-row
absorbing law.  Dividing by its absorption mass proves (2.1), and boundedness
of the rewards gives (2.2).  This is a statement about the actual repeated
profiles, not a formal replacement of their terminal law.

### Lemma 2.2 (exact finite-`n` cap and limiting Never gain)

Fix `j in B` and assume `B\{j}` is nonempty.  Let

```text
Q_(n,j)^B = payoff from Quit at date zero against sigma_(n,-j)^B,
N_(n,j)^B = payoff from literal Never against sigma_(n,-j)^B. (2.3)
```

Every deterministic pure quitting time has payoff in the closed interval
with endpoints `Q_(n,j)^B` and `N_(n,j)^B`.  Hence the exact unrestricted
behavioral cap is

```text
W_(n,j)^B=max(Q_(n,j)^B,N_(n,j)^B).                  (2.4)
```

Moreover,

```text
Q_(n,j)^B -> s_j,
N_(n,j)^B -> V_j(B\{j}),                             (2.5)
```

and the gain from replacing the prescribed stationary strategy by Never
converges to

```text
V_j(B\{j})-V_j(B)
 = lambda_j * sum_(k in B\{j}) lambda_k A_(j,k)
   / (Lambda_B*(Lambda_B-lambda_j)).                 (2.6)
```

In particular, if the numerator in (2.6) is positive, then for all
sufficiently large `n`:

1. `N_(n,j)^B>Q_(n,j)^B`;
2. literal Never attains the complete unrestricted cap exactly; and
3. the actual update `sigma_n^B -> sigma_n^(B\{j})` has strictly positive
   gain.

#### Proof

Against stationary opponents, let `a_n` be their one-row joint Continue
probability.  A pure Quit time `t` either sees opponent absorption in one of
the first `t` rows, with conditional payoff `N_(n,j)^B`, or survives to row
`t` and receives `Q_(n,j)^B`.  Its payoff is exactly

```text
(1-a_n^t)N_(n,j)^B+a_n^t Q_(n,j)^B.                 (2.7)
```

Never and Quit-at-zero attain the two endpoints.  The checked pure-time
extremality theorem upgrades their maximum to the supremum over every
behavioral deviation, proving (2.4).

The same singleton-law estimate as Lemma 2.1 proves (2.5).  Finally,

```text
V_j(B)=lambda_j/Lambda_B*s_j
       +(Lambda_B-lambda_j)/Lambda_B*V_j(B\{j}).     (2.8)
```

Subtracting and using (1.3) gives (2.6).  Positivity separates the two limits
in (2.5), so the three eventual finite-`n` statements follow.  Notice that
“exact-cap Never update” means exact cap attainment at each sufficiently
large finite `n`; only the displayed value of its gain is a limiting formula.

## 3. Chronological leading-support descent

### Theorem 3.1

Under (1.1)--(1.4):

1. if `|K|=2`, one literal exact-cap Never update reduces the leading hazard
   support to one player;
2. if `|K|=3`, two successive literal exact-cap Never updates reduce the
   leading support to one player; and
3. if `|K|=4`, two successive literal exact-cap Never updates reduce the
   leading support to two players.

The player labels are fixed along the subsequence.  In cases 2 and 3, the
second cap is evaluated at the actual child produced by the first update; the
proof does not treat two source siblings as chronological profiles.

#### Proof

At `B=K`, for every `i in K`, (1.4) and (2.6) give the limiting source gain

```text
lambda_i*kappa/(1-lambda_i)>0.                       (3.1)
```

Thus any support owner can make the first exact-cap Never update for all
large `n`.  This proves case 1.

Suppose now that `|K|>=3`.  Fix any `j in K`.  The common-clearance identity
is

```text
sum_(k in K\{j}) lambda_k A_(j,k)=kappa.             (3.2)
```

There are at least two summands.  They cannot all be at least `kappa`, since
their sum is `kappa>0`.  Choose `i!=j` such that

```text
lambda_i A_(j,i)<kappa.                              (3.3)
```

First update player `i` to Never.  At the resulting child take
`B=K\{i}`.  The numerator in player `j`'s formula (2.6) is

```text
sum_(k in K\{i,j}) lambda_k A_(j,k)
  =kappa-lambda_i A_(j,i)>0.                         (3.4)
```

Thus Lemma 2.2 proves that player `j`'s Never strategy is the exact complete
cap at this child for all sufficiently large `n`, and its gain converges to

```text
lambda_j*(kappa-lambda_i A_(j,i))
 / ((1-lambda_i)*(1-lambda_i-lambda_j))>0.           (3.5)
```

Removing `i,j` leaves `|K|-2` leading owners, proving cases 2 and 3.

## 4. Exact reactivation regression

Theorem 3.1 does not imply a nonresetting or renewable support rank.

Let the players be

```text
I=Option (Fin 3)
```

and let `A` be the checked `duplicatedCyclicMatrix`.  On

```text
K={some 0,some 1,some 2}
```

it is

```text
    [ 0 -1  2 ]
A = [ 2  0 -1 ],                                     (4.1)
    [-1  2  0 ]
```

while the `none` row and column duplicate coordinate zero.  Put

```text
lambda_(some k)=1/3,       lambda_none=0.             (4.2)
```

Then

```text
A lambda=(1/3,1/3,1/3,1/3),       kappa=1/3.         (4.3)
```

The declarations listed above prove full recursive normal core, standard Q
on the full normal matrix, and absence of a homogeneous simplex solution.

Define an actual reward table by

```text
r_i({k})=A_(i,k),
r_i(S)=0 when |S|>=2.                                 (4.4)
```

Thus every solo payoff is zero and the normalized singleton matrix is exactly
`A`.  Let the three players in `K` use stationary hazard `h`, let player
`none` use stationary hazard `h^2`, and let `h` decrease to zero.  These are
actual almost-surely absorbing stationary profiles with exact Bellman return.
Their terminal law tends to the uniform singleton lottery on `K`.  Directly,

```text
U_i -> 1/3                       for every i,
NeverCap_i -> 1/2                for i in K,
debt_none -> 0,
endpointRegret/totalHazard -> 1/3.                    (4.5)
```

The Quit-now endpoint tends to the zero solo payoff.  Hence literal Never is
the exact unrestricted cap for every player in `K` for all sufficiently small
positive `h`, and each source Never gain tends to `1/6`.

Make any first support owner `i` Never.  Of the two remaining support owners,
exactly one `j` sees the last owner `k` through the positive entry

```text
A_(j,k)=2.                                            (4.6)
```

This is the unique second Never direction with positive limiting gain; that
gain tends to one, so it is again an exact cap update for small `h`.  The
cyclic sign pattern simultaneously forces

```text
A_(i,k)=-1.                                           (4.7)
```

After both updates, the terminal law tends to singleton `k`.  The first
removed player therefore receives a payoff tending to `-1`, whereas Quit at
date zero tends to its solo payoff zero.  Its exact cap is Quit-at-zero for
all sufficiently small `h`, and its reactivation gain tends to one.

This happens for every first owner and the forced profitable second Never
owner.  Equivalently, no pair of the three leading owners can be removed while
leaving both removed players best responding by Never.  The table has the
exact all-Never terminal Nash profile, so its true global minimum debt is
zero.  It is not a counterexample to Fin4 and does not satisfy a positive
minimum hypothesis.

## 5. Consequence and remaining edge

Theorem 3.1 is a genuine source-preserving construction:

```text
actual soft source
  -- exact cap: i Never --> actual stationary child
  -- exact cap: j Never --> leading support smaller by two. (5.1)
```

It strictly improves the prior sibling statement because the second
unrestricted cap is recomputed and attained at the first child.  It does not
produce a terminal approximation.  Section 4 proves that the output cannot be
iterated using support cardinality alone, even after adding full normal core,
standard Q, homogeneous infeasibility, exact Bellman return, the cap formulas,
and the positive regret-density limit.

The exact unresolved transition is now the reactivation edge.  A renewable
theorem must use the counterexample's positive global minimum or source
ancestry to show that the first removed player's later Quit-now response
either incurs a charged off-minimum excursion, enters a checked chronological
consumer, or is impossible.  Without such a field, the cyclic regression
shows that support reduction resets after two steps.

## Scope and nonclaims

- The positive theorem applies to the actual period-one stationary source
  sequence, not merely to an abstract LCP vector.
- “Exact cap” is a finite-`n` statement for every sufficiently large `n`.
  The explicit gain constants in (3.1) and (3.5) are limits.
- Zero-share outsiders retain their original positive source hazards until a
  displayed update says otherwise.
- The theorem neither invokes nor lifts a two- or three-player equilibrium.
- It does not identify profile siblings with chronological steps.
- The regression carries every named singleton-matrix hard field but has
  global minimum zero; it only proves that those fields do not make the
  descent renewable.
- No uniform-equilibrium conclusion, Nash--Bellman packet, or positive-minimum
  reactivation charge is claimed.

## Requested review

Please check the exact stationary pure-time envelope (2.7), the denominator
and orientation in (2.6), the finite-label selection (3.3), finite-`n` cap
attainment after the first update, and the duplicated-cyclic reactivation
calculation (4.6)--(4.7).
