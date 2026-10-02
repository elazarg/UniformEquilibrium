# Returned-block homogeneous-tangent review

Reviewer: `CODEX_NOETHER`

Reviewed note:
[`../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`](../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md)

Scope: Section 35, Propositions 46--47. I independently checked the
probability-weighted endpoint signs, compactness with fixed and varying finite
horizons, the product-law first-order expansion, and the telescoping
normalization. This is ordinary mathematics, not Lean-checked.

## Verdict

**Propositions 46--47 are valid ordinary mathematics as stated.** They give a
genuine universal obstruction at the repository's standard endpoint-Nash
scale: a uniformly bounded returned product block with vanishing total hazard
and aggregate Bellman/endpoint regret `o(total hazard)` forces
`HasHomogeneousSimplexSolution (normalizedSoloMatrix reward)`.

**Gate qualification added after the initial review.** The theorem's output is
for the **full** normalized singleton matrix. By contrast,
`ResidualHardClass.no_homogeneous` in
`UniformEquilibrium/Quitting/Classification/LCP/Gate.lean` excludes a
homogeneous solution only for `normalizedNormalPlayerMatrix reward`, the
recursive normal-core principal matrix. Thus the bare algebraic theorem does
not contradict every ambient residual-hard block. The direct corollary holds
for blocks whose Quit support stays in the recursive normal core, after
restricting the reward table to that subtype. Ambient blocks require a further
support argument; the sharp nonvertex/vertex reduction is recorded below.

The result is not a producer. Its exact surviving branch is a chronology with
nonvanishing accumulated hazard/payoff motion, an exact positive returned
block obtained by compactness, a pure first-layer-abnormal limiting owner, or
another solved dispatch.

## 1. Endpoint signs and support pinning

Write `D=Quit-Continue` and let the prescribed Quit probability be `p`. The
definition `IsεQuittingRootEndpointNash` in
`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean` is exactly

```text
(1-p)D<=epsilon,       -epsilon<=pD.
```

At vanishing total hazard, forced Quit converges uniformly to the solo payoff
`s_i`, forced Continue converges uniformly to the common phase-value limit
`w_i`, and therefore `D->s_i-w_i` uniformly over the phases.

- If `w_i<s_i`, the first endpoint regret is bounded below by a positive
  constant at every phase (eventually `1-p>=1/2`). This contradicts
  `E_n/S_n->0`, since `S_n->0`.
- If `w_i>s_i`, the second endpoint regret at phase `k` is asymptotic to
  `p_(k,i)(w_i-s_i)`. Summing and dividing by `S_n` forces the normalized
  cumulative owner mass `mu_i` to vanish.

Thus `w_i>=s_i` for every player and `mu_i>0 -> w_i=s_i`. This correctly
handles the semantic loophole in a single row: a negative raw gap is cheap at
one small hazard, but its cumulative hazard weight is exactly what becomes
`mu_i` after a returned-block telescope.

Zero-hazard phases cause no exception. If `w_i<s_i`, even a zero-hazard row
retains the full Quit-deviation inequality; if `w_i>s_i`, it simply
contributes no owner mass.

## 2. Varying-horizon compactness

Let `q_k=sum_i p_(k,i)` and `S_n=sum_k q_k`. Uniform boundedness of values and
the finite reward table give a fixed constant `K` with

```text
|T(v_(k+1),p_k)-v_(k+1)| <= K q_k.
```

Therefore the total phase-value variation around the returned block is at
most `K S_n+B_n`, which tends to zero. Extracting only the base value is
enough: every phase value, even with varying horizon, is then uniformly close
to one common limit `w`. No product compactness over a changing phase set is
being assumed.

For the one-row product law, uniformly on the bounded value box,

```text
T_i(v_(k+1),p_k)-v_(k+1,i)
 = sum_j p_(k,j)(r({j})_i-v_(k+1,i)) + O(q_k^2).
```

The singleton coefficient error is bounded by `p_(k,j) q_k`; the total
multi-quitter probability is `O(q_k^2)`. Since `q_k<=S_n`,

```text
sum_k q_k^2 <= S_n^2.
```

Summing the Bellman equations around the returned block telescopes the phase
values exactly. Division by `S_n`, followed by the preceding uniform
phase-value convergence, gives

```text
0=sum_j mu_j(r({j})-w).
```

Because `mu` is a probability vector,

```text
(normalizedSoloMatrix reward * mu)_i=w_i-s_i>=0,
mu_i>0 -> w_i-s_i=0.
```

This is precisely `SingletonLCPFeasible`, hence the repository abbreviation
`HasHomogeneousSimplexSolution`, in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`.

## 3. Fixed-horizon reduction and boundary tests

For fixed nonzero horizon `m` and finite player set,

```text
A_n <= S_n <= m*|I|*A_n.
```

The rowwise hypotheses give
`B_n<=m*|I|*beta_n` and `E_n<=2m*|I|*epsilon_n`, so Proposition 46 follows
from Proposition 47. For small hazards, `S_n`, maximum hazard, and whole-block
absorption are comparable; the claimed scale change is sound.

I tested the following potential failures.

- A single owner gives the zero normalized singleton matrix, which is
  homogeneous, as the theorem predicts.
- Alternating cheap negative endpoint gaps do not evade the result: their
  standard regret is quadratic rowwise, but after normalization their total
  owner hazards enter `mu`; the Bellman telescope then forces the supported
  equality.
- Extra collision rows do not affect the limit, because their aggregate
  contribution is bounded by `sum q_k^2=o(S_n)`.
- No assumption about a Never atom is needed: these are finite returned blocks,
  and their cemetery outcome is exactly the next phase value.

No falsifier or hidden sign reversal was found.

## 4. Source and novelty scope

The closest checked one-row result is
`singletonLCPFeasible_of_stationaryEndpointNash_tangent`
(`UniformEquilibrium/Quitting/Stationary/ApproximabilityCompactification.lean`).
A narrow search found no returned-block or varying-horizon telescope with the
aggregate semantic regrets used here. Propositions 46--47 are a legitimate
ordinary-mathematics extension of that tangent obstruction, but supply no
punishment-floor path, recurrence producer, or all-behavior consumer by
themselves.

The exact conjecture-facing consequence needs the normal-core support
qualification. If every quitting owner lies in
`N=normalCore (normalizedSoloMatrix reward)`, restrict coalitions and payoff
coordinates to `N`. The restricted reward has normalized singleton matrix
`principalMatrix (normalizedSoloMatrix reward) N` by direct singleton
expansion; ambient product laws with zero outside hazards, Bellman rows, and
endpoint regrets agree literally on `N`. Proposition 47 then contradicts
`ResidualHardClass.no_homogeneous`.

For a general ambient block, its full homogeneous limit can evade the normal-
core contradiction only in a very narrow way. If a full homogeneous simplex
witness has at least two positive coordinates, its support lies in the normal
core: for each supported `i`, residual zero and zero diagonal force a distinct
supported `j` with `M_ij<=0`; induction puts the whole support in every normal
layer. Restriction then gives a homogeneous solution of the normal-player
matrix. Hence under `no_homogeneous` every full witness is a vertex supported
outside the core. If one also assumes no uniform payoff, the vertex owner has
no distinct blocker `M_owner,blocker<=0`, since its homogeneous column is
nonnegative and
`exists_uniformEquilibriumPayoff_of_nonnegative_column`
(`UniformEquilibrium/Quitting/Classification/LCP/LaterLayerAbnormal.lean`)
would dispatch otherwise. Thus it is absent already from `normalLayer M 1`.

Accordingly, on the residual-hard no-uniform branch a vanishing returned block
either contradicts the normal-core homogeneous gate or its normalized
cumulative hazard converges to one pure first-layer-abnormal owner. Bounded-
horizon compactness is ruled out only after that remaining vertex escape is
dispatched; the broader theorem and all of its analytic calculations remain
valid.
