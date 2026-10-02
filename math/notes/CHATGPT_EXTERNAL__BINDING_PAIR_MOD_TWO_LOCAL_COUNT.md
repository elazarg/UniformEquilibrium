# Explicit finite-cap mod-two local count for the Fin4 binding pair

Author: `CHATGPT_EXTERNAL`

Status: `PROOF_DRAFT`; paper computation and source scoping, not Lean-checked.

Source: supplied as `ephemeral/FIN4_BINDING_PAIR_EXPLICIT_MOD_TWO_LOCAL_COUNT.md`
and moved here without rewriting the mathematical body.

Paper-only scoping note. No Lean was written and no build was run. Everything
below marked *verified* was checked by reading the actual Lean declarations
named; everything marked *hand computation* is my own pen-and-paper derivation
from those declarations; everything marked *asserted* is taken from the packet
or a docstring and not independently checked.

## Verdict

**The chain closes.** For the cardinality-two binding face the explicit
finite-cap local complete-simplex count is computable in closed form at every
sufficiently fine mesh, for both support patterns, with no homotopy, no
regularity theory, no subdivision invariance and no
`ModTwoBoxComplementarityParitySpec` inhabitant:

- both binding hazards positive: **exactly two** complete simplices have their
  anchor in the localization ball, hence local parity `0`;
- exactly one binding hazard positive (the degenerate solo segment): **exactly
  zero** complete simplices, hence local parity `0`.

Against the Sperner layer's global parity `1` this is a contradiction, and the
existing top-level consumer
`BoxComplementarityProblem.not_eventually_localCompleteSimplexParity_eq_zero`
(`Research/Topology/BoxComplementaritySpernerEventualLocalParity.lean`) has
exactly the right shape to receive it.

Two costs the review's three-ingredient list did not mention appear instead:
a Kuhn-simplex structure lemma, and a coordinate-order normalization
(the computation is clean only when the binding pair sits at coordinates
`{2, 3}`).

The produced contradiction reaches the source-attached conclusions in
`StrictRayBindingCardinality.lean`, but **not through the existing structures**:
they are parameterized by a parity spec nobody can construct, so that file must
gain a parallel Sperner-level certificate. The downstream theorems only consume
`card ≠ 1` and `card ≠ 2`, so the rewiring is mechanical.

## 1. The endpoint-difference system, checked against the source

*Verified.* Chasing `quittingRootEndpointDifference` →
`quittingRootQuitPayoff` / `quittingRootContinuePayoff`
(`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`) →
`quittingRootExpectedPayoff` / `quittingRootPayoff`
(`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/RootContinuation.lean`),
with `x_h` the Quit probability of `h` and `b` the continuation cap:

```
g_i(x) = Σ_{S ⊆ I \ {i}} π_S(x) · [ r_i({i} ∪ S) − (S ≠ ∅ ? r_i(S) : b_i) ]
```

with `π_S(x) = Π_{h∈S} x_h · Π_{h∉S∪{i}} (1 − x_h)`. This is literally
`quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticEndpointDefectPolarity.lean`);
that lemma already exists and will carry the Lean evaluation.

Two structural facts fall out and matter later:

- `g_i` does not depend on `x_i` at all;
- on the face where every player outside `A = {i, j}` plays pure Continue,
  only the coalitions `∅` and `{j}` carry mass, giving

```
g_i = −(1 − x_j)·δ_i + x_j·J_ij ,   δ_i = b_i − s_i ,  s_i = r_i({i}) ,
                                    J_ij = r_i({i,j}) − r_i({j})
```

**The packet's equation (1) is correct as transcribed**, with the repository's
sign convention (Quit minus Continue) and with `s_i` equal to
`reward (quittingSingletonTerminal i) i`, which is the same quantity that
defines `bindingFinset` in `Research/Quitting/ForwardExactCapTailFlow.lean`.
Note the face formula is *exact and global on the face*, not a local
linearization — this is what makes the whole computation finite.

## 2. What the Sperner layer actually delivers

*Verified* by reading `Research/Topology/BoxComplementarityCubicalSperner.lean`,
`.../BoxComplementaritySpernerLocalCount.lean` and
`.lake/packages/fixed-point-theorems/FixedPointTheorems/cubical_sperner_prep.lean`.

Grid label at a vertex `v ∈ (Fin (p+1))^n`, with `x = v/p`:

```
RL(v) = min { h : (x_h > 0 ∧ g_h(x) < 0) ∨ x_h = 1 }   (= n if that set is empty)
```

`simplex SC n I` is: `I` injective, `I₀ ≤ I₁ ≤ … ≤ I_n` coordinatewise, and
`I_n ≤ I₀ + 1` coordinatewise. With `n+1` distinct points this forces the `n`
increments to be `n` *distinct unit vectors*: a Kuhn simplex, a base vertex plus
a permutation of the coordinates. `complete_simplex` additionally requires the
`n+1` labels to be exactly `{0, …, n}`, so labels are pairwise distinct
(`rl_inj_of_complete`). The label-`n` vertex is the anchor.

Global input, precisely: **for every problem and every `p > 0`,**

```
boxComplementarityLocalCompleteSimplexParity problem p hp Set.univ = 1
```

(`boxComplementarityLocalCompleteSimplexParity_univ`), which is `strong_cubical_sperner`
applied to `boxComplementaritySpernerCube`. Unconditional, resolution by
resolution — exactly the global parity the argument needs, and nothing weaker.

The localization input already exists too:
`BoxComplementarityProblem.eventually_localCompleteSimplexParity_eq_one`
(region open and containing `solutionSet` ⇒ eventually the local count is `1`),
and its consumer `not_eventually_localCompleteSimplexParity_eq_zero`.
So the only missing piece is the explicit finite count.

## 3. Coordinate-order normalization (the unlisted ingredient)

*Hand computation.* Write `A = {i, j}` for the binding pair and `O` for the two
outsiders. Inside the localization ball the outsiders have `g_h < 0` strictly,
so outsider `h` is violated iff `x_h > 0`, i.e. iff `v_h ≥ 1`.

The labels `2, 3, 4` in a complete simplex are the ones that need
"no smaller coordinate is violated". The computation stays on the face — where
the exact affine formulas of §1 apply — **iff every label that reads a binding
gain forces every outsider coordinate to `0`, i.e. iff `O = {0, 1}` and
`A = {2, 3}`.**

I checked the other five orderings. For `A = {0,1}`, `{1,3}`, `{0,3}`, `{0,2}`,
`{1,2}` there is always a chain shape in which a binding gain must be evaluated
at a vertex with an outsider coordinate at `1/p`. There the sign of `g_i` is
genuinely ambiguous: the zero set of `g_i` is a hypersurface
`x_j = φ(x_{h₁}, x_{h₂})` whose tilt `∂φ/∂x_h` is an arbitrary real, so a
one-mesh step in an outsider coordinate can move the threshold by many mesh
widths. Those orderings need the general degree theory.

Fix: conjugate the *problem*, not the bridge. Define

```
(P.permute π).gain y h := P.gain (y ∘ π⁻¹) (π h)
```

a legitimate `BoxComplementarityProblem (Fin 4)` whose solution set is the
coordinate-permutation image of `P`'s. Choose `π` sending `A` to `{2,3}`.
The localization ball `{x : ∀ h, x_h < ε}` is permutation-invariant, so the
region is literally unchanged. Estimated 80–150 Lean lines. This does **not**
require touching `QuittingEndpointNashBoxBridge`, whose coordinate-preserving
`quitProbability_eq` would otherwise have to be weakened.

Everything below assumes the normalized ordering `O = {0,1}`, `A = {2,3}`.

## 4. The explicit region

Choose, at a fixed late ray time `k`:

- `ρ > 0` such that `g_h(x) < 0` for both outsiders `h ∈ {0,1}` whenever
  `‖x‖_∞ ≤ ρ`. Exists because `h ∉ bindingFinset` gives
  `capLimit h > reward (quittingSingletonTerminal h) h` (with
  `singleton_le_capLimit`), so `δ_{k,h} ≥ δ̄_h/2 > 0` for large `k` by
  `cap_tendsto`, and `g_h` is Lipschitz with an explicit reward-bound constant.
- `ε := ρ/2`, and `k` large enough that `quittingRootAbsorptionMass (q_k) < ε/2`
  (available: `absorption_summable` ⇒ absorption `→ 0`).

Region:

```
V := { x ∈ [0,1]^4 : ∀ h, x_h < ε }        (relatively open in the cube)
```

**Isolating and total.** By `quittingMaximalCapSemanticRoot_maximal`
(`Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`) — *verified to exist* —
every exact root against `b_k` has absorption at most `α(q_k)`, and
`quittingQuitProbability_le_absorptionMass` turns that into `x_h ≤ α(q_k) < ε/2`
for every coordinate. So

```
solutionSet ⊆ { x : ‖x‖_∞ ≤ ε/2 } ⊂ V ,    solutionSet ∩ frontier V = ∅ .
```

That is the inequality that makes `V` isolating, and it is also exactly the
hypothesis `not_eventually_localCompleteSimplexParity_eq_zero` wants. Note that
`V` swallows *both* the origin and the mixed point, so no second region and no
disjoint-excision step is needed; the additivity lemma
`boxComplementarityLocalCompleteSimplexParity_union_of_disjoint` is available but
unnecessary.

Every vertex of a complete simplex whose anchor is in `V` lies within `1/p` of
that anchor, hence in `{‖x‖_∞ < ε + 1/p} ⊆ {‖x‖_∞ ≤ ρ}` for `p` large: the
outsider margin holds at every vertex we ever label, and no coordinate reaches
`1`.

## 5. Position forcing

*Hand computation.* Let `u⁰ … u⁴` be a complete simplex with anchor in `V`.

Labels `2`, `3`, `4` each require coordinates `0` and `1` unviolated; in
`V^{1/p}` that means `u_0 = u_1 = 0`. Three distinct vertices carry those
labels, the chain is monotone, and each coordinate increments exactly once, so
`u⁰_0 = u⁰_1 = 0` and coordinates `0, 1` increment at steps `3` and `4`.
Hence:

```
u⁰, u¹, u²  lie on the face  x₀ = x₁ = 0  and carry labels {2, 3, 4};
steps 1,2 increment coordinates 2 and 3 in some order;
u³ = u² + e₁  (label 1),   u⁴ = u³ + e₀  (label 0).
```

The step order is forced to `σ = (·, ·, 1, 0)` because `u⁴` always has
`u_0 = 1` and therefore label `0`.

This is the lemma that makes the whole thing finite: **only the exact affine
face formulas of §1 are ever evaluated.** Writing `(m, n)` for the grid
coordinates `(v₂, v₃)` of the face part, the three face vertices are either

- Option A: `(m,n), (m+1,n), (m+1,n+1)`, or
- Option B: `(m,n), (m,n+1), (m+1,n+1)`.

## 6. Both binding hazards positive

*Hand computation.* `q_k` mixes both, so `0 < x₂*, x₃* < 1` and both
indifference equations hold exactly:

```
(1 − x₃*)·δ₂ = x₃*·J₂₃ ,      (1 − x₂*)·δ₃ = x₂*·J₃₂ .
```

### 6.1 The sign facts, derived and not assumed

The packet asserts "both `J`-entries are nonnegative" without proof. That
assertion is *not* automatic — `J_ij = r_i({i,j}) − r_i({j})` has no sign in a
general quitting game — and if it failed the argument would genuinely collapse:
with `δ₂ < 0` the origin is not a root at `b_k`, the solution set is the single
point `q_k`, the local count is `1`, and there is no contradiction. So this step
is load-bearing.

It is however derivable, cheaply, from the hypothesis the consumer already
carries, `HasUniqueAllContinueAtCapLimit`. At the limiting cap `b̄`, both
binding players have `δ̄ = 0`, so on the face

```
ḡ₂ = x₃·J₂₃ ,     ḡ₃ = x₂·J₃₂ .
```

Take the root "only player 3 quits, with probability `t`", `t > 0` small.
Player 3 is indifferent (`ḡ₃ = 0` because `x₂ = 0`); player 2 needs
`ḡ₂ = t·J₂₃ ≤ 0`; the outsiders are strict Continue for small `t`. So if
`J₂₃ ≤ 0` that is a positive-absorption exact root at `b̄`, contradicting
uniqueness. Symmetrically for `J₃₂`. Hence

```
J₂₃ > 0 ,  J₃₂ > 0 ,  and then  δ₂ = x₃*·J₂₃/(1 − x₃*) > 0 ,  δ₃ > 0 ,
```

so both face slopes `δ + J` are positive and

```
g₂ < 0  ⟺  x₃ < x₃* ,        g₃ < 0  ⟺  x₂ < x₂* .
```

Two remarks. First, this replaces the packet's maximality argument for (4) with
something much shorter, and it needs no maximality at all. Second, it is not
circular: the limiting cap is used only to pin down the *fixed constants*
`J₂₃, J₃₂` of the game, while the parity certificate itself lives entirely at
the finite cap `b_k`.

### 6.2 The count

Face labels, with `M := ⌈p·x₂*⌉` and `N := ⌈p·x₃*⌉` (no tie handling needed —
the thresholds are strict inequalities, so `x₂ < x₂* ⟺ m < M`):

```
label 2  ⟺  m ≥ 1  ∧  n ≤ N−1
label 3  ⟺  ¬(label 2)  ∧  n ≥ 1 ∧ m ≤ M−1
label 4  ⟺  (m,n) = (0,0)   or   (m ≥ M ∧ n ≥ N)
```

For `p > 1/min(x₂*, x₃*)` (so `M, N ≥ 2`), enumerating Options A and B over all
`(m,n)` — anchor at the origin corner, anchor in the upper quadrant, and the
degenerate positions in between — gives **exactly two** complete simplices, both
with step order `σ = (3, 2, 1, 0)`:

| base | vertices (coords `0,1,2,3`) | labels |
|---|---|---|
| `(0,0,0,0)` | `0000, 0001, 0011, 0111, 1111` | `4,3,2,1,0` |
| `(0,0,M−1,N−1)` | `(0,0,M−1,N−1), (0,0,M−1,N), (0,0,M,N), (0,1,M,N), (1,1,M,N)` | `2,3,4,1,0` |

Both anchors, `(0,0,0,0)` and `(0,0,M,N)/p`, lie in `V` for large `p`. Every
other position clashes (two vertices claim the same label) or requires `M = 1`
or `N = 1`. So

```
boxComplementarityLocalCompleteSimplexParity problem p hp V = 2 = 0   in ZMod 2
```

for all large `p`, against the eventual `1`. Contradiction.

Sanity check on the geometry: the count `2` is the strict pure equilibrium
(index `+1`) plus the regular mixed coordination equilibrium (index `−1`),
which is exactly what the signed argument computes. The mod-two count sees only
`1 + 1`.

### 6.3 Why the 2-cube shortcut does *not* work

Worth recording, because it is the tempting simplification. One cannot run the
whole argument on the two-player face problem alone. The restricted 2×2
coordination game has *three* equilibria — all-Continue, the mixed point, and
both-Quit — with indices `+1, −1, +1` summing to `+1`. There is no
contradiction. Both-Quit is killed only by an outsider's deviation in the
4-player game, i.e. only by the maximum-absorption localization, which is a
genuinely 4-dimensional statement. The outsider coordinates must be present in
the cube; §5 is what keeps them from entering the arithmetic.

## 7. Exactly one binding hazard positive (the solo segment)

*Hand computation.* This is the case the packet handles with a cap-raising
homotopy, and it is where the shortcut pays best: **no homotopy is needed and
the count is zero for a trivial reason.**

Say player `2` is the solo mixer (`x₂ > 0`, `x₃ = 0`); the other sub-case is
symmetric with `2` and `3` exchanged. Since `2` mixes strictly and `x₃ = 0`,
`g₂(q_k) = −δ₂ = 0`, so `δ₂ = 0` and on the face

```
g₂ = x₃ · J₂₃    with  J₂₃ > 0   (§6.1, unchanged — it only used binding + uniqueness).
```

Hence `g₂ ≥ 0` everywhere on the face, and `x₂ < 1` throughout `V^{1/p}`. But
label `2` requires coordinates `0, 1` unviolated — i.e. being on the face — and
coordinate `2` violated, i.e. `g₂ < 0` or `x₂ = 1`. Both fail. **Label `2` is
unattainable, so no complete simplex has an anchor in `V`:**

```
boxComplementarityLocalCompleteSimplexParity problem p hp V = 0 .
```

In the other sub-case (`3` solo) it is label `3` that is unattainable, by the
same one-line argument. Either way the local count is `0` against the global `1`.

Two things this dodges. The solution component is the compact segment
`E_k = {(x₂, 0) : 0 ≤ x₂ ≤ x₂†}` — infinite, non-regular, and containing the
origin, so all-Continue is not even a strict equilibrium here. The parity-spec
route has to perturb it; the Sperner route never looks at it. And the region
`V` automatically contains all of `E_k`, because localization bounds every
solution coordinate by `α(q_k)` — no separate endpoint identity
`(1 − x_k)δ₃ = x_k J₃₂` is needed, which means the maximality argument for the
segment endpoint is not needed either.

## 8. The homotopy question, answered

The task asked for the explicit condition guaranteeing no zero touches
`∂V` along the cap-raising homotopy `b_{k,i} ↦ b_{k,i} + s·η`. **There is no
homotopy in this route, so the condition is vacuous.** For the record, the step
that would have been most likely to fail is the one the packet glosses as
"compactness of the boundary of a smaller isolating neighborhood and continuity
of the endpoint inequalities give one `η > 0`": raising `δ₂` from `0` to `η`
moves the mixed point to `x₃*(η) = η/(η + J₂₃)`, so the neighborhood must
contain the whole segment *and* the moving mixed point for all `s ∈ [0,1]`
while excluding everything else — and the outsider margins must survive the cap
change uniformly. That is a real uniformity obligation. Replacing it with
"label 2 never occurs on the face" is the single biggest simplification found
here.

## 9. Does it feed the existing consumer?

*Verified* by reading
`Research/Quitting/FinFourProducerAtlas/StrictRayBindingCardinality.lean`.

Partly. The mechanism is right, the plumbing is not.

- The final consumer `bindingFinset_card_ne_two_of_unique_allContinue` derives
  `False` by producing a solution outside the neighborhood and contradicting
  `contains_every_solution`. Our chain produces the same `False` from the same
  ingredients (all solutions inside `V`, computed parity `≠ 1`), so the *root it
  produces is consumed immediately*, not left dangling. This is not "another
  unconsumed positive root".
- But every structure in that file — `FinFourBindingPairFiniteCapParityWitness`,
  `FinFourBindingPairLocalParityZero`, `FinFourBindingPairParityCertificate` —
  is parameterized by `parity : ModTwoBoxComplementarityParitySpec (Fin 4)`,
  which is uninhabited by design and whose construction is precisely the general
  theory the shortcut avoids. As written those theorems cannot be instantiated
  by this route.
- Required change: a parallel certificate carrying Sperner-level data (late time
  `k`, bridge, permutation, region `V`, openness, `solutionSet ⊆ V`, and the
  eventual local count), and re-proofs of
  `bindingFinset_card_ne_two_of_unique_allContinue`,
  `bindingFinset_eq_univ_or_card_eq_three_of_unique_allContinue` and
  `positiveAbsorptionExactRoot_at_capLimit_or_bindingFinset_eq_univ_or_card_eq_three`.
  The latter two only consume `card ≠ 1` and `card ≠ 2`, so they transfer
  unchanged in substance.

The source-side hypotheses are available:
`quittingMaximalCapSemanticRoot_maximal` gives finite-cap root maximality;
`absorption_summable` gives `α(q_k) → 0`; `eventually_currentHazard_supported_binding`
gives support inside the binding set; `bindingFinset` plus `singleton_le_capLimit`
plus `cap_tendsto` give the outsider margin; `HasUniqueAllContinueAtCapLimit` is
already a field of the certificate and is what §6.1 consumes.

## 10. Which of the three ingredients still need general theory

- **Global mod-two degree** — already delivered, unconditionally, at every
  resolution, by `boxComplementarityLocalCompleteSimplexParity_univ`. No general
  theory needed.
- **One common isolating neighborhood for the homotopy** — evaporates. There is
  no homotopy. A single relatively open ball `V` suffices, and it is isolating
  for the trivial reason that every solution has sup-norm below `ε/2`.
- **Local parity zero** — computed in closed form, `2` and `0` respectively. No
  regularity notion, no local degree, no subdivision invariance, no
  perturbation invariance.

Two ingredients appear that the review did not list:

- **Kuhn structure**: from `simplex SC n I` (injective, monotone, `I_n ≤ I₀+1`),
  the `n` increments are `n` distinct unit vectors. Needed by §5.
- **Coordinate-order normalization** (§3): the computation is clean only for
  `A = {2,3}`.

A third, easy to miss: `QuittingEndpointNashBoxBridge` currently has **no
inhabitant anywhere in the repository**. Constructing one needs the
`UnitCube ι ≃ (ι → PMF Bool)` equivalence and continuity of the gain — the
latter is immediate from `quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle`
(a finite sum of products), the former is Bernoulli plumbing.

## 11. Pessimistic Lean estimate

| piece | pessimistic lines |
|---|---|
| Kuhn structure lemma | 250 |
| `BoxComplementarityProblem.permute` and solution transport | 150 |
| `QuittingEndpointNashBoxBridge` inhabitant (equiv + continuity) | 450 |
| face endpoint-difference evaluation at pair support | 200 |
| sign facts `J₂₃, J₃₂ > 0` from `HasUniqueAllContinueAtCapLimit` | 250 |
| finite-cap localization, outsider margin, choice of `k` | 500 |
| position-forcing lemma (§5) | 350 |
| both-mixed enumeration: exactly two complete simplices | 700 |
| solo enumeration: zero complete simplices | 250 |
| Sperner-level certificate and consumer rewiring | 250 |
| dichotomy and glue | 250 |
| **total** | **~3,600** |

For comparison, constructing a `ModTwoBoxComplementarityParitySpec (Fin 4)` —
regularity, subdivision invariance, homotopy invariance, the regular-counting
law — is a several-thousand-line effort with genuine research risk. The
shortcut is the cheaper branch by a wide margin, and it is bounded work rather
than open work.

## 12. Single most likely failure point

The **completeness direction of the both-mixed enumeration** (§6.2): proving in
Lean that no complete simplex *other than* the two exhibited ones has its anchor
in `V`. On paper it is a clean case split, but in Lean it becomes arithmetic on
`Fin (p+1)` indices under the `Fin.ofNat`-indexed `simplex` predicate, with the
`M, N ≥ 2` side conditions threaded through every branch. That is where I would
expect the 700-line estimate to be wrong by a factor.

Runner-up, and the only place I see residual *mathematical* risk rather than
formalization risk: the uniform outsider margin. `ρ` must be chosen from the
limiting data (`δ̄_h > 0` plus a reward-bound Lipschitz constant) and then hold
at the finite cap `b_k` *and* on the `1/p`-thickening of `V`. I believe this
closes — `b_k → b̄` makes `δ_{k,h} ≥ δ̄_h/2` eventually and the gain is
Lipschitz with an explicit constant — but it is the one quantifier order I would
re-check before committing.

## 13. Nonclaims

Nothing here is checked by Lean. No file was created, no build was run. This
note establishes that a specific finite computation exists and is correct on
paper; it does not establish that any theorem is proved. The source-level
results imported by reference (the tail-normalized cap flow, the strict-ray
producer, the reward-bound estimates) were not re-derived. The cardinality-three
face, the full-binding face, and the positive-absorption limiting root remain
untouched by this route.
