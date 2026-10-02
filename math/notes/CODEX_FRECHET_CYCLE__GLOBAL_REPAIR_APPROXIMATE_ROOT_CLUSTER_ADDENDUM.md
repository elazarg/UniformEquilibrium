# Approximate-root transport and payoff clusters of global repair minima

Author: `CODEX_FRECHET_CYCLE`.

Status: ordinary-mathematics addendum, not independently reviewed or
Lean-checked. It preserves the frozen finite-calendar proof and makes one
extension: an approximate root incurs its explicit one-stage Nash defect
as an additive cost in the same N+2 contraction. Consequently every exact
root at a payoff cluster of positive limiting global repair minima is
all-Continue. This is a direct finite-calendar route to the same cluster
uniqueness that RENY obtains through the compact maximum-debt carrier; it
is not an additional solution of the all-Continue branch.

## 1. Frozen input and exact additional statement

Use precisely the canonical Fin4 data, independent stopping-law semantics,
complete unrestricted caps, and joint relaxed geometric-repair optimization
m_N in
[`GLOBAL_REPAIR_PAYOFF_FLOOR_ESCAPE`](CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_PAYOFF_FLOOR_ESCAPE.md).
That input is frozen at SHA-256

```text
5a719508f3970be8e5e33721c29d44e049e83ad32d069cafba4afe743e762335.
```

Thus own singletons are `s=(1,0,0,0)`, rewards have absolute value at most
`M≥1`, every nonpivot ranges over all laws on
`F_N={0,…,N−1,Never}`, and the pivot has a finite head and geometric tail,
including the relaxed `α=0<λ` boundary. The optimizer's prescribed payoff
vector U is exactly realized by positive-α implementations even at that
boundary. Its value satisfies `m=m_N∈[0,2M]`.

For any independent root `q∈[0,1]^4`, let Q_i(q) and C_i(q;U) be player
i's Quit and Continue endpoints in the one-stage game with all-Continue
reward U. Define its prescribed root payoff V_i and root Nash defect e_i:

```text
c_i(q)=∏_(j≠i)(1−q_j),       a(q)=1−∏_i(1−q_i),
V_i(q;U)=q_i Q_i(q)+(1−q_i)C_i(q;U),
e_i(q;U)=max(Q_i(q),C_i(q;U))−V_i(q;U)≥0,
e(q;U)=max_i e_i(q;U).
```

These are finite one-stage quantities; e is not the full terminal regret
of an implemented profile. An exact root is precisely one with e=0.

**Approximate-root extension.** For every global relaxed optimizer at N
with `m=m_N>0`, and **every** independent root q,

```text
m_(N+2) ≤ m − a(q)m²/(32M) + e(q;U).                    (AR)
```

Unlike the frozen exact-root theorem, q need not be selected from the
Nash correspondence at U. This additional flexibility is what permits
the fixed-root cluster argument below.

## 2. Prefix identity with the root defect retained

First take an implementable source profile with actual debts d_i and
payoff U. Prefix q literally at a new date, then shift the complete source
law by one date. Its unrestricted cap is still

```text
B′_i=max(Q_i(q),C_i(q;U)+c_i(q)d_i).
```

Its prescribed payoff is V_i(q;U), not necessarily the larger endpoint.
Adding and subtracting the larger endpoint gives the exact identity

```text
d′_i=[c_i(q)d_i−(Q_i(q)−C_i(q;U))_+]_+ + e_i(q;U)
     ≤c_i(q)d_i+e_i(q;U).                               (Pε)
```

This follows from the same unrestricted cap decomposition as the frozen
proof. It does not assert that q is Nash or that its prefix preserves a
continuation equilibrium.

If a=0, (AR) follows already from `m_(N+2)≤m_N` and e≥0. Otherwise choose
k with largest q_k, so `q_k≥a/4`. With `d_i≤m` and `e=e(q;U)`, (Pε) gives

```text
d′_k≤m+e,             d′_j≤(1−a/4)m+e  (j≠k).
```

Use the complete pure best reply τ_k from Section 5 of the frozen proof,
and privately mix it into k's entire law with
`θ=am/(32M)`. Its own debt is multiplied by `1−θ`; every other debt
increases by at most `4Mθ`. Thus

```text
d″_k≤(1−θ)(m+e)≤m−am²/(32M)+e,
d″_j≤(1−a/4)m+e+4Mθ=m−am/8+e  (j≠k).
```

Since `m≤2M`, both bounds are at most `m−am²/(32M)+e`.
The response remains in `{0,…,N+1,Never}`: its support proof uses only
the finite-opponent/geometric-pivot shape, not exact root Nash. The
resulting profile therefore belongs literally to the N+2 geometric family
by exactly the same head/tail bookkeeping. This proves (AR) for a literal
source optimizer.

For `α=0<λ`, implement the source with positive α and full regret at most
`m+ε`. Its U, q, a, e and θ remain fixed. The two displayed upper bounds
merely acquire an additional ε. Every repaired profile is in the same
N+2 family, independently of ε. Taking the numerical infimum as ε tends
to zero proves (AR) on the relaxed boundary. Neither cap weak-limit
continuity nor attainment by a literal optimizer is required.

## 3. A root fixed at a nearby continuation

For fixed q, Q_i(q) is independent of the continuation vector and

```text
C_i(q;U)−C_i(q;W)=c_i(q)(U_i−W_i),
V_i(q;U)−V_i(q;W)=(1−q_i)c_i(q)(U_i−W_i).
```

Both the maximum of the two endpoints and the prescribed root payoff
are 1-Lipschitz in U in the sup norm. Hence

```text
|e_i(q;U)−e_i(q;W)|≤2‖U−W‖∞.
```

In particular, if q is exact Nash against W, then

```text
e(q;U)≤2‖U−W‖∞.
```

Substituting in (AR) gives the directly usable inequality

```text
m_(N+2)≤m_N−a(q)m_N²/(32M)+2‖U−W‖∞                    (NEAR)
```

for every exact root at W and every global optimizer payoff U at N.
The root at W is held fixed. No nearby exact root at U is asserted.

## 4. Every exact root at a positive-limit payoff cluster is all-Continue

Let `m_N↓m_∞>0`, choose arbitrary global optimizers along a sequence
`N_ℓ→∞`, and suppose their payoff vectors converge to W. Such payoff
subsequences exist because they lie in the finite box `[-M,M]^4`.

Fix **any** exact root q against W; finite mixed Nash existence assures
at least one. Apply (NEAR) to every source optimizer along this sequence.
Both `m_(N_ℓ)` and `m_(N_ℓ+2)` tend to m_∞, while the payoff-distance term
tends to zero. Therefore

```text
m_∞≤m_∞−a(q)m_∞²/(32M).
```

Since m_∞>0, necessarily a(q)=0, so every q_i=0. As the chosen exact
root was arbitrary, **all-Continue is the unique exact root against W**.
Its Nash inequalities also give `W_i≥s_i` for every i.

This is stronger than merely saying that the absorption masses of exact
roots at the source U_N tend to zero. It does not infer lower
hemicontinuity of the exact-root correspondence. The proof instead uses
a root at the limiting payoff as an approximate root at each source and
pays the resulting finite defect explicitly.

## 5. Comparison, status, and precise limit of the result

Before writing this addendum, the complete 261-line note
[`CODEX_RENY__MAXIMUM_DEBT_MINIMUM_TIES_AND_ACTUAL_ROOT_UNIQUENESS.md`](CODEX_RENY__MAXIMUM_DEBT_MINIMUM_TIES_AND_ACTUAL_ROOT_UNIQUENESS.md)
was read. It proves two distinct compact-minimum facts for arbitrary
finite player sets and signed reward tables: a positive minimum of maximum
debt has at least two maximizing coordinates; and every exact root at
its actual payoff is all-Continue. It handles nonattainment using actual
approximating profiles and separately selected approximate full replies.
Its geometric-compression comparison then identifies m_N with a sequence
decreasing to the unrestricted maximum-debt infimum, giving the same
payoff-cluster uniqueness as Section 4 here.

That attained-carrier geometry and this finite-calendar estimate are
different proofs, not different cluster conclusions. The present
additional formula is (AR), with a finite root defect as an additive cost
and the same fixed N+2 incidence. It does not claim a novel qualitative
cluster-isolation theorem beyond RENY's argument. The checked-source
comparison remains Section 8 of the frozen input; in particular the
existing actual-U all-Continue existence theorem and strict auxiliary
shift uniqueness theorem must not be conflated.

Neither proof excludes the actual-U all-Continue region. Unique exact
root at W does not assert strict inequalities `W_i>s_i`, exact-root
uniqueness throughout a neighborhood, or a positive-absorption choice
near W. No positive lower bound for a joint repair decrement in that
residual region has been proved here, and no general convergence
`m_N→0`, finite-menu producer, or uniform-equilibrium conclusion is made.

Requested independent check: (Pε), the additive e coefficient through the
one-coordinate reply, the unchanged N+2 incidence on the relaxed boundary,
and the fixed-root limiting argument. The unresolved research question
remains the construction of a genuinely joint product-law improvement
inside the actual-U all-Continue region.
