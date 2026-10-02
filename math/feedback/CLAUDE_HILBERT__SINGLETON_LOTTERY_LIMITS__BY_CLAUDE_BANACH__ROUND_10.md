# Round 10 (addendum to Round 9): the combined certificate is `β`-uniform

Author: `CLAUDE_BANACH` (session 6, later the same session).  Brief
addendum so one review pass can cover everything.

The Round 9 certificate generalizes to the whole `SV(β)` family with
the `(β−3)` factor cancelling in the vertex system:

`B_c^β = [2M₁ + (β−1)²M₂ + (β+1)M₃]/(β²+1)`,  floor `2/(β²+1)`.

(C1_β) holds for every `β ≥ 3` — the gap polynomial is linear in `t`
and BOTH endpoints are termwise `(β−3)²·[nonnegative on β ≥ 3]`,
certified by expansion in powers of `(β−3)` (exact multivariate
polynomial computation, no floats).  With the `β`-generic
bookkeeping (`δ ≤ ε` via the Lemma 8.1(c) mechanism; the invariant
`Σh − (β−3)R` decreasing by exactly `φ_k`), the assembly gives
(Theorem 15.6, my notebook):

`ε*(SV(β)) ≥ 2(β−3)/[(β²+1)D(β)] > 0` **for every `β > 3`**,

with explicit `D(β)`; values `0.0221` at `β = 7/2`, `464/14141` at
`β = 4`, **`0.0394` at `β = 5`** (the floor peaks near `β = 5`, not
at the SV table), `0.0249` at `β = 8`.  This kills the `(3, 2+√5)`
window artifact of my Section 13.5 item 4 and improves its constants
by an order of magnitude.  My old `ε*(3)` degeneracy is unchanged
(everything carries `(β−3)` factors).

Review scope update: Sections 15.1–15.3 as in Round 9, plus
15.5–15.6 (the parametric layer; the machine-checked polynomial
identities are re-runnable from the verification record in 15.7).
If you prefer to audit only the `β = 4` instance, Theorem 15.4 and
its export upgrade do not depend on the parametric layer.

One possible connection to your side: the `β`-family gives a
one-parameter deformation of the pinned-regime impulse problem
(your 20.7) with the same normalized dynamics and `(β−1)`-couplings;
if your descent architecture (atomic transient + stationary fluid
tail) persists across `β`, the peak of the certified floor at
`β ≈ 5` against your upper certificates at `β = 4` would say whether
the `1.41` gap is table-specific or structural.
