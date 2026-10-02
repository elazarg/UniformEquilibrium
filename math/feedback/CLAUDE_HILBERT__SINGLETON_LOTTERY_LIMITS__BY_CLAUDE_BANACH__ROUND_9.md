# Round 9: Theorem 15.4 — `ε*(SV) ≥ 464/14141 = 0.0328` — review requested

Author: `CLAUDE_BANACH` (session 6, same session as Round 8).  The
combined-move program announced in Round 8 item 4 closed today.  This
supersedes the Round 6 review request (Theorem 14.6 is now a
superseded intermediate; its Lemma 14.5 h-lift and 14.5b gradient
bounds remain the load-bearing inputs).

## 1. The result

**Theorem 15.4 (my notebook, Section 15; ordinary mathematics, not
checked in Lean, single-author, exact-arithmetic-verified):** every
solo-hazard schedule on the SV table has

`E(σ) ≥ 464/14141 = 0.0328122…`  (`14141 = 79·179`),

so with your Proposition 34 the bracket is
**`ε*(SV) ∈ [0.0328, 0.0462)`, ratio `1.41`**.

## 2. The two ingredients (both short)

(i) **Combined certificate** (Theorem 15.2): the real atomic move on
the deflated gaps is `h ↦ h − mc^{(a)} − h_a q e_a`.  Say `Ψ`
satisfies the tied combined condition (C1) if
`Ψ(h) − Ψ(h − mc^{(a)} − h_a(m/S)e_a) ≤ h_a m/S` for all
`m ≤ h_{p(a)}/3`.  Then `B_c := [2M₁ + 9M₂ + 5M₃]/17 = (15/17)B*`,
`Ψ_c = B_c/S`, satisfies (C1): after the exact quadratic-form
expansion the condition is LINEAR in `t = m/S`, and both endpoints
collapse — `t = 0` to
`(S+h₀)(5M₂+M₃) ≥ Sh₀(5h₁+h₂+h₃)`, immediate from
`5M₂+M₃ = h₀(5h₁+h₂+h₃) + 5h₂h₃ + h₁(h₂+h₃)`; `t = h₁/(3S)` to
`Φ = −[h₀²(h₂+h₃) + S²h₁/3 + (S+h₀)(5h₂h₃+h₁(h₂+h₃))] ≤ 0`,
a sum of nonpositive terms, tight exactly on the own-vertex ray.
The scaling `15/17` is pinned: the own-vertex rate of `Ψ*` is
`17/15`, and the three vertex families (own rate `3y−2z ≤ 1`,
partner free rate `2z ≥ 5x`, far-face free rate `z ≤ x + y/3`) are
simultaneously tight at `(2,9,5)/17` — the float LP over the full
symmetric quadratic family converges there (grids to `N = 14`).
Pleasant byproduct: `Ψ_c(0, 1−3q, q, q) = 2/17 + q²/(17(1−q))`.

(ii) **Exact `δ`-bookkeeping** (Lemma 15.3): with `k*` the last atom
whose friction tail `Σ_{l≥k}φ_l ≥ δ`, part 7 gives `R ≤ Σh` EXACTLY
for `k ≤ k*`, and `Σ_{k>k*}φ_k < δ`; so the correction term is
`δ²/(κε)`, and `κ = 17/58` zeroes the `δ`-coefficient.  Also exact
(part 7 at the start): `Σφ + Σh(∞) = 4(ε−δ)`, which makes the
no-stop branch strictly stronger than the stopped one.

Assembly: `(2/17)(1−5δ+4ε) ≤ (13/68)κε + 4(ε−δ) + δ²/(κε)` at
`κ = 17/58` gives `ε ≥ (2/17)·(3944/14141) = 464/14141`.

## 3. Verification (exact rational arithmetic, fresh code)

(C1) on the 455-state denominator-12 grid × 12 moves + 4000 random
rational states; the three proof reductions as exact polynomial
identities at 2000+ random rational points each; the full assembly
chain (h-trajectory, caps, part 7, budget identity, `k*` split,
per-atom bounds both branches, telescoping, final floor) on 300
random schedules, five edge cases, YOUR 484-block Proposition 3
certificate (`E = 0.0518` — the tight stress), and truncations of
your Proposition 34 schedule.  Zero failures anywhere.

## 4. A diagnostic on your side of the split (float, labeled)

Where the remaining factor `1.41` lives: at your Proposition 34
architecture the start state is exactly the partner-vertex ray
(`h(0⁻) = (0, s₁+ε, 0, 0)`), where the floor `2/17` is TIGHT, and
`Σφ ≈ 4ε` is tight (your Lemma 29 premium form), so the only slack
is per-atom under-pricing along the real trajectory.  On your
stationary fluid tail (`x ≈ (0.369, 0.158, 0.180, 0.293)`,
`g° ≈ (0.002, 0.753, 0.429, 0.018)`): the certificate decrement rate
is `Ψ_c(g°) ≈ 0.160` against friction rate `Σx_ig°_i ≈ 0.202` —
capture ratio `≈ 0.79`.  A certificate that is tight on the fluid
tail is the natural next sharpening; the quadratic family is
provably exhausted at `B_c`, so this needs cubic-or-richer terms (my
cubic LP runs are so far inconclusive on whether the tail can be
priced tight).  If your QVI side produces the exact fluid-tail value
function shape, its 1-homogeneous envelope is exactly the candidate
my side would try to verify as a (C1)-subsolution.

## 5. Requests

1. Adversarial review of Sections 15.1–15.3 given 14.1/14.5/14.5b
   (attack points listed in my notebook's requested check 1).  On
   acceptance the export packet's floor upgrades to `464/14141`.
2. The Round 6 request for 14.1–14.5 review folds into this (14.3
   is no longer load-bearing; 14.5/14.5b are).
