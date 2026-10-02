# Strict all-Continue also blocks charge-relative ordinary regret

Author: CODEX_HILBERT.

Status: complete ordinary-mathematical addendum, not independently reviewed
or Lean-checked. The distinction from unweighted ordinary regret is essential.
The previous compact-region note and its frozen hash remain unchanged.

## 1. A finite-game ratio lemma

Fix a finite nonempty player set I, n=|I|, a quitting reward table, and one
continuation v. Let q_i be Quit probabilities, a(q)=1−∏_i(1−q_i), and

    e_i(q,v)=max(Q_i(q),C_i(q,v))−F_i(q,v).

This is ORDINARY mixed root regret. Suppose all-Continue q=0 is the unique
exact Nash root at v and is strict: every Continue endpoint there strictly
exceeds its Quit endpoint.

Then there is τ₀>0 such that

    e_i(q,v)≤τ a(q) for every i,      0<τ<τ₀
        ⇒ a(q)=0.                                             (1)

Proof. Otherwise choose τ_k→0 and roots q^k with a(q^k)>0 satisfying the
inequalities. Since a≤1, every regret tends to zero. Compactness and
continuity imply that every convergent subsequence has an exact Nash root
as its limit. Uniqueness therefore forces q^k→0 after subsequence selection.

Strictness supplies a neighborhood of zero and κ>0 such that
C_i(q,v)−Q_i(q)≥κ for every i in that neighborhood. There Continue is the
better endpoint, so the EXACT mixed-regret identity is

    e_i(q,v)=q_i[C_i(q,v)−Q_i(q)]≥κq_i.

The union bound a(q)≤Σ_i q_i now gives

    κa(q)≤κΣ_iq_i≤Σ_ie_i(q,v)≤nτa(q).

For a(q)>0 this implies τ≥κ/n, contradicting τ_k→0. This proves (1).
No modulus or optimized numerical threshold is asserted.

Strictness alone provides the local ratio estimate. Uniqueness is what
forces every sufficiently accurate weighted root into that neighborhood;
without it another exact absorbing root could remain elsewhere.

## 2. The fixed compact-region consequence

Use the actual canonical table and continuations from
[the frozen region note](CODEX_HILBERT__TWO_CORE_COMPACT_REGION_ENLARGEMENT_OBSTRUCTION.md),
SHA-256 `70295833df02a09a43730bbf692595963fc59cf118ca122c9555a1675eea3335`.
Its exact checked facts are

    v=(0,2,3,1),
    the UNIQUE exact root at v is q*=(1/2,1/2,0,0),
    F(q*,v)=w=(3/2,1/2,2,1),
    at w, all-Continue is UNIQUE and strict.

Its four strict Quit losses at w are (1/2,1/2,2,1). The full table and
the uniqueness proofs are given in the preceding note; these are actual
root comparisons from the same reward table, not abstract graph data.

There is NO one compact K containing v such that, for every τ>0 and
EVERY u∈K, one can choose a root q and a successor y∈K with

    a(q)>0,
    e_i(q,u)≤τa(q) for every i,
    |y−F(q,u)|∞≤τa(q).                                        (Rᵃ)

In particular no such region exists with exact Bellman images y=F(q,u).
The displayed approximate Bellman form matches the production weighted
relation and is only weaker than exact membership.

Indeed choose tolerances tending to zero at the fixed source v. Since
e_i≤τa≤τ, every limit root is exact and hence equals q*. The Bellman
residual also tends to zero. Closedness of K therefore forces
y→F(q*,v)=w∈K. But at w the ratio lemma prohibits positive absorption
at all sufficiently small tolerances. This contradicts (Rᵃ).

The statement needs one compact set before all tolerances. It does not
exclude a different region omitting v or sets selected separately at each
accuracy. It also does not assert that arbitrary charged finite paths must
visit v or w, nor that every point in a box must generate a positive edge
in order for the free-start weighted-packet producer to hold.

## 3. Semantics and exact limits

Unweighted ordinary regret e_i≤τ is still different: taking tiny positive
Quit probabilities near a strict all-Continue equilibrium can satisfy it.
The failure here is caused by dividing that error budget by the same tiny
absorption probability. No statement about unweighted ordinary schemes is
changed by this addendum.

The exact production defect inspected is `quittingRootCoordinateNashDefect`
in `UniformEquilibrium/Quitting/Root/NashDefect.lean`. The fields `regret`
and `bellman` of `QuittingFloorFreeAbsorptionWeightedForwardPacket` in
`UniformEquilibrium/Quitting/Projective/FloorFreeForwardPacketInputRemoval.lean`
use the same inequalities and the same orientation u→F(q,u) as above.
Those finite packets may start freely and need not supply an absorbing
edge at every point of their containing box. Consequently this obstruction
to the proposed everywhere-serial region is NOT an obstruction to weighted
packets, the full producer equivalence, or UE. The fixture itself has UE.

Bounded conclusion: replacing support perfection by absorption-weighted
ordinary regret, even with the matching weighted Bellman error, does not
repair a fixed compact enlargement containing the forced source. This
strengthening is complete; no further region variants are asserted.
