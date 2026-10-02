# Review of the robust blocker-switch theorem

Reviewer: `CODEX_NOETHER`
Reviewed note: `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`
Scope: Proposition 6, its stationary/uniform compilation, and the stated
strictness and overlap claims
Verdict: `VALID WITH A ROBUSTNESS QUALIFICATION`

## Claim checked

Let `I` be nonempty and finite, let `pi` be a fixed-point-free permutation,
and assume:

1. `r(S)_i=0` whenever `i` does not belong to the nonempty quitting coalition
   `S`; and
2. for every `i` and `T subset I-{i,pi(i)}`,

   `r(T union {i})_i>0` and
   `r(T union {i,pi(i)})_i<0`.

Proposition 6 claims an interior product root at which every pure-Quit and
pure-Continue endpoint has value zero, followed by exact terminal Nash and
uniform-equilibrium payoff zero against unrestricted behavioral deviations.

## Poincare--Miranda audit

For fixed `i`, the pure-Quit value `Q_i(p)` is a finite multilinear polynomial
in the opponents' quit probabilities and is independent of `p_i`; continuity
is therefore immediate. On the face `p_(pi(i))=0`, its expansion is a convex
combination over exactly the coalitions `T subset I-{i,pi(i)}` of the positive
numbers `r(T union {i})_i`. It is strictly positive, including when some other
probabilities are zero or one. On the opposite face it is a convex combination
of exactly the negative numbers `r(T union {i,pi(i)})_i`, hence is strictly
negative. Arbitrary nonlinear dependence on the remaining quitting coalition
does not affect either sign.

Because `pi` is a permutation, reindexing by
`F_j=Q_(pi^{-1}(j))` assigns these opposite signs to the two faces for the
same cube coordinate `p_j`. The Brouwer reduction in the note is sound. For

`H_j(p)=clamp_[0,1](p_j+F_j(p))`,

a fixed point cannot have `p_j=0` or `p_j=1` by the strict face signs. At an
interior fixed point the clamp cannot return an interior value from an input
outside `[0,1]`; it is therefore inactive and `F_j=0`. Thus all coordinates
of `p` are strictly between zero and one and all `Q_i(p)` vanish. No additional
monotonicity or additivity hypothesis is being used silently.

## Endpoint and unrestricted-deviation audit

At target zero, pure Continue for player `i` has value zero: every absorbing
coalition formed by opponents omits `i` and pays it zero by passive continuers,
while all-Continue returns continuation zero. Pure Quit has value `Q_i(p)=0`.
The prescribed endpoint mixture is therefore zero, giving both the fixed-point
identity and exact endpoint Nash.

The checked corollaries used in the note have exactly the required scope:

- `isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`; and
- `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`

in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.

Joint absorption holds because every quit probability is positive. For each
player `i`, the distinct opponent `pi(i)` quits with positive probability, so
the all-opponents-Continue mass is strictly below one. These are precisely the
joint and playerwise contraction hypotheses of the named corollaries. Their
conclusions cover unrestricted behavioral deviations; Proposition 6 is not
merely a stationary-deviation verifier.

## Actual-data and strictness audit

The two hypothesis families are finite equalities/strict inequalities on the
raw reward table and force existence of a root without taking a root as input.
This is a genuine actual-data producer for a special class, rather than a
supplied-root verifier.

Proposition 5 is a strict special case of Proposition 6. For an exact witness,
take a three-cycle and keep passive continuers. In one quitting row, let the
positive reward be `1` or `2` according as the third player Continues or Quits,
and the blocker-present reward be `-1` or `-2` on those same backgrounds; use
any analogous strict-sign rows for the other players. The uniform blocker
switch holds, but that row cannot be represented by Proposition 5's two
background-independent constants `A_i,-B_i`.

The overlap qualifications in the note are correct. Every three-player
instance already has existence-level coverage through
`quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three`
(`UniformEquilibrium/Quitting/Classification/PlayerReindex.lean`). The uniform
five-cycle center is covered by `exists_uniformEquilibriumPayoff_colliderReward`
(`UniformEquilibrium/Quitting/Classification/Circulant/TerminalExploitabilityColliderClosure.lean`).
For an odd single blocker cycle, the strict signs also rule out a pure sure
exit coalition: membership would have to alternate around the odd cycle. This
does not apply to every fixed-point-free permutation, since even cycle
components do admit alternating coalitions.

## Required wording correction

The core theorem is valid, but two robustness phrases are too broad in the
ambient space of all reward tables. Passive-continuers is an exact family of
zero equalities. Consequently Proposition 6 is robust only under perturbations
of the *quitter entries* which preserve the strict signs while keeping all
continuer entries exactly zero. Its class is relatively open inside the
passive-continuers affine subspace, not an open subset of the full reward-table
space. In particular, the phrases “perturbations of every reward entry” and
“an actual open set of asymmetric tables” should carry that qualification.
Small nonzero perturbations of continuer rewards can destroy the zero Continue
endpoint and the zero fixed target, so they are not covered by the proof.

## Exact weak-sign boundary tests

Strictness is genuinely used to force an interior root. With two players who
block each other, passive continuers, solo quitting payoff `1`, and joint
quitting payoff `0`, the weak signs hold but

`Q_1(p)=1-p_2`, `Q_2(p)=1-p_1`.

The unique zero is the boundary point `(1,1)`, not an interior root (it still
gives a contracting exact zero equilibrium). Conversely, with solo payoff
`0` and joint payoff `-1`, the common zero is all-Continue and contraction is
not forced. Thus replacing strict by non-strict signs needs a separate boundary
selection/admissibility theorem; the present Poincare--Miranda proof does not
silently supply one.

## Recommendation

Proposition 6's mathematical and semantic conclusions survive independent
review. Correct the ambient robustness/open-set wording before treating the
claim as export-ready; no change to the theorem hypotheses or conclusion is
otherwise needed.
