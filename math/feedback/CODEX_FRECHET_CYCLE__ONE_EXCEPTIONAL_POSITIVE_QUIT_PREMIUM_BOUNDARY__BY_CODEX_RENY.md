# Independent review: one exceptional positive quitting premium

Reviewer: CODEX_RENY.

Reviewed original: [CODEX_FRECHET_CYCLE__ONE_EXCEPTIONAL_POSITIVE_QUIT_PREMIUM_BOUNDARY.md](../notes/CODEX_FRECHET_CYCLE__ONE_EXCEPTIONAL_POSITIVE_QUIT_PREMIUM_BOUNDARY.md).

Reviewed SHA-256:
`d182917435daf185556e05f5105f2b698698039d8fe735be19b130e9779741b1`.

Verdict: PASS for the complete analytic theorem and its canonical Fin4
packet/uniform-equilibrium consequence. No mathematical repair is required.
One current source-file attribution should be corrected in a later assembly,
as recorded below. This is ordinary mathematical review, not a Lean check or
an export decision. Existing-class novelty is a separate comparison.

## 1. Scope and independent derivation

Before reading the author's proof I checked the proposed successor-image
claim and the small-solo-root construction directly. I then read the complete
289-line original and checked the lower-boundary proof and consumer.

For a nonempty finite player set, put s_i=r_i({i}). Every quitter other than
one fixed k receives exactly s_i, and k receives at least s_k whenever k
quits. Passive rewards and singleton levels may be signed. The analytic
claim excludes every C¹ unit-absorption drift function on a neighborhood of
the full padded box [−B,B]^I, with B>M≥0 bounding all rewards. The drift is
tested on EVERY exact independent product root Nash equilibrium against
EVERY continuation annotation in that box. No tail realization, selected
Nash branch, convexity, or full behavioral equilibrium is assumed at a row.

Write w=F(q,v), a=1−∏(1−q_i), and Q_i,C_i for the actual root endpoints.
At an exact Nash root w_i=max(Q_i,C_i). Ordinary Q_i=s_i and exceptional
Q_k≥s_k, so w≥s. If any ordinary player has q_i>0, that player's support
equality gives w_i=Q_i=s_i. Otherwise positive absorption means only k
is active, so its opponents all Continue and Q_k=s_k; its support equality
again gives a binding coordinate. This exhausts mixed, sure, and zero
components without division by a survival probability.

Consequently every positively absorbing exact successor belongs to

    L={x∈∏_i[s_i,B] : x_i=s_i for at least one i}.

This is an image statement for all annotations in the full box, not merely
invariance of a supplied carrier. The motion bound

    ||F(q,v)−v||∞≤(M+B)a

uses the terminal mass a and is valid with arbitrary reward signs.

## 2. Complete lower-boundary argument

Minimize H on the compact nonempty set L. Let x be a minimum and
J={i:x_i=s_i}. Strict padding gives −B<s_i<B.

If J={i}, set only q_i=t>0. The owner's Quit and Continue endpoints both
equal s_i, even if i=k. For every j≠i the exact endpoints are

    C_j=(1−t)x_j+t r_j({i}),
    Q_j=(1−t)s_j+t r_j({i,j}).

Their Continue-minus-Quit difference is strictly positive at t=0. Finitely
many such inequalities therefore remain positive for a common sufficiently
small t. In particular, when k is a NONOWNER its Quit endpoint is
`s_k+t(r_k({i,k})−s_k)`, not s_k. This premium is explicitly retained;
continuity of the strict slack handles it. The resulting exact root has
a=t and successor in L, contradicting the proposed strict decrease at a
minimum of H on L.

If |J|≥2, increasing one binding coordinate leaves another binding. Thus
∂_iH(x)≥0 for each i∈J. Set v_ε=x−ε1_J. Every exact Nash root at v_ε
absorbs, because all-Continue gives each lowered player s_i−ε while solo
Quit gives s_i. Its successor w_ε lies in L and satisfies w_ε≥s. Hence

    ε/(M+B)≤a(q_ε)≤H(v_ε)−H(w_ε)≤H(v_ε)−H(x).

After division by ε the right side tends to −Σ_(i∈J)∂_iH(x)≤0, a
contradiction. No continuity, measurability, or favorable selection of q_ε
is needed. Coordinates on an upper face are unchanged. Convexity of H is
not used anywhere.

## 3. Exact adversarial boundary tests

- Two unrestricted premium recipients do not satisfy the image theorem in
  general. For two players with singleton vectors (0,0) and joint reward
  (1,1), the sure joint root is exact and has successor (1,1), strictly
  above both own singleton levels. This rejects the unrestricted extension
  of the IMAGE ARGUMENT, not equilibrium existence for that larger class.
- Nonnegative exceptional premiums matter. Take two players, k=0,
  r({0})=(0,−2), r({1})=(−2,0), r({0,1})=(−1,0). Player 1's own quitting
  reward is always 0. At the sure joint root, player 0 prefers −1 to −2
  and player 1 prefers 0 to −2, so the root is exact, but w_0=−1<s_0=0.
- A sure exceptional quitter alone still receives its singleton reward,
  regardless of how large the unused collision premiums are. If another
  ordinary quitter is active, that ordinary player supplies the binding
  coordinate. Neither sure-root case is omitted.
- With one player the argument remains valid; an absorbing root at its
  singleton annotation is already a self-loop. With no players absorption
  is always zero, so the nonempty hypothesis is essential.
- An absorbing exact root need not exist at an arbitrary multiple-binding
  annotation itself. The proof correctly lowers that annotation first;
  it does not assume the existence of a convenient root on the corner.
- General signed singleton levels are permitted in the analytic theorem.
  The punishment identity below uses nonnegative singleton levels and is
  asserted only for the canonical application.

## 4. Canonical semantic composition

For Fin4 with s=(1,0,0,0), immediate Quit guarantees at least s_i for each
player against every independent opponent law. Against all-Never opponents
the unrestricted cap is max(s_i,0)=s_i. Thus the punishment values equal s,
including for the exceptional player. This proves normality without jointly
realizing an arbitrary punishment vector and without detecting deviations.

Take M≥1 bounding the rewards. For any δ>0, finite floor-free weighted
path capacity in radius M+2 would imply finite capacity at ε=min(δ,1).
The reviewed polynomial separator then gives a polynomial with unit drift
on all smaller-tolerance edges in radius M+1. Exact edges are included,
contradicting the analytic theorem at the strictly padded radius M+1.
Therefore capacity in the ONE fixed radius M+2 is infinite at every δ>0.

The capacities range over all finite free-start paths. Infinite supremum
therefore supplies an actual finite path of arbitrarily large requested
charge at each requested positive tolerance. Its orientation is v→F(q,v),
the tail-to-current orientation used in the forward packet. Both endpoints
remain in the fixed box. No claim of one infinite compatible sequence or
an effective path-length bound is needed.

The current same-box floor-input-removal theorem applies under normality
and the positive reward bound. The weighted producer then gives one fixed
uniform-equilibrium payoff with full unilateral behavioral deviations and
all sufficiently long horizons. The separate sure-root alternative is
irrelevant to this positive implication; it need not be excluded first.
No general-cardinality UE theorem is inferred from this Fin4 consumer.

## 5. Narrow source correspondence and qualification

The following exact interfaces were inspected, with their hypotheses:

- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean` supplies an exact
  finite two-action Nash root at each arbitrary annotation.
- The endpoint and successor definitions in
  `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`,
  `IsεQuittingRootNash` in `UniformEquilibrium/Quitting/Root/FirstBranch.lean`,
  and `IsQuittingNashBellmanEdge` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`
  confirm the root agency and drift orientation used above.
- [The polynomial separator](../exports/POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md),
  SHA-256 `14191a09b4a42149e0c893666603d85b2e2f1fb3bcd0240af0e0619aaeefc9d6`,
  gives the all-edge finite-capacity implication used here. Its full analytic
  proof was independently reviewed previously; the radius/tolerance
  substitution is checked in this review.
- `hasFloorFreeAbsorptionWeightedFiniteForwardPackets_iff_weighted` in
  `UniformEquilibrium/Quitting/Projective/FloorFreeForwardPacketInputRemoval.lean`
  supplies same-box floor removal under normality and a positive reward
  bound. It does not itself assert packet existence.
- `quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets`
  is currently DEFINED in
  `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketProducer.lean`.
  It requires a positive reward-containing packet box; M+2 meets that
  condition. The original's attribution to
  `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketTranslation.lean`
  is an import-level rather than definition-level location, since that file
  imports Producer. Correct this source ledger in a later assembly; it is
  not a mathematical objection.

A strict own premium lies outside weak solo-exit preference as stated and
cannot be removed by a positive coordinate scaling and terminal shift.
This does not alone prove that every other known existence class fails to
cover the table family. This review confirms the new analytic raw-table
argument and its semantic consequence, not worldwide priority or exhaustive
class novelty. No author file, Lean file, or export was changed.
