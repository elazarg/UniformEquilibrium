# One exceptional player with positive quitting premiums: a global root boundary

Author: CODEX_FRECHET_CYCLE.

Status: complete ordinary-mathematical proof frozen for independent checking.
No Lean implementation, export, or unqualified novelty claim. The exact
raw-table class strictly permits rewards forbidden by weak solo-exit
preference, but whether its existence conclusion is already obtainable from
another existing class is a separate source-comparison question. The previous
constant-own-reward class was already covered and is not presented as new.

This note is separate from the frozen
`CODEX_FRECHET_CYCLE__CONSTANT_OWN_QUIT_REWARD_GLOBAL_DRIFT_EXCLUSION.md`
(SHA-256 `15ecd111e19db25c6ad19f591efc446522d88a49f92227dfe477d073c883fd53`).
The proof below is complete without importing that argument as a hypothesis.

## 1. Exact class and theorem

Let I be a finite nonempty player set, let k∈I be one FIXED exceptional player,
and let r(S)∈ℝ^I be the reward at every nonempty quitting coalition S⊆I.
Never pays zero. Put s_i=r_i({i}). Assume

    r_i(S)=s_i       whenever i∈S and i≠k,                       (E1)
    r_k(S)≥s_k       whenever k∈S.                              (E2)

All nonmember reward coordinates are arbitrary signed real numbers. At a
singleton {k}, (E2) is necessarily equality. At every other coalition
containing k the premium may independently be any nonnegative number. There
is no upper restriction other than the finite reward bound below, no equality
between distinct premiums, and no pair-only or sparse-coalition assumption.

The minimal modification included in this class changes just one coordinate
r_k(S₀), with k∈S₀ and |S₀|≥2, from s_k to s_k+h for h>0, leaving all other
own-quitting rewards constant. The theorem covers that modification with any
passive completion; it also covers simultaneous premiums for the same k at
every coalition containing k. This is a search restriction, not WLOG.

Fix M≥0 with |r_i(S)|≤M, and choose B>M. Let K_B=[−B,B]^I. Define

    p_q(S)=∏_(i∈S)q_i ∏_(i∉S)(1−q_i),
    c(q)=∏_i(1−q_i),       a(q)=1−c(q),
    R(q)=Σ_(S≠∅)p_q(S)r(S),
    F(q,v)=R(q)+c(q)v.

Here q∈[0,1]^I is an independent product Quit root and v∈K_B is an arbitrary
continuation annotation. Write Q_i(q) and C_i(q,v) for the pure Quit and
Continue payoffs against the opponents' product root. Then

    F_i(q,v)=q_iQ_i(q)+(1−q_i)C_i(q,v).

An exact root Nash equilibrium means

    F_i(q,v)=max(Q_i(q),C_i(q,v))                 for every i.    (RN)

This is Nash equilibrium of the finite two-action root game. It does not
assert that v is an actual tail payoff or that this root followed by an
arbitrary realizing tail is a behavioral equilibrium.

THEOREM. Under (E1)--(E2), no C¹ function H on an open neighborhood of K_B
satisfies

    H(v)−H(F(q,v))≥a(q)                                         (D)

for EVERY v∈K_B and EVERY exact root Nash equilibrium q against v.

The theorem permits arbitrary signed singleton levels. It requires neither
convexity nor a polynomial ansatz. It excludes a universal robust polynomial
certificate because every exact root/Bellman edge is among its tested edges.
Its canonical Fin4 packet and UE consequences are stated separately below.

## 2. The common boundary is derived from the table

Write the exceptional premium as

    h(T)=r_k(T∪{k})−s_k≥0                    for T⊆I\{k},

with h(∅)=0. The actual endpoints are

    Q_i(q)=s_i                             if i≠k,
    Q_k(q)=s_k+Σ_(T⊆I\{k})p_(q,−k)(T)h(T)≥s_k.               (1)

Thus every exact Nash successor w=F(q,v) satisfies w_i≥s_i for every i.
If any nonexceptional player i≠k has q_i>0, exact Nash implies

    w_i=Q_i(q)=s_i.                                            (2)

If no such player is active but a(q)>0, then k is the only active player.
Every opponent Continues surely, Q_k=s_k, and again exact Nash implies

    w_k=s_k.                                                   (3)

This exhausts all mixed roots, including roots with a sure quitter and roots
with zero-probability components. In the second case the positive premiums
are absent because a collision with another prescribed quitter is impossible.

Since F(q,v) is a convex combination of v and the terminal rewards,
F(q,v)∈K_B. Define

    C=∏_i[s_i,B],
    L={x∈C : x_i=s_i for at least one i}.

We have proved, without a selected-root or invariance hypothesis,

    q exact against v∈K_B and a(q)>0  ⇒  F(q,v)∈L.               (4)

The same uniform motion bound as for any bounded quitting table holds:

    |F_i(q,v)−v_i|≤(M+B)a(q).                                  (5)

Indeed |R_i(q)|≤M a(q) and F_i−v_i=R_i−a(q)v_i.

## 3. Proof of the arbitrary-C¹ drift exclusion

The set L is nonempty and compact. Suppose H satisfies (D), choose a minimizer
x of H on L, and put J={i:x_i=s_i}. The strict padding B>M ensures
−B<s_i<B for every coordinate.

### 3.1 One binding coordinate

Suppose J={i}. Set q_i=t>0 and q_j=0 for every j≠i.

Player i's Quit endpoint is s_i even if i=k, because all its opponents
Continue; its Continue endpoint is x_i=s_i. Hence its prescribed mixture is
an exact best reply. For each j≠i,

    C_j(q,x)=(1−t)x_j+t r_j({i}),
    Q_j(q)=(1−t)s_j+t r_j({i,j}).                             (6)

At t=0, C_j−Q_j=x_j−s_j>0. Finitely many strict inequalities remain true
for all sufficiently small t>0. Thus every other player is exactly best
responding by Continue. In particular, when j=k the possibly positive
premium appears explicitly as

    Q_k(q)=s_k+t[r_k({i,k})−s_k];

it does not invalidate the small-root continuity argument. For |I|=1 there
are no opponent inequalities and any 0<t≤1 is permitted.

The resulting root is exact Nash, has a(q)=t, and has successor in L by (4).
Then H(F(q,x))≥H(x), contradicting (D).

### 3.2 At least two binding coordinates

Suppose |J|≥2. For each i∈J the segment x+t e_i stays in L for small
t≥0, since another coordinate remains binding. Hence

    ∂_iH(x)≥0                              for every i∈J.          (7)

Coordinates at the upper face B are not changed. For small ε>0 set

    v_ε=x−ε 1_J∈K_B.

Differentiability gives

    [H(v_ε)−H(x)]/ε → −Σ_(i∈J)∂_iH(x)≤0.                     (8)

Choose any exact Nash equilibrium q_ε of the finite root game against v_ε.
All-Continue is not Nash: every i∈J gets s_i−ε by Continue and s_i by Quit
when all opponents Continue. Thus a(q_ε)>0. Its successor w_ε lies in L
by (4), and w_ε,i≥s_i for each i∈J. It follows from (5) that

    ε≤w_ε,i−v_ε,i≤(M+B)a(q_ε),
    a(q_ε)≥ε/(M+B).                                           (9)

No continuity or favorable branch selection of q_ε is used. EVERY Nash
root at v_ε satisfies this estimate and the common-boundary conclusion.

Applying (D) and minimality on L gives

    ε/(M+B)≤a(q_ε)≤H(v_ε)−H(w_ε)≤H(v_ε)−H(x).

Divide by ε and take its limit to contradict (8). This proves the theorem.

## 4. Canonical punishment and unrestricted UE

Assume now I=Fin4 and s=(1,0,0,0). The exceptional label k can be ANY of
the four players; it is not required to be the positive-singleton player.

For i≠k, immediate Quit guarantees exactly s_i against every opponent law.
For k, immediate Quit guarantees AT LEAST s_k, since every possible terminal
coalition contains k and (E2) applies. Hence P_i≥s_i for every i, where P
is the infimum over independent opponent laws of the unrestricted behavioral
response cap. Conversely all-Never opponents allow only the singleton reward
s_i when i eventually quits, and zero when i never quits. Since s_i≥0,
the full cap against those opponents equals s_i. Therefore

    P=s,                                                        (10)

and punishment normality holds. This argument does not assume the exceptional
Quit endpoint is constant, nor that any arbitrary punishment infimum is
attained. It proves the matching bounds directly for this table class.

Choose a reward bound M≥1. The reviewed analytic polynomial separator implies

    Cap⁰_δ(M+2)=∞                            for every δ>0.         (11)

Indeed, finite capacity at δ would imply finite capacity at ε=min(δ,1).
The separator applied with inner radius M+1 and outer radius M+2 would then
give a polynomial H with unit drift on ALL absorption-weighted edges at
tolerance ε/4 in K_(M+1). Exact edges are included, contradicting Section 3.

Thus this class has finite floor-free absorption-weighted forward packets
in ONE fixed box at every accuracy and arbitrarily large requested charge.
Their values are absolute bounded payoff annotations; no normalized loop,
known equilibrium tail, supplied start, or actual-source assumption is used.
This is an existential argument through the analytic separator, not an
effective bound on degree, packet length, or a finite algorithm.

By (10), checked punishment-floor input removal supplies the floors, and
the checked weighted-packet consumer supplies one fixed uniform-equilibrium
payoff against all unilateral behavioral deviations at every sufficiently
long finite horizon. Never and arbitrarily late finite deviations are included.

Alternatively the reviewed fixed-box no-UE characterization would produce
a polynomial robust-drift certificate under no UE, contradicting Section 3.
The separate sure-root branch need not be excluded or synthesized here.

No general-cardinality UE consequence is inferred from a Fin4 consumer.
The general finite-player statement proved here is the root-drift exclusion.

## 5. Exact source comparison and boundaries

The existing Solan--Vieille class has unit solos and capped own-quitting
rewards. Its weak-solo version still requires r_i(S)≤s_i when i∈S. A
strict premium h(T)>0 violates that inequality for player k. Positive
coordinate rescaling and a common terminal-coordinate shift preserve the
strict difference r_k(S)−s_k, so the elementary zero-solo closure used for
the constant-own class does not itself remove this positive premium.

This establishes a strict difference in RAW HYPOTHESES, not by itself proof
that no other existing existence theorem covers the same games. Independent
source comparison remains necessary before classifying the consequence as
new coverage.

The narrow checks made before freezing were:

- `UniformEquilibrium/Quitting/Classification/SoloExitPreference.lean`:
  `QuittingWeakSoloExitPreference` and `QuittingCappedJointExit` do not
  admit a strict exceptional premium after positive affine column transport.
- `UniformEquilibrium/Quitting/Classification/Existence/SureExitChambers.lean`:
  `QuittingPureSingletonChamber` and `QuittingPurePairChamber` require
  extra no-leave/no-join inequalities involving the freely chosen passive
  rewards. (E1)--(E2) do not supply those inequalities.
- `UniformEquilibrium/Quitting/Stationary/CoalitionToggleDeletion.lean`:
  `QuittingOwnerJoinAntitone` compares r_i(S∪{i}) with r_i(S), not with
  s_i. Arbitrary passive rewards need not satisfy it. Its Never-deletion
  result also assumes a strict singleton/punishment inequality, whereas
  the canonical family has the exact equality (10).
- `UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean`:
  `exists_leave_or_join_gain` and `exists_collision_gain` are necessary
  pure-profile rejection tests, not an all-table producer for this class.
- `math/formalized/CONDITIONAL_FACE_GAP_STATIONARY_EQUILIBRIUM.md`:
  its two opposite face-sign hypotheses on a supplied stationary box are
  additional reward-dependent assumptions. The unrestricted passive rows
  here do not automatically provide them.

The proof's production inputs are the finite exact-root existence theorem
`exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`, and, for the Fin4
consequence, the same reviewed analytic and checked semantic inputs as the
previous note:

- `math/exports/POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md`,
  SHA-256 `14191a09b4a42149e0c893666603d85b2e2f1fb3bcd0240af0e0619aaeefc9d6`;
- `hasFloorFreeAbsorptionWeightedFiniteForwardPackets_iff_weighted` in
  `UniformEquilibrium/Quitting/Projective/FloorFreeForwardPacketInputRemoval.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets`
  in `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketTranslation.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_iff_fixedBoxPackets_or_sureRoot`
  in `UniformEquilibrium/Quitting/Projective/FixedBoxForwardCharacterization.lean`.

No production declaration here is asserted to implement the new boundary
proof. No source says that supplied exact-root Nash play is automatically
a full behavioral equilibrium; the packet consumer performs that separate job.

## 6. What the argument does not permit

With TWO exceptional players, both can be active and both Quit endpoints can
strictly exceed their singleton levels. Then neither (2) nor (3) supplies a
binding successor coordinate. The proof has not established a replacement
invariant boundary in that case. Likewise, permitting negative premiums for
k can destroy w_k≥s_k. These changes cannot be hidden inside the present
theorem's hypotheses.

The requested checks are (a) independent falsification of the all-root
boundary and Section 3 proof, (b) the canonical punishment and consumer
composition, and (c) existing-class coverage. No numerical certificate was
fitted, and no claim of a positive-gap game or general quitting-game solution
is made.
