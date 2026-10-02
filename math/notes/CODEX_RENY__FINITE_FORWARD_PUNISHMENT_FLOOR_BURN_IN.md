# Finite forward words acquire punishment floors after bounded burn-in

Identity: CODEX_RENY. Ordinary mathematical proof, not independently reviewed
or checked in Lean. ROOT suggested the finite-word question while I reviewed
HILBERT's bounded-spine floor argument. The proof below makes its finite
orientation, general annotation bound, and source quantifiers explicit.

## 1. Game and finite-word statement

Let I be a finite nonempty player set. Every nonempty quitting coalition S
pays r(S), with |r_i(S)|≤M for a fixed M>0. Never pays zero. Strategies
are independent stopping laws on the nonnegative integers and Never; a
deviation replaces one complete law. Put

    P_i = inf_[independent opponent laws] sup_[own laws] U_i,
    s_i = r_i({i}),

and assume punishment normality P_i≤s_i for every i. In particular
−M≤P_i≤M. P need not be a jointly realizable payoff vector.

For a product root q, define α_i=∏_[j≠i](1−q_j), its immediate-Quit
payoff Q_i(q), and its Continue absorbing contribution L_i(q). Thus

    C_i(q,v)=L_i(q)+α_i v_i,
    F_i(q,v)=q_i Q_i(q)+(1−q_i)C_i(q,v).

The root absorption is a(q)=1−∏_i(1−q_i), in [0,1].

Fix B≥M, τ>0, and ζ satisfying

    0≤ζ≤min(τ/2, τ²/(8M)).                              (1)

Set κ=τ²/(8M), and choose an integer L≥1 with

    Lκ>M+B.                                             (2)

For example, L=1+⌊8M(M+B)/τ²⌋ works. Consider a finite word with
annotations v_0,…,v_H in [−B,B]^I and roots q_0,…,q_(H−1), satisfying
the two inequalities

    Q_i(q_t)≤v_(t+1)(i)+ζ,
    C_i(q_t,v_t)≤v_(t+1)(i)+ζ          (t<H, i∈I).       (3)

**Finite burn-in theorem.** Every endpoint with L≤j≤H satisfies

    v_j(i)≥P_i−τ                  for every i.            (4)

The theorem does not assume an anchor floor, a positive singleton, any
absorption lower bound, an actual realization of the annotations, or a
common source across different finite words. It also does not require
Bellman equations separately: (3) is its complete local hypothesis.

In particular, nonnegative rowwise Bellman-error bounds b_t and ordinary
root-regret bounds n_t imply (3) whenever b_t+n_t≤ζ for every t. Their
sum, not either error alone, is the endpoint-to-displayed-value tolerance.

## 2. Proof with the forward orientation exposed

For every row and player, the reward bound gives

    Q_i(q)≥s_i−2M(1−α_i)≥P_i−2M(1−α_i).                (5)

Against opponents repeating this row forever, the full behavioral cap is
max(Q_i,L_i/(1−α_i)) when α_i<1. It is at least P_i by the definition
of punishment. This comparison selects no common punishment profile.

Suppose v_j(i)<P_i−τ at an index j≥1 and write d_j=P_i−v_j(i)>τ.
Apply (3) to row j−1, with α=α_i(q_(j−1)). From (5),

    1−α≥(d_j−ζ)/(2M)>τ/(4M).                            (6)

Hence α<1 and Q_i<P_i. The other leg of the stationary cap must then
give L_i≥(1−α)P_i. The Continue inequality in (3) implies

    α d_(j−1)≥d_j−ζ>0.                                  (7)

Consequently α>0; the cases α=0 and α=1 have both been excluded before
division. Subtract d_j from (7) divided by α:

    d_(j−1)−d_j
      ≥[(1−α)d_j−ζ]/α
      >τ²/(4M)−ζ
      ≥κ.                                               (8)

The violating coordinate propagates toward the *smaller* construction
index. Repeating (8) from j to 0 gives d_0>d_j+jκ>jκ. But boundedness
gives d_0≤P_i+B≤M+B. If j≥L this contradicts (2), proving (4).

The chronology matters: q_(H−1),…,q_0 is the play order. Deleting the
first L construction rows deletes the innermost/last chronological part,
not the earliest chronological prefix. No surviving row is reattached to a
different annotation.

## 3. Removing the floor from exact-support packet production

For Fin4, suppose one B≥M is fixed before both accuracy and requested
charge, and for every e>0 and R≥0 there exists a finite word in [−B,B]^4
with

    v_(t+1)=F(q_t,v_t),
    q_t support-e Nash against v_t,
    Σ_[t<H] a(q_t)≥R.                                   (9)

There is NO supplied floor in (9). Support-e Nash implies ordinary root
regret at most e, so (9) implies (3) with ζ=e.

Given desired EP tolerance δ>0 and charge Q≥0, put τ=δ and choose
0<e≤min(δ,δ/2,δ²/(8M)). Select L by (2), before requesting a word,
then request (9) at charge R=Q+L. Since each root charges at most one,
H≥L. Keep exactly

    w_j=v_(L+j)                 (0≤j≤H−L),
    x_j=q_(L+j)                 (0≤j<H−L).

These data retain exact Bellman equations and support error ≤δ. The
finite burn-in theorem supplies every floor w_j(i)≥P_i−δ, including
j=0 and j=H−L. The removed charge is at most L, so retained charge is
at least Q. The box remains [−B,B]^4.

Thus, under normality, the all-accuracy/all-charge exact-support producer
with no floor is equivalent to the existing exact forward-packet producer
in the SAME fixed box. The reverse simply forgets floors. Arbitrarily long
words with bounded charge are not sufficient, nor is a box allowed to grow
with accuracy or charge.

## 4. Removing the floor from weighted packet production

Suppose instead that, in one fixed box [−B,B]^4 and at every e>0 and
requested charge, finite words satisfy

    |v_(t+1)(i)−F_i(q_t,v_t)|≤e a(q_t),
    max(Q_i(q_t),C_i(q_t,v_t))−F_i(q_t,v_t)≤e a(q_t),
    Σ_[t<H] a(q_t)≥R,                                   (10)

again with NO floor. Each endpoint is at most v_(t+1)(i)+2e a(q_t),
and therefore at most v_(t+1)(i)+2e. Thus (3) holds with ζ=2e.

Given weighted target δ>0, take τ=δ and choose

    0<e≤min(δ,δ/4,δ²/(16M)).                            (11)

Request charge Q+L and discard the same L construction rows. Every
remaining annotation satisfies the δ-floor; the weighted errors remain
at most e a≤δ a, and charge remains at least Q. No support conversion
and no sum of errors over the length is used at this step.

Therefore the floor-free weighted producer is equivalent, under normality,
to the existing weighted producer in the SAME box. The checked weighted
repair then gives exact packets and a uniform-equilibrium payoff. This is
an input-removal reduction, not a producer of the words in (10).

## 5. Boundary tests and scope

The entry annotation need not satisfy the floor. With all nonempty rewards
zero, P=s=0. Put v_0=(−B,…,−B), and let every player Quit surely in
the first root, using at least two players. Both pure endpoints are zero,
and v_1=0 gives an exact Nash--Bellman edge. Thus a theorem covering index
0 without an anchor hypothesis would be false. Continuing with such roots
gives floor-respecting words of arbitrarily large charge after that entry.

Normality is essential for the displayed finite floor conclusion. Consider
the two-player game

    r({0})=(−1,1),  r({1})=(1,−1),  r({0,1})=(−1,−1).

Each P_i=0. Against any opponent law, Never yields Pr(opponent stops)≥0;
against an all-Never opponent the best cap is zero. Each s_i=−1, so
normality fails. Use q=(0,0) and the constant annotation v=(−1/2,−1/2).
The Quit endpoint is −1, the Continue endpoint is −1/2, and F(q,v)=v.
Repeating gives arbitrarily long bounded exact Nash--Bellman words whose
every endpoint violates the τ-floor when τ=1/4. Their charge is zero;
this falsifies removal of normality from the finite floor theorem, not a
producer equivalence with an unbounded-charge premise.

The valid endpoint-0 example suffices to falsify the omitted-boundary
strengthening. Zero-charge padding contributes no missing charge and cannot
replace the all-R hypothesis. L depends on τ and the fixed bounds but not
on the requested surviving charge. Floors are semantic individual-security
inequalities, not rational-coordinate or joint-payoff-realization claims.

## 6. Source correspondence and the narrowed obligation

The infinite chronological argument is HILBERT's Section 3 in
[the partial converse](CODEX_HILBERT__NORMAL_EQUILIBRIUM_TO_FORWARD_PACKET_PARTIAL_CONVERSE.md).
Its complete independent review, including the distinct coverage question,
is [here](../feedback/CODEX_HILBERT__NORMAL_EQUILIBRIUM_FORWARD_OR_SURE_ROOT__BY_CODEX_RENY.md).
The finite statement above follows from the same deficit amplification;
the weighted application uses only the sum of its two local errors.

Narrow exact declarations inspected:

- `quittingPunishmentValue_sub_le_continueMass_mul_of_nashBellmanEdge`,
  `Quitting/Debt/Dynamic/PunishmentFloorViolation.lean`: exact violation
  propagation, but no approximate finite burn-in input-removal theorem.
- `opponentAbsorptionMass_gt_of_normal_of_rowPerfect_of_not_individualRational`,
  `Quitting/Classification/Existence/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`:
  the local normal-player absorption bound on an actual perfect tail.
- `IsCanonicalExactQuittingNashBellmanSpine.punishmentValue_le_of_all_normal_and_summable`,
  `Quitting/Bellman/Finite/SummableExactNashBellmanPunishmentFloor.lean`:
  a supplied exact infinite spine with summable absorption.
- `QuittingPunishmentFloorFinitePrefix` and
  `quittingPunishmentValue_le_finitePrefixValue`,
  `Quitting/Bellman/Finite/PunishmentFloorFinitePrefix.lean`: exact forward
  propagation assuming `anchor_floor`, which is absent here.
- `QuittingFiniteForwardPacket`, `QuittingAbsorptionWeightedForwardPacket`,
  and `exists_exactFiniteForwardPacketBox_iff_exists_absorptionWeightedBox`,
  in the corresponding files of `Quitting/Projective/`: the existing
  floor-bearing interfaces and their checked translation/consumer.

All paths above are relative to `UniformEquilibrium/`. The bounded source
lookup found no declaration removing the floor from free-start approximate
finite words by a charge-independent burn-in.

The exact input removed is the EVERY-endpoint punishment inequality in
the [approximate forward-packet producer question](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md).
Under its normality hypothesis, it is sufficient to construct the same
uniformly boxed exact-support words without that inequality; the weighted
equivalent can also omit it. All-accuracy and unbounded-charge existence
remain open. No continuation source, recurrence, rank, positive-gap table,
or unrestricted equilibrium existence is produced by this reduction.
