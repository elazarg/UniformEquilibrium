# Independent review: finite own-premium support peeling

Reviewer: CODEX_RENY.

Reviewed original: [CODEX_FRECHET_CYCLE__FINITE_SUPPORT_QUIT_PREMIUM_PEELING.md](../notes/CODEX_FRECHET_CYCLE__FINITE_SUPPORT_QUIT_PREMIUM_PEELING.md).

Reviewed SHA-256:
`aff6930efa2be95f654de9097482763fd6103780ff55c09a7059e1491514f329`.

Verdict: PASS for the complete mathematical surface. The finite support
condition, ordering condition, and universal exact-root successor boundary
are equivalent as stated. The arbitrary-C¹ exclusion and the nonnegative-
singleton Fin4 packet/UE consequence follow. No mathematical correction is
required. This is not a Lean implementation or an export decision; exhaustive
existing-class novelty is outside this review.

## 1. Independence and exact scope

I derived the support/order equivalence and the earliest-active-player
argument before reading this original. I also independently obtained the
failed-support construction by solving each active player's Continue/Quit
indifference equation, before reading the author's converse. I then read
all 351 lines of the frozen original, including its complete proof, consumer,
source qualification, and exact boundary examples.

The earlier [one-exception review](CODEX_FRECHET_CYCLE__ONE_EXCEPTIONAL_POSITIVE_QUIT_PREMIUM_BOUNDARY__BY_CODEX_RENY.md)
checks the common lower-boundary argument and the semantic consumer in that
subclass. This review checks the genuinely new finite support condition and
its necessity, and verifies that the broader final statement supplies every
input to that argument. No unreviewed fixed-point or strategy construction
is imported.

Let I be nonempty finite, Never pay zero, s_i=r_i({i}), and
d_i(S)=r_i(S)−s_i≥0 whenever i∈S. Passive rewards and, for the analytic
theorem, singleton levels may be signed. For a reward bound M and a fixed
B>M, the source annotation ranges over the WHOLE box [−B,B]^I. Roots are
independent products; root Nash means exact best reply against both actual
endpoints in the finite two-action game. The conclusion tests every exact
root, not one favorable choice or a previously supplied semantic carrier.

## 2. The finite equivalence is correct and is not graph acyclicity

The support condition is

    every nonempty A has some i∈A with d_i(S)=0
    for every coalition i∈S⊆A.

Repeatedly select such an i from the remaining set. At removal, a coalition
paying i a strict premium must already contain a removed player. This yields
an ordering in which every strict premium requires SOME earlier member of
that coalition. Conversely, choose the earliest player in an arbitrary A.
No coalition contained in A can pay that player a positive premium. The
nonnegative-premium hypothesis then makes every such premium zero.

Two exact three-player patterns distinguish this condition from pairwise
tests. Set every own premium to zero except those explicitly listed; passive
rewards may be arbitrary.

- Let only players 1 and 2 receive positive premiums at {0,1,2}. The order
  0,1,2 satisfies the condition. Connecting a premium recipient to EVERY
  other member of its rewarding coalition creates a 1↔2 cycle, despite
  the valid ordering. The condition requires one earlier coalition member,
  not that all co-members be earlier.
- Let ALL three players receive a positive premium only at {0,1,2}. Every
  proper support passes, but the full support fails. There are no positive
  pair-coalition premiums at all. A graph based only on pair rewards would
  miss the obstruction entirely.

Thus neither a naive all-co-members graph nor a pair-coalition-only graph
can replace the actual hypercoalition condition.

## 3. Both directions of the root-image equivalence

Write Q_i for Quit, C_i=G_i+α_i v_i for Continue, and
w_i=q_iQ_i+(1−q_i)C_i. Nonnegative own premiums give Q_i≥s_i. Hence at
an exact root w_i=max(Q_i,C_i)≥s_i.

For positive absorption the actual active set A={i:q_i>0} is nonempty.
Choose its support-test owner i. Opponents outside A Continue surely, so
every possible coalition in that owner's Quit endpoint lies inside A and
pays s_i. Thus Q_i=s_i. The owner's positive Quit probability and exact
support equality give w_i=Q_i=s_i. This proves the full boundary image,
including sure roots and zero components, without any survival division.

For the converse, suppose the condition fails at A. Each i∈A has a strict
premium on some S_i⊆A containing it. Put q_i=t∈(0,1) on A and q_j=0
outside. Every relevant opponent coalition has positive probability. Since
all other premiums are nonnegative, Q_i>s_i for every i∈A.

All α_i are positive. Defining

    v_i=(Q_i−G_i)/α_i               for i∈A

makes Continue equal Quit exactly. As t→0, these coordinates approach s_i,
so they lie strictly inside the padded box for sufficiently small t. This
coordinatewise construction is legitimate: player i's continuation endpoint
uses v_i only, and Q_i,G_i,α_i depend on the root rather than the other
continuation coordinates.

For j outside A choose v_j=B. Its Continue endpoint tends to B, while
its Quit endpoint tends to s_j<B. Therefore Continue is strictly optimal
and its prescribed payoff strictly exceeds s_j for all sufficiently small
t. Finiteness supplies one common t for all conditions. The constructed
root is exactly Nash and has w>s in EVERY coordinate. Furthermore
w_i≤(1−a)B+aM<B because a>0 and M<B. Thus its successor really lies
in the interior above s, not on a hidden upper boundary.

This proves necessity for EACH padded box B>M. Failure of the condition
disproves only the universal singleton-boundary image, not UE or existence
of some other potential, invariant set, or proof mechanism.

## 4. Complete smooth-drift argument and boundary tests

Under the support condition, minimize H on
L={x∈∏[s_i,B] : some x_i=s_i}. If the minimum x has only one binding
coordinate i, a sufficiently small solo root owned by i is exactly Nash:
the owner's endpoints both equal s_i and each outsider has

    C_j−Q_j=(1−t)(x_j−s_j)+t(r_j({i})−r_j({i,j})),

which is positive near t=0. This retains arbitrary outsider premiums,
including several premium recipients. Its positively charged successor
belongs to L, contradicting strict drift at a minimum.

If at least two coordinates bind, increasing any one leaves another binding,
so each binding partial derivative is nonnegative. Lower all binding
coordinates by ε. Every exact root now absorbs, since all-Continue is not
Nash. Its successor is back in L and is at least s coordinatewise. The
motion bound ||F−v||∞≤(M+B)a gives a≥ε/(M+B). Drift and minimality
would then force a positive directional quotient for H along the lowering,
whereas differentiability makes its limit the negative sum of nonnegative
binding partial derivatives. This is a contradiction. Upper-face coordinates
are unchanged. Neither convexity nor continuous root selection is used.

I checked the two canonical full-table fixtures in Section 7 literally:
the simultaneous positive-premium root has all relevant no-leave/no-join
inequalities and successor (2,1,1,1)>s; the negative-premium root is exactly
Nash and has successor zero with 0<s_0. Their use is confined to rejection
of the proposed image extensions. They are not negative UE examples.
For one player, a positively charged self-loop at s already excludes H;
for no players absorption is zero, explaining the nonempty hypothesis.

## 5. Nonnegative-singleton Fin4 consumer and source boundaries

When all s_i≥0, immediate Quit guarantees at least s_i against every
opponent law, while all-Never opponents have full response cap s_i. Thus
P=s without any joint-punishment realizability assumption. This argument
uses nonnegative premiums but not the support condition.

Fix a positive reward bound M. Finite floor-free capacity in radius M+2
at any δ>0 would give finite capacity at ε=min(δ,1). The reviewed
analytic separator would produce polynomial unit drift for all smaller-
tolerance edges in radius M+1, including every exact edge. The theorem
just checked excludes that polynomial. Hence capacity is infinite at EVERY
positive tolerance in ONE fixed box. Because capacity is over all finite
free-start paths, this supplies the literal all-accuracy, arbitrary-charge
finite packet source; it is not just failure of one proposed potential.

The current declarations checked for this composition are
`hasFloorFreeAbsorptionWeightedFiniteForwardPackets_iff_weighted` in
`UniformEquilibrium/Quitting/Projective/FloorFreeForwardPacketInputRemoval.lean`
and `quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets`
in `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketProducer.lean`.
The first uses normality and a positive reward bound; the second uses a
positive reward-containing packet box. The chosen M and M+2 supply these
hypotheses. Neither declaration requires a positive own singleton. The
source-file attribution in this final surface is correct.

The analytic input is the already reviewed
[polynomial separator](../exports/POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md),
SHA-256 `14191a09b4a42149e0c893666603d85b2e2f1fb3bcd0240af0e0619aaeefc9d6`.
The root existence, exact endpoints, and Bellman orientation are the same
named source interfaces recorded in the one-exception review.

Consequently the stated nonnegative-singleton Fin4 conclusion gives one
fixed uniform-equilibrium payoff and unrestricted behavioral deviations.
The all-zero singleton boundary also directly has the all-Never equilibrium.
The general signed, arbitrary-finite-player theorem remains the analytic
exclusion; the note does not silently generalize the Fin4 semantic consumer.

The exact finite condition is more than a supplied-root verifier: it forces
the image property from reward data and has a proved finite converse. It
does not follow that this is a previously uncovered UE class. In particular,
an older conditional root-choice existence theorem might consume the same
image property by a shorter route. That comparison must remain explicit in
any final packet. No author file, export, or Lean source was changed.
