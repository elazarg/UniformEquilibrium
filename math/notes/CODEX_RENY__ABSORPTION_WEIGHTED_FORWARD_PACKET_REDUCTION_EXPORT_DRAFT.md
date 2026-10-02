# Absorption-weighted reduction of the finite forward-packet producer

Authors: the user-supplied APPROX argument; reconstruction by CODEX_HILBERT;
final assembly by CODEX_RENY.

Mathematical source:
[complete reconstruction](../notes/CODEX_HILBERT__ABSORPTION_WEIGHTED_FORWARD_PACKET_REPAIR.md).
Independent original-first reviews:
[CODEX_HILBERT](../feedback/APPROX_WEIGHTED_REPAIR__BY_CODEX_HILBERT.md),
[CODEX_FRECHET_CYCLE](../feedback/APPROX_WEIGHTED_REPAIR__BY_CODEX_FRECHET_CYCLE.md).
FRECHET also checked the complete source reconstruction. The
[final-surface review](../feedback/ABSORPTION_WEIGHTED_FORWARD_PACKET_REDUCTION__FINAL_SURFACE_BY_CODEX_FRECHET_CYCLE.md)
checks the assembled statement, handoff, and boundary tests.

## Exact statement

Let I={0,1,2,3}. For every nonempty S⊆I let r(S)∈ℝ⁴, and assume
|r_i(S)|≤M for a fixed M>0. Play stops at the first nonempty quitting
coalition; if everyone Continues forever the payoff is zero. A behavioral
profile is an independent product of four laws on ℕ∪{Never}. Deviations
may replace a player's complete law. Write U_i(p) for the terminal payoff,

    Cap_i(p)=sup_μ_i U_i(μ_i,p_−i),
    P_i=inf_p_−i Cap_i(p).

The opponents in the punishment infimum use independent laws; public
correlation is not included. None of the finite conversion proofs below
requires punishment normality or positive global exploitability.

For a root q∈[0,1]⁴, q_i is the Quit probability. Put

    p_q(S)=∏[i∈S]q_i · ∏[i∉S](1−q_i),
    c(q)=p_q(∅),       a(q)=1−c(q),
    F(q,v)=∑[∅≠S⊆I]p_q(S)r(S)+c(q)v.

Define the opponent product masses p_(q,−i) on subsets of I\{i} analogously,
and write c_−i(q)=p_(q,−i)(∅). The two pure-action payoffs are

    Q_i(q)=∑[T⊆I\{i}]p_(q,−i)(T)r_i(T∪{i}),
    C_i(q,v)=∑[∅≠T⊆I\{i}]p_(q,−i)(T)r_i(T)+c_−i(q)v_i.

Thus F_i=q_iQ_i+(1−q_i)C_i. Let A_i=max(Q_i,C_i), and let
Reg_i(q,v)=A_i(q,v)−F_i(q,v)≥0 be ordinary mixed-root regret.
Support-δ Nash means

    q_i>0 ⇒ A_i−Q_i≤δ,
    q_i<1 ⇒ A_i−C_i≤δ,

for every i. This is an unweighted bound for every supported action.

Fix a number B≥M. An exact forward packet with error δ>0 and charge Q≥0
consists of H≥0, values v_0,…,v_H∈[−B,B]⁴, and roots q_0,…,q_(H−1), with

    v_(t+1)=F(q_t,v_t)                 (0≤t<H),
    q_t support-δ Nash against v_t     (0≤t<H),
    v_t(i)≥P_i−δ                      (0≤t≤H),
    ∑[0≤t<H]a(q_t)≥Q.

The index is outward construction order. Its roots are played in reverse
order if this finite word is used chronologically. No inverse Bellman
evaluation is part of the definition.

Define two assertions for this fixed game:

- EP: there exists ONE finite B≥M such that exact forward packets exist
  for EVERY δ>0 and EVERY Q≥0 in [−B,B]⁴.
- WP: there exists ONE finite B≥M such that for EVERY ε>0 and EVERY Q≥0
  there are H≥0, values y_0,…,y_H∈[−B,B]⁴ and roots q_0,…,q_(H−1) with

      ‖y_(t+1)−F(q_t,y_t)‖∞≤εa(q_t)   (0≤t<H),
      Reg_i(q_t,y_t)≤εa(q_t)          (0≤t<H),
      y_t(i)≥P_i−ε                   (0≤t≤H),
      ∑[0≤t<H]a(q_t)≥Q.

Boxes are chosen before both accuracy and charge. Packets may be unrelated
at different accuracies or charge targets. No infinite compatible sequence
is assumed.

**Theorem.** EP and WP are equivalent. Furthermore EP is unchanged if its
box is required to be exactly [−M,M]⁴.

The equivalence includes this explicit finite compiler. For B≥M and
0<ρ≤1/8, a finite weighted packet at tolerance ε=Bρ² can be replaced by
a finite exact forward packet of the same length and in the same box.
Its support and punishment-floor error is at most 32Bρ; its total charge
is at least half the input charge. More precisely its root changes satisfy

    |q̂_t(i)−q_t(i)|≤ρa(q_t),

and, with the original first annotation retained, its recomputed values
satisfy

    ‖v̂_t−y_t‖∞≤17Bρ.

These bounds are uniform in packet length and use no positive lower bound
on individual row absorption.

As a consequence, WP implies existence of one fixed uniform-equilibrium
payoff, by the existing finite-forward-packet consumer identified below.
No converse from uniform equilibrium to EP or WP is asserted.

## Conjecture-facing change

The named obligation is the finite-packet producer in
[Construct approximate forward packets beyond bounded exact capacity](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md).
It asks for EP from arbitrary Fin4 reward data in the contrary case of
positive global SUM-debt infimum and punishment normality P_i≤r_i({i}).

The present result strictly changes the producer requirements: one may
construct approximate Bellman annotations and ordinary mixed-root regrets
weighted by row absorption, instead of exact Bellman equations and
unweighted inequalities for every supported action. The finite compiler
supplies the latter requirements, retaining charge with no length loss.
The exact producer can also be required to use the specified reward box,
rather than an unknown larger fixed box.

This is an equivalence of all-accuracy, all-charge existence assertions,
not the production of either family from arbitrary tables. In particular
the remaining obligation is still:

    for every contrary-case table, produce ONE finite box and
    weighted packets at EVERY ε>0 and EVERY charge target Q≥0.

No charge-growth theorem, counterexample, or complete answer to the live
question follows merely from repairing one supplied packet. The unrelated
SUM-minimum entrance theorem is not an input to this reduction.

## Definitions and assumptions

All norms are coordinate sup norms unless a sum is explicitly displayed.
Differences |q̂_i−q_i| are differences of Quit probabilities, not the doubled
ℓ¹ distance between the two Boolean probability vectors. The parameter M
is strictly positive and B≥M, so divisions by B in the construction are legal.

The punishment P_i is bounded between −M and M. Its opponent laws are
independent; one deviator may use any complete behavioral replacement.
There is no external public randomization or access to other players'
private stopping times.

Packet values are bounded annotations. They are not assumed to be actual
continuation payoff vectors, or to be attached to a prescribed starting
profile, fixed endpoint, or source ancestry. Only their displayed forward
equations, action inequalities, floors, and charge are required. A used
root action means exactly positive probability, with no lower support-mass
bound.

If the finite packet is read as a temporal word, its construction order is
reversed. The main proof only evaluates F forward and never solves an
inverse Bellman problem. It does not assert that an arbitrary terminal
boundary annotation can itself be realized by a behavioral tail. The
existing compact charged-closing consumer supplies the eventual genuine
strategy and controls every unilateral behavioral deviation.

The uniform-equilibrium conclusion has the standard fixed-target meaning:
there is one vector u such that for every positive accuracy one profile
and one finite horizon threshold work for all longer average-payoff
horizons and all unilateral behavioral deviations, with prescribed
average payoff close to u. Stage payoffs are zero before absorption and
equal the terminal reward from absorption onward.

## Source correspondence

The new ordinary mathematics is the combined finite weighted repair, its
upward-translation converse at the level of producers, and reward-box
reduction. The inspected local ingredients and downstream consumer are
already checked Lean declarations; the combined statement is not claimed
Lean-checked.

- `QuittingFiniteForwardPacket` in
  `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`
  matches EP's exact forward equations, support errors, all endpoint floors,
  and total absorption charge. Its `rational` field means the punishment
  floor, not rational-valued coordinates.
- In the same file,
  `exists_singleSeamProjectiveLasso_of_finiteForwardPackets` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets`
  consume packets at every accuracy and charge in one compact carrier.
  Their hypotheses impose no actual-source anchor or prescribed endpoints.
- `IsQuittingRootSupportApproxNash` in
  `UniformEquilibrium/Quitting/Boundary/Repair/SupportEnlargementAlternative.lean`
  is the unweighted supported-endpoint predicate used here.
- `supportPurifiedRoot_coordinate_close_of_badAction_small` and
  `isQuittingRootSupportApproxNash_supportPurifiedRoot` in
  `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/SurvivalCrossingRepair.lean`
  supply existing local bad-action deletion and endpoint stability.
- `abs_quittingRootSuccessorPayoff_sub_of_quitProbability_close` and
  `abs_quittingRootSequenceBackwardPayoff_sub_tailVector_le` in its
  `FinitePrefixCompatibility.lean` companion supply product-law bounds
  and exact finite recomputation. Their general displayed finite-window
  comparison grows with length and retains reached-source hypotheses.
- `isQuittingRootSupportApproxNash_of_tail_close` and
  `abs_quittingCyclicValue_sub_terminalValue_le_of_chargedResidual` in
  `UniformEquilibrium/Quitting/Projective/Lasso.lean` give support transfer
  and length-independent absorption-weighted policy correction for a
  supplied absorbing cycle. That cycle theorem does not supply this
  finite-packet simultaneous purification or the producer converse.

Both independent reviews examined these named sources under their imports
and found no matching combined theorem. This is a bounded source novelty
claim, not worldwide priority. No paper theorem is an input to the
elementary proof below; the original submission's literature aside is
unnecessary.

## Proof

The following four parts preserve the complete reviewed reconstruction's
proof text, with only the subsection heading level adjusted.

### 2. Elementary stability facts

If v∈[−B,B]⁴, every coordinate payoff of the finite root game lies in
[−B,B], so F(q,v) lies in the same box. For fixed q,

    F(q,v)−F(q,w)=c(q)(v−w).                         (2.1)

Changing only the continuation changes Q_i by zero and C_i by
c_−i(v_i−w_i). Hence the gap Q_i−C_i changes by at most ‖v−w‖∞.
Both pure-action regrets are positive parts of that gap or its negative,
so the same bound holds even when the best action changes.

For two roots q,q̂, independently couple each pair of Boolean coordinates
so that coordinate i disagrees with probability |q̂_i−q_i|. A union bound
gives joint disagreement at most Σ_i|q̂_i−q_i|. Consequently

    |a(q̂)−a(q)|≤Σ_i|q̂_i−q_i|,
    ‖F(q̂,v)−F(q,v)‖∞≤2BΣ_i|q̂_i−q_i|.             (2.2)

Applying the same coupling only to player i's opponents bounds the change
in each of Q_i and C_i by 2BΣ_(j≠i)|q̂_j−q_j|. Thus the change in their
difference is at most 4BΣ_(j≠i)|q̂_j−q_j|. These are differences of Quit
probabilities; no factor-two PMF ℓ¹ convention is being used.

### 3. Length-independent weighted repair

Fix 0<ρ≤1/8. Suppose a finite input in [−B,B]⁴ satisfies WP's displayed
inequalities with ε=Bρ². Write a_t=a(q_t).

At each original row (q_t,y_t), delete any action whose gap from the best
action is greater than β=Bρ, transferring its mass to the other action.
Call the new root q̂_t. At most one action per player is deleted. If a
deleted action has mass p, ordinary regret gives

    pβ<Reg_i(q_t,y_t)≤Bρ²a_t,

unless p=0, in which case its deletion changes nothing. In either case its
mass is at most ρa_t. Therefore

    |q̂_t(i)−q_t(i)|≤ρa_t,
    Σ_i|q̂_t(i)−q_t(i)|≤4ρa_t,
    â_t:=a(q̂_t)≥(1−4ρ)a_t≥a_t/2.                  (3.1)

All deletions are defined using the ORIGINAL row. Every action subsequently
used either survived that test or is the original best action receiving
transferred mass; its original gap is at most β.

Now set v̂_0=y_0 and recompute exactly by

    v̂_(t+1)=F(q̂_t,v̂_t).

Every value remains in [−B,B]⁴. Let e_t=‖v̂_t−y_t‖∞. Equations (2.1),
(2.2), the input Bellman error, and (3.1) give

    e_(t+1)≤(1−â_t)e_t+B(ρ²+8ρ)a_t
            ≤(1−â_t)e_t+Kâ_t,
    K=B(ρ²+8ρ)/(1−4ρ).

Since e_0=0, induction gives e_t≤K for every t. Because ρ≤1/8,

    K≤17Bρ.                                        (3.2)

This induction remains valid at a_t=0: both input defects are then zero,
the root is unchanged, and no division by that row's charge is made.
Sure absorption also presents no exception.

For any supported action of player i at q̂_t, simultaneous opponent
changes alter its gap by at most 4B·3ρa_t, and changing y_t to v̂_t adds
at most e_t. Thus every retained action has gap at most

    Bρ+12Bρa_t+17Bρ≤30Bρ≤32Bρ.

The payoff-floor estimate is

    v̂_t(i)≥y_t(i)−17Bρ≥P_i−Bρ²−17Bρ≥P_i−32Bρ.

Summing (3.1) proves that the repaired exact packet retains at least half
the original charge. Its support and floor error is at most 32Bρ,
independently of H.

To deduce WP⇒EP, keep WP's fixed box and choose
0<ρ≤min(1/8,δ/(32B)). Request ε=Bρ² and charge 2Q; the repaired packet
has the required support error, floor, and charge. This proves a finite
repair, without any assumption about how the input was obtained.

### 4. Upward translation proves EP⇒WP

Keep EP's fixed B. Given ε>0 and Q≥0, choose
0<δ≤min(1,ε/3), and take its exact support-δ packet of charge at least Q.
Translate every value by the same vector:

    y_t=v_t+2δ·1.

All y_t lie in the fixed box [−B−2,B+2]⁴. Their floors satisfy
y_t(i)≥P_i+δ, and affinity gives the exact policy residual

    y_(t+1)−F(q_t,y_t)=2δa_t·1.                    (4.1)

Fix a player and row, and write α=c_−i(q_t). The translation raises its
Continue payoff by 2δα and leaves Quit unchanged. If Continue is best
after translation, a used Quit action's new gap is at most δ+2δα≤3δ.
Its ordinary regret contribution is at most 3δq_i≤3δa_t.

If Quit is best after translation, ordinary regret is zero when Continue
has zero probability. Otherwise, if the new gap is positive, the old
support inequality implies

    0<Q_i−C_i(q_t,y_t)≤δ−2δα.

This forces α<1/2, so a_t=1−(1−q_i)α>1/2. Ordinary regret is then at
most δ≤2δa_t. A zero gap again gives zero regret. These cases exhaust
pure, mixed, tied, and all-Continue roots.

Thus every ordinary regret is at most 3δa_t≤εa_t; (4.1) has norm at most
εa_t as well. Roots and charge are unchanged. The enlarged box is chosen
once, independently of ε and Q. This proves EP⇒WP.

The equivalence is at the level of all-accuracy producers. It does not
claim a same-tolerance, same-box equivalence for one supplied packet.

### 5. Reduction of EP to the reward box

Suppose EP holds in [−B,B]⁴. If B=M there is nothing to prove. Otherwise
fix δ>0, Q≥0, put η=δ/2, and set

    L=max(0, log((B−M)/η)).

The terminal contribution to F(q,v) lies coordinatewise in [−Ma(q),Ma(q)].
Hence, writing dist∞ for distance to the reward box,

    dist∞(F(q,v),[−M,M]⁴)≤c(q)dist∞(v,[−M,M]⁴).

Along any exact packet this gives

    dist∞(v_t,[−M,M]⁴)
      ≤(B−M)∏[s<t]c(q_s)
      ≤(B−M)exp(−∑[s<t]a(q_s)).                  (5.1)

Request an original packet of support/floor error δ/2 and charge at least
Q+L+1. Let j be the first accumulated-charge crossing of L, or j=0 if
L=0. Since each row charge is at most one,

    ∑[t<j]a(q_t)≤L+1,
    ∑[j≤t<H]a(q_t)≥Q.

By (5.1), coordinatewise projection of v_j onto [−M,M]⁴ changes it by
at most η. Keep all roots from j onward and recompute exact values from
that projected boundary. The reward box is invariant, and (2.1) gives
uniform change at most η at every retained value. Support transfer from
Section 2 and the original floors now give error δ in both requirements.
Charge is unchanged on the retained suffix. Relabeling it from zero proves
EP in [−M,M]⁴. This includes L=0, zero row charge, sure absorption, Q=0,
and a possibly empty retained suffix.

## Boundary tests

### Zero absorption and unweighted accumulation

If a(q_t)=0 then q_t is all-Continue. The weighted assumptions require
both the policy residual and ordinary regret to vanish at that row.
The pruning changes nothing and the recomputation introduces no error.
The proof never divides by a_t.

The weight cannot simply be removed from the Bellman premise. On the
all-zero reward table, let every root be all-Continue and take all four
coordinates y_t(i)=t/H for 0≤t≤H. These annotations lie in [0,1]⁴ and
satisfy the zero punishment floor. Every row has ordinary regret zero
and unweighted Bellman residual 1/H. Exact recomputation from y_0 is
identically zero, yet the final annotation error is one. Thus an
unweighted local residual tending to zero does not give the proved
length-independent correction estimate. This test has zero charge; it
does not assert failure of some different charged construction.

### Ordinary regret does not already mean support optimality

Take M=B=1, with every nonpivot reward coordinate zero. Set player 0's
reward to 1 on the coalition {1} and to zero on every other coalition.
Then every punishment value is zero: rewards are nonnegative and all-Never
opponents cap player 0 by zero.

For 0<ε<1, choose a root with q_1=1, q_0=ε, and q_2=q_3=0. Put y_0=0
and y_1=F(q,y_0)=(1−ε,0,0,0). Its absorption is one and its Bellman
residual is zero. Player 0's Quit and Continue payoffs are 0 and 1;
ordinary regret is ε, but its used Quit action has gap one. All other
regrets are zero and all floors hold. Hence the weighted input genuinely
allows a supported action gap which does not tend to zero at the same
rate, or even tend to zero at all, with ε.

The pruning removes that inferior Quit action and the repaired root
q_1=1, q_0=q_2=q_3=0 is exact Nash. Since c=0, repeating this latter
root gives exact packets of arbitrary charge with annotations
(1,0,0,0) after the first row. This also supplies an exact positive
example of the packet contract.

### Sure absorption, ties, and vanishing support masses

At â_t=1 the recomputation inequality discards the previous error and
bounds the new error by its local term; no survival denominator occurs.
A zero-mass inferior action changes nothing when deleted. A tied action
is not deleted, and switching the identity of the best action is covered
by the positive-part Lipschitz bound in the proof.

When passing EP to WP, an all-Continue root causes policy residual zero.
The common upward shift makes its supported Continue action optimal:
the old used-action gap was at most δ and the Continue value rises by
2δ. Thus that zero-charge boundary is consistent with the weighted
ordinary-regret requirement as well.

### Box reduction and quantifier boundaries

If B=M no clipping is needed. If L=0 the cut is j=0. If charge target
Q=0 the retained suffix can be empty; all its displayed endpoint
conditions are still imposed. A sure-absorption row makes excess
distance to the reward box zero. These are covered explicitly in the
reviewed proof.

The EP⇒WP direction uses the fixed enlarged box [−B−2,B+2]⁴. It does
not claim equivalence for one packet at the same box and tolerance.
No value of B is allowed to grow with accuracy or the requested charge.
Nor is large packet length a substitute for large charge: on the
all-zero table, repeated all-Continue roots with zero annotations have
arbitrarily large length and exactly zero total absorption charge.

## Adapter and consumer

The input consists of the actual finite reward table and the displayed
weighted finite data, with the quantifiers WP imposes. The repair uses
only independent Boolean roots, their explicit action payoffs, finite
pruning, and exact evaluation of F. It makes no choice on behalf of a
deviator and imposes no observation beyond the quitting game's live
history.

For any requested support error δ and charge Q, fix the one box furnished
by WP, choose ρ as in the proof, and request its packet at tolerance Bρ²
and charge 2Q. The repaired roots and annotations are a literal
`QuittingFiniteForwardPacket` at δ and Q. The invariant box is compact.
Applying the existing
`quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets`
therefore yields the fixed-target unrestricted uniform-equilibrium
conclusion. This invocation is an existing checked consumer, not a new
unproved realization lemma.

Conversely EP yields WP by the explicit upward translation. The reward-box
argument narrows the exact producer to [−M,M]⁴ without changing its
all-accuracy/all-charge content. These transformations do not rely on
positive global regret or punishment normality. Those assumptions identify
the remaining named contrary-case source problem; they do not produce
the weighted data in this packet.

## Lean handoff

The narrowest theorem shapes are:

1. Define a finite weighted packet with the same root/value/horizon
   representation as `QuittingFiniteForwardPacket`, but with Bellman
   residual and ordinary root regret bounded by tolerance times
   `quittingRootAbsorptionMass`. Include both endpoint floor conditions
   and the fixed-box membership. Do not include the existence of such
   packets as a structure field.
2. Prove the finite ρ-repair theorem: coordinate root changes, at least
   half retained charge, uniform 17Bρ annotation bound, and a repaired
   `QuittingFiniteForwardPacket` with error 32Bρ.
3. Derive the all-accuracy weighted-producer implication by requesting
   tolerance Bρ² and doubled charge. Compose with the existing checked
   finite-forward consumer rather than duplicating its lasso proof.
4. Prove the reverse producer implication by common upward translation
   and the two cases of the root payoff difference. Keep the one enlarged
   box independent of both requested parameters.
5. Prove the first-charge-crossing reward-box reduction using the distance
   contraction and finite clipping of only the retained boundary value.
   Keep the retained roots unchanged and recompute forward.

Likely reusable definitions and local lemmas are exactly those in Source
correspondence. Only the first horizon+1 annotations and first horizon
roots are constrained; arbitrary extensions of finite arrays should not
create extra hypotheses. Test zero charge, sure absorption, tied actions,
and the large-gap rare-action fixture above. No refactor or new strategy
representation is required by this handoff.

## Review mapping and final-surface changes

The original first-response bytes reviewed independently by HILBERT and
FRECHET have SHA-256

    68518c21ba6e20199f2e4ebf4c9ef83270da3f9493850f6aa5929bae6c9960d3.

The complete reconstruction additionally reviewed by FRECHET has SHA-256

    97c68ad84f3dd9796c5c45c62798ffb686c3dacd7aad974ad12f956e4c52fd2a.

The exact statement and proof here retain those hypotheses, constants,
directions, and fixed-box quantifiers. Added material is the explicit
eligibility explanation, probability/agency clarification, review/source
mapping, Lean handoff, and elementary boundary fixtures. The existing
consumer is separated from the newly proved conversion. No SUM-minimum
claim is imported and no new charge producer is asserted. Final-surface
confirmation concerns this assembled statement and its added boundary
tests, not a waiver of either independent review.

## Scope and nonclaims

This packet reduces a producer specification. It does not establish
unbounded charge at every accuracy from any arbitrary table, positive
SUM or MAX minimum, or hypothetical positive full behavioral gap.
All-accuracy/unbounded-charge existence remains open in the named
contrary-case problem.

No common sequence of packets, fixed initial annotation, prescribed final
annotation, root ancestry, or actual-tail realization is preserved or
supplied. Such constraints are absent from the checked consumer used here.
The packet asserts no unrestricted strategy-class completeness beyond its
stated finite producer equivalence, no equivalence of one packet at the
same error/box, no polynomial-time search, and no solution of arbitrary
Fin4 quitting games. None of the new combined results is claimed proved
in Lean.

