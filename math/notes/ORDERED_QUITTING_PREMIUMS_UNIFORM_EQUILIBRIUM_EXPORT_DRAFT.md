# Ordered positive quitting premiums yield a uniform-equilibrium payoff

Authors: CODEX_FRECHET_CYCLE (finite table criterion and global boundary
geometry), CODEX_HILBERT (classical consumer attachment and source audit).
The signed-premium weakening was proposed by ROOT and independently
identified by CODEX_RENY.

Independent final review records:

- [RENY: full assembled theorem and source scope](../feedback/ORDERED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM__FINAL_BY_CODEX_RENY.md);
- [TARSKI: independent whole-proof falsification](../feedback/ORDERED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM__FINAL_BY_CODEX_TARSKI_PREMIUM.md).

The mathematical adapter proved here is ordinary mathematics, not a new
Lean-checked theorem. Existing production inputs are identified separately.

## 1. Exact statement

Let I be a finite nonempty player set. At every live date each player chooses
Quit or Continue using independent private randomization. Play absorbs at the
first nonempty quitting coalition S⊆I, paying r(S)∈ℝ^I. If no player ever
quits, the payoff is zero. Put s_i=r_i({i}).

Assume all own-singleton rewards are nonnegative:

    s_i≥0                                      for every i.

Put d_i(S)=r_i(S)−s_i when i∈S. Negative own-quitting premiums and all
passive rewards r_i(S), i∉S, are unrestricted. Impose the finite weak
support-peeling condition

    For every nonempty A⊆I, there exists i∈A such that
        d_i(S)≤0 for every coalition i∈S⊆A.                  (WSP)

Equivalently, there is an ordering i₁,…,i_n of the players such that

    d_(i_m)(S)>0 and i_m∈S
        ⇒ S contains i_ℓ for some ℓ<m.                        (ORD)

This orders PLAYER LABELS in the reward table, not chronological quitting
dates. It imposes no order in which the players must quit during play.

MAIN THEOREM. Every such table has one fixed uniform-equilibrium payoff
against unrestricted unilateral behavioral deviations. More specifically,
for every ε>0 there is an actual periodic behavioral profile whose EVERY
surviving-date suffix is terminal ε-Nash against every unilateral behavioral
replacement. The profile, period, and horizon thresholds may depend on ε;
one uniform payoff target can nevertheless be chosen before ε.

Here terminal ε-Nash means that no unilateral replacement increases expected
terminal payoff by more than ε. A uniform-equilibrium payoff v means: for
every ε>0 there are a profile and finite threshold such that at every longer
finite horizon the expected average payoff is within ε of v in each
coordinate and no unilateral behavioral deviation improves its expected
average payoff by more than ε. Active-stage rewards are zero and the
absorbing reward persists. The claim includes Never, arbitrarily late finite
quits, and deviations depending on all observed histories.

AUXILIARY ROOT THEOREM. In this separate statement let singleton levels be
arbitrary signed reals, ADD the hypothesis

    d_i(S)≥0                                  whenever i∈S,    (NN)

and fix |r_i(S)|≤M with M≥0 and B>M. Under (NN), (WSP) becomes the
equality condition

    For every nonempty A⊆I, some i∈A has d_i(S)=0
        for every coalition i∈S⊆A.                            (SP)

Then (SP) is equivalent to the assertion that EVERY absorbing
exact Nash root against EVERY continuation v∈[−B,B]^I has its Bellman
successor in

    L_B={w∈∏_i[s_i,B] : w_i=s_i for at least one i}.             (LB)

Under (SP), no C¹ function H on a neighborhood of that full box can satisfy

    H(v)−H(F(q,v))≥a(q)                                        (D)

for all such exact root Nash edges. Convexity is not assumed. Definitions
of F, a, and root Nash are given next. These boundary and C¹ conclusions
retain (NN); they are not asserted for the main signed-premium class.
Failure of peeling is not asserted to preclude equilibrium or to supply a
negative certificate.

## 2. Definitions, information, and agency

Write q_i for the probability of Quit, so the paper's Continue probability
is 1−q_i. A product root q∈[0,1]^I has

    p_q(S)=∏_(i∈S)q_i ∏_(i∉S)(1−q_i),
    c(q)=∏_i(1−q_i),       a(q)=1−c(q),
    R(q)=Σ_(S≠∅)p_q(S)r(S),
    F(q,v)=R(q)+c(q)v.

For player i let p_(q,−i)(T) be the opponents' product probability of
quitting coalition T⊆I\{i}, and define

    α_i(q)=∏_(j≠i)(1−q_j),
    Q_i(q)=Σ_(T⊆I\{i})p_(q,−i)(T)r_i(T∪{i}),
    G_i(q)=Σ_(∅≠T⊆I\{i})p_(q,−i)(T)r_i(T),
    C_i(q,v)=G_i(q)+α_i(q)v_i.

These are the pure Quit and Continue endpoints, and

    F_i(q,v)=q_iQ_i(q)+(1−q_i)C_i(q,v).

Exact root Nash means F_i=max(Q_i,C_i) for every i. Support-τ root Nash
means every pure action used with positive probability has payoff at least
max(Q_i,C_i)−τ. This is stronger than merely bounding ordinary mixed-root
regret. It implies the production row-perfect inequalities: both endpoints
are at most F_i+τ, and every supported endpoint is at least F_i−τ.
Indeed F_i is an average of supported endpoints in [max(Q_i,C_i)−τ,
max(Q_i,C_i)].

Before absorption there is only the public history in which everybody has
Continued; its length is the live date. Thus behavioral play has independent
stopping-law representatives on ℕ∪{Never}. An arbitrary unilateral
behavioral replacement is permitted, not merely a stationary hazard or a
bounded clock. Post-absorption choices cannot affect payoffs. Our periodic
profiles specify a row at EVERY date, including dates with zero on-path
reach. No public correlation, joint lottery over profiles, shared random
seed, or signal-dependent recommendation is introduced.

An arbitrary root continuation v is only a payoff annotation. Root Nash
against v does not make a root followed by an arbitrary tail into a full
behavioral equilibrium. Section 5 constructs actual suffix payoffs, and
Section 6 invokes the separate full-response consumer.

## 3. The finite ordering test and exact boundary equivalence

### 3.1 Weak support peeling is equivalent to an ordering

Apply (WSP) first to I and remove the selected player i₁, then apply it to
the remaining set and remove i₂, continuing until the set is empty. When
i_m is removed it has no positive premium at a coalition wholly contained
in the remaining set. Therefore every coalition that pays it a positive
premium contains an earlier removed player. This proves (ORD).

Conversely, in a nonempty A take its earliest player i_m. A positive premium
at a coalition i_m∈S⊆A would require an earlier member of A by (ORD), a
contradiction. Its premiums on all those coalitions are therefore at most
zero. This proves (WSP)⇔(ORD) without any restriction on negative premiums.

This is a finite hypercoalition condition. Replacing it by a graph containing
an edge from a rewarded player to EVERY co-member of its rewarding coalition
is generally too strong; ignoring premiums paid only at larger coalitions
is generally too weak. Exact tests appear in Section 9.

### 3.2 Peeling forces all absorbing exact roots onto the same boundary

For Sections 3.2--4 ONLY assume (NN). Then (WSP) is exactly (SP).
Nonnegative own premiums imply Q_i(q)≥s_i. Hence an exact root Nash
successor w satisfies w_i=max(Q_i,C_i)≥s_i for every i.

If a(q)>0, the active support A={i:q_i>0} is nonempty. Choose its player
i from (SP). Opponents outside A Continue surely. Every coalition in i's
Quit endpoint is consequently a subset of A containing i, and each pays
it s_i. Thus Q_i(q)=s_i. Since q_i>0 and Quit is a best reply,

    w_i=Q_i(q)=s_i.

Moreover F(q,v) stays in [−B,B]^I by convexity of the box and the reward
bound. Therefore w∈L_B. No equilibrium selector is restricted: this applies
to EVERY exact Nash root, including roots with mixed, sure, and zero
components.

### 3.3 Failed peeling gives an exact interior successor

Suppose (SP) fails at A. Every i∈A then has a coalition i∈S_i⊆A with
d_i(S_i)>0. Necessarily |A|≥2. Set q_i(t)=t for i∈A, q_j(t)=0
otherwise, with 0<t<1. Every relevant opponent coalition inside A occurs
with positive probability. Nonnegativity and the strict premium at S_i give

    Q_i(q(t))>s_i                              for every i∈A.

For i∈A define

    v_i(t)=[Q_i(q(t))−G_i(q(t))]/α_i(q(t)).                     (1)

All denominators are positive, and (1) makes Continue equal Quit exactly.
As t→0 these coordinates tend to s_i and hence lie inside the padded box
for all sufficiently small t. For j∉A set v_j(t)=B. Its Continue endpoint
tends to B, whereas its Quit endpoint tends to s_j<B; Continue is strictly
best and its payoff is strictly above s_j for small t. One small t works
for all players by finiteness.

Thus q(t) is exact Nash against v(t) in the box, has positive absorption,
and EVERY successor coordinate is strictly above its singleton. The upper
coordinates are also strictly below B because M<B and a(q)>0. This proves
the claimed equivalence, not merely a sufficient invariant-set assertion.

## 4. Smooth global drift exclusion

This section permits signed s but retains (NN) and (SP). For every bounded
table and v in the box,

    |F_i(q,v)−v_i|≤(M+B)a(q),                                  (2)

since |R_i(q)|≤Ma(q) and F_i−v_i=R_i−a(q)v_i.

Suppose H satisfies (D). Minimize it on compact nonempty L_B, obtaining x,
and let J={i:x_i=s_i}.

If J={i}, take a small solo root q_i=t>0, q_j=0 for j≠i. Player i has
both endpoints equal to s_i. For every other player,

    C_j−Q_j=(1−t)(x_j−s_j)
                 +t[r_j({i})−r_j({i,j})].                      (3)

It is strictly positive at t=0 and remains so for small t. Thus this root
is exact Nash, its absorption is t, and its successor lies in L_B by
Section 3. Minimality contradicts the strictly positive drift. For one
player there are no outsider inequalities.

If |J|≥2, each segment x+t e_i for i∈J stays in L_B for sufficiently
small t≥0 because another singleton coordinate remains binding. Hence
∂_iH(x)≥0 for all i∈J. Lower just the binding coordinates:

    v_ε=x−ε1_J,
    [H(v_ε)−H(x)]/ε → −Σ_(i∈J)∂_iH(x)≤0.                      (4)

For small ε>0 these sources lie in the full box, since s_i>−B. Choose
ANY exact Nash root q_ε at v_ε, using finite-game existence. It is not
all-Continue: every i∈J would gain ε by quitting against all-Continue.
Its successor w_ε lies in L_B and is coordinatewise at least s. Thus (2)
gives

    a(q_ε)≥ε/(M+B).

Minimality and (D) would imply

    1/(M+B)≤[H(v_ε)−H(x)]/ε,

contrary to (4). Upper-box coordinates are not moved, and no continuous
selection of roots is used. This proves the auxiliary smooth-drift theorem.

## 5. Actual-data producer for unit singleton levels

We now return to the main (WSP) theorem, with arbitrary negative premiums,
and prove it through the classical
Solan--Vieille mechanism, without using the polynomial separator. First
suppose s_i=1 for all i. Choose R≥1 bounding all absolute terminal rewards
and put

    W={v∈[−R,R]^I : v_i≤1 for some i}.

This is a nonempty compact set.

### 5.1 Exact root choice and positive absorption

At each v∈W choose an exact Nash root q. If q is not all-Continue,
apply (WSP) to its active set A={i:q_i>0}. The selected player's Quit
endpoint averages only coalitions contained in A that include it; each pays
it at most 1. Thus Q_i(q)≤1 and, since Quit is supported,
F_i(q,v)=Q_i(q)≤1. This step does NOT use the lower-orthant conclusion
of Section 3. If q is
all-Continue, root Nash implies v_j≥1 for every j. Membership in W then
supplies a player i with v_i=1, indifferent between Quit and Continue.

For any 0<δ≤1, replace only i's Quit probability by

    q'_i=q_i+δ(1−q_i),

leaving every opponent's root unchanged. Then a(q')≥δ. If i was mixed
it was indifferent; if it was surely Quit it is unchanged; and in the
all-Continue case its new Quit action is also indifferent. Its payoff remains
unchanged and at most 1, with equality in the all-Continue case. Hence
F(q',v)∈W, including the cube constraint. In the absorbing case the selected
player was active, so no previously unused Quit action is introduced there.

Every other player's pure-action payoff changes by at most 2Rδ: condition
on the single changed independent Bernoulli coordinate. Its support is
unchanged, so every supported action is within 4Rδ of each pure action.
Player i's supported actions remain exact best replies. Thus q' is a
support-(4Rδ) root equilibrium. This supplies, from the raw table itself,
a charged row and successor in W at every v∈W. There is no supplied
correspondence or favorable-root assumption left open.

### 5.2 A finite mesh supplies literal periodic tails

Given a desired row tolerance τ>0, choose

    δ=min(1/2,τ/(8R)),          ζ=δτ/4.

Take a finite ζ-net of W with representatives in W. For each representative
choose the row just constructed, and map it to a representative within ζ
of its successor. This self-map of a finite nonempty set has a directed
cycle. Read that cycle backwards. Label a row's current annotation by its
forward successor representative and its next-tail annotation by its forward
source representative. The resulting periodic lists satisfy

    |v_ℓ−F(q_ℓ,v_(ℓ+1))|∞≤ζ,
    a(q_ℓ)≥δ,
    q_ℓ is support-(4Rδ)-Nash against v_(ℓ+1),                 (5)

with indices interpreted cyclically.

Repeat these INDEPENDENT product rows forever. Survival for n further dates
after any restart is at most (1−δ)^n. Therefore every suffix terminates
almost surely. Let U_ℓ be its ACTUAL expected terminal payoff vector. These
vectors are periodic, bounded by R, and obey

    U_ℓ=F(q_ℓ,U_(ℓ+1)).

Maximize |U_ℓ−v_ℓ|∞ over one period. The Bellman coefficient c(q_ℓ) is
at most 1−δ, so (5) gives

    max_ℓ |U_ℓ−v_ℓ|∞≤ζ/δ.

Each pure endpoint is 1-Lipschitz in that player's continuation coordinate.
Every row is consequently support-(4Rδ+2ζ/δ)-Nash against its ACTUAL
next-tail payoff. The selected constants make this error at most τ.

This is a genuine chronological producer. It supplies a periodic actual
profile with a positive row-absorption floor and arbitrarily accurate
support-perfect rows. No continuity of a Nash selector, correlation between
players, selected-source preservation, or payoff realization assumption is
needed. The mesh and period can depend on τ and the table.

## 6. Full-response extraction and nonnegative singleton closure

### 6.1 The existing nonlocal consumer

Small row error does NOT by itself control unrestricted terminal regret,
even with termination at every restart. We use the following existing
production theorem, the Solan--Vieille perfect-sequence extraction:

For a finite table with unit own singletons and every target full terminal
error η>0, there exists a row tolerance τ>0 such that any periodic root
sequence with a positive common absorption bound and production row
τ-perfectness against its ACTUAL next-tail payoffs yields a periodic root
sequence whose every suffix is terminal η-Nash against ALL unilateral
behavioral deviations.

The exact declaration is
`quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
in `UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`.
Its only reward-shape hypothesis is `QuittingUnitSoloExit`; it does NOT
assume capped joint quitting rewards. The source is Solan--Vieille (2001),
Proposition 2.4, restated as Proposition 2.6. The extracted sequence may be
the constructed sequence or a stationary repair represented with period one.
No claim is made that every generated row-perfect profile is already Nash.

Choose the consumer's τ first and then apply Section 5. The support-perfect
inequalities imply its production row-perfect predicate as explained in
Section 2. This proves periodic every-suffix full terminal approximate Nash
existence at every accuracy in the unit case.

### 6.2 Nonnegative levels and the zero-Never correction

Let s_i≥0. For t>0 define terminal rewards

    r^t_i(S)=r_i(S)+t,
    d_i=s_i+t>0,
    hat r^t_i(S)=r^t_i(S)/d_i,

and leave Never at zero in both transformed games. The transformed own
singletons are 1, and its own premiums are the original premiums divided
by d_i. Thus (WSP), equivalently the positive-premium order, survives
exactly; no lower bound on the premiums is used. The transformed reward bound
may grow when t→0; no common bound over t is needed in Section 5.

Given original target error ε>0, take t=ε/4 and η=ε/2. Apply the unit
case with full error η/max_i d_i. Undoing the positive coordinate scales
gives full terminal error at most η for r^t, separately in every suffix.
For every profile π, including EVERY unilateral replacement,

    U_i(r^t,π)−U_i(r,π)=t·P_π(absorption)∈[0,t].                (6)

The safe two-sided estimate transfers η-regret in r^t to at most
η+2t=ε in r. No absorption-one hypothesis is imposed on a deviating
profile or on the extracted profile. This is not a strategic equivalence
under an additive shift: Never was not shifted, and (6) retains precisely
the required correction. Periodicity and the every-suffix comparison survive.

Finally the checked declaration
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
selects one fixed payoff of the ORIGINAL game. It applies to arbitrary
finite player sets. In outline, actual approximate-Nash payoff vectors lie
in one compact reward cube; a convergent subsequence, the full behavioral
terminal-to-uniform comparison, and fixed-profile Cesàro convergence produce
a target fixed before the accuracy. This completes the main theorem.

If all s_i=0, all-Never is also a direct exact equilibrium: a deviator can
produce only its zero singleton or Never. This shortcut is not necessary
for the perturbation proof. Mixed signed singleton levels are outside the
stated semantic theorem.

## 7. Conjecture-facing change and source correspondence

The change is an explicit finite REWARD-TABLE adapter into an old conditional
existence mechanism. It discharges the root-choice hypothesis of
Solan--Vieille Proposition 2.2 for the ordered-premium class, supplies the
actual periodic input of Proposition 2.3, and reaches the unrestricted
semantic endpoint through the already established unit-only extraction.
No strategy or equilibrium witness is required as an input field.

This is a class-level producer, not a supplied-object verifier. The class
admits positive joint-quitting premiums forbidden by the existing capped
joint-exit generator. It therefore changes that named source boundary while
leaving arbitrary quitting tables outside the class unresolved. Its export
relevance is the explicit new table adapter and complete semantic consumer,
not a claim that the classical mechanism itself is new.

Primary source: Eilon Solan and Nicolas Vieille, [“Quitting Games”](https://doi.org/10.1287/moor.26.2.265.10549),
*Mathematics of Operations Research* 26(2), 265--285 (2001). Printed
pp.269--272 state the one-shot definitions and Propositions 2.2--2.4 and
prove the generation steps; pp.272--274 restate and explain the nonlocal
extraction. Proposition 2.2 expressly allows an active quitter with payoff
at most 1, rather than assuming all quitting rewards are capped. The paper
explicitly observes that this hypothesis is weaker than its assumption A.2.
The local original PDF inspected was
`literature/SOLAN_VIEILLE_2001__QUITTING_GAMES__JSTOR.pdf`.

The finite row perturbation and mesh construction in Section 5 reproduce
that old mechanism, with slack constants and literal actual-tail accounting.
The new part is deriving its input from (WSP), its exact ordering
characterization, and the resulting stated table class. The all-root
boundary characterization is a separate refinement under the additional (NN).
No worldwide priority claim is made.

Exact repository correspondence, at inspected HEAD e9f3e90:

- `Root/NashExistence.lean`:
  `exists_isZeroQuittingRootNash` supplies finite exact root Nash existence.
- `Classification/SoloExitPreference.lean` defines
  `QuittingUnitSoloExit`, `QuittingCappedJointExit`, and
  `QuittingWeakSoloExitPreference`. The last condition requires
  r_i(S)≤s_i when i∈S and therefore excludes a strict positive premium.
- `Classification/Existence/PerfectAbsorbingRow.lean`:
  `exists_quittingPerfectAbsorbingRow_of_soloExitPreference` currently
  takes unit solos AND capped joint exit.
- `Classification/Existence/PerfectAbsorbingRootSequence.lean`:
  `exists_periodic_quittingPerfectAbsorbingRootSequence_of_soloExitPreference`
  likewise has the stronger capped-reward input. A generic/raw-table
  generator adapter remains an implementation task, not an input assumption.
- `Classification/Existence/PerfectSequenceExtraction.lean`:
  `quittingPerfectSequenceExtraction_of_soloExitPreference` and
  `quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
  need only unit solos. Their conclusions control full behavioral deviations.
- `Classification/ExistenceBranches.lean` defines the literal production
  `QuittingPlayerRowεPerfect` and `QuittingRowεPerfect` predicates.
- `Terminal/TerminalAffineReward.lean`:
  `quittingTerminalPayoff_playerwiseAffine` already gives the exact
  absorption-weighted shift formula used in (6), not an unconditional shift.
- `Terminal/TargetTail/TerminalUniformPayoffSelection.lean` supplies
  `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  for arbitrary finite player sets.
- `Classification/Existence/AcyclicSoloPreemption.lean` defines augmented
  player edge i→j by r_j({i})<s_j. This uses PASSIVE singleton entries,
  which (WSP) leaves free. Its theorem
  `exists_uniformEquilibriumPayoff_of_acyclic_augmentedSoloPreemption`
  concerns different data, not the premium order.
- `Classification/Existence/SureExitChambers.lean` requires additional
  no-leave/no-join signs. `Stationary/CoalitionToggleDeletion.lean` defines
  `QuittingOwnerJoinAntitone` by comparing r_i(S∪{i}) with the passive
  reward r_i(S), not with s_i. Neither hypothesis follows from (WSP).

These abbreviated paths are under `UniformEquilibrium/Quitting/`.
`Literature/SolanAndVieille2001.lean` contains matching statements
`proposition2_2`, `proposition2_3`, and `proposition2_4`, but that lane is
unbuilt and imported nowhere. It is a source-transcription reference, not
the claimed production status of the generic generator.

The whole weak-solo-preference subclass, with no positive own premiums,
was already covered in ordinary mathematics by the unit-solo/capped theorem
plus the perturbation/scaling in Section 6. In that subclass every ordering
passes (WSP), including arbitrary negative premiums.
The narrow audit did not locate a previously stated finite-support peeling
class theorem. It did locate the classical conditional consumer, which is
credited rather than silently replaced. No fresh Lean build is claimed.

## 8. Independent Fin4 polynomial proof and punishment equality

Define P_i=inf_(τ_−i) sup_(τ_i) U_i(τ_i,τ_−i), where U_i is expected
terminal payoff, the infimum runs over tuples of independent opponent
behavioral laws, and the supremum runs over all own behavioral laws,
including Never and arbitrarily late finite quitting dates.

For δ>0 and B≥0, floor-free weighted capacity Cap⁰_δ(B) is the supremum
of Σ_(t<N)a(q_t) over ALL finite free-start paths with N≥0,
v₀,…,v_N∈[−B,B]^I and product roots q₀,…,q_(N−1), satisfying

    |v_(t+1)−F(q_t,v_t)|∞≤δa(q_t),
    max(Q_i(q_t),C_i(q_t,v_t))−F_i(q_t,v_t)≤δa(q_t)
                                      for every t<N and every i.

The second inequality is ordinary root regret. Length-zero paths at every
source are included, and neither a starting annotation nor a punishment
floor is prescribed.

This section ADDS (NN) to (WSP), so (SP) also holds. For Fin4 with s_i≥0
and (NN), the actual unrestricted punishment vector
equals s. Immediate Quit guarantees at least s_i against every independent
opponent profile. All-Never opponents cap every own law at max(s_i,0)=s_i.
These bounds are exact and do not require a jointly realized punishment
vector. Thus normality holds. The main signed-premium theorem does not
assert this equality; its proof in Sections 5--6 needs no punishment input.

Choose M>0 bounding the rewards. The reviewed analytic separator in
[Polynomial forward certificates without punishment-floor inputs](../exports/POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md)
says finite floor-free weighted capacity at tolerance ε in radius B+1
produces a rational polynomial with unit drift on all tolerance-ε/4 edges
in radius B, for B≥M and 0<ε≤1. These edges allow Bellman defect and
ordinary root regret at most the tolerance times a(q).

If capacity were finite at some δ>0 in radius M+2, it would be finite at
ε=min(δ,1). Apply the separator with B=M+1. Exact Nash/Bellman edges are
included among the tested edges, so Section 4 contradicts its polynomial.
Hence in the ONE fixed radius M+2, floor-free weighted packets exist at
every positive accuracy with arbitrarily large requested charge.

The checked
`hasFloorFreeAbsorptionWeightedFiniteForwardPackets_iff_weighted` in
`Projective/FloorFreeForwardPacketInputRemoval.lean` restores the floors
under the established normality. The checked
`quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets`
in `Projective/AbsorptionWeightedForwardPacketProducer.lean` consumes the
result. Translation imports that defining file; it is not the defining home.

This is an independent Fin4 proof and an additional all-accuracy packet
conclusion. It is not needed for the arbitrary-player theorem. No degree
bound, computability of punishment, or constructive length estimate follows.

## 9. Exact positive and negative boundary tests

All default tables below specify r_i(S)=s_i for every nonempty S and every
coordinate, before the listed changes. They are full tables, not unspecified
coalition completions.

1. **Several ordered recipients; graph simplification can be too strong.**
   Take Fin4, s=(1,0,0,0), and change only
   r_1({0,1,2})=2 and r_2({0,1,2})=3. Ordering 0,1,2,3 works: each
   rewarding coalition contains earlier player 0. The graph connecting
   each recipient to all its co-members nevertheless contains 1→2→1.
   Thus such graph acyclicity is not the finite criterion proved here.

2. **Two exceptional simultaneous quitters can lose the boundary.**
   Take the same canonical singleton vector and change the whole pair row
   r({0,1}) to (2,1,1,1). Own premiums are nonnegative, but (SP) fails on
   {0,1}. At q=(1,1,0,0), players 0 and 1 get respectively 2 versus 1,
   and 1 versus 0, by staying rather than leaving; each outsider gets
   1 rather than 0 by not joining. This root is exact against EVERY
   continuation and its successor is strictly above s in all coordinates.
   It is itself a pure terminal equilibrium, so this is only a boundary
   counterexample, not evidence of a positive gap.

3. **Pair-only tests can miss a larger-coalition obstruction.**
   Instead change only r({0,1,2}) to (2,1,1,1). All pair premiums are
   zero, but (SP) fails on {0,1,2}. The root q=(1,1,1,0) is exact
   against every continuation and again has a strictly interior successor:
   each quitter's deviation to Continue gives only its singleton baseline,
   and the outsider loses 1 by joining. This is also a solved equilibrium
   fixture, used only to test the finite criterion.

4. **Negative premiums can lose the lower orthant.**
   Starting from the default canonical table, change r_0({0,1})=0 and
   r_0({1})=−1. The root q=(1,1,0,0) is exact against every continuation:
   player 0 gets 0 rather than −1 by not leaving, and everyone else is indifferent
   at 0. Its successor is zero, below s_0=1. Thus nonnegative premiums
   cannot simply be omitted from the root-boundary assertion. This table
   DOES satisfy (WSP) and hence the main theorem. It also shows why P=s
   must not be asserted there: player 0's punishment is 0, since immediate
   Quit guarantees at least 0 while opponents with only player 1 quitting
   surely cap it at 0, strictly below s_0=1.

5. **Zero premiums recover the already covered class.**
   With every d_i(S)=0, every ordering passes (SP). Arbitrary signed
   passive rewards remain allowed. The ordinary nonnegative-singleton
   UE class here was already covered by the classical capped-reward
   theorem and its elementary closure. If also s=0, all-Never is exact.

6. **Solo-preemption acyclicity is genuinely different data.**
   Preserve any ordered premium pattern but set each passive singleton
   r_j({i})=s_j−1 for i≠j. Every distinct pair then has both directed
   solo-preemption edges, while (SP) is unchanged. This separates the
   hypotheses; it does not claim exclusion from every other known class.

All these tests use independent product roots. None substitutes a correlated
lottery or a selected finite-menu Nash law for the unrestricted consumer.

## 10. Actual-data adapter, handoff, and frozen proof identities

The adapter takes a finite reward table, nonnegative singleton levels,
and either the finite weak test (WSP) or an ordering
verified against every rewarding coalition. It computes no semantic cap.
After a small terminal perturbation and positive coordinate scaling, it
constructs charged root rows on a fixed compact W, a finite mesh cycle,
and literal periodic actual-tail rows. The existing unit-only extraction
then produces full terminal approximate equilibria, and the existing
all-errors consumer selects a fixed uniform payoff. Nothing equivalent to
the desired equilibrium or actual-tail sequence is an assumed structure field.

A narrow Lean handoff is:

- define weak support peeling and its positive-premium ordering equivalence
  by finite deletion, without imposing a lower bound on premiums;
- prove the selected active-support Quit endpoint UPPER bound for the main
  theorem; separately add (NN) to obtain equality, the all-root lower-boundary
  image, and the small-root converse using (1);
- expose a generic active-low-payoff version of the existing one-shot and
  periodic generators, or implement the finite table adapter directly;
  do not weaken the statement by assuming a sequence exists;
- reuse `quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
  without adding capped joint exit back into its input;
- implement the positive-scaling and small terminal-shift closure using
  `quittingTerminalPayoff_playerwiseAffine`, keeping the Never correction;
- reuse the full terminal-all-errors/fixed-uniform-payoff equivalence;
- formalize the smooth-boundary theorem separately if useful; it is not a
  prerequisite for the classical semantic proof.

The narrowest falsification checks are the failed-support inactive-player
constraints, the exceptional pair premium in (3), near-zero-charge roots in
the multi-binding proof, support rather than ordinary regret in Section 5,
actual chronological tail matching, and the all-behavior Never correction.

Frozen original proof surfaces, retained unchanged:

- [FRECHET: finite support, boundary equivalence, C¹ proof, Fin4 composition](../notes/CODEX_FRECHET_CYCLE__FINITE_SUPPORT_QUIT_PREMIUM_PEELING.md),
  SHA-256 `aff6930efa2be95f654de9097482763fd6103780ff55c09a7059e1491514f329`;
- [HILBERT: classical producer and all-player closure](../notes/CODEX_HILBERT__FINITE_PREMIUM_PEELING_SOLAN_VIEILLE_ADAPTER.md),
  SHA-256 `48933b7ca0a0e321c8dfd38253f668d8e00f751b514d0a7282d5619560f68084`;
- [HILBERT: unrestricted negative-premium weakening](../notes/CODEX_HILBERT__ORDERED_POSITIVE_PREMIUM_WEAKENING.md),
  SHA-256 `09ab58dbcd2dc0d13053b13b0f62c6ea233344211ca15c587497f23f831a1f92`;
- reviewed analytic separator used only in Section 8,
  SHA-256 `14191a09b4a42149e0c893666603d85b2e2f1fb3bcd0240af0e0619aaeefc9d6`.

## 11. Scope and nonclaims

The theorem is a finite-table sufficient class, not a WLOG reduction or an
equivalence between (WSP) and UE. It does not settle the unrestricted
quitting-game conjecture, construct a positive-gap table, prove a uniform
period or packet-length bound, or claim an executable game-solving algorithm.
It does not require stationary equilibrium, and does not identify a fixed
equilibrium target by an explicit algebraic formula. Failure of peeling or
the common-boundary property leaves other equilibrium constructions available.
Mixed signed singleton levels retain only the stated root-geometric theorem
when its ADDITIONAL (NN) hypothesis holds, not the main semantic conclusion.
The main theorem permits arbitrary negative own premiums but does not infer
the lower-boundary property or P=s from them. The classical root-choice and nonlocal
extraction machinery are credited to their existing sources; no worldwide
priority claim or new Lean implementation is made.
