# Constant own-quitting rewards exclude every smooth global root-drift potential

Author: CODEX_FRECHET_CYCLE.

Status: complete ordinary-mathematical proof, initially frozen for independent
falsification. No Lean implementation or export is claimed. The root theorem
below holds for every finite nonempty player set and arbitrary signed singleton
levels. Its stated uniform-equilibrium consequence is restricted to canonical
Fin4 tables and uses the separately reviewed polynomial alternative.

Important source qualification: the canonical search subfamily is already
covered in ordinary mathematics by the existing Solan--Vieille unit-solo,
capped-joint-exit theorem plus the elementary perturbation/scaling argument in
Section 6. The production theorem has literal UNIT singleton hypotheses; the
small closure argument is not represented here as an already named Lean
declaration. Thus this note does not establish a previously unexcluded UE class.
It rejects the proposed negative-certificate search family without fitting any
polynomial, and preserves an independent exact-root geometric proof.

## 1. Complete data and claim

Let I be a finite nonempty set. For every nonempty coalition S⊆I, let
r(S)∈ℝ^I be its terminal reward. Never pays zero. Fix real numbers M≥0 and
B>M with

    |r_i(S)|≤M                              for every i and nonempty S.

Write s_i=r_i({i}), and impose the raw-table restriction

    r_i(S)=s_i                              whenever i∈S.             (CQ)

All rewards to NONmembers remain arbitrary signed numbers within the bound.
This is not participant-only reward, not symmetry, and not a WLOG normalization
of an arbitrary quitting table.

For a product root q∈[0,1]^I, write

    c(q)=∏_i(1−q_i),       a(q)=1−c(q),
    p_q(S)=∏_(i∈S)q_i ∏_(i∉S)(1−q_i),
    R(q)=Σ_(S≠∅) p_q(S) r(S),
    F(q,v)=R(q)+c(q)v.

For player i, let Q_i(q) be its payoff from choosing Quit at this root and
C_i(q,v) its payoff from choosing Continue, while every opponent uses the
indicated independent root randomization. Then

    F_i(q,v)=q_i Q_i(q)+(1−q_i) C_i(q,v).

The assertion that q is an exact root Nash equilibrium against v means

    F_i(q,v)=max(Q_i(q),C_i(q,v))             for every i.           (RN)

This is a finite two-action normal-form Nash condition, not a claim of full
behavioral equilibrium against an arbitrary tail realizing v. The annotation
v may be ANY point of K_B=[−B,B]^I. Finite-game Nash existence guarantees at
least one such q at every v.

THEOREM. Under (CQ), there is no C¹ function H on an open neighborhood of K_B
such that

    H(v)−H(F(q,v))≥a(q)                                          (D)

for EVERY v∈K_B and EVERY exact root Nash equilibrium q against v.

No convexity, polynomial degree bound, positive-gap premise, punishment
normality, or actual-payoff realization is assumed. In particular, a genuinely
nonconvex polynomial cannot satisfy (D) either. The same conclusion holds for
any fixed positive drift coefficient in front of a, by rescaling H.

## 2. Exact-root images and a quantitative displacement bound

Restriction (CQ) makes the Quit endpoint independent of ALL opponents:

    Q_i(q)=s_i.                                                  (1)

Consequently (RN) implies, for w=F(q,v),

    w_i=max(s_i,C_i(q,v))≥s_i,
    q_i>0  ⇒  w_i=s_i.                                          (2)

The second implication includes a pure quitter: its prescribed payoff is
then exactly s_i. A genuinely mixed player is indifferent. No division by
q_i, c(q), or an opponent-survival probability is used.

Because F is a convex combination of v and the terminal reward vectors,
F(q,v)∈K_B whenever v∈K_B. Also

    |R_i(q)|≤M a(q),
    |F_i(q,v)−v_i|=|R_i(q)−a(q)v_i|≤(M+B)a(q).                  (3)

Define the upper singleton box and its lower boundary by

    C=∏_i[s_i,B],
    L={x∈C : x_i=s_i for at least one i}.

Both are nonempty compact sets; B>M≥|s_i| makes every singleton face strictly
inside the corresponding lower and upper faces of K_B. By (2), EVERY
positive-absorption exact root has its successor in the same set L:

    q exact against v∈K_B and a(q)>0  ⇒  F(q,v)∈L.                (4)

This is the special global feature of (CQ). General reward tables do not
satisfy (4), even when the singleton vector is the same.

## 3. Proof of the smooth drift exclusion

Suppose H satisfies (D). Choose x minimizing H over L, and put

    J={i : x_i=s_i}.

The set J is nonempty. The proof separates its two possible sizes.

### 3.1 Exactly one binding singleton coordinate

Suppose J={i}. Let only i Quit, with probability t>0, and let every other
player Continue surely. Player i has Q_i=s_i=C_i(q,x), so both actions are
best replies. For j≠i,

    Q_j=s_j,
    C_j(q,x)=(1−t)x_j+t r_j({i}).                               (5)

At t=0 the latter endpoint is x_j>s_j. There are finitely many opponents,
so for all sufficiently small t>0 every such Continue endpoint remains
strictly above s_j. The root is therefore exact Nash against x. When I has
one player there are no opponent inequalities and any 0<t≤1 works.

Its absorption is a(q)=t. Its successor lies in L by (4), or directly by
the equality in coordinate i and the inequalities (5). Minimality gives
H(F(q,x))≥H(x), contradicting (D).

This argument does not incorrectly assume solo-root availability when more
than one singleton coordinate binds.

### 3.2 At least two binding singleton coordinates

Suppose |J|≥2. For each i∈J, the segment x+t e_i stays in L for all
sufficiently small t≥0: another binding coordinate remains equal to its
singleton, and x_i=s_i<B. Since x minimizes H on L,

    ∂_i H(x)≥0                              for every i∈J.          (6)

Upper-box boundary coordinates outside J cause no problem; none is moved.

For sufficiently small ε>0 define

    v_ε=x−ε 1_J.

It lies in K_B because s_i>−B for every i. Differentiability at x gives

    [H(v_ε)−H(x)]/ε
        → −Σ_(i∈J) ∂_i H(x) ≤0.                               (7)

Choose ANY exact root Nash equilibrium q_ε against v_ε. It is not
all-Continue: at such a root every i∈J would improve by ε by quitting.
Therefore a(q_ε)>0 and w_ε=F(q_ε,v_ε) lies in L by (4).

For any i∈J, (2) gives

    w_ε,i−v_ε,i≥s_i−(s_i−ε)=ε.

Applying (3) yields the quantitative absorption lower bound

    a(q_ε)≥ε/(M+B).                                            (8)

There is no continuity or measurable selection assumption on q_ε. The bound
holds for EVERY exact Nash root at the lowered continuation.

Now (D), minimality on L, and (8) imply

    ε/(M+B)≤a(q_ε)
        ≤H(v_ε)−H(w_ε)
        ≤H(v_ε)−H(x).

Divide by ε and use (7). The positive lower bound 1/(M+B) contradicts
the nonpositive limit. This finishes the proof.

## 4. Consequences for the frozen robust relation

For four players the frozen polynomial packet defines an edge (v,q,w) in
ℛ_δ(B) by

    v,w∈K_B,
    |w−F(q,v)|∞≤δa(q),
    max(Q_i,C_i)−F_i≤δa(q)                    for every i.

Every exact edge in this note belongs to ℛ_δ(B) for every δ>0. The theorem
therefore excludes EVERY polynomial universal robust-drift certificate on a
padded reward box for tables satisfying (CQ), irrespective of whether a
sure-root semantic certificate is available.

One may also apply the reviewed analytic separator directly. Fix Fin4,
M≥1, and outer box radius M+2. If its free-start capacity were finite at
some δ>0, it would be finite at ε=min(δ,1). The analytic theorem with inner
radius B=M+1 would produce a polynomial with unit drift on
ℛ_(ε/4)(M+1), contrary to Section 3. Hence

    Cap⁰_δ(M+2)=∞                           for every δ>0.          (9)

Equivalently there are floor-free weighted packets in ONE fixed box at
every positive accuracy and every finite requested charge. This is an
existential consequence of the reviewed analytic separator, not an explicit
algorithm producing their roots, lengths, or payoff annotations. It does not
assert exact charged recurrence or require a known equilibrium tail.

## 5. Canonical Fin4 UE consequence, and only its justified scope

Now assume I=Fin4 and s=(1,0,0,0). The actual semantic punishment vector is
P=s. Indeed, player i can Quit immediately, obtaining exactly s_i under
(CQ), against every opponent profile. Conversely all-Never opponents give
player i payoff s_i times its probability of ever quitting, whose supremum
is s_i because s_i≥0. These two bounds use unrestricted independent laws,
including Never, and require no simultaneous realization of punishment
coordinates by a single joint profile. Thus normality holds and one singleton
is positive. Any reward bound has M≥1.

The reviewed fixed-box polynomial alternative on radius M+2 states that
no UE implies both the absence of the sure-root certificate and existence of
a polynomial universal robust-drift certificate. The latter contradicts
Section 3. Therefore this canonical Fin4 table has a uniform-equilibrium
payoff against unrestricted behavioral deviations.

Alternatively (9), normality, the checked floor-input-removal theorem, and
the checked weighted-packet consumer give the same conclusion. The target
payoff is fixed before the accuracy request. This is not merely stationary,
terminal-only, or finite-menu Nash existence.

The root theorem was stated for arbitrary finite I, but this section does
NOT infer a general-cardinality UE theorem from an unchecked extension of
the fixed-box polynomial characterization.

## 6. Existing-class coverage: why this is not new UE coverage

The exact existing source theorem assumes unit own-singleton rewards and
r_i(S)≤1 whenever i∈S. It places NO sign restriction on rewards of players
outside the quitting coalition. Its production implementation is listed in
Section 7. The canonical table here does not literally have unit solos;
three of them are zero. The following ordinary-mathematical adapter resolves
that distinction without treating a shift of absorbing rewards as strategically
irrelevant.

For t>0 define, for every nonempty S,

    r^t_i(S)=r_i(S)+t,
    d_i=s_i+t>0,
    hat r^t_i(S)=r^t_i(S)/d_i.

Never remains zero in both games. Under (CQ), hat r^t_i(S)=1 whenever
i∈S. More generally weak solo-exit preference would suffice for the upper
bound 1. Thus the existing unit-solo/capped-joint-exit theorem supplies
terminal approximate Nash profiles for hat r^t at every requested error.

Multiplication of coordinate i's rewards by the positive number d_i preserves
the sign of every unilateral payoff difference, including the Never event.
Given a target error η>0 for r^t, request normalized error
η/max_i d_i. The same independent behavioral profile then has every full
terminal regret at most η in r^t.

For EVERY profile π, including EVERY unilateral deviation,

    U_i(r^t,π)−U_i(r,π)=t·P_π(absorption)∈[0,t].                (10)

In particular absolute payoff differences are at most t, so the safe
two-sided estimate transfers η-regret in r^t to at most η+2t regret in r.
No absorption probability is assumed uniformly positive or close to one.
Choose, for example, η=γ/2 and t=γ/4 for a desired original regret γ.
The original game has full terminal approximate Nash profiles at every γ>0.
The existing terminal-approximation/uniform-payoff equivalence then yields
one fixed UE payoff. This argument applies to the canonical family and is
already an elementary consequence of the previously established class theorem.

Therefore the honest comparison is:

- old checked input: unit-solo/capped-joint-exit existence, with arbitrary
  signed nonowner rewards;
- elementary ordinary adapter: positive coordinate scaling and small
  terminal-reward perturbation cover the nonnegative singleton boundary;
- independent argument preserved here: exclusion of ALL C¹ exact-root drift
  potentials under constant own-quitting rewards, even for signed singleton
  levels, using the full exact-root image and its common boundary;
- no new negative instance, new arbitrary-table UE proof, or new canonical
  class beyond the old existence theorem and its elementary closure.

The source header's warning that normalization is not supplied in that Lean
module remains relevant to the distinction between ordinary mathematical
coverage and a literal named production theorem for the zero-solo boundary.

## 7. Exact sources inspected

Repository source check made at HEAD e9f3e90; no Lean build was performed.
Paths below are relative to the repository root unless stated otherwise.

- `docs/TOOLKIT.md` and `docs/FRONTIER.md` supplied the narrow root,
  fixed-box, and existing-class routes.
- `UniformEquilibrium/Quitting/Root/NashExistence.lean`:
  `exists_isZeroQuittingRootNash` is the finite-game existence input.
- `UniformEquilibrium/Quitting/Root/NashDefect.lean`:
  ordinary root defect and the action-probability positive-part identity
  `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart`.
- `UniformEquilibrium/Quitting/Punishment/SingletonCapBindingCollision.lean`:
  exact solo-root endpoint formulas and
  `exists_quittingSingletonCollisionGain_pos_of_unique_allContinue`.
  Its collision gain is r_j({i,j})−r_j({i}), NOT the own-singleton premium.
  It does not already prove the full boundary argument in Section 3.
- `UniformEquilibrium/Quitting/Classification/SoloExitPreference.lean`:
  `QuittingUnitSoloExit`, `QuittingCappedJointExit`, and
  `QuittingWeakSoloExitPreference`, including their literal normalization
  distinction.
- `UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`:
  `exists_cyclic_subgamePerfectTerminalNash_of_soloExitPreference`,
  `quittingCappedJointExitUniformεExistence_holds`, and
  `exists_uniformEquilibriumPayoff_of_soloExitPreference`.
- `UniformEquilibrium/Quitting/Classification/TerminalExploitabilitySoloExitPreference.lean`:
  `exists_uniformEquilibriumPayoff_of_unitSoloExit_and_cappedJointExit` and
  `exists_uniformEquilibriumPayoff_of_weakSoloExitPreference`; the latter
  still explicitly assumes unit solos.
- `Literature/SolanAndVieille2001.lean`, model and Theorem 1.2 statement:
  faithful source identification for Solan and Vieille, *Quitting Games*,
  Mathematics of Operations Research 26(2), 265--285 (2001). The argument
  here relies on the named production theorem, not an unproved Literature
  statement or a fresh claim about the paper beyond those assumptions.
- `UniformEquilibrium/Quitting/Projective/FixedBoxForwardCharacterization.lean`:
  `quittingGame_exists_uniformEquilibriumPayoff_iff_fixedBoxPackets_or_sureRoot`.
  It is a packet-or-sure-root equivalence, not an unconditional producer.
- `UniformEquilibrium/Quitting/Projective/FloorFreeForwardPacketInputRemoval.lean`:
  `hasFloorFreeAbsorptionWeightedFiniteForwardPackets_iff_weighted`;
  `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketTranslation.lean`:
  `quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets`.
- `UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumUniformPayoffEquivalence.lean`:
  the existing full-terminal-all-errors to fixed-uniform-payoff equivalence
  used in the old-class comparison.
- Frozen reviewed ordinary source in `math/exports/`:
  `POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md`, SHA-256
  `14191a09b4a42149e0c893666603d85b2e2f1fb3bcd0240af0e0619aaeefc9d6`.
  Its analytic separator and fixed-box polynomial characterization supply
  Sections 4--5. Those are distinguished from the production declarations.

## 8. Bounded outcome and requested independent check

The proposed canonical constant-own-reward family is rejected as a
negative-certificate search family. No coefficient fitting, parameter grid,
or degree expansion was run.

The specific requested falsification is the full Section 3 boundary argument:
all exact roots, one versus several singleton bindings, upper-box boundary
coordinates, and the charge lower bound after lowering the bindings. A second
scope check should verify the consumer and existing-class comparison. Nothing
in this note permits replacing (CQ) by mere own-singleton normalization or
extending the common-boundary image property to arbitrary tables.
