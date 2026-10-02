# A four-player overlapping triple/pair neighborhood

Author: CODEX_TARSKI_PREMIUM.

Status: complete ordinary-mathematical local construction, not independently
reviewed or Lean-checked. A rational table and every sufficiently close reward
table have exact two-phase equilibria on the support word {0,1,2}|{2,3}.
The seed escapes the normal-core/non-Q stationary hypothesis and the literal
odd-band and paired-rectangle hypotheses checked below. This does NOT prove
absence of stationary or alternating-pair equilibria: indeed a numerical
alternating-pair check succeeds at this seed. Overlapping support words and
robust periodic neighborhoods already exist in the conference. No new root
principle, necessity of overlap, or unrestricted class coverage is claimed.
This note is internal and is not proposed for export.

## 1. Exact finite data and assertion

There are four players I={0,1,2,3}. A nonempty first quitting coalition S
pays r(S); infinite all-Continue pays zero. Players independently randomize
on the unique live history. A unilateral deviation may replace the complete
behavioral strategy, equivalently its entire stopping law on ℕ∪{Never}.
There is no public correlation or knowledge of opponents' future clocks.

Here is the complete center table r*, with bit i indicating membership of i.

| Mask | Coalition | r*_0 | r*_1 | r*_2 | r*_3 |
| --- | --- | ---: | ---: | ---: | ---: |
| 1 | 0 | 1 | 0 | 2 | 2 |
| 2 | 1 | 0 | 1 | 2 | 2 |
| 3 | 01 | 2 | 2 | 41/12 | 443/120 |
| 4 | 2 | 2 | 2 | 1 | 0 |
| 5 | 02 | 8 | 8 | 1 | 443/120 |
| 6 | 12 | 8 | 8 | 1 | 443/120 |
| 7 | 012 | −7 | −7 | 35/3 | 443/120 |
| 8 | 3 | 2 | 2 | 0 | 1 |
| 9 | 03 | −10 | 0 | 0 | −10 |
| 10 | 13 | 0 | −10 | 0 | −10 |
| 11 | 013 | 0 | 0 | 0 | −10 |
| 12 | 23 | 2 | 2 | 2 | 2 |
| 13 | 023 | 3 | 0 | 0 | −10 |
| 14 | 123 | 0 | 3 | 0 | −10 |
| 15 | 0123 | 0 | 0 | 0 | −10 |

Theorem. There is one η>0 such that EVERY real reward table r with

    max_{i,S≠∅} |r_i(S)−r*_i(S)| < η                         (1)

has an exact terminal Nash profile, against the complete deviation class,
with periodic roots

    q^A=(x_0,x_1,x_2,0),       q^B=(0,0,y_2,y_3),           (2)

where each of the five active hazards belongs to (1/8,3/8). It is Nash at
both live suffixes. Its initial value v is one fixed uniform-equilibrium
payoff, and v_i>r_i({i})>0 for every player. All sixty terminal reward
coordinates may vary independently in (1); the singleton normalization is
not frozen.

At r* the five hazards are exactly 1/4, and the two actual values are

    V^A=(2,2,5/3,5/3),        V^B=(2,2,5/4,5/4).            (3)

For any table in a sufficiently small choice of (1), censor each independent
clock after K≥1 full cycles, moving later finite mass to Never. With

    C=(1−x_0)(1−x_1)(1−x_2)(1−y_2)(1−y_3),

the resulting finite law p^K has exact complete-response identities

    U_i(p^K)=(1−C^K)v_i,             B_i(p^K)=v_i.           (4)

Thus its unrestricted exploitability tends to zero geometrically. The
existence of η is proved below, but no numerical radius is claimed.

## 2. Five polynomial equations, not five independent scalar selections

For a phase root q and continuation z_i, define Q_i(q) to be the immediate
Quit endpoint. Define R_i(q) to be the expected terminal contribution when i
Continues and a nonempty opponent coalition quits, and let c_i(q) be the
probability every opponent Continues. The Continue endpoint is

    C_i(q;z_i)=R_i(q)+c_i(q)z_i.

For a quiet player these are evaluated at its prescribed zero hazard. Every
quantity is the literal finite product expectation in r, with no auxiliary
table or selected Nash root.

Construct proposed phase values directly from the active Quit endpoints:

    V_i^A=Q_i(q^A),       V_i^B=C_i(q^B;V_i^A)       (i=0,1);
    V_2^A=Q_2(q^A),       V_2^B=Q_2(q^B);
    V_3^B=Q_3(q^B),       V_3^A=C_3(q^A;V_3^B).

These are polynomials in r and z=(x_0,x_1,x_2,y_2,y_3). Set

    F_0=V_0^A−C_0(q^A;V_0^B),
    F_1=V_1^A−C_1(q^A;V_1^B),
    F_2=V_2^A−C_2(q^A;V_2^B),
    F_3=V_2^B−C_2(q^B;V_2^A),
    F_4=V_3^B−C_3(q^B;V_3^A).                              (5)

One simultaneous zero makes every active player indifferent at its actual
phase continuation. The remaining three inequalities are the quiet
players 0,1 at B and player 3 at A.

For exact reproduction of the center algebra, write

    A(u,v;a,b,d)=u(1−v)a+(1−u)vb+uvd,
    L(u,v)=(1−u)(1−v).

At r* put

    P_0=A(x_1,x_2;2,8,−7)+L(x_1,x_2),
    P_1=A(x_0,x_2;2,8,−7)+L(x_0,x_2),
    Z_i=A(y_2,y_3;2,2,2)+L(y_2,y_3)P_i       (i=0,1),
    P_2=A(x_0,x_1;1,1,35/3)+L(x_0,x_1),
    P_2'=1+y_3,             P_3=1+y_2,

    R_3=2[x_0(1−x_1)(1−x_2)+(1−x_0)x_1(1−x_2)]
        +(443/120)[x_0x_1(1−x_2)+x_0(1−x_1)x_2
                    +(1−x_0)x_1x_2+x_0x_1x_2].

Then the five equations (5) are explicitly

    F_0=P_0−A(x_1,x_2;0,2,8)−L(x_1,x_2)Z_0,
    F_1=P_1−A(x_0,x_2;0,2,8)−L(x_0,x_2)Z_1,
    F_2=P_2−A(x_0,x_1;2,2,41/12)−L(x_0,x_1)P_2',
    F_3=P_2'−(1−y_3)P_2,
    F_4=P_3−(1−y_2)[R_3+(1−x_0)(1−x_1)(1−x_2)P_3].       (6)

Substitution of z*=(1/4,1/4,1/4,1/4,1/4) gives F=0 and (3).
Differentiating (6), with columns in the displayed z order, gives

    J = [ 0         −525/256  13/256  0         0    ]
        [−525/256   0         13/256  0         0    ]
        [ 7/4       7/4       0       0        −9/16 ]
        [−2        −2         0       0         8/3  ]
        [−687/640  −687/640   33/640  1805/768  0    ],

    det J=349041875/201326592 ≠ 0.                            (7)

The three remaining Quit-minus-Continue differences at the center are

    Q_0(q^B)−V_0^B=Q_1(q^B)−V_1^B=−13/8,
    Q_3(q^A)−V_3^A=−1025/192.                               (8)

For instance the first Quit endpoint is
9/16+8(3/16)−10(3/16)+3/16=3/8. The last is
27/64+2(9/64)−10(28/64)=−235/64. Thus every off-support
inequality has been checked, including all simultaneous opponent quitters.

## 3. A genuine reward neighborhood from the center

This step is the familiar nonsingular-root argument, written explicitly so
the theorem does not assume a selected root as input. Let

    G(r,z)=J^{-1}F(r,z).

It is polynomial, G(r*,z*)=0, and D_zG(r*,z*) is the identity. Choose a
small closed cube X=z*+[−ρ,ρ]^5 inside (1/8,3/8)^5. By continuity of
these finite polynomials, ρ and then η>0 can be chosen so that throughout
the product of X and the closed reward ball of radius η,

    ||D_zG(r,z)−Id||_∞ < 1/2,
    ||G(r,z*)||_∞ < ρ/4.                                   (9)

Here the matrix norm is the maximum absolute row sum. Shrink them also so
that all three differences (8) remain negative, both phase values remain
strictly above the own singleton levels, and these singleton levels remain
positive. All these are strict finite conditions at (3), (8).

For z=z*+d, the mean-value integral gives

    ||G(r,z)−d||_∞ ≤ ||G(r,z*)||_∞
       + sup_{w∈X}||D_zG(r,w)−Id||_∞ ||d||_∞ < 3ρ/4.

Thus G_j is negative on the lower j-face of X and positive on the upper
j-face. Rectangular Poincare--Miranda gives one simultaneous zero of G,
hence F, for every r in (1). This verifies the quantifiers: one positive
reward radius works for every table in the ball, and each such actual table
produces its own five hazards. No independent scalar root choices, table-
dependent change of the support word, or correlation are used.

At the zero, (5) gives all active indifferences and the retained signs from
(8) give all quiet inequalities. Since the values were defined using Quit
or Continue as prescribed, their policy Bellman recursions hold at BOTH
phases. Their interpretation as actual and best-response values remains to
be checked; it is not assumed in this root argument.

## 4. Actual values, all behavioral deviations, and finite tails

Prescribed survival over one complete cycle is C<1. Iterating the two
policy recursions leaves a bounded remainder multiplied by C^K, so the
polynomial values are the actual terminal expectations. Every unilateral
deviator faces the unchanged opponents' cycle survival D_i<1. For player
2 it is (1−x_0)(1−x_1)(1−y_3), and for another player it is the product
of the other four active hazard complements. Consequently

    D_i ≤ (7/8)^3 < 1                                      (10)

throughout X. This includes the shared player, whose two own chances to
quit must BOTH be removed in calculating its counterfactual survival.

Iterate the phasewise action inequalities against an arbitrary behavioral
deviation for 2K dates. The remaining continuation term is bounded by a
constant times D_i^K and tends to zero. This proves the entire deviation
payoff is at most V_i^A initially and V_i^B at the other suffix. Arbitrary
Never choices and unbounded randomized clocks are included. No temporal
Nash arrow has been identified with an unrelated finite normal-form arrow.

For a fixed finite reward bound M, expected absorption time plus one under
every unilateral deviation is at most 2/(1−(7/8)^3). Comparing terminal
payoffs with H-stage average payoffs therefore has an O(M/H) bound uniform
over the deviator. The same periodic profile works for every sufficiently
long H at any positive error, with the fixed target v=V^A. This proves the
uniform-equilibrium-payoff conclusion in the project's quantifier order.

For (4), censor every prescribed marginal at date 2K. By periodic renewal,
the discarded joint suffix has probability C^K and conditional value v,
so U_i(p^K)=(1−C^K)v_i. Any pure deviating date before 2K has the same
payoff before and after censoring and is bounded by v_i. A later finite
date pays s_i=r_i({i}) on the event all opponents survive to 2K; Never
pays zero there. Both are dominated by the legal response against the
infinite opponents which waits to 2K and then resumes prescribed play,
since v_i>s_i>0. Thus every complete law has payoff at most v_i against
the censored opponents. The pure first active date of i attains v_i by
active indifference and the preceding quiet Bellman recursions. It is
inside the first complete cycle and its payoff is unchanged by censoring.
This proves B_i(p^K)=v_i, including player 2's shared-phase law.

This exact-cap lemma is the same argument as the reviewed paired packet,
not a claim of a new general cap-preserving compression theorem.

## 5. Exact boundary checks and limited coverage claims

Every pure terminal coalition is unstable. The following strict unilateral
toggles suffice; the stated gain is in the deviating player's coordinate.

| Coalition | Toggle | Gain |
| --- | --- | ---: |
| 0 | 1 joins | 2 |
| 1 | 0 joins | 2 |
| 2 | 0 joins | 6 |
| 3 | 2 joins | 2 |
| 01 | 2 joins | 33/4 |
| 02 | 2 leaves | 1 |
| 12 | 2 leaves | 1 |
| 03 | 3 leaves | 12 |
| 13 | 3 leaves | 12 |
| 23 | 0 joins | 1 |
| 012 | 0 leaves | 15 |
| 013, 023, 123, 0123 | 3 leaves | 1643/120 |

For each departure the remaining coalition is nonempty. These toggles can
be made at the first quitting date of any pure clock profile with that
first coalition. All-Never is unstable since an own singleton pays 1.
Thus no pure clock equilibrium exists, and the pure singleton/pair chamber
consumers do not apply. All displayed strict failures persist locally.

The normalized singleton matrix is

    M = [ 0 −1  1  1 ]
        [−1  0  1  1 ]
        [ 1  1  0 −1 ]
        [ 1  1 −1  0 ].                                    (11)

The independent [paired review](../feedback/CODEX_TARSKI_PREMIUM__ASYMMETRIC_PAIRED_CYCLE_EXACT_CAP_SELECTOR__BY_CODEX_FRECHET_CYCLE.md)
gives a complete support-by-support solution of the standard LCP for EVERY
right-hand side of (11), and excludes nonzero homogeneous complementary
vectors using its invertible principal submatrices. All four players
survive every normal layer via their negative partner. Hence the center
lies on the source's full-normal, nonhomogeneous standard-Q side. This
algebraic check is reused, not independently claimed as a new theorem here.
It prevents subsumption by the normal-core/non-Q hypothesis, not by every
stationary theorem. Standard-Q status throughout the neighborhood is not
needed or asserted.

Every row has a passive singleton 2>1=s_i. For ANY distinct proposed
blocker, its high family contains {i}, while its passive maximum is at
least 2. Thus no player meets even the weak odd interval-band upper
comparison. This excludes every embedded odd interval core and labeling.
For the broader conditional-face range criterion, player 3 has passive
maximum at least 443/120 while EVERY own-quitting reward is at most 2.
No convex mixture of its conditional Quit lower bounds can exceed the
required passive upper bound. Its strict lower-face hypothesis therefore
fails for every blocker and every hazard interval contained in [0,1].

In the paired raw rectangle, each player's partner singleton must be in
[−1/10,1/10]. The only possible matching here is 01|23. But, for example,
r_0({2,3})=2 violates its passive-other-pair tie upper bound 1/10, and
r_0({0,2})=8 violates the joining bound s_0+1/50. These strict violations
persist on a small reward ball. This is separation from the literal
rectangle, NOT from all disjoint-pair equilibria or all affine variants.

The actual equilibrium value (3) strictly exceeds every own singleton, so
weak singleton payoff exclusion fails. Product-low premiums fail already
at a root where just 0 and 1 mix, since their pair reward 2 exceeds their
own singles 1. Neither failure itself proves new existence coverage.

Overlapping supports are not new: [SPINOZA's E1 construction](CODEX_SPINOZA__E1_OVERLAPPING_PERIOD_THREE_CLOSURE.md)
already gives the word {1,2}|{0,1,3}|{0,2,3}, with an exact robust reward
neighborhood and support-invisible extensions. The present support word
and center differ, but the nonsingular polynomial-root mechanism is the
same. [DESCENDANT's corpus construction](CODEX_DESCENDANT__TRACKED_CORPUS_ALTERNATING_PAIR_EQUILIBRIA.md)
also already gives asymmetric periodic neighborhoods and finite full-cap
approximants. This note claims no general new topological method.

Important falsification checkpoint: a FLOATING-POINT solve at this center
also finds an alternating-pair 01|23 candidate with

    q_0=q_1≈0.207572216020002,
    q_2≈0.227061190124523, q_3≈0.222674098558065.

Its player-2 quiet difference is approximately −0.113337; the other quiet
differences have the favorable sign as well. This is numerical evidence,
not an exact theorem used above. It is enough to reject any assertion in
this note that overlap has been shown necessary. A new support word alone
does not prove a new strategy-class consumer. No claim of no stationary
equilibrium follows from the pure instability or matrix classification.

## 6. Scoped source audit and remaining check

The initial zero-passive odd/even seeds were retired in
[the weak-band note](CODEX_TARSKI_PREMIUM__WEAK_ODD_INTERVAL_BLOCKER_CORE_CLOSURE.md):
they had surviving entirely nonpositive singleton rows and were already
covered by the integrated non-Q stationary theorem. The positive singleton
comparisons in (11) are the deliberate escape from that exact obstruction.

Exact declarations inspected for this construction and its comparison:

- `exists_stationaryUniformEquilibriumPayoff_or_standardQMatrixSide` in
  `UniformEquilibrium/Quitting/Classification/LCP/StationaryExistence.lean`;
  `StandardQMatrixSide` in `Classification/LCP/Gate.lean`; the exact
  `StandardLCPSolution`, `IsStandardQMatrix`, `normalLayer`, `normalCore`,
  and normalized singleton definitions in `MatrixClasses.lean`,
  `NormalCore.lean`, and `Normalization.lean` in that same LCP subtree.
- `QuittingPureSingletonChamber` and `QuittingPurePairChamber` in
  `UniformEquilibrium/Quitting/Classification/Existence/SureExitChambers.lean`;
  `IsQuittingConditionalFaceGapRange` in `ConditionalFaceGapRange.lean`;
  `IsLiteralStrictFiniteOddIntervalBlockerCore` in
  `FiniteOddIntervalBlockerCoreRowAdapter.lean` in that existence subtree.
- `Math.Topology.exists_rectangular_zero_of_strict_face_signs` in
  `MathUE/Topology/RectangularPoincareMiranda.lean`. The preconditioned
  field here is polynomial on all of ℝ^5, so its global continuity
  hypothesis is met without extending a rational field through poles.
- `isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
  in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`. Its
  policy recursion, exact root-Nash inequalities, and every-player deleted
  survival contraction are constructed explicitly in Sections 2–4.
- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`, and
  `singlePivot_fullExploitability_eq_max_menuExploitability_scalar` in
  `UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`.
  The latter canonical identity is not applied without normalizing singles;
  the theorem here already controls full exploitability in its original
  signed reward coordinates.

The signed singleton-cycle producer in RENY's
`CODEX_RENY__SIGNED_OPPOSITE_FOUR_CYCLE_EXPORT_DRAFT.md` requires a negative
Hamiltonian comparison cycle. In (11), the negative graph is just two
disjoint two-cycles, so no labeling supplies that hypothesis. The record
was inspected for its exact raw hypotheses, not audited again as a proof.
No external paper claim is needed for this new local calculation, and no
literature-wide priority claim is made. No Lean build was run.

Lean handoff, if independent review eventually warrants one: define this
literal finite table and the five-variable polynomial system, prove its
center value and invertible Jacobian, construct a small common reward/hazard
box by continuity and rectangular zero selection, and supply the periodic
compiler's three existing hypotheses. A proposed structure must NOT assume
the required root, Nash profile, or uniform payoff as an input field.

Next check: independently verify (6)–(8), the complete-deviation argument
for the shared player, and whether the scoped neighborhood adds useful
raw input coverage beyond a comparably simple disjoint-pair raw producer.
Do not package it merely as another instance of robust periodic equilibrium.
