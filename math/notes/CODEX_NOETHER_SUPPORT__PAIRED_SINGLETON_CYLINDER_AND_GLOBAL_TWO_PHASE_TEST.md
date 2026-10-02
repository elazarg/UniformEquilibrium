# The paired singleton cylinder and a complete two-phase strategy test

Author: CODEX_NOETHER_SUPPORT.

Status: bounded source audit, completed falsification of one global
strategy rule, and an exact stationary repair of a pure-exit-free
completion. Section 6 removes every pure terminal equilibrium while
preserving the failed family's entire unilateral response integrals.
Section 7 solves that repaired table by full four-player active support,
and proves local persistence. No current entire-cylinder consumer was
found in the named paired/cyclic/LCP routes below. None of these tests
is a counterexample to uniform equilibrium or arbitrary periodic play.

## 1. Exact benchmark and current coverage

There are four players, zero live and Never payoff, independent private
behavioral strategies, and unrestricted complete behavioral deviations.
The benchmark consists of EVERY table with arbitrary own-singleton
levels s_i and

    r_i({j})=s_i+Γ_ij,
    Γ=[ 0  3 −1 −1; 3  0 −1 −1; −1 −1  0  3; −1 −1  3  0 ].

All 44 nonsingleton reward coordinates are arbitrary signed reals. Rows
are payoff recipients; columns are sole quitters.

This is literally `FourPlayerPairedSingleton.pairedSingletonMatrix` in
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingleton.lean`.
Its determinant is 45 and its inverse is strictly positive, with diagonal
2/15, within-pair entries 7/15, and cross-pair entries 1/5. The new
negative-determinant index theorem does not apply. No contradiction from
local index +1 is attempted here.

The inspected production sources give the following exact boundaries.

- `pairedSingletonMatrix_normalCore_eq_univ`,
  `pairedSingletonMatrix_standardQ`, and
  `pairedSingletonMatrix_noHomogeneous` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonLCP.lean`
  apply to the singleton matrix. They are not an ordinary UE consumer
  for all its completions.
- `pairedSingletonMatrix_not_projectiveQBar` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`
  excludes the current projective-Q-bar route already on {0,2}. Indeed
  the cross principal is [0 −1; −1 0]; nonnegative residual at right-hand
  side (−1,−1) is impossible even in the projective convention. The same
  file correctly separates residual hardness from nonexistence.
- `stationaryCompletion_isUniformEquilibriumPayoff` in
  `FourPlayerPairedSingleton.lean` fixes all own singletons to zero and
  every nonsingleton payoff to −2. It is one solved completion, not the
  cylinder. `periodTwo_isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`
  fixes the entire `SolanVieilleBoundary.boundaryReward` table. Its
  exact nonstationarity theorem is also table-specific.
- `PairedCycle.exists_exact_allSuffix_uniformPayoff_of_rawRegion` in
  `UniformEquilibrium/Quitting/Cycles/PairedCycleEquilibrium.lean`
  consumes `RawRegion` from `PairedCycleSchedule.lean`. The input includes
  own-pair reward bounds, passive pair rewards, and every quiet-player
  joining reward bound. These are not consequences of the singleton
  matrix and cannot hold for all arbitrary nonsingleton completions.
  In fact its singleton pattern needs one negative partner and TWO
  positive quiet singleton comparisons in each row. Here every row has
  two negative comparisons and only one positive comparison. Positive
  playerwise affine changes preserve that sign count.
- `SignedFourCycleSingletonData` in
  `UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`
  requires negative successor and positive reverse edges. Here each
  reverse edge has the SAME sign as its forward edge. No relabeling
  supplies that hypothesis. The open-sign input in
  `UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean`
  requires only the first cyclic comparison negative and all later
  comparisons nonnegative, also impossible for these rows.
- `TwoBlockTargetSingletonConditions.target_isUniformEquilibriumPayoff`
  in `UniformEquilibrium/Quitting/Examples/Cyclic/FinFourTwoBlockSingletonFiber.lean`
  uses a different singleton fiber. In particular its two active owners
  have one zero directed singleton comparison; Γ has no zero off-diagonal
  entry. It is not an adapter for this benchmark, even after positive
  playerwise affine changes and relabeling.

These are exact non-subsumption checks of the named consumers, not an
assertion about every possible theorem or an unbounded literature search.
The supplied balanced singleton certificate interface is a verifier; no
certificate for this cylinder is inferred from its presence. The current
frontier descriptions distinguish these matrix diagnostics and solved
completions in the same way.

## 2. A concrete global strategy rule to test

Consider the natural complete infinite strategy family that alternates
cross pairs A={0,2} and B={1,3}. At even dates only A can quit, at odd
dates only B can quit; at every eligible date each active player quits
independently with the SAME hazard q. An inactive player continues.
The parameter q ranges over ALL of [0,1], not just a selected small
branch or a finite grid. Deviation restrictions are not imposed: a player
can quit at an inactive date, use Never, or replace its whole strategy.

The entire-cylinder claim would need this rule to produce arbitrarily
small full regret on every completion if it were to be a universal
producer. The following literal completion disproves that rule:

    s_i=1 for all i;
    r_i({j})=1+Γ_ij;
    r_i(S)=4 if i∈S, and −2 if i∉S, whenever |S|≥2.

Never is zero, not one. This table is itself solved: all four players
Quit0. Any unilateral response either also quits, giving 4, or continues
while the other three quit, giving −2. Hence the grand-coalition profile
is exact terminal Nash against all behavioral deviations and has fixed
uniform payoff (4,4,4,4).

We will prove a positive full-regret floor ONLY for the displayed
equal-hazard alternating family. No general periodic impossibility is
inferred from this solved table.

## 3. Exact prescribed values and unrestricted caps

Fix 0<q<1 and put a=1−q. Every player and every deleted-opponent family
is proper. Thus absorption is certain even if the queried player uses
Never. Subtracting the common payoff baseline 1 in the following
calculations is legitimate for these outcome integrals. This is not an
affine transformation of the game, and does not apply at q=0.

Relative to a queried player, phase A means its active phase, and phase B
its inactive phase. Let z_A,z_B be its prescribed terminal payoffs minus
1. In its active phase the other active player is a cross-pair opponent;
in the inactive phase the two active players are its original partner
and a cross-pair opponent. Therefore

    Q_A=3q,                  Q_B=3q(2−q),
    h_A=−q,     c_A=a,      h_B=2qa−3q²,     c_B=a².      (1)

Here Q is the terminal payoff of immediate Quit minus 1, while h+c w
is the Continue endpoint minus 1 if the next-phase value minus 1 is w.
All singletons, cross-pair ties and joining triples are retained in (1).

The actual prescribed equations are

    z_A=q Q_A+a(h_A+a z_B)=3q²−qa+a²z_B,
    z_B=h_B+a²z_A.

In particular

    z_A=(3q²−qa+a²h_B)/(1−a⁴),       z_B=h_B+a²z_A.       (2)

Never has values minus 1

    n_A=(h_A+a h_B)/(1−a³),
    n_B=(h_B+a²h_A)/(1−a³).

The EXACT full behavioral caps minus 1 are

    w_A=max(Q_A, h_A+a Q_B, n_A),
    w_B=max(Q_B, h_B+a²Q_A, n_B).                         (3)

Proof of completeness of (3): the three terms are actual responses
(Quit now, Continue once and Quit next phase, Never). Their maxima solve
the two Bellman equations w_A=max(Q_A,h_A+a w_B) and
w_B=max(Q_B,h_B+a²w_A). For example the extra full-cycle candidate
h_A+a h_B+a³Q_A is the convex combination
(1−a³)n_A+a³Q_A and cannot beat max(n_A,Q_A). Iterating the Bellman upper
bound caps any adaptive complete response; its surviving continuation
remainder tends to zero at rate at most a^(3n) after n periods. Thus no
stationary-only restriction or unlisted deadline is hidden in (3).

At a common initial calendar phase two players occupy each relative
phase, so the original full exploitability is exactly

    E(q)=max(w_A−z_A,w_B−z_B).                            (4)

## 4. Every parameter fails, including boundary sequences

Suppose E(q)=0 for some 0<q<1. The queried active player uses both
actions with positive probability, and its full cap bounds each action's
continuation response. Equality of its prescribed payoff and cap
therefore forces z_A=Q_A=3q. Equations (2) then give

    z_B=4q/(1−q),
    F(q):=1−16q+14q²−3q³=0.                              (5)

Equivalently

    1−4q+2q²=3q(2−q)²>0.

The left side is decreasing on (0,1) and is negative at 3/10, so q<3/10.
On [0,3/10], F'=−16+28q−9q²<0, while
F(1/10)=−463/1000<0. Hence (5) forces q<1/10.

But a player currently in its inactive phase can Quit immediately,
obtaining the strictly positive gain

    Q_B−z_B=q(2−9q+3q²)/(1−q)>0.                        (6)

This contradicts E(q)=0. It is precisely the inactive-phase response
that active-phase indifference alone misses.

The endpoint calculations also exclude approximate selection through
the boundary. At q=1 the first active pair quits surely, so its members
get 4 and outsiders get −2; an outsider joins for 4. Thus E(1)=6.
As q decreases to zero through positive values, equations (1)–(3) give

    z_A,z_B→1/4,      n_A,n_B→1/3,
    Q_A,Q_B,h_A+aQ_B,h_B+a²Q_A→0,
    E(q)→1/12.

The literal q=0 strategy is all Never and has E(0)=1. Extend E from
(0,1] by its limit 1/12 at zero. This extension is continuous and
strictly positive on [0,1]. Compactness supplies a positive minimum,
which, together with the literal E(0)=1, proves

    inf_(q∈[0,1]) E(q)>0.                                (7)

No constant is optimized. Formula (7) excludes every choice of q and
every sequence of parameters, not merely the exact balancing root.
The unrestricted game nevertheless has the exact grand-coalition
equilibrium already exhibited. Asymmetric hazards, other partitions,
additional phases, and general independent laws remain outside (7).

## 5. Verification and remaining question

Exact symbolic arithmetic checked (2), the balance identity

    z_A−3q=(1−q)F(q)/(4−6q+4q²−q³),

the inactive gain (6), and all limits used above. At 99 rational values
q=k/100, k=1,...,99, exact arithmetic independently verified both full
Bellman cap equalities in (3) and positivity of (4). These finite tests
check the formulas; the all-parameter proof is Section 4.

For nearby source calibration I inspected the named matrix files above,
the paired raw-region definition and interval fields, the exact
period-two endpoint consumer, the open-sign and signed-cycle premises,
and the two-block singleton source. The existing
`SolanVieilleBoundaryAnchoredSoloPeriodicTerminalGap.lean` concerns
one-owner calendars at a DIFFERENT fixed completion; its 1/12 statements
are not used as evidence for (7). No Lean source or export was changed,
and no Lean build was run.

The entire arbitrary-singleton-level, arbitrary-nonsingleton cylinder
has not been solved by this audit or test. A next construction must use
the actual collision rewards to choose a more flexible strategy, rather
than infer quiet-player caps from symmetric active indifference. In
particular this table is removed immediately by its grand-coalition
terminal exit: it does not test the family on a genuine no-UE residual.
The next source-facing question must have the form “an existing terminal
exit OR a new mechanism,” and must retain at least absence of every pure
terminal equilibrium before testing further rates or calendars. The
failure of the unqualified family is not evidence against that disjunction.
This note does not promote a new no-go project or request an export gate.

## 6. A pure-exit-free repair invisible to the tested family

Keep all singleton coordinates and all pair coordinates of Section 2.
Of the triple coordinates change exactly

    r_0(012)=r_3(013)=r_2(023)=r_1(123)=−3.              (8)

All other triple coordinates remain 4 for members and −2 for outsiders.
Set every grand-coalition reward to

    r_i(0123)=−158/7.                                   (9)

Here strings name sets, not dates. The common value in (9) is chosen to
make the positive construction below exactly rational. It is not a
consequence of the singleton matrix or of a no-UE assumption.

Every nonempty pure coalition has a strict profitable membership toggle.
The following table checks all 15 coalitions; the displayed change is
implemented at the original stopping date.

| Original coalition | Deviator | New coalition | Gain |
| --- | --- | --- | --- |
| 0 | 2 | 02 | 4 |
| 1 | 2 | 12 | 4 |
| 2 | 0 | 02 | 4 |
| 3 | 0 | 03 | 4 |
| 01 | 2 | 012 | 6 |
| 02 | 1 | 012 | 6 |
| 03 | 1 | 013 | 6 |
| 12 | 3 | 123 | 6 |
| 13 | 0 | 013 | 6 |
| 23 | 0 | 023 | 6 |
| 012 | 0 | 12 | 1 |
| 013 | 3 | 01 | 1 |
| 023 | 2 | 03 | 1 |
| 123 | 1 | 23 | 1 |
| 0123 | 0 | 123 | 144/7 |

Leaving in the last five rows leaves other sure quitters at that same
date, so there is no hidden tail or sole-owner issue. This excludes
every deterministic complete-clock equilibrium, not merely date-zero
profiles: apply the same toggle at its earliest finite stopping date.
The deterministic all-Never profile is also not an equilibrium, since
every player's immediate singleton reward is 1.

Punishment normality also holds literally. Against all three opponents
playing Never, an arbitrary owner strategy gets its singleton reward 1
times its probability of eventually quitting. Its full best reply value
is therefore 1, and taking the infimum over opponent profiles gives
P_i≤1=s_i. No payoff shift, correlated punishment, or normality
continuity is used. This is only the normality inequality, not a claim
that all other no-UE source conditions hold.

The changes (8)–(9) leave the alternating-family calculation EXACTLY
unchanged, including every complete unilateral behavioral replacement.
At each date, at most two of the queried player's opponents can quit.
The only triple including that player which a unilateral intervention
can produce is as follows:

| Payoff recipient / deviator | Possible joining triple | Changed own triple |
| --- | --- | --- |
| 0 | 013 | 012 |
| 1 | 012 | 123 |
| 2 | 123 | 023 |
| 3 | 023 | 013 |

No grand coalition is possible under any such intervention. Prescribed
play itself uses only singletons and the pairs 02 and 13. Consequently
every changed reward coordinate has zero probability under its own
recipient's prescribed law AND every unilateral replacement of that
recipient. This is same-labelled operational-law preservation, not only
equality of cap values or preservation after retiming. Equations (1)–(7)
hold for the repaired table without alteration, including q=0 and q=1.

Thus absence of all pure terminal equilibria together with P≤s does
NOT force success of this particular equal-hazard alternating family.
This is a scoped failure of the proposed pure-exit-or-family disjunction,
not evidence that the repaired table is a no-UE residual. Indeed the
next section supplies its equilibrium.

## 7. Full active support gives an exact stationary repair

At every live date let ALL FOUR players quit independently with
probability 1/2. These are fresh private stationary behavioral choices;
no public randomization or correlated participation is introduced.

For a general stationary hazard vector q, write a_i(q) for the product
of the three opponent continuation probabilities. Let Q_i(q) be the
expected terminal reward if i quits now, and let H_i(q) be the expected
terminal reward contributed by nonempty opponent coalitions if i
continues now. The latter excludes the all-Continue event. Define

    D_i(q)=(1−a_i(q))Q_i(q)−H_i(q).                    (10)

All three quantities depend only on the opponents' hazards, with the
ORIGINAL reward table and zero Never payoff. When a_i<1 the exact full
behavioral cap is

    B_i(q)=max(Q_i(q), H_i(q)/(1−a_i(q))).               (11)

For completeness, a pure deadline t yields
H_i(1−a_i^t)/(1−a_i)+a_i^t Q_i, a convex combination of the two
endpoints in (11). Never yields H_i/(1−a_i). Every complete behavioral
response is bounded by the same Bellman cap: after any live history the
opponents have the same stationary law, and the unabsorbed remainder
vanishes geometrically. Thus (11) keeps every deadline and Never, not
only stationary deviations.

At q=(1/2,1/2,1/2,1/2), each owner sees the same reward multiset. Its
eight Quit coalitions have rewards: singleton 1, three pairs of reward
4, two triples of reward 4, one triple of reward −3, and grand reward
−158/7. Its seven nonempty Continue coalitions have singleton rewards
4,0,0, three pair rewards −2, and one triple reward −2. Hence

    a_i=1/8,
    Q_i=(1+12+8−3−158/7)/8=−4/7,
    H_i=(4−6−2)/8=−1/2,
    D_i=0.                                             (12)

Both endpoints in (11) equal −4/7. The prescribed stationary payoff
also equals −4/7: both actions have that value with continuation −4/7,
and the joint continuation probability is 1/16<1. Therefore this is
an exact terminal Nash profile against unrestricted behavioral
deviations, with payoff (−4/7,−4/7,−4/7,−4/7).

The negative payoff is not inconsistent with Never being assigned zero:
the queried player can choose Never, but the three fixed opponents still
absorb almost surely and give that player expected payoff −4/7. Never
means no player ever quits, not the queried player merely continuing.

The SAME stationary profile delivers this fixed uniform payoff. For any
unilateral deviation, the probability of remaining live through t dates
is at most (1/8)^t. Thus terminal versus N-stage Cesàro payoff differs
uniformly over deviations by at most a constant times 1/N, obtained by
summing this geometric tail. The prescribed profile has the analogous
bound with 1/16. Combining these bounds with exact terminal Nash gives
the fixed-target uniform-equilibrium contract. This also supplies all
suffixes because the strategy is stationary.

This positive construction uses a freedom missing from the failed
family: all four players can be active in the SAME row. Unequal rates
are unnecessary at this center. In particular it uses the previously
invisible triple and grand coordinates rather than assuming they can
be ignored.

## 8. Local persistence, source correspondence, and the remaining cylinder

This stationary solution is not an isolated coincidence of equations.
In coordinate order 0,1,2,3, the Jacobian of D from (10) with respect
to the four hazards at the displayed table and q=(1/2,...,1/2) is

    J=(1/112)[  0  −765  −541  −198;
               −422    0  −541  −541;
               −541  −198    0  −765;
               −541  −541  −422    0 ],
    det J=−1785823609/1229312 ≠ 0.                      (13)

These exact entries follow by differentiating the finite eight-outcome
formulas for Q_i,H_i and a_i. For a short determinant check, 112J has
block form [A B; B A], with
A=[0 −765; −422 0] and B=[−541 −198; −541 −541]. Thus its determinant
is det(A+B)det(A−B)=(−422·1504)·360154, giving (13).
Exact rational arithmetic also checked
all 15 toggle rows, the endpoint equalities (12), and (13). These are
finite identity checks; the full-response argument is (11).

Here is a direct local existence argument. For a nearby reward table r
define T_r(q)=q−J⁻¹D_r(q). At the center T fixes q and its derivative
in q is zero. Continuity of the polynomial derivative supplies a closed
hazard box around the center, contained in (0,1)^4, and a reward
neighborhood on which T_r has Lipschitz constant at most 1/2. Shrink the
reward neighborhood so T_r moves the center by less than half that
box's radius. It then maps the box to itself; successive iteration is
Cauchy and converges to a fixed point q(r). Thus D_r(q(r))=0 and (11)
gives a full-support exact stationary terminal equilibrium for every
table in this neighborhood. No rate or radius is optimized.

This is an open-neighborhood conclusion in all 60 nonempty-coalition
reward coordinates, and hence also relative to the fixed-Γ cylinder.
Shrinking the neighborhood preserves the strict pure-toggle gains and
positive own singleton levels. Against all-Never opponents, the same
argument gives P_i≤s_i for these nearby positive singleton levels.
The previously proved family floor also persists after a sufficiently
small shrink: each terminal payoff changes by at most the reward
sup-norm distance, uniformly over all actual profiles and deviations,
so full exploitability changes by at most twice that distance. This
does not assert that all these tables evade every existing UE theorem.

The exact source correspondence is the supplied-root stationary
verifier, not a new stationary existence theorem. I inspected
`quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never`
in `UniformEquilibrium/Quitting/Stationary/CompleteBehavioralCap.lean`,
the underlying full-rate behavioral verifier in
`UniformEquilibrium/Quitting/Stationary/FullRateStationaryVerifier.lean`, and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.
The latter's inputs are exactly joint absorption, a stationary payoff
fixed point, endpoint Nash, and opponent contraction. Equations
(10)–(12) supply them here; (13) supplies an ordinary mathematical local
producer. This note's computation was not checked by Lean.

The ENTIRE degree-1 singleton cylinder remains open in this investigation.
Choosing (8)–(9) to make (12) true is not production of a root for a
supplied arbitrary collision completion. The next conjecture-facing
question is whether the actual same-table no-UE restrictions force an
all-four-support stationary solution OR a different existing exit.
The limited pure-exit and punishment-normality premises alone have now
been tested, and do not justify the smaller alternating family.

## 9. Existing boundary table stops the stationary-only inference

The analogous inference to full-support stationary existence is already
false under these LIMITED source premises, without inventing another
completion. The same-cylinder `SolanVieilleBoundary.boundaryReward` has
s_i=1, every pair member reward 1, and the displayed singleton matrix.
Hence P_i≤s_i by all-Never opponents. Moreover every positive-owner
solo/join rate condition holds with margin 1: for each owner k choose
a cross-pair recipient i, so for every h∈(0,1]

    (1−h)s_i+h r_i({k,i})−r_i({k})=1.                 (14)

Its literal table also excludes every pure terminal profile. A singleton
has a cross-pair join gain 1. Each pair 01 or 23 has a member leave gain
3; each cross pair has an outsider join gain 1. Each triple has a
zero-paid member who can leave for 1. Each grand-coalition member can
leave from −1 to 0. All-Never has singleton gain 1. These checks use
`boundaryReward` as defined in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`.

Nevertheless `periodTwo_no_stationary_exactTerminalNash` in
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwoStationary.lean`
excludes EVERY stationary product profile, including all boundary
supports, against complete behavioral deviations. I inspected its exact
statement and its gain-complementarity/absorbing-versus-all-Continue
dispatch; I am not claiming a fresh audit of its entire polynomial proof.
The table is solved by `periodTwo_isUniformEquilibriumPayoff` in
`FourPlayerPairedSingletonPeriodTwo.lean`, so this is an existing exit,
not a no-UE source or a negative conclusion about the required disjunction.

The bounded diagnostic is therefore complete: source-aware pure exits
do not rescue the original two-phase family; full support repairs one
open completion neighborhood; and even full support cannot replace the
different existing exits. A genuinely new cylinder argument must select
between mechanisms using the supplied collision data, rather than infer
stationary existence from pure exclusion, P≤s, or (14) alone.
