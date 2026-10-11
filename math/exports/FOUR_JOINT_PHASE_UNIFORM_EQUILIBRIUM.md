# Four joint phases with local, upper-only and arbitrary rewards

## Exact statement

Let I={0,1,2,3}. At every live date players independently choose Continue
or Quit, using private randomization and publicly observed past actions.
The first nonempty quitting coalition S absorbs at a given finite reward
vector r(S) in R^4. The live and selecting dates pay zero; subsequent
absorbed dates pay r(S). Perpetual continuation pays zero. Every unilateral
deviation is a complete behavioral replacement, with unrestricted memory,
randomization, finite deadlines and Never. All conclusions are in expectation.
No public correlation is added.

Define the following center on the fourteen proper nonempty coalitions:

| S | r*(S) |
|---|---|
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (5,9/2,13/2,10) |
| 02 | (−3,−3,−3,−3) |
| 03 | (2,5/4,2,2) |
| 12 | (2,2,2,5/4) |
| 13 | (−3,−3,−3,−3) |
| 23 | (13/2,10,5,9/2) |
| 012 | (−3,−3,15/2,−3) |
| 013 | (−3,2,−3,−3) |
| 023 | (15/2,−3,−3,−3) |
| 123 | (−3,−3,−3,2) |

Partition the sixty reward coordinates (S,i) into three disjoint sets:

- P_rw consists of all four recipients in the eight rows
  0,1,2,3,01,12,23,03. Its size is32.
- C_rw consists of the twelve coordinates listed in the next table.
- F_rw consists of the remaining sixteen coordinates, also listed below.

| S | Upper-only recipients in C_rw | Their center rewards | Arbitrary recipients in F_rw |
|---|---|---|---|
| 02 | 0,2 | −3,−3 | 1,3 |
| 13 | 1,3 | −3,−3 | 0,2 |
| 012 | 0,2 | −3,15/2 | 1,3 |
| 013 | 1,3 | 2,−3 | 0,2 |
| 023 | 0,2 | 15/2,−3 | 1,3 |
| 123 | 1,3 | −3,2 | 0,2 |
| 0123 | none | none | 0,1,2,3 |

**Theorem.** There exists delta in (0,1/2] such that EVERY finite raw
table r satisfying

    |r_i(S)−r*_i(S)| < delta for every (S,i) in P_rw,
     r_i(S) ≤ r*_i(S)+delta for every (S,i) in C_rw             (1)

has an exact terminal Nash equilibrium against all complete behavioral
deviations. It uses the deterministic repeated pair schedule

    A=01,       B=12,       C=23,       D=03,

with independent scheduled Quit probabilities in (1/4,3/4), and pure
Continue for unscheduled players. There is NO lower bound on the twelve
C_rw rewards, and NO condition except finiteness on the sixteen F_rw
rewards. In particular the grand row r(I) is ANY finite vector in R^4.

The profile's actual phase-A terminal payoff v(r) is a fixed original-game
uniform-equilibrium payoff. The same profile works for every accuracy and
all sufficiently large finite horizons. There is no payoff normalization,
row transport or supplied strategic witness in (1). The radius is
existential; no numerical lower bound on delta or executable rate selector
is claimed. All sixty rewards remain finite inputs of the original game;
none may be infinite. This is ordinary mathematics, not a new Lean-checked
result or an arbitrary-Fin4 existence theorem.

## Conjecture-facing change and strategic inputs

The result supplies an actual producer on a32-coordinate open box, times a
12-coordinate lower set with upper bounds, times the entire remaining
16-coordinate space. The repeated owners and four overlapping joint phases
are not an ordered partition into two scheduled pairs. A concrete asymmetric
completion below fails the named
finite singleton, quotient, quiet-child, two-pair and sure-owner source
screens over their complete stated selection sets. This is not a claim that
four phases are necessary, that stationary equilibria do not exist, or that
earlier unquantified implicit-function neighborhoods are disjoint.

The only inputs are the raw sixty finite rewards and the fixed numerical
center. Eight hazards are produced by the nonsingular local system below;
all phase values are its actual policy evaluation. No continuation target,
Nash row, child equilibrium, return rule, degree certificate, clock or
punishment plan is an input.

## Policy evaluation and literal endpoint equations

Order the eight scheduled hazards as

    q=(a0,a1,b1,b2,c2,c3,d0,d3).

For phase t with pair {i,j}, write x=q_ti and y=q_tj. Put

    S_t=(1−x)(1−y),
    G_t=x(1−y)r(i)+(1−x)y r(j)+xy r(ij),
    P=S_A S_B S_C S_D,
    U_t=[G_t+S_t G_(t+1)+S_t S_(t+1)G_(t+2)
                    +S_t S_(t+1) S_(t+2)G_(t+3)]/(1−P).      (2)

Phase subscripts are cyclic. For proper rates these are the actual terminal
values: summing the geometric cycle gives (2), and

    U_t=G_t+S_t U_(t+1).                                    (3)

Write s_i=r_i(i). The pure endpoints for an active i with scheduled mate j
and mate rate y are

    Q_ti=(1−y)s_i+y r_i(ij),
    C_ti=y r_i(j)+(1−y)U_(t+1),i.

Define its indifference equation

    F_ti(r,q)=Q_ti−C_ti=0.                                  (4)

There are eight rows, ordered A0,A1,B1,B2,C2,C3,D0,D3. For an inactive k,

    Q_tk=(1−x)(1−y)s_k+x(1−y)r_k(ki)
                    +(1−x)y r_k(kj)+xy r_k(kij),
    C_tk=U_tk.                                             (5)

All rows in (2), (4) and (5) are proper coalitions. A single replacing
player can add at most itself to the two scheduled quitters, so even its
entire behavioral replacement can never produce the grand coalition.
This proves exact grand-row irrelevance, not merely continuity in that row.

## Exact center arithmetic

At q*=(1/2,...,1/2), joint survival per period is P=1/256, and the four
actual policy values are

    U_A=(3,11/4,2,3),       U_B=(2,3/2,3/2,2),
    U_C=(2,3,3,11/4),      U_D=(3/2,2,2,3/2).                (6)

For example each phase identity is U_t=(r(i)+r(j)+r(ij)+U_(t+1))/4.
The active endpoint values, with Quit=Continue in every entry, are

| Phase | First owner's Q=C | Second owner's Q=C |
|---|---|---|
| A | player0:3 | player1:11/4 |
| B | player1:3/2 | player2:3/2 |
| C | player2:3 | player3:11/4 |
| D | player0:3/2 | player3:3/2 |

The complete inactive Continue-minus-Quit margins at the center are

| Phase | First inactive margin | Second inactive margin |
|---|---|---|
| A | player2:1/8 | player3:15/4 |
| B | player0:2 | player3:7/8 |
| C | player0:1/8 | player1:15/4 |
| D | player1:7/8 | player2:2 |

These follow by averaging k,ki,kj,kij with weights 1/4 in (5). In
particular every inactive inequality has strict slack at least1/8.

## Nonsingular raw rate producer

First construct an auxiliary two-sided local source. Regard F as a smooth
function on a neighborhood in R^56×R^8, extending
rates temporarily to real coordinates. At (r*,q*), 1−P=255/256 and F=0.
Its rate Jacobian J is K/255, with the orderings above and

    K = [   0   504  −256   256   −80   −80     0     8 ]
        [ 249     0     0   128  −128  −128   −10    22 ]
        [ −24     0     0  1022  −512  −512   −40    88 ]
        [ −20   −20  1022     0     0  −384    64   −64 ]
        [ −80   −80     8     0     0   504   256  −256 ]
        [−128  −128    22   −10   249     0   128     0 ]
        [   0  −384   −64    64   −20   −20     0  1022 ]
        [−512  −512    88   −40   −24     0  1022     0 ].

For a reproducible derivative formula, differentiate (3):

    partial U_t=partial G_t+(partial S_t)U_(t+1)
                                      +S_t partial U_(t+1).

Changing the first owner's rate at its phase gives center forcing
(r(i)−r(j)+r(ij)−U_(t+1))/2. Propagate with S_t=1/4 around the cycle
and divide by 1−(1/4)^4, then differentiate (4). This yields every
displayed entry. Exact elimination gives

    det K=2^10 3^7 5^5 17^4 ·29·151·6421
         =16435089066040617600000,
    det J=det K/255^8=28792380416/31320375 >0.                 (7)

For an additional check, rational elimination with row swaps (0,1) and
(2,3) gives upper-triangular diagonal

    249, 504, 63746/63, 85850/83, −40163520/3219173,
    842743233/98440, 97699680/4928323, −35849887725/606632.

Its product equals det K; the two row swaps have net positive sign.

The implicit function theorem supplies a smooth local selector q(r), with
q(r*)=q* and F(r,q(r))=0. Shrink its raw domain to a max-coordinate
ball of radius delta_0≤1 such that every rate lies in (1/4,3/4) and all
eight strict inactive margins remain positive. This is possible by (5),
(6) and continuity. These are exactly the active and inactive root-Nash
conditions; policy values are already produced by (2). No independent
continuation or strategic certificate is assumed. All quantities are
independent of the free grand row, so the same delta_0 works for every
such row. The next section proves the full semantic conclusions for this
auxiliary proper-row cylinder; the subsequent domination step proves (1).

## Actual clocks, full behavioral caps and uniform horizons

For a table in the auxiliary proper-row cylinder, let q_i(t) be the
produced periodic hazard when i is scheduled, and zero otherwise. Define
independent private clocks by

    Pr(T_i=t)=q_i(t) product_(s<t)(1−q_i(s)).

Each player is scheduled twice per period with rates above1/4, so its
Never mass is zero. This implements exactly the policy (2). The schedule
depends only on the deterministic date, not on a public seed.

At each live date U bounds both unilateral endpoints and equals the policy
value. Fix any player and any complete replacing behavior. Its opponents
still supply six independent scheduled coins per period, and survival of
a live period requires all six to Continue. Therefore

    Pr(survive m periods under the replacement) <= rho^m,
    rho=(3/4)^6=729/4096<1.                                 (8)

Opponents' coins on the unique all-Continue public history are unaffected
by the replacement. Its own memory and randomization only mix its two
current endpoints. Iterating their upper bounds through m periods and
retaining realized absorbing rewards gives an upper continuation remainder
bounded by a fixed value bound times rho^m. Letting m grow proves that
every complete replacement pays at most U_Ai in terminal expectation.
The prescribed profile attains U_Ai. Thus its full cap, including every
pure deadline and Never, is exactly U_Ai, and its full terminal debt is zero.

All proper rewards in this auxiliary cylinder have absolute value at most
M=11 because delta_0≤1.
This bound is independent of the unrestricted grand row. For the first
quitting date tau starting at zero, (8) gives

    E[tau+1] <= 4/(1−rho)

under every unilateral replacement, including Never. The N-date expected
average differs from terminal expectation by at most

    4M/[(1−rho)N].                                        (9)

The selecting date's zero payoff is included in tau+1. Applying (9) to
the prescription and to a deviation bounds every N-date behavioral gain
by 8M/[(1−rho)N]. Hence v(r)=U_A is chosen once before accuracy, and
the same profile and one common threshold work for every larger horizon.
This proves the auxiliary two-sided cylinder conclusion.

## Removing lower bounds and irrelevant reward coordinates

Fix any hazards on the four scheduled pairs, with unscheduled players
Continue. Every prescribed nonempty coalition is a singleton or one of
01,12,23,03, so every prescribed recipient reward belongs to P_rw.

Now fix one player and any complete unilateral replacing rule. If the
player is scheduled, its opponents can produce only the other member of
the scheduled pair; its own reward is again a P_rw coordinate. If the
player is unscheduled, it can add itself to zero, one or both of the two
scheduled opponents. Checking these simultaneous cases gives exactly

| Replacing player i | Extra non-P_rw coalitions in its own reward |
|---|---|
| 0 | 02,012,023 |
| 1 | 13,013,123 |
| 2 | 02,012,023 |
| 3 | 13,013,123 |

These are precisely C_rw, with the replacing player as recipient. All
other unilateral outcomes use P_rw. An F_rw coordinate might affect
ANOTHER player's reward under this replacement, but never the replacing
recipient's own reward. The grand coalition is unreachable under every
unilateral replacement. The assertion is about unilateral Nash, not
coalitional deviations.

Suppose two finite raw tables r and rhat agree on P_rw and satisfy
r_C_rw≤rhat_C_rw coordinatewise, with arbitrary differences on F_rw.
Couple the prescribed players' private seeds and one fixed complete
replacing rule in the two tables. Their actions, all preabsorption
information, stopping date and quitting coalition are identical. The
replacing player's realized terminal reward under r is no larger than
under rhat; Never is zero in both. Its finite-horizon payoff multiplies
that reward by the same nonnegative fraction of absorbed dates, so the
same comparison holds at every horizon. Prescribed payoffs are identical.
Thus for every i, every complete rule nu_i and every finite horizon N,

    U_i^r(sigma)=U_i^rhat(sigma),
    U_i^r(nu_i,sigma_-i)≤U_i^rhat(nu_i,sigma_-i),
    gamma_N,i^r(sigma)=gamma_N,i^rhat(sigma),
    gamma_N,i^r(nu_i,sigma_-i)
                       ≤gamma_N,i^rhat(nu_i,sigma_-i).     (9a)

No information or agency is removed by this coupling. Before absorption
the only public history is the date and all-Continue past; a complete
behavioral rule with any private memory or seed is retained literally.
In particular taking all pure-deadline and Never caps, or the full
behavioral supremum, preserves the inequalities.

Set delta=delta_0/2. For an arbitrary original table r satisfying (1),
define a comparison table by

    rhat_P_rw=r_P_rw,
    rhat_i(S)=r*_i(S)+delta on C_rw,
    rhat_i(S)=r*_i(S) on proper F_rw coordinates,
    rhat(I)=0.                                             (9b)

Every proper coordinate of rhat is STRICTLY within delta_0 of the center:
the P_rw error is<delta, the C_rw error is delta<delta_0, and the other
proper error is zero. The auxiliary producer therefore supplies actual
independent hazards in(1/4,3/4), exact terminal Nash and a fixed uniform
payoff v for rhat. Since r and rhat agree on P_rw and r_C_rw≤rhat_C_rw,
(9a) transfers the SAME profile, actual payoff v and every uniform cutoff
to the ORIGINAL table r. This proves the theorem.

There is no boundedness assumption on the enlarged lower or arbitrary
coordinate ranges. For any individual original table all rewards are
finite, so the geometric argument could instead use a table-specific
reward bound. The pathwise transfer avoids any additional uniform estimate
on the newly unbounded coordinates and adds no new continuation theory.

## Exact tests and bounded source separation

For these comparisons fix the proper center and choose

    r*(I)=(−100,−101,−102,−103).                            (10)

This is one concrete member of the source region; no claim that every
grand row avoids the compared criteria is needed or made. All comparisons use
literal reward differences, not a translation of the game or of Never.

### Singleton and response-quotient sources

The receiver-row/solo-owner-column comparison matrix is

    Gamma=[ 0  3 −1 −1; 3  0 −1 −1;
           −1 −1  0  3; −1 −1  3  0 ].

It has eigenvalues1,5,−3,−3 and determinant45. Its inverse has
diagonal2/15, favorite entries7/15 and cross entries1/5. Pair determinants
are −9 or −1; every triple determinant is6 and every triple inverse
has a diagonal entry−1/6. Thus Gamma is R0: a nonzero homogeneous
complementarity support of size at least two would have to lie in the
kernel of a nonsingular principal matrix; a singleton support is excluded
by a negative entry in every column. Its nonnegative-inverse R0 degree is
sign(det Gamma)=+1. The full negative-determinant inverse criterion and
every nonnegative-inverse triple criterion fail.

The paired-matrix source also establishes ordinary standard-Q, full normal
core, absence of a homogeneous simplex solution, and failure of projective
Q-bar. Thus those actual singleton screens do not dispatch this completion.
Failure of Q for a harmful principal pair is not treated as failure of Q
for the full matrix or as a standalone parent-game producer.

At all-sure hazards the four actual response displacements are

    r_i(I)−r_i(I−i)=(−97,−98,−99,−100).

Every nondiscrete partition identifies two unequal responses and therefore
fails literal response invariance. This covers all fourteen nondiscrete
partitions. It also covers positive playerwise affine transports: summing
the necessary block-row identities forces equal positive row scales inside
any proposed block, since all original singleton row sums are1; the four
unequal responses stay unequal. The discrete quotient has degree+1.

An instructive boundary test is replacing (10) by a constant grand row.
The proper center then has the half-turn automorphism (0 2)(1 3), and an
existing response quotient DOES solve that symmetric completion. The new
producer is insensitive to this change, while the coverage witness is not.
No symmetry-based exclusion is transferred to all grand rows.

### Every nonnegative-weight quiet child

The capped-clock quiet-child source requires, for an outsider k, all
nonempty child coalitions T and some nonnegative child weights lambda_i,

    r_k(T+k)−r_k(T)
       <= sum_(i in child) lambda_i [r_i(T+i)−r_i(T)].       (11)

Every triple child fails (11) for every weight vector:

| Child | T | outsider join gain | only child outside T's join gain |
|---|---|---|---|
| 013 | 01 | 1 | −13 |
| 123 | 23 | 1 | −13 |
| 012 | 12 | 3/4 | −5 |
| 023 | 03 | 3/4 | −5 |

Members of T have zero join gain, so the right side is nonpositive. Each
of the four pair children01,12,23,03 fails at its whole coalition with
the same positive outsider gain. Child02 fails at T={2}: outsider1 gains2
where child0 gains−3; child13 fails at T={3}: outsider0 gains2 where
child1 gains−3. Each singleton child has an outsider join gain2. Thus the
ENTIRE proper-child selection set fails this nonnegative donor source.

### Every sure-owner induced Nash row and punishment-floor compiler

For sure owner0, let x,y,z be hazards of players1,2,3 in the full induced
three-player game. Their Quit-minus-Continue differences are

    d1=(1−y)(1/2+z/4)−98yz,
    d2=(1−z)(−3+4x)−z(5+94x),
    d3=2−15x−2y−85xy.

At Nash, z>0 implies d3≥0 and x≤2/15. Then d2<0 forces y=0;
d1>0 forces x=1, a contradiction. Thus z=0. If y<1, d1>0 forces
x=1, then d2>0 forces y=1. The full induced Nash set is precisely

    z=0, y=1, x in [3/4,1].

Owner0's actual payoff is−3 and its Continue payoff is2x. Opponents'
joint Continue mass is zero, so NO punishment value can alter its strictly
positive floor excess3+2x.

For sure owner1, let x,y,z be hazards of players0,2,3. The differences are

    d0=(1−z)(1−6y)−97yz,
    d2=(1−z)(2−x)−99xz,
    d3=−3−10x+(15/4)y−(363/4)xy.

At z=0, d2>0 forces y=1, then d0<0 forces x=0 and d3>0 contradicts
z=0. For z>0, d3≥0 implies y≥4/5; d0<0 forces x=0. If z<1,
d2>0 forces y=1 and d3>0 forces z=1. Hence the full Nash set is

    x=0, z=1, y in [4/5,1].

The owner payoff is−3, Continue payoff10y, and joint Continue mass zero,
so every floor excess is3+10y>0.

For owner2 use the owner0 calculation in coordinates (x,y,z)=(q3,q0,q1),
replacing coefficients (98,94,85) by (100,92,83). For owner3 use the
owner1 calculation in coordinates (q2,q0,q1), replacing (97,99,363) by
(99,97,355). Every sign implication above is unchanged, giving the same
respective Nash sets and strictly positive owner floor excesses.

These computations cover all smaller free-player sets too: a Nash point
on a smaller set together with the compiler's fixed-outsider no-join signs
extends by Continue outsiders to a full induced Nash point. None of those
full points satisfies the floor input. The all-Never-tail version separately
requires a nonpositive own singleton, whereas all four here equal1.
In fact no full one-shot zero-tail Nash root has any sure quitter: its other players
would form one of the induced Nash points above, where that sure owner
strictly benefits from Continue. This excludes EVERY pair/triple-base and
free-player selection whose induced Nash, base leave and fixed-outsider
join conditions are accepted by the persistent-large-base semantic adapter:
together those conditions give just such a full one-shot root with sure
quitters. The argument checks the whole existential screen, not just leave
signs at a pure base or at one selected free-player equilibrium. It does
not assert nonexistence of proper stationary roots.

### Named scheduled, guarded and premium sources

All three pair partitions fail the two-pair join-cap raw criterion:
01|23 has r_0(03)=2>s_0; 02|13 has participant comparison−3<0;
03|12 has r_0(01)=5>s_0. This also excludes its weak crossed-matching
specialization. For the signed inverse-column source all column signs must
be positive here; partitions01|23 and03|12 have positive forbidden passive
increments K_0=11/2 and1, while02|13 has negative participant premiums.
The opposite-sign and below-singleton matching raw families have additional
incompatible participant/sign equalities or their joining caps.

At any receiver i the only positive singleton neighbor is its favorite
f(i), with comparison3. For a selected nonfavorite partner, the favorite
outsider axis has negative displacement at all sufficiently small positive
hazards. For favorite partner f(i), a sure harmful outsider (2,3,0,1 for
receivers0,1,2,3 respectively) has displacement−3. Thus EVERY ordered
lower face fails, excluding the inspected lower-ranking, weak-polynomial
and one-sided guarded sources under all relabelings.

The positive singleton graph is two transpositions, not a favorable three-
or four-cycle. Every triple omits some member's favorite and has a negative
inverse entry. Four positive pair traps01,12,23,03 overlap; their greatest
premium core is all four, excluding the at-most-two and triple-core sources
and the mixed-trap source's disjointness consequence. Every player's grand
participant reward is below its singleton, so its protected set P_max is
empty. Product-low fails at the positive pair01.

The implemented ordered-partition `RawRegion` additionally requires its
normalized partner reward in [−1/10,1/10] and its scheduled participant
reward in [19/10,21/10]. Favorite partners have passive reward4, and harmful
partners have pair reward−3 or the failed joining caps above. Its named raw
criterion cannot be selected. A general periodic certificate consumer does
not itself claim to produce certificates from this table.

These are bounded source comparisons, not an exhaustive theorem about all
possible stationary certificates. Earlier local stationary and two-joint
IFT producers concern other centers with unspecified neighborhood radii;
different centers alone do not establish disjointness of those unspecified
neighborhoods. No stationary-equilibrium nonexistence is asserted here.

## Source correspondence and Lean handoff

The game-semantic consumers are already available under their imports:

- `quittingRootSuccessorPayoff`, `quittingRootQuitPayoff`,
  `quittingRootContinuePayoff` and the endpoint-mixture identities in
  `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`;
- `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
  `isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
  in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.

For K=4, the new finite-data producer must establish actual policy recursion,
exact `IsεQuittingRootNash` with error0, and playerwise opponent-cycle
contraction. Equations (2)–(8) supply these inputs and then reuse the existing
consumers; no new all-behavior verification framework is required.

The mathematical implementation tasks are the concrete proper reward center,
the eight-rate actual policy map, its 8×8 derivative/determinant calculation,
and a parametric implicit-function theorem yielding proper hazards and strict
inactive slack on an auxiliary raw56-coordinate ball. The final source then
uses the exact P_rw/C_rw/F_rw support partition and payoff monotonicity (9a)
to remove all lower bounds on C_rw and all bounds on F_rw. The final theorem shape should
quantify delta first, then ANY finite reward table satisfying the32 local
and12 upper-only conditions (1), then produce the rates/cycle and both
semantic conclusions. Neither the sought Nash property nor any produced
strategic object should occur as a raw class hypothesis. The sixteen free
coordinates are absent from their recipient's unilateral comparisons; the
twelve upper-only coordinates are monotone there. No unbounded reward
value is allowed in any single table.

Relevant bounded comparison declarations are:

- `pairedSingletonMatrix_standardQ`, `pairedSingletonMatrix_noHomogeneous`
  and `pairedSingletonMatrix_normalCore_eq_univ` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonLCP.lean`;
- `pairedSingletonMatrix_not_projectiveQBar` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`;
- `exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse` in
  `UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`;
- `r0Degree_eq_sign_det_of_nonnegative_inverse` in
  `MathUE/LinearProgramming/NonnegativeInverseDegree.lean`;
- `exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple` in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`;
- `quittingSingletonBlockRowSum_eq_of_responseInvariant` in
  `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`;
- `CappedClockParentRewardCertificate` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`;
- `QuittingInducedOwnerChamber`, `QuittingInducedOwnerNeverChamber` in
  `UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`;
- `quittingSingletonBaseOwnerFloorExcess_nonpos_iff` and
  `nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`;
- `nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
  `exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`,
  with the equivalent remaining screen
  `quittingPersistentLargeBaseExcess_nonpos_iff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`;
- `RawRegion` in `UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`;
- `QuittingHalfWeakPolynomialGuards` in
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`;
- `QuittingOneSidedWeakUnitGuards` in
  `UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.

The derivative producer and table instance above remain ordinary mathematics.
These named source declarations establish correspondence and delimit the
compared inputs; they do not confer a Lean trust seal on this new construction.
