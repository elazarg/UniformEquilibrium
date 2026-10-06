# Opposite-sign matching phases: a raw uniform-equilibrium producer

## 1. Game, finite hypotheses, and conclusion

This is ordinary mathematics for the original four-player quitting game.
It is not a Lean verification or a result for every four-player table.

Let I={0,1,2,3}. At each live date the players independently choose Continue
or Quit using private randomization and public past actions. A nonempty
quitting coalition S absorbs at an arbitrary finite signed vector r(S).
The live reward is zero, including the date selecting the absorbing
coalition; subsequent dates pay r(S). Infinite all-Continue pays zero.
Deviations are arbitrary complete behavioral replacements, and all payoff
and equilibrium conclusions are in expectation. There is no public
correlation, payoff translation, or restriction to bounded stopping times.

Write f=(01)(23), a=(02)(13), o=f∘a=(03)(12), A={0,2}, B={1,3}.
For each i choose a signed real s_i and a positive real b_i. Choose common
real parameters

    H>2,       Π_A<−1,       Π_B>−1,       k>0.

Put h=H−1>1, β=−Π_A>1, γ=β−1>0, c_B=Π_B+1>0. The actual singleton
coordinates must satisfy

    r_i({i})=s_i,
    r_i({f(i)})=s_i+H b_i,
    r_i({a(i)})=r_i({o(i)})=s_i−b_i.                    (1)

The two scheduled-pair rows must satisfy

    r_i(A)=s_i+Π_A b_i   for i∈A,
    r_i(B)=s_i−k b_i     for i∈A,
    r_i(B)=s_i+Π_B b_i   for i∈B,
    r_i(A)=s_i+K_B b_i   for i∈B,                       (2)

where K_B is a real raw coefficient constrained below. Thus participant
and passive coordinates of both actual joint rows are retained.

Choose from this raw data

    y_L>max(h/k,β/(h+2k)),

for example y_L=1+max(h/k,β/(h+2k)). Define

    D_L=(1+y_L)²,       C_L=h y_L−k y_L²<0,
    x_L=[β−γD_L−C_L+√((γD_L−β+C_L)²−4γD_L C_L)]/(2γD_L).

Require the finite raw threshold

    K_B>[c_B y_L(1+x_L)²−h x_L−Π_B y_L/(1+y_L)]/x_L².  (3)

Define m=y_L(k y_L−h)/[γ(1+y_L)²]>0, and choose a raw finite bound

    Y>max(y_L,[K_B+h/m+max(Π_B,0)/m²]/c_B).

One plus this maximum is always a possible choice. Put

    δ=(1/2)min(k,[(2k+h)y_L−β]/[Y(Y+2)]),
    C_A=k−δ,       L_i=s_i−C_A b_i for i∈A,
                    L_i=s_i       for i∈B.            (4)

Then δ>0 and 0<C_A<k. The eight remaining raw bounds are

    r_i({i,f(i)})+r_i({i,o(i)})≤2L_i,
    r_i({i,f(i),o(i)})≤L_i                         for all i.  (5)

The two individual cross-pair coordinates need not be bounded by L_i.
All other nonsingleton coordinates, including every grand-coalition
coordinate and all nonscheduled passive coordinates, are arbitrary signed
finite rewards. These assumptions specify a whole completion family.
Neither quitting rate, strategic root, continuation value, nor equilibrium
certificate is among the hypotheses.

**Theorem.** Every reward table satisfying (1)–(5) has an exact proper
period-two terminal Nash profile and one fixed original-game uniform-
equilibrium target. In each row both scheduled players independently use
the same internally produced proper hazard, while the other two Continue.
The same profile witnesses every accuracy and every sufficiently large
finite horizon. Own-singleton levels may have any signs, and Π_B may be
negative in (−1,0).

## 2. Producing a global positive branch

For y≥y_L let D(y)=(1+y)² and C(y)=hy−ky²<0. Consider

    −γxD(y)+βx/(1+x)=C(y).                             (6)

After multiplication by1+x it is the quadratic

    γD(y)x²+[γD(y)−β+C(y)]x+C(y)=0.

The leading coefficient is positive and the constant negative. The
discriminant is strictly positive and the roots have opposite signs.
Hence exactly one root is positive. Define x(y) by the displayed formula
for x_L with y replacing y_L. It is continuous on the entire half-line.
No implicit-function neighborhood, oracle root, or continuity of a root
selection in all reward data is assumed.

Equation (6) gives

    γD(y)x=βx/(1+x)+ky²−hy>ky²−hy.

The function y(ky−h)/[γ(1+y)²] has derivative
[(2k+h)y−h]/[γ(1+y)³]>0 on this half-line. Thus x(y)>m>0 uniformly.
The separate inequality β<(2k+h)y gives

    βx/(1+x)−hy<β−hy<2ky,
    γD(y)x<ky²+2ky<kD(y),

and therefore x(y)<k/γ. Both branch bounds are global on[y_L,∞).

## 3. A scalar crossing produces the second rate

Define the continuous raw residual

    R_B(y)=c_B y(1+x(y))²−h x(y)−K_Bx(y)²−Π_B y/(1+y).

The threshold (3) is exactly R_B(y_L)<0. Using x(y)>m and Π_B of
either sign,

    R_B(y)/x(y)²
      ≥c_B y−K_B−h/m−max(Π_B,0)/m².

The chosen Y consequently gives R_B(Y)>0. The intermediate value theorem
produces some y∈(y_L,Y) with R_B(y)=0. Fix this y once, set x=x(y)>0,
and define

    q_A=x/(1+x),       q_B=y/(1+y).

Both hazards lie strictly between0 and1. The produced equations are

    −γx(1+y)²=hy−ky²−βx/(1+x),
    c_B y(1+x)²=h x+K_Bx²+Π_B y/(1+y).                 (7)

No uniqueness of the scalar crossing is asserted or needed. Every selected
root in the specified interval satisfies all subsequent bounds.

## 4. The collision bound and the weaker average caps

For y∈(y_L,Y), equation (6) gives the exact identity

    γx/[1−(1+y)⁻²]
      =[βx/(1+x)−hy+ky²]/[y(y+2)].

Its positive numerator estimate and positive denominator yield

    γx/[1−(1+y)⁻²]
      ≤k−[(2k+h)y−β]/[y(y+2)]
      ≤k−[(2k+h)y_L−β]/[Y(Y+2)]
      ≤k−2δ<C_A.                                      (8)

The uniform gap follows from the raw interval bounds, not from evaluation
at a supplied strategy. Since δ≤k/2, C_A is positive and strictly below k.

When a player is passive, its two scheduled opponents have the same hazard
q. Their two singleton-exit events have identical probability q(1−q).
Its actual forced-Quit endpoint is therefore exactly

    (1−q)²s_i
      +q(1−q)[r_i({i,f(i)})+r_i({i,o(i)})]
      +q²r_i({i,f(i),o(i)}).

The average caps (5) bound this by

    s_i−C_A b_i[1−(1−q)²]   for i∈A,
    s_i                         for i∈B.               (9)

No individual pair cap is used. These particular reward coordinates do
not enter (7), because only a passive deviator accesses them.

The condition C_A<k is also important for real coverage. At a pure B
exit, an A outsider receives s_i−k b_i, while its permitted triple join
can be strictly larger, up to s_i−C_A b_i. Thus these caps do not already
protect a pure B equilibrium. A crude cap at or below its passive reward
would destroy that distinction.

## 5. All sixteen Bellman and unilateral endpoints

Alternate row A followed by row B. In its active row each player in A
uses q_A, each player in B uses q_B in its own row, and passive players
always Continue. Define rowwise phase values

    i∈A: U_i=s_i−β b_i x/(1+x),   W_i=s_i−γ b_i x;
    i∈B: U_i=s_i+Π_B b_i y/(1+y), W_i=s_i+c_B b_i y.     (10)

U_i is the active-phase value, W_i the passive-phase value. The proposed
vectors are v^A=(U_0,W_1,U_2,W_3) and v^B=(W_0,U_1,W_2,U_3).

At an active phase with mate hazard q, forced Quit has value
s_i+Π b_i q=U_i. Forced Continue has value

    q(s_i−b_i)+(1−q)W_i=U_i.

For A this follows from β=γ+1, and for B from c_B=Π_B+1. The active
policy mixture therefore also equals U_i, regardless of the player's
own mixing probability.

At a passive phase its opponents' singleton rewards sum to2s_i+h b_i.
Their joint row pays s_i+K b_i, with K=−k for A and K=K_B for B.
The actual forced-Continue endpoint is

    q(1−q)(2s_i+h b_i)+q²(s_i+K b_i)+(1−q)²U_i.

After substituting opponent odds and (10), this is exactly W_i by (7).
The simultaneous other-pair reward K is present; it has not been discarded.
Passive forced Quit is bounded by (9). For A, with q=q_B, (8) makes
this bound strictly below W_i. For B, with q=q_A, it is≤s_i<W_i.

The sixteen endpoint results can be displayed in eight player/phase rows:

| Phase and player | Forced Quit | Forced Continue | Policy value |
|---|---|---|---|
| A,0 | U_0 | U_0 | U_0 |
| A,1 | ≤s_1<W_1 | W_1 | W_1 |
| A,2 | U_2 | U_2 | U_2 |
| A,3 | ≤s_3<W_3 | W_3 | W_3 |
| B,0 | ≤s_0−C_A b_0[1−(1+y)⁻²]<W_0 | W_0 | W_0 |
| B,1 | U_1 | U_1 | U_1 |
| B,2 | ≤s_2−C_A b_2[1−(1+y)⁻²]<W_2 | W_2 | W_2 |
| B,3 | U_3 | U_3 | U_3 |

Every possible unilateral simultaneous outcome is included, particularly
the two cross pairs and the triple seen by a passive deviator. Under one
unilateral replacement the grand coalition cannot occur: at each date at
most the scheduled pair and that deviator can Quit. Its rewards are
unrestricted in the actual game, not replaced by zero.

## 6. Actual terminal values and unrestricted behavioral Nash

The prescribed two-row survival probability is

    ρ=(1−q_A)²(1−q_B)²<1.

Iterating the exact policy identities in Section5 for n periods expresses
the proposed initial vector as the expected rewards absorbed in those
periods plus a residual continuation value times ρⁿ. The displayed values
are bounded, so that remainder tends to zero. Absorption occurs almost
surely, and the vectors in (10) are the actual terminal values, including
when they or the own singletons are negative.

For a deviator i∈A, deleted-opponent period survival is
ρ_i=(1−q_A)(1−q_B)²<1; for i∈B it is
ρ_i=(1−q_A)²(1−q_B)<1. These are fixed independently of that player's
replacement. Conditional on any live history, prescribed opponents keep
their independent phase hazards. The deviator may use any history-based
randomization, but its current expected endpoint is a convex combination
of the two upper-bounded pure endpoints in Section5.

Iterating these inequalities through n periods bounds its expected
absorbed payoff plus a proposed continuation remainder by the initial
phase value. Comparing with its actual bounded terminal payoff leaves an
absolute error at most a fixed finite bound times ρ_iⁿ. This tends to
zero uniformly over all replacements. Thus no behavioral deviation beats
the prescribed value. Literal Never, arbitrary late stopping, and
unbounded randomized stopping are included. Opponent absorption is almost
sure even under those replacements. The profile is exact terminal Nash.

This argument uses neither a phasewise singleton floor nor a positive
reward normalization. In particular, A's passive value W_i is strictly
below its own singleton, while B's is strictly above it.

## 7. One fixed uniform target and all large horizons

Let M=max_{i,S≠∅}|r_i(S)| and put

    C_time=max_i[1+2/(1−ρ_i)].

Under every unilateral replacement the expected absorption date-plus-one
is at most C_time: survival through n complete periods is bounded by
ρ_iⁿ, and summing the two-date geometric tail proves the assertion.
This also bounds the prescribed profile's absorption time.

For horizon N, the difference between terminal payoff and finite average
payoff is at most2M C_time/N in each coordinate, uniformly over every
unilateral replacement. The bound includes the initial live-zero date and
the zero date selecting absorption. Comparing the prescribed terminal
Nash payoff with a deviator's terminal payoff gives finite-horizon regret
at most4M C_time/N. The delivery error for the prescribed profile is at
most2M C_time/N.

Fix v^A once, together with the root selected in Section3. For every ε>0,
any integer threshold at least max(1,4M C_time/ε) suffices: every N above
it has ε-Nash regret and delivery error at most ε for this same profile
and this same target. The target is not allowed to change with ε or N.
This establishes uniform equilibrium in the original game.

## 8. Signed, negative-premium and binding-cap stress test

An exact admitted point with negative Π_B is

    H=3, Π_A=−2, Π_B=−1/2, k=110/27, K_B=79/32,
    y_L=1, Y=13, x=2, y=3.

Here m=14/27, δ=22/1053 and C_A=4268/1053. At y_L the positive root
solves108x_L²−2x_L−56=0 and exceeds1/2, because the quadratic is−30
there. Its residual is

    R_B(1)=3/4−x_L−63x_L²/32<−31/128<0.

The upper raw-threshold slack is
13−[K_B+h/m+max(Π_B,0)/m²]/c_B=39/112>0. Thus this point satisfies
the actual finite raw tests, not merely the two root equations. Substitution
at x=2,y=3 gives both identities (7) exactly.

Take s=(−3,2,−1,4), b=(1,2,3,4). Set both cross-pair coordinates and
the capped triple coordinate equal to L_i in each row, and set every
remaining unused coordinate to37. This is a completely specified finite
table with the required singleton and scheduled rows. Its hazards are
q_A=2/3,q_B=3/4, and

    U=(−13/3,5/4,−5,5/2),       W=(−5,5,−7,10).

All eight active endpoint equalities hold exactly. Passive B gaps are3
and6, while passive A gaps are2527/1404 and2527/468. This tests signed
singleton levels, negative active and passive values, equality in all
average caps, negative Π_B, and arbitrary unused rewards simultaneously.

## 9. A complete rational new-coverage table

Take s_i=b_i=1, H=3, Π_A=−11/10, Π_B=1, k=68/25, K_B=10,
y_L=59/34 and Y=6. Then m=272816/43245>6. The lower endpoint test is

    R_B(y_L)/x_L²<2y_L(7/6)²−10=−3229/612<0,

and the upper test is

    R_B(6)/x(6)²>12−10−1/3−1/36=59/36>0.

These prove (3) and the upper raw condition exactly. The value in (4) is
δ=10039/81600. Put ζ=1−k+δ/2=−54133/32640. Its individual cap slack
and its pure-B outsider joining gain are both δ/2=10039/163200>0.

| S | r(S) |
|---|---|
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (ζ,1/2,0,0) |
| 02 | (−1/10,11,−1/10,11) |
| 03 | (ζ,0,0,1/2) |
| 12 | (0,1/2,ζ,0) |
| 13 | (−43/25,2,−43/25,2) |
| 23 | (0,0,ζ,1/2) |
| 012 | (−100,1/2,−100,0) |
| 013 | (ζ,100,0,100) |
| 023 | (−100,0,−100,1/2) |
| 123 | (0,100,ζ,100) |
| 0123 | (1000,−101,1001,−102) |

Every coordinate and every raw bound is explicit. The theorem produces
some6<x<136/5 and59/34<y<6. Approximate values y≈4.471486,x≈15.524067
are an experiment only and are not inputs or evidence for the root proof.

The average-cap theorem strictly enlarges the individual-cap class: change
only r_0(01) to ζ+2 and r_0(03) to ζ−2. Their sum is unchanged and the
triple remains ζ, so every equation, selected rate and endpoint remains
valid. The old individual cap at01 fails. This separate split-coordinate
test proves the theorem's additional raw scope; the source exclusions
below are asserted only for the unchanged complete table displayed above.

## 10. Separation from the other matching architectures

The relevant arbitrary-passive matching predicate requires a unique
nonnegative favorite singleton partner, two nonpositive other comparisons,
and for a harmful scheduled mate a(i)

    r_i({i,a(i)})≥r_i({a(i)}),

with all passive outsider joins bounded by s_i. Passive pair increments
may be arbitrary. In the displayed table singleton signs force f. On the
scheduled matching02/13 an A participant gets−1/10<0, its mate's
singleton payoff; on03/12 it gets ζ<0. Thus every relabeling fails the
weak participant comparison. Allowing arbitrary passive rewards cannot
repair this finite input failure.

The separate general inverse-positive criterion requires a strictly
positive inverse, harmful scheduled mates, nonnegative participant
premiums, nonpositive passive increments, and the same individual caps.
Every perfect matching has an A member with negative participant premium:
its pair payoff is−1/10 or ζ, both below own1. It therefore fails under
every partition. A pure-pair alternative is excluded by Section11.

A signed-column extension instead requires signs σ_j∈{−1,1} with
Γ⁻¹diag(σ) strictly positive, together with σ_iΠ_i≥0 and
σ_i(Π_i−Γ_i,a(i))>0. Our inverse is strictly positive, so every σ_j
must be positive. Each partition still has a negative A participant
premium, contradicting σ_iΠ_i≥0. Thus that finite extension cannot
absorb this table either.

The common below-singleton scalar family requires all normalized pair
premiums Π<−1 and produces both phase values below each own singleton.
Our B premium is+1 on02/13 and−1/2 on03/12. More strongly, no exact
proper two-pair profile with every phase below own levels can use either
harmful matching, even with unequal hazards: on02/13 active B has
U_B=1+q_mate>1; on03/12 active indifference forces
W_B=1+(1/2)q_mate/(1−q_mate)>1.

The third, favorable matching01/23 cannot even be an exact proper
two-phase equilibrium. With arbitrary proper hazards q_i, player1's
active value is U_1=1−q_0/2<1. At its passive23 phase all absorbing
Continue rewards are zero, so W_1=(1−q_2)(1−q_3)U_1. Its exact
forced-Quit deficit relative to Continue has the opposite sign:

    Q_1−W_1=(1−q_2)(1−q_3)(1−U_1)
      +(1/2)q_2(1−q_3)+2(1−q_2)q_3+100q_2q_3>0.

This excludes all three relabelings of the proper below-floor pair-word
architecture. It does not guess a radius for a local persistence theorem
or claim absence of arbitrary periodic or stationary equilibria.

## 11. Pure exits and actual quiet-child raw tests

There is no pure equilibrium. A sole A quitter is joined by its B
o-partner for1/2 rather than0; a sole B quitter is joined by its B mate
for2 rather than0. At full A a participant withdraws from−1/10 to0;
at full B an A outsider joins for gainδ/2. At any cross pair its A
participant withdraws from ζ<0 to0 or4. At a triple containing full A
an A participant withdraws from−100 to0. At a triple containing full B
the omitted A joins for1000 or1001 instead of0. At I a B participant
withdraws from its negative grand reward to0. All Never loses to own1.

Every proper child has a zero-Never exact terminal Nash profile with a
profitable omitted deviation. Singletons use their sure own exit. Child A
uses one sure solo member, B its sure joint exit, and a cross pair its sole
B member. A triple with only one B uses that B's sure solo exit; a triple
with full B uses its full sure triple. In the latter, the A participant
obtains ζ>−43/25 and the B participants100>0. The omitted player's
positive gains in these cases are1/2,2,δ/2, or1000/1001. Thus universal
quiet-lift bounds charging outside debt solely to nonnegative multiples
of child debts and joint Never fail for every proper child. This does not
assert that every separately selected child equilibrium is unsafe.

There is also a direct test of the actual nonnegative raw F/J family.
For a nonempty proper child S it asks for λ_ki≥0 such that, for every
nonempty T⊆S and outsider k,

    s_k−r_k(T)≤∑_{i∈S}λ_ki[s_i−r_i(T)],
    r_k(T∪{k})−r_k(T)
      ≤∑_{i∈S}λ_ki[r_i(T∪{i})−r_i(T)].                (11)

Every one of the fourteen children fails already the second inequality.
For an A-only child use an A singleton and its omitted B o-partner,
whose gain is1/2 while child gains are nonpositive. For a B singleton,
cross pair, or triple with only one B, use that B's singleton and its
omitted B mate: omitted gain2 faces only nonpositive child gains. For
child B use its full coalition and an A outsider's gainδ/2; child gains
are zero. For a triple with full B use its full coalition and the omitted
A's positive grand gain; child gains are again zero. These cases exhaust
the four singletons, six pairs and four triples.

The five-kind universal withdrawal consumer inspected is
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
The exact child counterprofiles above have all child debts and joint Never
zero, so they directly falsify its required universal outside-debt bound.
The raw F/J test is stronger coverage evidence than absence of a supplied
child-strategy certificate alone.

## 12. No proper-three stationary support

The rows of size at most three are invariant under a=(02)(13), not under
an exchange of the two pair types. A support with full B and one A has a
B player whose favorite is omitted. Its Never payoff is zero, while every
forced-Quit outcome is1,2,1/2 or100. It cannot mix properly.

For support012 let the proper hazards for0,1,2 be(a_0,z,a_2). Player2's
Never payoff is zero. Put C_0=1−ζ>0 and
D(z)=11/10+(999/10−C_0)z>0. Its indifference is

    1−C_0z−D(z)a_0=0.

Player0's forced Quit becomes D(z)(a_0−a_2), whereas its Never payoff
is4z(1−a_2)/(z+a_2−za_2)>0. Thus a_2<a_0. Player1's Never payoff is

    a_0[4(1−a_2)+11a_2]/(a_0+a_2−a_0a_2)
      >(4+7a_2)/(2−a_2)≥2.

All its forced-Quit outcomes are1 or1/2, so Quit≤1, a contradiction.
The permutation a handles the other full-A support. All four proper-three
supports are excluded, including relabelings and positive affine reward
transports; full-support and sure-boundary stationary profiles are not.
This excludes the actual output of
`PairedCubicStationaryExample.exists_local_stationary_branch` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`.

## 13. Further bounded finite-source comparisons

The only premium traps are B and I. Here a trap means every member has
some subcoalition containing it with reward strictly above its own
singleton. A members have positive participant premiums only at I;
B members have them at B. The greatest trap is therefore full, excluding
proper pair/triple core criteria. No player has nonnegative participant
premiums everywhere. Sure B violates both product-low and supportwise
premium balance. At sure A every forced-Quit premium is negative:
(−11/10,−1/2,−11/10,−1/2). Hence no nonzero nonnegative weight vector
can give a global nonnegative forced-Quit floor.

For the full trap and its subset B the literal joining charge is

    L_I(B)=∑_{i∈I\B}[r_i(B∪{i})−r_i(B)]=δ>0.

Thus larger-trap and mixed-trap predicates requiring every intermediate
joining charge to be nonpositive fail. This is a finite raw inequality,
not a claim about all possible trap-based strategies.

The singleton matrix Γ_ij=r_i({j})−s_i, with Γ_ii=0, is

    Γ=[[0,3,−1,−1],[3,0,−1,−1],
       [−1,−1,0,3],[−1,−1,3,0]].

Its determinant is45 and its inverse has diagonal2/15, favorite entries
7/15 and other entries1/5. All principal pairs and triples are nonsingular;
singleton positive homogeneous supports are forbidden by their negative
column entries. Thus Γ is R₀ and its nonnegative-inverse degree is+1.
The harmful principal pairs are not Q or homogeneous admissible. Every
triple inverse has negative diagonal entries: two−1/6 at the favorite
pair and−3/2 at its unmatched player. These fail the actual negative-
determinant, degree-not-one and child-nonnegative-inverse exit inputs in
`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`,
`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`, and
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.

All Γ row sums are1. Hence Γᵀλ≤0 with λ≥0 forces λ=0, excluding
`exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`.
At all-sure, the four quitting displacements are1000,−101,1001,−102.
They are distinct. The necessary block-row-sum identity forces equal
positive scales inside any response-invariant block after a positive
affine row transport; all-sure equality then cannot hold. Thus there is
no nondiscrete response quotient, including after these transports. The
exact identity is `quittingSingletonBlockRowSum_eq_of_responseInvariant`
in `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.

The favorable graph consists of two transpositions. Every row has two
harmful comparisons and reciprocal signs agree. These exclude the
favorable-four-cycle, cyclic-child, unique-negative paired, and integral
tournament patterns. The paired necessary property inspected is
`RawRegion.eq_partner_of_singleton_lt` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`. All participant
pair gap ratios have absolute value≥1/2, whereas the visible affine
period-three cylinder has zero participant pair gaps at its center and
radius1/50000000; all such coordinates are visible. The literal center
and visibility data are in
`UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreeReward.lean`
and `UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreeInvisibleCoordinates.lean`.
The ratio is invariant under positive affine row transport. The literal
owner-risky family requires a zero off-diagonal singleton comparison;
Γ has none.

Every crossed lower guard fails. If the selected partner is not the
favorite, let the favorite surely Quit: joining-minus-waiting is ζ−4<0
for an A owner or1/2−4<0 for a B owner. If it is the favorite, an A
owner's scheduled mate surely Quits, giving−1/10; for a B owner both A
outsiders surely Quit, giving1/2−11<0. These witnesses directly violate
`QuittingHalfWeakPolynomialGuards` and `QuittingOneSidedWeakUnitGuards` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`
and `UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.

For every conditional range blocker, ContinueUpper≥4 and QuitWithoutLower≤1.
An A empty-background pair gives QuitWithLower≤max(ζ,−1/10)<0; a B
maximal background gives QuitWithLower bounded by its negative grand
payoff. Their lower mixture is therefore≤1<4, contradicting the strict
lower-face range inequality. The actual predicate is
`IsQuittingConditionalFaceGapRange` in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`.

Influence1→0 is ζ−5<0 at the empty background but k−1=43/25>0 at{3}.
Thus `SignConsistentQuittingInfluence` and `IsAffineQuittingMembershipGain`
fail in `UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`
and `UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`.

These comparisons concern actual raw predicates or intrinsic output
architectures. They are not generic absence claims about supplied-strategy
verifiers. Together with Sections10–12, the displayed table witnesses
strict narrowing of a previously surviving class, while Sections1–7
produce the whole opposite-sign completion family.

## 14. Formalization handoff and limits

The exact existing strategic consumers inspected are
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`. Their policy,
root-Nash and player-deleted-contraction hypotheses are all produced here.
No standard-Q or no-uniform-payoff reduction is needed in this theorem.

A likely implementation separates the finite raw predicate (1)–(5), the
positive quadratic branch, the interval residual crossing, and the
average-cap endpoint estimate. It then constructs the two cyclic root
rows and vectors (10), proves the exact certificate, and invokes those
consumers for the original `quittingGame reward`. The resulting raw
theorem should quantify over every actual Fin4 reward table satisfying
the predicate and conclude existence of an exact proper cyclic terminal
Nash profile and a uniform-equilibrium payoff, without a supplied root
or equilibrium hypothesis. No Lean file or declaration is supplied here.

The theorem does not allow arbitrary singleton comparisons, arbitrary
four separate normalized participant coefficients, arbitrary A passive
coefficients, or unbounded passive joining averages. It does allow
arbitrary signed own levels, row scales, negative Π_B, all unused reward
coordinates, and individual pair rewards above the former caps. It does
not settle the unrestricted finite-quitting conjecture or assert strategy-
class completeness. Its evidence is ordinary raw production, a complete
unrestricted behavioral/horizon proof, and an exact separating table.
