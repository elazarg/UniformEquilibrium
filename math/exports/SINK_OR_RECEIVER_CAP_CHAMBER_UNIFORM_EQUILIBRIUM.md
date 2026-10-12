# Sink-or-receiver escape for a two-ledger cap chamber

This is an ordinary-mathematical finite-reward class theorem. Its raw
adapter is not implemented in Lean. The argument uses the actual semantic
carrier and the full-behavior uniform-payoff consumer. No arbitrary-table
theorem or exact terminal-Nash existence is asserted. Throughout, E is
maximum coordinate debt, not total debt.

## 1. Finite data, graph convention and exact theorem

Let I be any finite player set with at least two elements. For every
nonempty S subset I let r(S) be a finite real reward vector. Live and
Never rewards are0. Randomization is private and independent, and a
deviation replaces one player's ENTIRE behavioral law. Put s_i=r_i({i})
and assume s_i>=0. Fix nonzero weights a_i>=0 and define, for every
nonempty proper S,

    H_a(S)=sum_i a_i[r_i(S)-s_i],
    J_a(S)=sum_(i notin S) a_i[r_i(S union{i})-r_i(S)].

Assume:

1. H_a(S)>=0 for every nonempty proper S, and H_a({j})>0 for some j.
2. J_a(S)<=0 for every nonempty proper S.
3. Every nonempty proper A contains i such that r_i(S)<=s_i for EVERY
   nonempty S subset A containing i.
4. In EVERY nonempty proper induced subset L, the graph

       j -> i  iff  i!=j and r_i({i,j})>r_i({j})

   has a sink OR a vertex receiving an arrow from every other vertex
   of L. A sink has NO outgoing positive arrow within L. A universal
   recipient has ALL the stated incoming arrows, strictly positive;
   no outgoing-arrow assumption is imposed on that vertex.

THEOREM. These raw guards imply a uniform-equilibrium payoff in the
original game against all unrestricted behavioral replacements. There
is ONE target v such that every positive accuracy has a profile and a
horizon threshold, after which all expected average payoffs approximate
v and every complete unilateral replacement earns at most v_i plus the
accuracy. There is no supplied profile, continuation, root selection,
carrier, convergence rate, chronology or public correlation.

FIN4 COROLLARY. For four players guard4 is equivalent to: NO proper
triple induces EXACTLY a directed triangle, with its three reverse
arrows absent. Thus two-cycles and triangles with ANY additional
positive reverse chord are allowed. The acyclicity guard is strictly
stronger, as the exact witness in Section 5 shows. This is not a claim allowing
all graphs, nor a necessary condition for existence of UE.

The strict singleton clause is automatic if the singleton comparison
matrix Gamma, Gamma_ii=0 and Gamma_ij=r_i({j})-s_i, is standard-Q.
The complementary problem at offset-minus-ones supplies x>=0 with
Gamma*x>=ones. Thus a*Gamma*x>0, so a*Gamma*e_j>0 for some j, which is
H_a({j})>0. This does NOT infer any of the other guards from standard-Q.

To check the graph equivalence, sets of size1 have sinks. A two-vertex
set either has a sink or is a two-cycle, whose vertices both receive
the other arrow. On three vertices, if there is no sink and no universal
recipient, every outdegree is at least1 and every indegree at most1.
There are therefore exactly three arrows and every degree equals1;
without loops this is exactly a directed triangle. Conversely that
triangle has neither a sink nor a universal recipient. Zero and negative
insertion differences simply mean an absent arrow.

## 2. Full finite-game escape, including inactive players

LEMMA. In the finite Boolean root game, let all-Continue payoff B satisfy
B>=s and let L={i:B_i=s_i} be nonempty. If the induced graph on L has
a sink or a universal recipient, the game has a nonzero FULL mixed Nash
root. No sign restriction on other finite rewards is needed.

For a sink i, let only i quit with probability p>0. It is indifferent,
since its two endpoints are s_i=B_i. For every other player j,

    Continue_j-Quit_j
      =(1-p)(B_j-s_j)+p[r_j({i})-r_j({i,j})].       (G1)

This is nonnegative on L by the sink property. It is nonnegative outside
L for all sufficiently small p>0 because B_j>s_j; finitely many strict
inequalities are retained simultaneously. Hence this is a FULL root,
not merely an owner-subgame root.

For a universal recipient i, suppose for contradiction that all Continue
is the ONLY Nash root. Perturb the finite game by adding epsilon>0 to
player i's payoff whenever IT chooses Quit, without changing any other
payoff or the all-Continue vector. Choose any Nash root q^epsilon of the
perturbed finite game. Finite mixed Nash existence applies to every
epsilon. Compactness of the product cube and the closed Nash graph imply
q^epsilon->0: every convergent subsequence as epsilon->0 has an original
Nash limit, which by assumption is0.

Every j outside L strictly prefers Continue at q=0, since s_j-B_j<0.
Continuity therefore forces q_j^epsilon=0 for all sufficiently small
epsilon. Delete those coordinates. The ORIGINAL forced-Quit minus
forced-Continue difference of player i has the finite multiaffine
expansion

    g_i(q)=sum_(j in L minus{i}) h_ij q_j+O(t^2),
    h_ij=r_i({i,j})-r_i({j})>0,
    t=sum_(j in L minus{i}) q_j.                       (G2)

The constant term is0 because B_i=s_i, and own q_i never enters its
endpoint difference. The remainder bound is uniform in a neighborhood
of0; it follows directly by expanding finitely many opponent-coalition
probabilities. If L has another vertex, put h=min h_ij>0 and bound the
remainder by Kt^2. Then g_i(q)>=h t-Kt^2>=0 for sufficiently small t.
If L={i}, g_i(q)=0 exactly. In BOTH cases the perturbed difference is
g_i(q^epsilon)+epsilon>0, so Nash optimality forces q_i^epsilon=1.
This contradicts q^epsilon->0. A nonzero ORIGINAL full root exists.

No limit of the perturbed roots is declared nonzero. The contradiction
shows that the original finite correspondence already contains a distant
nonzero root; continuity of a root selector is neither proved nor used.
The perturbation is a proof inside the finite root game, not a payment
or correlated device added to the original quitting game.

A sharp finite-game guardrail is the following three-player Boolean game,
not a UE counterexample. All Continue and own singletons pay0. At sole j,
recipient j+1 gets-2 and recipient j-1 gets0, modulo3. Every participant
in a pair or the grand coalition gets-1; a pair's passive recipient gets0.
For each i the root difference is exactly

    g_i=q_(i-1)-q_(i+1)-q_(i-1)q_(i+1).

The graph is a bare directed triangle and ALL participants are flat.
Nevertheless all Continue is its unique Nash root: one active label gives
its inactive successor a positive gap; two active labels give one of them
a strictly negative gap; with all three active the sum of the three gaps
is minus the positive sum of pair products, whereas supported Nash would
make every gap nonnegative. Thus flatness alone cannot replace guard4.
This finite-game example does not assert failure of the other chamber
guards, nonexistence of quitting-game UE, or completeness of this graph
criterion.

## 3. Actual full-cap carrier, seed and root ledgers

For an actual independent private-clock profile let U_i be its terminal
payoff and B_i the supremum over ALL complete replacements. Affinity in
the replacement law makes this the supremum over every finite pure
deadline and literal Never. Let d_i=B_i-U_i>=0, E=max_i d_i, and

    L_a(B)=sum_i a_i(B_i-s_i).

The closure S_actual of all actual pairs(U,B) is compact in the finite
reward box and retains B>=U. It need not be convex, and a closure point
is NOT silently declared an actual profile.

For a fixed independent product root q, put

    c=product_i(1-q_i), alpha_i=product_(j!=i)(1-q_j),
    Q_i=E[r_i(A union{i})],
    b_i=E[r_i(A) 1_(A nonempty)],

where A is its opponent quitter set. Full prefix semantics is exactly

    U_i'=q_i Q_i+(1-q_i)(b_i+alpha_i U_i),
    B_i'=max{Q_i,b_i+alpha_i B_i}.                     (G3)

This continuous map preserves S_actual: it is actual prefixing on actual
profiles, followed by closure for a FIXED selected q. At a FULL cap-Nash
root, namely a Nash root of the finite game with continuation B,

    B'=cB+sum_(S nonempty) p_q(S)r(S),
    d_i'=c d_i,                         E'=cE.         (G4)

The zero-hazard players' Nash inequalities are essential to this exact
identity. If any q_i=1 then c=0 and (G4) gives a diagonal of S_actual,
which already supplies the conclusion.

The seed is produced from raw data. Choose j with H_a({j})>0, prescribe
sure Quit0 to j and Never to everyone else. Then

    U_i=r_i({j}), B_j=s_j,
    B_i=max{r_i({j}),r_i({i,j})} for i!=j.

For the owner every finite deadline pays s_j and Never0; for another
player Quit0 and any strictly positive deadline/Never give the two listed
rewards. Thus these are ACTUAL unrestricted caps. By B>=U and a>=0,
L_a(B)>=H_a({j})>0, while min(B-s)<=0. If E=0 the seed solves the game.
Otherwise define lambda=L_a(B)/E>0 and the nonempty compact chamber

    C={(U,B) in S_actual: min_i(B_i-s_i)<=0,
                               L_a(B)>=lambda E}.     (G5)

There is no global B>=0 assertion. At a positive-E chamber point a root
with all q_i in(0,1) would give, by active indifference and z_i=q_i/(1-q_i),

    B_i-s_i=sum_(empty!=A subset I minus{i}) z_A
                       [r_i(A union{i})-r_i(A)],
    L_a(B)=sum_(empty!=S proper subset I) z_S J_a(S)<=0. (G6)

But L_a(B)>=lambda E>0. Every full cap-Nash root at such a point therefore
has proper support, unless a sure probability already gives the diagonal.
For nonempty proper support A, guard3 gives i in A whose forced-Quit
endpoint Q_i<=s_i. Supported Nash optimality makes B_i'=Q_i, preserving
the low face. Every nonempty root coalition is proper, so guards1 and
(G4) give

    L_a(B')=c L_a(B)+sum_(S nonempty) p_q(S)H_a(S)
              >=c L_a(B)>=lambda cE=lambda E'.         (G7)

Consequently EVERY full cap-Nash root preserves C at a positive-debt
point or immediately gives a diagonal. All Continue fixes the pair.
No correlation, target preservation or cross-accuracy chronology is used.

## 4. Compact minimum and fixed-target unrestricted conclusion

Suppose the attained minimum E* on C is positive, at(U*,B*). If some
B_i*<s_i, all Continue is not Nash; finite Nash existence gives a nonzero
full root. By(G4),(G7) it stays in C with smaller E, or gives a diagonal.
Both are contradictions.

Otherwise B*>=s. Its tied set L={i:B_i*=s_i} is nonempty by the low-face
condition and proper because L_a(B*)>=lambda E*>0. Guard4 and Section 2 supply
a nonzero FULL original root. Once again(G4),(G7) contradict minimality:
c<1, and either E'=cE*<E* inside C or c=0 closes the game immediately.
Thus min_C E=0. At the minimizing carrier point B=U=v. Actual profiles
approximate this diagonal with terminal regret tending to0 and payoff
tending to the SAME v. The full-behavior diagonal consumer yields the
stated uniform conclusion with target selected before accuracy.

This is global CONSTRAINED minimization on an actually generated semantic
carrier, not minimization over a chosen root spine. No chronological
temporalization is required. The new principle is only finite-game escape
from the low tied face; the two different raw higher-coalition ledgers and
proper-support low-face preservation remain genuine hypotheses.

## 5. Exact four-player witness outside proper acyclicity

Let I=Z/4 and a_i=1. On a singleton{j}, owner j gets1, opposite j+2 gets4,
and both other recipients get0. On adjacent pair{j,j+1}, donor j gets-1,
successor j+1 gets2, and both outsiders get3/2. On an opposite pair both
members get0 and both outsiders get2. On a triple all members get-1 and
the omitted player gets10. The grand row is(9,9,9,9). Make exactly TWO
exceptions:

    r_0({0,1})=1/2,            r_2({0,1,2})=2.          (G8)

Never0. Every unmentioned coordinate is fixed by the preceding rules.
The exact ledgers are

    H(singleton)=1;
    H(01)=3/2, H(other pairs)=0;
    H(012)=6, H(other triples)=3;
    J(1)=-3/2, J(other singletons)=-3;
    J(01)=-2, J(other adjacent pairs)=-5;
    J(opposite pairs)=-6, J(triples)=-1.

Every proper A has a flat participant. In an adjacent pair take its
donor, including donor0 at reward1/2<1 in pair01; in an opposite pair take
either member. For triples012,013,023,123 use respectively0,3,2,1.
Each such player has EVERY participant reward in that triple at most1,
including its subpairs. Singletons are flat by equality. The graph is
the Hamiltonian cycle0->1->2->3->0 PLUS1->0. No induced triple is a bare
directed triangle. The two-cycle0<->1 violates proper acyclicity.
Thus this table is admitted by Section 1 and not by proper acyclicity.

The actual sole-owner0 seed has

    U=(1,0,4,0), B=(1,2,4,0), E=2, L=3, lambda=3/2.

## 6. ENTIRE sure-owner and punishment-tail selections

For each sure owner, the following exhausts the FULL induced game of ALL
other players, including mixed and boundary choices. Continuation values
do not enter those players' endpoints because their sure opponent already
quits. Write each listed rate vector in increasing player order.

* Owner0: player3's joining-minus-Continue values against the four pure
  choices of players1,2 are(-1,-5/2,-3,-1), hence3 strictly Continues.
  The remaining two response gaps are

      g1=2-5q2,                g2=-4+(9/2)q1.

  Their unique Nash point is(q1,q2,q3)=(8/9,2/5,0); the opposite slopes
  exclude all four pure corners and force this interior intersection.
  The owner's forced-Quit payoff Q0=-1/45, absorbed Continue contribution
  b0=32/45 and empty-opponent mass alpha0=1/15. Hence even continuation
  B0=-1 gives Continue29/45>Q0. In particular every NONNEGATIVE
  punishment continuation fails the owner floor condition.
* Owner1: opposite3 has four strict negative gaps(-4,-5/2,-5/2,-1).
  Once3 Continues, g2=2-(3/2)q0>0, forcing2 sure; then
  g0=1/2-3q2<0. Unique induced(q0,q2,q3)=(0,1,0).
* Owner2: opposite0 has the same strict negative table. Once0 Continues,
  predecessor1 strictly Continues and successor3 surely Quits.
  Unique induced(q0,q1,q3)=(0,0,1).
* Owner3: opposite1 has the same strict negative table. Once1 Continues,
  predecessor2 strictly Continues and successor0 surely Quits.
  Unique induced(q0,q1,q2)=(1,0,0).

For owners1,2,3 the owner Quit value is-1, Continue contribution0 and
empty-opponent mass0. No continuation can repair these owner inequalities.
All passive rewards are nonnegative, so Never guarantees each player's
punishment lower value at least0. This excludes the ENTIRE singleton-base
induced-Nash punishment-floor compiler, not only one selected child.
It also excludes every full zero-tail Nash root with a sure label, hence
all persistent-base/free selections whose full leave/join tests furnish
such a root. A multi-owner punishment base has another sure opponent
for each deviator, so the tail is irrelevant and is excluded as well.

The quantifier is NOT arbitrary signed continuation: owner0 could be
supported with a sufficiently negative continuation. In particular no
blanket 'no sure Nash at every finite continuation' is being asserted.

## 7. Every universal quiet-child certificate fails

For every nonempty proper child C other than01 and013, choose j in C
with j+1 outside C and, if j=1, with0 outside C. Such a choice exists
by inspection of the four-cycle; the two exceptions are precisely where
the reverse insertion1->0 prevents the old singleton witness.
Sole-j-Quit0 with every other child player Never is exact unrestricted
child Nash. Its predecessor can join for-1 versus0, its opposite for0
versus4, and its favorable successor is absent; the new reverse edge
is excluded by the choice. All child debts and joint-Never mass are0.
Missing successor j+1 can Quit0 for2 instead of its prescribed0.

For C=01 or013, prescribe sure simultaneous Quit0 to players0 and1, and Never
to player3 if it is in C. The two owners receive1/2 and2 and can withdraw only
for0; child3 receives3/2 and could join only for-1. Thus this is exact
full child Nash with joint-Never mass0. Omitted2 can Quit0 for
r2(012)=2 instead of r2(01)=3/2, gain1/2.

Therefore EVERY child has an actual zero-debt, zero-Never profile whose
quiet full-game lift has a positive outsider debt. No finite-slack
universal inequality

    outsider debt <= nonnegative weighted child debts + rho*jointNever

can hold for that child, for ANY weights or finite rho. This excludes
all raw kinds whose checked conclusion is such a universal inequality,
including withdrawal/future/join and capped-clock certificates. It does
NOT exclude a new source permitted to choose ONLY another favorable
child equilibrium rather than certify every child profile.

## 8. No stationary exact Nash, over the entire support set

The sure-owner calculation excludes every stationary root with any sure
label: stationary continuation is an actual payoff in[-1,10], while
Section 6 excludes all B0>=-1 and excludes the other owners without a bound.
All-Never fails since each own singleton is1. For any remaining stationary
exact Nash, all passive rewards are nonnegative, so its literal Never
response gives B_i=U_i>=0.

Full support is impossible. Every terminal coalition has nonnegative
unit-weight H, including grand H=32. Singleton terminal probabilities
are strictly positive, hence sum B-4>0. But full-support root identity(G6)
and all negative J give sum B-4<0. One-player support fails because its
successor prefers joining for2 to passive0. On opposite two-player
support, an active player's Never earns4 while its Quit endpoint is<=1.
On adjacent two-player support, the successor's Never is0 while its
Quit endpoint is1 plus its opponent hazard, strictly positive.

For support012 write q=(a,b,c,0), a,b,c in(0,1). The active endpoint
identities and U0>=0 imply

    Q0=1-b/2-c-bc/2, b0=c(4-(5/2)b),
    0<=Q0-b0=1-b/2-5c+2bc.

Thus c<=(1-b/2)/(5-2b)<=1/5. Player1 has
Q1=1+a-2c-ac>=3/5, whereas its Never payoff is
2ac/(a+c-ac)<=2c<=2/5. Exact stationary indifference of an active player
makes its value equal its Never payoff, contradiction.

For supports123 and230, rotate their three labels to(a,b,c). Neither
exception(G8) occurs in an active player's payoff. The first player's
identity is

    Q=1-2b-c+bc, b_abs=c(4-(5/2)b),
    0<=Q-b_abs=1-2b-5c+(7/2)bc.

It forces b<1/2 and c<=(1-2b)/(5-(7/2)b)<=1/5. The middle player again
has Quit>=3/5 and Never<=2/5. Finally for support301, let
(a,b,c)=(q3,q0,q1). The first player's identical inequality still gives
c<=1/5. Middle0 now has

    Q0=1+a-c/2-(5/2)ac>=9/10,
    Never0=2ac/(a+c-ac)<=2/5,

again impossible. Every support has been exhausted. Thus all sound raw
producers concluding an EXACT stationary product Nash fail on this table,
including all their parameter and support choices. This statement does
not exclude small stationary regret or nonstationary approximate families.

## 9. Bounded singleton, quotient, weight and template coverage

These are comparisons for the exact Section 5 table, not for every member of
the Section 1 class and not a claim of exhaustive novelty. The singleton matrix remains

    Gamma=[0,-1,3,-1; -1,0,-1,3; 3,-1,0,-1; -1,3,-1,0],
    det Gamma=45,
    Gamma^-1=(1/15)[2,3,7,3;3,2,3,7;7,3,2,3;3,7,3,2].

Every principal block of size>=2 is invertible; a singleton homogeneous
complementary root fails an external negative neighbor entry. Thus Gamma
is R0. At offset ones its entire strictly complementary root set is empty
support, four adjacent supports with coordinates(1,1), and four triples
with rotated coordinates(1/2,5/2,1/2). Their actual determinant indices
sum1-4+4=1; the matrix is standard-Q and has degree1. The degree-not-one
exit therefore fails. Every deleted triple has determinant6 and a negative
inverse diagonal, defeating ALL raw passive-row inverse child choices.
The positive singleton graph is an opposite matching, not a positive
three- or four-cycle, so the named singleton cyclic sources do not apply.
No new assertion about actual positive-gap membership is inferred.

For ACTUAL response quotients use F_i(q)=(1-alpha_i)Q_i-b_i, not H_a.
The necessary singleton block-row sum test on all15 partitions leaves
discrete, all-block,02|13,01|23,03|12,02|1|3,0|13|2. Each nondiscrete
partition fails actual response equality at the following exact hazard:

| blocks | q | unequal residuals |
| --- | --- | --- |
| all-block | (1/2,1/2,1/2,1/2) | F0=-171/128, F1=-3/2 |
| 02\|13 | (0,1/2,0,1/2) | F0=-1/32, F2=-5/16 |
| 01\|23 | (0,0,1/2,1/2) | F0=-1, F1=-25/16 |
| 03\|12 | (0,1/2,1/2,0) | F0=-41/32, F3=-1 |
| 02\|1\|3 | (0,0,0,1/2) | F0=3/4, F2=0 |
| 0\|13\|2 | (0,0,1/2,0) | F1=0, F3=3/4 |

Only the discrete quotient survives, with determinant45 and degree1.
In particular the nonnegative-inverse quotient exit's NEGATIVE determinant
guard fails, despite Gamma^-1 being strictly positive.

All proper supports have flat participants, while all incoming adjacent
participants receive2>1; hence the only premium trap is the full set.
For a global nonnegative weighted inserted-premium floor, summing its
four singleton tests gives

    -2 sum_i w_i+(3/2)w0 <=-(1/2)sum_i w_i<0

for every nonzero w>=0. Thus no weight selection passes. The global
weighted upper-average alternative fails at the grand row, giving
8sum_i w_i>0. For ANY boxed-charge coefficients on the only full trap,
singleton0 forces delta<=2 and gap<=3, while any penultimate coalition
forces tau>=8 and loss<=1. Consequently its threshold is at most13/2,
below required4+4M with every actual reward bound M>=10. This excludes
the ENTIRE boxed coefficient selection, not one selected tuple.

Only pair01 has both participant rewards positive; every other adjacent
pair has donor reward-1 and each opposite pair has both members0. Thus
every perfect matching contains a pair failing strict positive-member
templates and the two-pair join-cap source. Each triple has an opposite
pair with join gap0-4<0, excluding the all-six-strict-joins triple template.
Singleton favorites are forced to be opposite mates by Gamma. The literal
four-joint local box requires both favorite participants near5 and9/2
within radius<=1/2; here both get0. The rectangle and passive-reward-ray
classes likewise require positive favorite pair members, absent here.
The below-singleton scheduled-pair class requires a cross matching whose
two participants BOTH have strictly negative rewards; every cross pair
has a recipient with reward2, so ALL such matchings fail.

For the positive proper four-singleton calendar with opposite favorites,
write chronological Continue rates u0,u1,u2,u3 in(0,1). The owner equations
at the displayed singleton rows are

    E_l=u_l[4-4u_(l+1)+u_(l+1)u_(l+2)]-1=0,

Here E_l is the equation for the owner immediately preceding phase l,
with chronological indices modulo4. Writing(x,y,z,w)=(u0,u1,u2,u3),
subtracting opposite equations gives

    w(4-y)(x-z)+4(1-z)(y-w)=0,
    -4(1-y)(x-z)+z(4-x)(y-w)=0.

The determinant
wz(4-y)(4-x)+16(1-z)(1-y)>0, so x=z and y=w.
The remaining equation difference gives(y-x)(4+xy)=0. The common
polynomial is(u-1)(u^2-3u+1)=0, with unique interior solution
u=(3-sqrt(5))/2. At an owner's root the next and preceding nonmate
prescribed values are u and1, respectively. Their Quit endpoint is
u+(1-u)r_i({i,owner}), so the two nonmate participant caps are0 and1.
An incoming adjacent participant reward2 violates the cap in either
chronological orientation. Thus the ENTIRE named positive proper owner
solution set is excluded; longer words and boundary hazards are not
addressed. The one-joint
diffuse-solo-exit class needs a positive directed three-cycle among its
nonpivot singleton differences, absent for every deletion here.

Two further raw chamber classes fail their literal guards. The class
fixing these singleton rows, adjacent participant rewards(-1,2), opposite
participant rewards0, and ALL pair outsider rewards1 does not contain
this witness, whose pair outsiders are3/2 and2. The class imposing proper
insertion acyclicity fails at0<->1. Under recipient-affine transports
preserving the displayed singleton rows, the own-minus-low gaps force
unit positive scaling and the low singleton entries force zero translation,
so these literal discrepancies cannot be removed by such a transport.
The additional whole-selection checks in Sections 6--9 prevent relying
merely on that syntactic comparison. Unknown larger qualitative IFT
neighborhoods are NOT declared disjoint just because their centers differ.
No claim is made to have classified every possible producer architecture.

## 10. Source correspondence and Lean handoff

The proof uses the following checked semantic declarations:
`quittingTerminalSemanticCarrier`,
`exists_terminalProfile_sequence_tendsto_semanticPair`,
`quittingTerminalSemanticCarrier_isCompact`,
`continuous_quittingTerminalSemanticPrefix`, and
`quittingTerminalSemanticPrefix_mem_carrier` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
`exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`;
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` and
`quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`;
`isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier` in
`UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.
The strict all-Continue-basin no-go in
`UniformEquilibrium/Quitting/Root/StrictAllContinueBasinLinearAbsorptionDefect.lean`
is not applicable at a nonempty tied set; no claim here contradicts it.

The bounded source comparisons use the following exact definitions:
`quittingWeightedInsertedPremium`, `HasGlobalQuittingWeightedFloor`,
`quittingWeightedLeaveSum` and `HasWeightedQuittingTrapLeavers` in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`;
`QuittingTrapChargeCoefficients` and its exact cardinality-four threshold
in `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`
and `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeOdds.lean`,
plus `HasBoxedQuittingNashCharges` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`;
`QuittingResponseInvariantOnUnitCube` and
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
The quotient exit is
`finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`.
The deleted inverse predicate is consumed by
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.

Sure-base comparisons use
`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean` and
`singletonBase_inducedNash_floorExcess_semantics` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBaseStationarySemanticHandoff.lean`.
Universal child comparisons use the actual concluded inequalities
`quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`
and `quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_slack`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockChildDeletionAdapter.lean`.
Absorbing child approximants still require an individual original-table
outsider comparison. Such a comparison is not inferred from common-deadline
weighted H/J accounts; separately maximizing outsider deadlines remains
a real issue.

A narrow Lean handoff would replace only the minimum-specific sink
argument by Section 2, implement the finite graph equivalence for Fin4, and
reuse the SAME seed, root ledgers, compact chamber and diagonal consumer.
What this removes is the exclusion of all proper insertion cycles: a
two-cycle or a chorded triangle need not strand the chamber minimum at
all Continue, even if the only escaping Nash roots are distant. What
remains toward arbitrary Fin4 is not chronology but raw preservation:
standard-Q supplies the strict singleton seed, yet does NOT supply the
proper-coalition H/J signs or the flat participant on every proper
support. Bare directed triangles also remain outside this particular
escape lemma. No unconditional production of such preserved regions for
arbitrary Fin4 data is proved.
