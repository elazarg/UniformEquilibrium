# Closed actual geometry and bounded recovery of positive crossings

Owner: CODEX_COORDINATOR. Ordinary mathematics, not Lean checked.
This is the canonical internal record for actual continuation geometry and
bounded Nash-word recovery. The
[selected mixed-core theorem](../exports/PASSIVE_BOUND_TRIPLE_SELECTION_UNIFORM_EQUILIBRIUM.md)
contains the closed-passive selected-root consumer. The arguments below retain
its useful extensions without duplicating that proof or claiming another
independent reward-class exclusion for the recovery example.

For the numerical core, write a=-K. The selected theorem covers all real a
when p=0, and a<=0 or a>=1/2 when p>=0. The current target is the opposed-pair
strip 0<a<1/2,p>0, where pair12 has positive ambient index. A positive crossing
by itself supplies neither a counterexample nor an executable return.

## 1. Closed actual domains replace arbitrary virtual boxes

Players are I={0,1,2,3}. Native own and live/Never rewards are zero. Define
Gamma_ij=Z_i({j}) for ALL i,j in I; its diagonal is zero. Each owner
independently chooses its first Quit time among natural dates and Never;
one deviator can replace the complete law. Retain prescribed terminal payoff U, full response cap B, pure
Never response payoff e, and ORIGINAL marginal Never masses N. For a root q,
let h=product(1-q_i), H_i=product_(j!=i)(1-q_j), Q_i its forced-Quit offer,
P_i its nonempty-opponent passive payoff, and E_i=q_i Q_i+(1-q_i)P_i. Then

    U'=E+hU, B'_i=max(Q_i,P_i+H_iB_i),
    e'_i=P_i+H_ie_i, N'_i=(1-q_i)N_i.                    (1)

Every actual profile satisfies B>=e and d_i=B_i-U_i>=N_i(B_i-e_i).
Virtual seeds(U,B,e,N)=(z,z,z,1) satisfy the same inequalities, preserved by
EVERY prefix. The exact nonnegative residual decomposition is

 d'_i-N'_i(B'_i-e'_i)=q_i(B'_i-Q_i)
 +(1-q_i)(1-N_i)(B'_i-P_i-H_iB_i)
 +(1-q_i)H_i[d_i-N_i(B_i-e_i)].                         (2)

Thus zero debt at positive survival forces U=B=e. This assertion does not
bound arbitrary positive-debt intermediate U by passive rewards.

Let K be a compact set of(U,e) pairs containing all actual annotations and
preserved by every prefix map(1). Call a Nash root good if it has a sure
quitter or a nonpositive output coordinate. If every v with(v,v) in K and
min v<=0 has a good root, then the absorbing native debt infimum A_Z is0.
For nonnegative original own offsets this gives a fixed UE payoff through
the complete terminal consumer in the linked theorem.

Here is the exact closed-domain change to that proof. At a local stall
v>=0 with zero set S, a signed separator w Gamma_SS>>0 needs a nearby
marked seed with positive separator value. Choose j in S and set

    z=(1-t)v+t Gamma[:,j], t>0 small.                   (3)

Then z_j=0, w z_S=t w Gamma_SS[:,j]>0, and positive outsiders stay positive.
A solo-j prefix sends the pair(v,v) EXACTLY to(z,z), so the seed lies in K
without any interior or neighborhood assumption. Initialize its cap virtually
as B=z; this is not claimed to be the actual cap of the solo prefix.
Every budgeted zero-debt minimum has U=e by(2) and hence remains on K's
diagonal. Compact closure preserves K. Smaller zero sets use the same seed
construction. The remainder of the selected good-root induction, including
length-independent cap nonexpansiveness and the ORIGINAL Never-product
minimum, is unchanged. Strictly negative seeds are unnecessary; z_j=0 suffices.

One choice is a full-reward payoff box times the CLOSED passive box
[L_i,R_i], where L_i,R_i are the minimum/maximum of0 and all Z_i(A) with
i notin A. Another is the convex hull of deterministic calendar(U,e) vectors,
a correlated outer relaxation. The next section supplies the exact independent
annotation domain instead of that relaxation.

## 2. Exact independent annotations have a 32-date representation

For Fin4 let K_ind be the image of all actual independent profiles under(U,e),
WITHOUT B. Every such vector is realized on at most32 finite dates plus Never.

Fix opponents' laws and vary owner i's law. The eight coordinates(U,e) are
affine in it, but e_i is constant because forcing i Never removes its law.
Only seven coordinates vary. Their conditional vectors at each finite deadline
or Never are bounded. A countable average belongs to their convex hull, not
merely its closure: if the average is on a supporting face of the closed
convex hull, every positive-weight vector lies on that face, reducing affine
dimension; otherwise the relative interiors of the convex hull and its closure
coincide. Induction on dimension proves the assertion. Caratheodory therefore
replaces owner i's law by at most8 old support points, preserving ALL(U,e).

Apply this successively to all four owners. Every replacement preserves the
same eight annotations, including those depending on earlier owners. The
union of the four supports contains at most32 finite dates. Relabel them in
increasing order into{1,...,32}, retaining ties and Never. All prescribed and
counterfactual first-coalition outcomes, hence(U,e), stay unchanged.

Conversely every product law on{1,...,32,Never} is actual. Its probability
space is a product of four33-point simplexes, and its(U,e) map is polynomial.
Its compact image therefore equals K_ind. Prefixing gives another actual
profile, compressible again, so K_ind satisfies Section1 exactly; caps are not preserved.
For an exact warning, set all native rewards0 except Z1(01)=1. AllNever has
U=e=B=0. Having0 quit surely at date1 while all others Never also gives U=e=0,
but B1=1 by joining that date. Equal(U,e) does not determine Nash status.

## 3. Finite actual-data crossing tests

A counterexample with nonnegative own levels must admit v with(v,v) in K_ind,
min v<0, and NO good Nash root. Otherwise Section1 proves A_Z=0. This is a
finite real-algebraic existential/universal condition once K_ind is represented
by Section2; it is stronger than assuming one selected bad root exists.

A simpler necessary test asks for ONE proper fully positive crossing at such
an actual diagonal v. Empty and singleton active supports cannot cross, so
there are11 supports S of sizes2,3,4. Set q_j=0 off S,0<q_i<1 on S, and impose

    Q_i=P_i+H_i v_i>0                  for i in S,
    P_j+H_j v_j>=Q_j, P_j+H_j v_j>0    for j outside S,
    v_i=U_i=e_i for every i, min_i v_i<=0.              (4)

Use probabilities p_i,t>=0 summing to1 over{1,...,32,Never}, and define
S_i(t)=sum_(finite s>t or s=Never)p_i,s for FINITE t. Both sums below run
only over t=1,...,32, excluding Never:

 U_i=sum_t sum_(A nonempty) Z_i(A)
                   product_(j in A)p_j,t product_(k notin A)S_k(t),
 e_i=sum_t sum_(A nonempty,i notin A) Z_i(A)
                   product_(j in A)p_j,t product_(k notin A,k!=i)S_k(t).

Expanding the four choices of a nonpositive v_i gives at most44 systems in
at most140 variables, of degree at most4. Infeasibility proves A_Z=0;
feasibility is not a no-UE conclusion. No expanded generated payload is needed.
The cheaper passive-box relaxation eliminates v: active owners require
Q_i>0 and L_iH_i<=Q_i-P_i<=R_iH_i; quiet owners require
P_j+R_jH_j>0 and P_j+R_jH_j>=Q_j. An anchor requires Q_i-P_i<=0 for an active
owner, or P_j>0 and Q_j<=P_j for a quiet owner. Boundary inequalities are weak
where the passive interval is closed. This relaxation has only four hazards.

## 4. A bounded Nash-word consumer

Keep the closed domain K of Section1. Suppose a fixed finite L has this
property: every diagonal v in K with min v<=0 has a NONEMPTY word of1,...,L
Nash prefixes, each Nash at its current continuation, whose final payoff has
a nonpositive coordinate OR whose joint survival is0. Words are written in
prefix order; physical dates have the reverse order. Then A_Z=0.

The word correspondence is the finite DISJOINT UNION of lengths1,...,L.
Each fixed-length Nash graph and its good endpoint condition are closed.
An empty word is excluded; padding by zero roots is not assumed Nash.
At the least original-Never source, every nontrivial good word would lower
the same minimum or give zero absorbing debt. Thus all good words there
are all-zero. Compactness then makes every nearby good word uniformly small,
even if unrelated large bad roots remain. Zero words are Nash only at
nonnegative inputs. Positive outsiders strictly Continue throughout such
small words because L is fixed.

In the local separator fiber, replace one selected root by one selected good
word. Choose the root bound delta and c0 so
(1-4delta)^L(1-c0)>1-eta. Every intermediate root is supported on the same
zero set, preserves zero debt, and preserves the ORIGINAL separator inequality.
A nontrivial small good word returns to the marked fiber with less survival.
At a stall, the weighted inequality gives a proper smaller zero set. Apply
induction there, using the same L and closed-domain seeds(3). Kernel words,
compact endpoint extraction, and nonexpansive seed removal are unchanged.
This is the complete modification to the linked one-root consumer. The
length bound is essential to this compactness argument.

## 5. A raw02-to-023 recovery branch

The following produces an exact second prefix from certain positive outputs.
Assume every player0 participant reward is nonpositive and define

 d0=Z0(02)-Gamma02>0, d2=Z2(02)-Gamma20>0,
 A0=Gamma03-Z0(03)>0,
 D0=Z0(023)-Z0(03)-Z0(23)+Gamma03>A0,
 A=Z2(23)-Gamma23>0, D=A-Z2(023)+Z2(03)>A.

Require Z3(23)<Gamma32. Choose U>0 and put
X=A/D, B=max(U/(U+d0),A0/D0), both in(0,1). Let J(x,b,z) be the product
expectation of c_empty=0 and c_T=Z1(T)-Z1(T union{1}), for nonempty
T subset{0,2,3}, under hazards(q0,q2,q3)=(x,b,z). Require J>=0 at all eight
corners x in{0,X},b in{0,B},z in{0,1}.

Every positive v with v0<=U and v2<A*d2/(D-A) then has a proper nonzero Nash
root with nonpositive player0 output. Start at z=0 with
x=v2/(d2+v2), b=v0/(d0+v0), making owners0,2 indifferent. Quiet1 prefers
Continue by its comparison J+(1-x)(1-b)v1>=0. If quiet3 also Continues,
this is already the desired root. Otherwise continue the active equations via

 z*=v2/(v2+A),
 x(z)=[v2(1-z)-Az]/[(d2+v2)(1-z)-Dz],
 b(z)=[v0(1-z)+A0z]/[(d0+v0)(1-z)+D0z], 0<=z<=z*.

The first denominator stays positive through z*: its endpoint numerator is
A*d2-(D-A)v2>0. The derivative of x has negative numerator(D-A)v2-A*d2, so
x decreases from a value below X to0. The ratio b lies between
v0/(v0+d0) and A0/D0, hence in(0,B]. Multiaffine interpolation gives
J+(1-x)(1-b)(1-z)v1>=0 along the entire branch.

Player3's Quit-minus-Continue gap is continuous, positive at z=0 in the
remaining case, and at z* equals b[Z3(23)-Gamma32]-(1-b)v3<0.
An interior IVT zero makes owners0,2,3 indifferent, while1 Continues.
All hazards are proper and q0>0, so its supported Quit value is nonpositive.
No recovery branch or strategic root was assumed.

## 6. An interior opposed-pair barrier to every finite recovery word

This exact control lies in the remaining strip 0<a<1/2,p>0. It excludes
Nash-word return on the entire passive box, not on the actual domain K_ind.
The table itself has an absorbing equilibrium.

On coalitions contained in{1,2,3}, use the following complete table:

|A|Z0|Z1|Z2|Z3|
|---|---:|---:|---:|---:|
|1|0|0|-2|-2|
|2|-3|1/2|0|1|
|3|100|-3|-1|0|
|12|-3|1/4|1|-6|
|13|0|-100|-1|10|
|23|-3|9|3|-100|
|123|-3|11|2|1|

For each of the eight coalitions A containing0, put Z0(A)=0. For i in{1,2,3},
put Z_i(A)=-1 if i belongs to A, and otherwise put Z_i(A)=c_i, where
(c_1,c_2,c_3)=(0,1,10). This includes Z(0)=(0,0,1,10), and specifies
all60 coordinates. Thus row0 participant payoffs are nonpositive, row2
passive payoffs are at most1<=10, and the core is exactly the fixed mixed
core with a=1/4,p=1. No hypothesis is weakened from that opposed strip.

The literal closed passive box is

 D=[-3,100] x [-3,9] x [-2,1] x [-6,10].

The input v=(75,-1/36,1/3,9) lies in its STRICT interior and has min v<0.
Its UNIQUE whole-game Nash root is

 q=(0,1/10,1/10,0).

The output is

 u=(1209/20,1/40,1/10,357/50)>>0.

### Complete root uniqueness at v

For i in{1,2,3}, let g_i^core=Quit-Continue in the three-player core at
continuation v_i. If q0<1, the full gap is

 g_i=(1-q0)g_i^core-(1+c_i)q0.

If q0=1, all three core players strictly Continue; then player0 strictly
prefers Continue because v0=75>0. Hence q0<1 at every Nash root.
Write alpha=q0/(1-q0)>=0. Every active core player satisfies
 g_i^core >= (1+c_i)alpha.

If q1=0, then g3^core=-101q2-9(1-q2)<0, so q3=0. Next g2^core=-1/3<0,
so q2=0. Player0 now strictly Continues, so q0=0, after which player1
strictly Quits because -v1=1/36>0. This contradiction proves q1>0.

Player1's core gap is

 g1^core=(1-q3)(1-10q2)/36 +q3(-97+99q2).

It is strictly negative when 1/10<q2<97/99. Thus either q2<=1/10 or
q2>=97/99. The second branch is impossible: player0's Quit value is0,
whereas its Continue value is at most

 100(1-q2)-3q2 <= -91/99<0.

Nash would force q0=1, already excluded. Hence q2<=1/10. The player1
gap is now at most1/36, so alpha<=1/36 and q0<=1/37.

Suppose q0>0. Since q0<1, player0 is indifferent. Its exact Continue value is

 C0=(1-q1)(1-q2)(75+25q3)-3q2=0.

Therefore 1-q1<=3q2/[75(1-q2)]<=1/225, or q1>=224/225.
Player2's core gap is

 g2^core=3q1+4(1-q1)q3-(1-q1)(1-q3)/3
          >=3q1-(1-q1)/3>=403/135.

The full gap has the sign of g2^core-2alpha, which is strictly positive
because 2alpha<=1/18. This forces q2=1, contradicting q2<=1/10. Thus q0=0.

Since q2<1, its Continue action must be optimal, so g2^core<=0. The last
lower bound now gives q1<=1/10. For these q1, the gap of player3 is strictly
negative: its affine-in-q2 endpoint values are

 g3^core at q2=0: 12q1-9(1-q1)<=-69/10,
 g3^core at q2=1: -101(1-q1)+7q1<=-451/5.

Hence q3=0. If q2=0, player1 strictly Quits, contradicting q1<=1/10.
Therefore 0<q2<1, so g2^core=0 forces q1=1/10. Then 0<q1<1 and g1^core=0
force q2=1/10. All possible pure, mixed, and sure-owner roots were included.

Direct substitution confirms Nash: active1,2 are indifferent; quiet0 has
Continue1209/20>Quit0, and quiet3 has Continue357/50>Quit-809/100. The
active outputs are1/40 and1/10, giving the displayed vector u.

### Unique AllContinue at every positive input with u0<=100

The following stronger statement proves the claimed second-stage trap.
Let u>>0 with u0<=100. If q0=1, every core player strictly Continues, which
makes player0 strictly Continue as well; impossible. Thus q0<1.
If q1=0, then g3^core=-101q2-u3(1-q2)<0 and then g2^core=-u2<0.
So any nonzero core support requires q1>0. Its gap is now

 g1^core=(1-q3)[-q2/4-u1(1-q2)]+q3(-97+99q2).

The bracket is strictly negative. Thus q1>0 forces q2>=97/99, because
its full gap cannot be nonnegative otherwise. As before, player0's Continue
value is at most100(1-q2)-3q2<0, so q0=1, contradiction. Therefore every
core hazard is0. Player0 then strictly Continues because u0>0. AllContinue
is the only Nash root, and it preserves u. Repeating it never changes the
positive output or joint survival, proving the all-finite-word obstruction.

### Why this is not an actual positive-gap source

For EVERY coalition A, the raw vectors satisfy

 Z2(A)+Z0(A)/25<=3.

This follows directly from the table: equality holds at A=3; coalitions
containing0 have Z2<=1; all other listed rows satisfy the inequality.
Never also satisfies it. Thus every actual prescribed payoff U, and every
limit of such payoffs, obeys U2+U0/25<=3. But

 v2+v0/25=1/3+3=10/3>3.

So v is outside the actual payoff convex hull even though it is strictly
inside the passive box. It cannot occur on an actual zero-debt diagonal
U=B=e at positive Never product. This exposes the precise missing input:
one must restrict further to actual joint semantic data or use a mechanism
beyond exact Nash-prefix returns. Merely enlarging the allowed word length
on the entire passive box cannot handle this core strip.

The table itself has the exact absorbing native profile where player0 quits
immediately and all others Never. Owner0 is indifferent between native0 and
Never0; each other owner prefers its passive c_i>=0 to joining payoff-1.
For nonnegative original own offsets this also gives original UE. Therefore
neither the root trap nor the all-word failure is being misreported as a
game without UE or as a newly eliminated counterexample class.

The next obligation is to use the actual diagonal constraints of Section 3
to eliminate bad-only inputs in the opposed-pair strip, or to construct a
return on that smaller domain. The preceding barrier rules out obtaining
this by increasing the word-length bound on the full passive box alone.
