# A uniform equilibrium from one recipient's joining payoffs

Four owners independently decide whether to quit at each live date. The
first nonempty quitting coalition T pays r(T); live play and joint Never
pay zero. Set s_i=r_i({i}), Z_i(T)=r_i(T)-s_i at nonempty T, and
Gamma_ij=Z_i({j}) with zero diagonal. Rewards are finite and may have
either sign. For opponent hazards y in the closed three-dimensional cube,
write H_i for the probability all three continue, P_i for the expected
native payoff when i waits, counting zero at empty exit, and Q_i for the
expected native payoff when i quits. Thus P_i averages Z_i(T) and Q_i
averages Z_i(T+i) over the independent opponent coalition T. The empty
contribution is zero in both averages.

**One-row theorem.** It suffices that some recipient a satisfies

    P_a(y)>0  implies  Q_a(y)>=P_a(y)                                  (1)

for all independent opponent hazards. Then the original game has one
uniform-equilibrium payoff, fixed before accuracy, against every complete
unilateral behavioral strategy. All 45 entries of the other three
recipients are arbitrary.

A finite sufficient test uses one real c>=1 and the seven inequalities

    Z_a(T+a)>=c Z_a(T)    for each nonempty opponent subset T.         (2)

Averaging gives (1). Both (1) and (2) concern only the raw row. The
inequalities in (2) can all be strict, allowing open sets in the sixty
original entries. In particular it suffices for one row's joining
rewards to equal any factor c>=1 times its passive rewards, however
nonadditive those passive rewards may be.

There is a sharper necessary condition for a counterexample. For each
owner write B=P-(1-H)Q and take the relatively open set

    D={y in [0,1]^3 : P(y)>0 and B(y)>0}.

At every recipient of a counterexample, some connected component of D
whose closure contains the origin must contain a point with Q<P. Thus
in (1) one may restrict the test to these components of D. This is a
finite semialgebraic test in three variables. Neither the theorem nor
the component test assumes a strategy or a continuation payoff.

## The original-game consequences of a stationary root

Suppose the original game has no uniform-equilibrium payoff. Its
singleton matrix is R0, meaning that h(x)=min(x,Gamma x) has only its
zero root. This minimum map has local Brouwer degree one there. Also
the original upper punishment value mu_i of each owner is at most s_i.
The value is the infimum over opponent policies of the supremum of the
owner's original terminal payoff. These are same-table necessities for
signed rewards. See the [singleton reduction](FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md)
and [punishment-normal reduction, section 10](NATIVE_COLLISION_FLOOR_AND_GLOBAL_MASS_DICHOTOMY.md).

Use B_i=P_i-(1-H_i)Q_i for every row at a common hazard vector q.
Any nonzero q in the closed unit cube with B_i>=0 and q_i B_i=0 for
every i contradicts the assumed absence of a uniform payoff. If at
least two owners have positive hazards, each player faces geometric
opponent absorption. Always continuing has native value
V_i=P_i/(1-H_i), with V_i=P_i+H_i V_i. The inequalities give V_i>=Q_i,
with equality whenever the owner stops with positive probability. Each
finite stopping date therefore earns at most V_i, as does Never, and the
prescribed law earns exactly V_i. Before absorption there is only one
live history at each date. These comparisons price every behavioral
replacement. Original payoffs add s_i under every such law. Geometric
opponent absorption gives uniform convergence of the finite averages.

If just g has positive hazard, the other players' comparisons still
hold. After N prescribed dates followed by survival, use an original
punishment for g within epsilon of mu_g. A deviating g can earn only
s_g before this change and at most s_g+epsilon after it. Against any
other deviator and under the prescription, the probability of the
change is at most (1-q_g)^N, so its effect on original payoffs tends to
zero. This gives arbitrarily accurate original terminal Nash profiles.
The [terminal characterization](GLOBAL_LEAST_NEVER_SOURCE_REDUCTION.md)
gives a fixed original uniform payoff. This also covers a sole sure
owner and negative own payoffs.

## A shifted comparison on the positive-payoff region

Assume Q_a>=P_a on the union W of the components of D accumulating
at zero. The polynomials B satisfy B(q)=Gamma q+O(||q||^2) at zero.
For lambda>=0 extend to Euclidean space by the continuous field

    F_lambda(x)=min(x, Gamma x+B(x^+)-Gamma x^+-lambda e_a).

Here x^+ is the coordinatewise positive part. A zero in the closed
padded cube [-1,1]^4 has q=x>=0, B_i(q)>=lambda 1_(i=a), and equality
at every positive q_i. At lambda=0 the preceding argument makes zero
the only root in this cube. Homogeneity and R0 give ||h(x)||>=b||x||
for a constant b>0. Therefore F_0 has local degree one by the quadratic
error and a straight homotopy. For all sufficiently small positive
lambda, every root in the padded cube tends uniformly to zero by
compactness, and its norm is O(lambda) by the same bound on h. There
are no such boundary roots for small lambda. The degree on the open
padded cube stays one.

At each such root P_a>=lambda-O(lambda^2)>0, since B_a>=lambda and
(1-H_a)Q_a=O(||q||^2). Also B_a>0. A semialgebraic subset of a compact
cube has finitely many connected components. Thus all these roots have
their opponent vector in W for sufficiently small positive lambda.
Components are relatively open in D by local path connectivity, and
their union W is relatively closed in D. Fix a small delta>0 as above.
By excision F_delta has degree one on the bounded open set

    U={x in (-1,1)^4 : (x^+)_{-a} in W}.

Here the opponent cube carries its relative topology. Choose Lambda
greater than delta and the maximum of B_a on the unit cube. No root
exists in the closure of U at Lambda. The degree homotopy from delta
to Lambda gives a boundary root q at some lambda>=delta. Its opponent
vector is in the closure of W and hence Q_a>=P_a there. Also P_a>=0
and B_a>=delta>0. If P_a=0 then Q_a>=0 and B_a<=0, impossible. The
opponent vector is therefore in D and hence in W. The boundary must
come from a unit coordinate. A sure opponent of a would give H_a=0
and B_a=P_a-Q_a<=0. Consequently a is the sole sure owner.

At this opening every other owner faces a sure opponent. Its inequality
B_i=P_i-Q_i>=0, with equality at positive q_i, prices both actions used.
Owner a's original Quit payoff is s_a+Q_a. If it waits, follow survival
by an original punishment within epsilon of mu_a; the return from this
deviation is at most

    s_a+P_a+H_a(mu_a+epsilon-s_a) <= s_a+Q_a+epsilon.

Only a's deviation can reach the punishment. This gives a fixed on-path
original payoff and terminal Nash at every accuracy. The terminal
characterization gives the contradiction. This proof produces the
opening or the equilibrium by degree and the original no-UE necessities.
It makes no choice of a continuous branch of roots.

For formalization the existing endpoints include
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
[FinFourSingletonDegreeCriterion.lean](../../UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean)
and `quittingInstantPunishmentεEquilibriumExistence_of_hasPunishmentVectorNashRootWithSureQuitter`
in [InstantPunishmentSureQuitterCharacterization.lean](../../UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterCharacterization.lean).
For the simpler theorem (1), one may take W=D and omit connected
components altogether. The shifted-degree argument and the one-row
source are ordinary mathematics here.

## How a counterexample must violate the seven-coalition test

Write p_T=Z_i(T) and j_T=Z_i(T+i) in a single row. If there is no
T with p_T=0>j_T, test (2) passes exactly when

    max({1} union {j_T/p_T : p_T<0})
       <= min({+infinity} union {j_T/p_T : p_T>0}).

Thus every recipient of every counterexample has a failure witnessed
by at most two coalitions. Test (1) can still settle a game that has
such failures in all four rows.

A stronger test also takes just seven comparisons for any fixed c>=1.
For each nonempty subset S of the three opponents require

    sum_(empty != T subseteq S) (c-1)^(|S|-|T|) [j_T-c p_T] >= 0,       (3)

with the zeroth power equal to one. These are polynomial inequalities
in one scalar c, of degree at most three. At c=1 they reduce to (2).
For c>1, the expressions are the values of c^|S|(Q-cP) at the
nonzero corners of the box [0,1/c]^3. Multiaffinity therefore gives
Q>=cP throughout that box. Put d=1-1/c. Every point with H>=d is
in the box. On H=d one has B<=0, so a connected component of D whose
closure contains zero cannot reach H<=d. On such a component P>0
and Q>=cP>P. This proves the claim by the component theorem.
Pointwise test (2) implies (3) term by term. For a counterexample,
each of the four rows must fail (3) for every c>=1; this can be
decided by real univariate polynomial sign determination.

One can also test the curved boundary directly. Fix d in (0,1) and
c=1/(1-d). It suffices to have B<=0 everywhere on H=d. In fact the
multiaffine polynomial E=Q-cP is then nonnegative on H=d and vanishes
at zero. At any y with H>d and a positive coordinate y_j, keep the
other coordinates fixed. The point lies between the point with y_j=0
and the point with H=d. Affine interpolation and induction on the
number of positive coordinates give E>=0 throughout H>=d. The same
component argument applies. In particular, for every row of a
counterexample and every d in (0,1), some independent opponent hazards
have H=d and B>0. The surface is two-dimensional: in opponent survival
coordinates h take h_3=d/(h_1 h_2), with d<=h_1,h_2<=1 and h_1 h_2>=d.

## An exact separation of the raw comparisons

Use s=(1,1,1,1) and

    Gamma=[0,-1,2,-3; 2,0,-1,1; -1,2,0,-3; -3/2,-1/2,7/2,0].

All passive native rewards are additive singleton sums. Let J_i(T)
denote the native gain from joining the nonempty rival coalition T,
so the participant reward is Z_i(T)+J_i(T). For row 0, with hazards
(x,y,z) of (2,1,3) and D0=1-H_0, prescribe the joining-gap polynomial

    P_0=2x-y-3z,     Q_0-P_0=P_0+z(2x-y)+D0/4.

It is multiaffine and vanishes at zero, so its vertex values specify
the seven raw joining gaps. Set J_1(T)=2 when 2 belongs to T and -2
otherwise; set J_2(T)=-199/100 when 1 belongs to T and 99/100 otherwise.
For row 3 use participant rewards equal to two thirds of the passive
sum except that Z_3({0,3})=-1/2.

Row 0 passes (1) since its gap equals (1+z)P_0+3z^2+D0/4. Yet its
positive passive entry at {2} requires c<=17/8 in (2), and its
negative passive entry at {1,3} requires c>=35/16. The other three
rows each have a positive passive singleton with a negative joining gap
(respectively 3,1,2). Thus none of the four rows passes (2).

The [two-unrestricted-row test](TWO_UNRESTRICTED_RECIPIENTS_UNIFORM_EQUILIBRIUM.md)
also fails at every assignment. Its first scheduled row needs two
nonnegative singleton joining gaps toward the free owners. Only rows 2
and 3 qualify, with free pair {0,3} and {0,1} respectively. If row 2
is first, test the other scheduled row 1 with 0 sure at its scheduled
date and 2 sure at its passive date. If row 3 is first, use row 2 with
1 sure at its scheduled date and 3 sure at its passive date. In each
case the scheduled gap is strictly negative and the passive gap strictly
positive. Thus the earlier implication has A>0 and B<0 at these limits,
and also at proper hazards close enough. Unspecified hazards are zero.
The [cyclic subdivision test](CYCLIC_TRIPLE_PHASE_SUBDIVISION_UNIFORM_EQUILIBRIUM.md)
has just two oriented cyclic triples here. On 012 the phase-0 outsider
cap is -1/2 against A=-1 with eta=1. On 123 the lengths starting at
1 are proportional to (1,1/7,1/7), with next cycle scaled by 3/14.
The phase-2 outsider start A=-35/11 is negative but its predecessor's
joining reward is 1. Both tests fail.

One can also exclude every original punishment opening with a sure
quitter. Write q_i for the opening hazards. If 0 is sure, every other
player's opponents include 0. Rows 1 and 2 have gains 4q_2-2 and
(99-298q_1)/100. Their mutual best responses force
q_2=1/2, q_1=99/298. Row 3 then has strictly positive joining gain
-(1/4-q_1/2)/3+(1-q_1)/4, so 3 is sure. But row 0's joining gain
is -3/4-2q_1<0, precluding its sure action. If 1 is sure, 2 strictly
waits. Row 0's gain at x=0,y=1 is -3/4-4z<0, so 0 waits. Then 3
strictly joins, leaving 1 with a negative joining gain. If 2 is sure,
1 strictly joins, leaving 2 with a negative joining gain.

Finally, if 3 is sure, rows 1 and 2 again force q_2=1/2,q_1=99/298.
Row 0 strictly waits. Row 3's passive and forced native offers are
P_3=944/596 and Q_3=2P_3/3, with H_3=199/596. Pricing its withdrawal
would require a native continuation cap at most -944/597. Immediate
Quit guarantees native payoff at least -4/3 against every continuation.
Thus this opening also fails. The comparison excludes a full
punishment-value criterion and allows arbitrary signed differences
between the immediate offers. It does not exclude stationary
equilibrium with proper hazards. The theorem gives a uniform payoff
and leaves unrestricted Fin4 open.

The three tests also have distinct strength on this same matrix. Keep
the other three rows and replace the marked row by
Q_0=2P_0+D0/4-Lxyz. At L=1 the corner tests (3) hold at c=2:
on [0,1/2]^3 one has xyz<=max(x,y,z)/4<=D0/4.
But the singleton {2} requires c<=17/8 in (2) and the grand rival
coalition requires c>=19/8. At L=4 all seven-corner choices fail
while the component test still passes. For H_0>=1/2, put
m=(x+y+z)/3. The arithmetic-geometric mean inequality gives
H_0<=(1-m)^3 and m<=1-2^(-1/3)<1/4. Hence xyz<=m^3<=D0/16,
as D0>=m. Thus Q_0>=2P_0 on the entire H_0>=1/2 side, and B_0<=0
on H_0=1/2. This proves the component test as in the preceding
section. For (3), {2} still forces c<=17/8. The all-three corner
has c^3(Q_0-cP_0) equal to

    2(c-2)c^2 + (3c^2-3c+1)/4 - 4
      <= (289+523)/256 - 4 < 0

for every 1<=c<=17/8. The unchanged rows fail (3) at the same
positive singletons as before. The parameter examples distinguish
three raw tests without a choice of strategies in any of them.
