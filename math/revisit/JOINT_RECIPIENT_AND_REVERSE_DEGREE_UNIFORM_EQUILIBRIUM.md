# Joint restrictions on stationary incentives in four-player quitting games

Use the original four-player game with finite real exit rewards r_i(T),
zero live and Never rewards, and independent private stopping laws on the
positive dates and Never. Put s_i=r_i({i}) and subtract s_i on exits to
obtain the native rewards. At hazards q in [0,1]^4 write P_i for the
expected native reward of waiting at that date, counting an empty exit as
zero, and Q_i for the expected native reward of quitting. Write H_i for
the probability that no opponent quits. Define the stationary residual
B_i=P_i-(1-H_i)Q_i and the immediate joining gain g_i=Q_i-P_i. All
these polynomials are evaluated at the same q.

The following are three necessary conditions on a game with no original
uniform-equilibrium payoff. Failure of any one gives a fixed original
uniform payoff against complete unilateral behavioral replacements.

1. For each nonempty subset M of recipients there is a common q with
   max_(i in M) P_i(q)>0 and g_i(q)<0 for every i in M.
2. For every prescribed vector w with all four entries strictly positive
   there is a continuous semialgebraic path, starting at q=0 and ending
   with some q_i=1, on which q_i B_i=lambda w_i simultaneously for all
   four i. After the start all hazards and lambda are positive, and
   before the endpoint all hazards are below one. Consequently these
   equations must be realizable at every prescribed joint survival
   product_(i)(1-q_i) strictly between zero and one.
3. Fix an owner a and d in (0,1). Whenever B_a>=0 on the entire surface
   H_a=d, the stationary minimum map of the other three players with a
   silent must be free of boundary zeros and have degree one on H_a>d.
   The exact bounded domain and extension are specified below. In
   particular it is impossible in addition to have B_b<=0 with a silent
   throughout H_a>=d for some b distinct from a.

Condition 1 permits the row with a nonnegative joining gain to vary with
the hazards in a sufficient existence test. Condition 3 uses the reverse
inequality from the [one-recipient surface theorem](ONE_RECIPIENT_JOINING_PAYOFF_UNIFORM_EQUILIBRIUM.md).
Its simple two-row test is finite in the rewards. In row a, with
c=1/(1-d), it suffices that Q_a<=cP_a at the seven nonzero corners of
[0,1/c]^3 in opponent hazards. This implies B_a>=0 on H_a=d by
multiaffinity. In row b one may require only that waiting pays at most
native zero and joining pays at least as much, on each of the three
nonempty subsets of the two opponents other than a,b. Then P_b<=0 and
Q_b>=P_b on the deleted face, hence B_b<=H_b P_b<=0. The remaining
two rows and all entries of b on coalitions containing a are arbitrary.

## The index and the original decisions

Under the contrary no-UE hypothesis the hollow singleton matrix Gamma
is R0, its minimum map has local degree one, and each original upper
punishment value mu_i is at most s_i. Further, on the closed cube the
only solution of q>=0, B>=0, q_i B_i=0 for every i is zero. The
[one-recipient theorem](ONE_RECIPIENT_JOINING_PAYOFF_UNIFORM_EQUILIBRIUM.md)
proves these reductions or cites their original signed sources. With
two positive hazards each owner faces geometric opponent absorption and
Always Continue has native value P_i/(1-H_i). The complementary
comparisons make the stationary strategy optimal at every deadline and
at Never. A sole active owner is handled by a finite prefix followed
on survival by its original punishment. These exits give the stated
fixed-target payoff through the [terminal characterization](GLOBAL_LEAST_NEVER_SOURCE_REDUCTION.md).

Write L(x)=Gamma x+B(x^+)-Gamma x^+, defined on the padded cube
[-1,1]^4. At zero the minimum map min(x,L(x)) equals min(x,Gamma x)
up to O(||x||^2). R0 gives a linear lower bound on the norm of the
homogeneous minimum map, and hence local degree one for this field.

## Choosing which recipient to shift

Suppose the witness in condition 1 is absent for a fixed M, so whenever
m(q)=max_M P_i(q)>0 at least one joining gain in M is nonnegative.
For eta>0 form continuous weights on M proportional to

    [eta+g_i(q)-max_(j in M)g_j(q)]_+.

They sum to one; set weights outside M to zero. Consider
min(x,L(x)-lambda w(x^+)). At any root q in the padded cube, q>=0,
B_i>=lambda w_i, with equality whenever q_i>0. Uniformly in eta,
for small positive lambda every root is O(lambda) from zero. Indeed
compactness and the uniform bound on the perturbation first put all
roots near zero, and R0 then gives the claimed estimate. At one i in M,
B_i>=lambda/|M|, hence P_i>=lambda/|M|-O(lambda^2)>0.
Fix a small delta>0 independent of eta. By homotopy from zero and
excision the field at delta has degree one on m(x^+)>0 in (-1,1)^4.
For Lambda>|M| max_i ||B_i||+delta the degree is zero since there
are no roots. There must be a boundary root with delta<=lambda<=Lambda.

On the closure of the selected open set, max_M g_i>=0 by continuity.
Thus all positive-weight rows satisfy g_i>=-eta. If m=0, any such row
satisfies B_i=H_i P_i-(1-H_i)g_i<=eta. The row of weight at least
1/|M| contradicts this for eta<delta/|M|. A unit hazard is therefore
present. Let eta tend to zero and pass to a convergent subsequence of
the roots, weights and parameters. A positive limiting weight requires
B_i>0 and g_i>=0, so that owner cannot face a sure opponent. Consequently
there is a unique sure owner, it carries all the limiting weight, and
Q_i>=P_i prices its withdrawal against mu_i<=s_i. All others face a
sure opponent, have P_j-Q_j>=0 and are indifferent when they act.
This is a genuine original opening followed on survival by the sole
owner's approximate punishment. Its fixed on-path payoff contradicts
no UE.

## A path with prescribed residual ratios

For t>=0 use the continuous field with components

    (x_i+L_i(x)-sqrt((x_i-L_i(x))^2+4t w_i))/2.

At zero parameter this is the minimum map. At a positive parameter
its zeros are exactly q_i>0, B_i(q)>0 with q_i B_i(q)=t w_i for
every i. On the padded cube there are no such zeros for sufficiently
large t=T. The zero set in the closed padded cube times [0,T] is
compact and semialgebraic. The component containing (0,0) must meet
the spatial boundary. To see this, otherwise that component is compactly
contained away from the spatial boundary and separated from the finitely
many other compact components. Its section degree is locally constant
in t. Indeed at any t take disjoint isolating neighborhoods of its
section and the other zeros in that slice, the first inside the cube.
Compactness preserves the isolation for nearby parameters and degree
homotopy and excision apply. An empty section stays empty locally.
This would equate its initial degree one with its final degree zero.
Semialgebraic connected components are path connected and admit a
semialgebraic arc between distinct points. Use such an arc from (0,0)
and stop at its first spatial boundary point. The only zero with t=0
is the starting point. This proves condition 2, with lambda=t along
the arc. No monotonicity of t or individual hazards is required.

## Shifting in the other direction

Set U'={z in (-1,1)^3:H_a(z^+)>d} in the rival coordinates, and
Gamma'=Gamma with row and column a removed. The deleted field is

    f'(z)=min(z,Gamma'z+B_{-a}(0_a,z^+)-Gamma'z^+).

A boundary zero has H_a=d, since it is nonnegative and a sure rival
would give H_a=0. It lifts with q_a=0 to nonzero full complementarity
by B_a>=0, which is already an exit. On (-1,1) times U', in coordinate
order a and its rivals, use min(x,L(x)+lambda e_a). At lambda=0 its
degree is one. At a positive-parameter root, the rivals remain
complementary. A boundary point on H_a=d either has q_a>0 and
B_a=-lambda<0, impossible, or has q_a=0 and again lifts to full
complementarity. The only other possible exit is q_a=1 with H_a>d.
There B_a=-lambda<0 and at least one rival is active. Quit strictly
beats P_a/(1-H_a) in the stationary comparison. Every finite deadline
earns a convex combination of this Never value and the immediate
Quit value. The rivals face a sure opponent and satisfy their true
comparisons. Thus stationarity gives exact original Nash and a
uniform payoff in this case too.

In the absence of all exits the degree is constant. For large lambda
the a component is identically x_a. Homotoping its argument in the
other components to zero cannot move a root off x_a=0, so the product
property gives precisely the degree of f' on U'. It must be one.
If B_b<=0 on the reduced region, subtracting epsilon times the
all-ones vector from the three residuals eliminates every root for
epsilon>0. There are no boundary roots at epsilon=0 under no UE.
This gives reduced degree zero and proves the two-row conclusion.

## Different rows can take turns satisfying the joining comparison

Set all s_i=1, use additive passive rewards, and take

    Gamma=[0,-1,-1,1; -1,0,-1,1; 4,3,0,-1; 1,-2,4,0].

With x=q_3, y=q_2, W=x-y, h=3(x-2y)+(276/31)xy and
C=1-(1-q_0)(1-q_1), prescribe the immediate native joining gains by

    g_0=W+h,    g_1=W-h,    g_2=x-C/2,    g_3=(31/32)C-y.

All are multiaffine in the owner's opponents and zero at empty exit,
so their corner values define the actual rewards. The two passive
offers P_0=W-q_1 and P_1=W-q_0 are at most W. Their gains sum to
2W. Whenever either passive offer is positive, one gain is positive,
so condition 1 settles the game with M={0,1}.

Each individual positive-component test fails even near zero. For row
0 choose x=3y/2 with q_1=0 and small y>0; for row 1 use x>0 alone.
For row 2 use only a positive q_0, and for 3 only a positive q_2.
In each case P_i>0, g_i<0 and B_i>0 for small positive hazards.
The [two-unrestricted-row test](TWO_UNRESTRICTED_RECIPIENTS_UNIFORM_EQUILIBRIUM.md)
has only three possible choices of its first scheduled row and free
pair: 0 with 13, 1 with 02, or 3 with 01. For their second rows,
respectively, take sure scheduled/passive opponents 1/3, 2/0 or 0/3.
The scheduled gap is negative and the passive gap positive in every
case, violating the earlier implication also at nearby proper hazards.
The sole oriented cyclic triple is 123. At its phase 1 the outsider
joining reward is -1, whereas A=-6/5, from lengths (1,1/2,1/2) and
cycle ratio 1/6. Even the full phase fails its negative-start cap.
[Subdivision criterion](CYCLIC_TRIPLE_PHASE_SUBDIVISION_UNIFORM_EQUILIBRIUM.md)

There is no sure-quitter punishment opening. If 0 or 1 is sure then
C=1, and the other two roles' mutual best responses force x=1/2,
y=31/32. There h=0 and W=-15/32, so the other of 0,1 strictly waits.
The sure player would need native continuation cap at most
W/[(1-x)(1-y)]=-30. Immediate Quit guarantees at least -9 since
|h|<=6 by its four corners, |W|<=1, and Q_i=2W-q_j plus or minus h
for the two marked owners. If 2 is sure then 3 waits; at x=0,y=1 the
gain of 1 is 5, so 1 must be sure, already excluded. If 3 is sure
then 2 strictly joins, likewise impossible. The singleton determinant
is 23, with strict positive inverse columns 2 and 3. The conclusion
comes from actual finite game data.

## The reverse test can succeed when all joint tests fail

Use s_i=1 and the singleton matrix

    Gamma=[0,-1,2,-3; 2,0,-1,1; -1,2,0,-3; -3/2,-1/2,7/2,0].

The passive rewards are additive except that rows 1 and 3 receive -1
on coalition 02. For nonempty rival sets T define the native joining
gaps by the following rules:

    g_0(T)=-3 if 2 belongs to T, otherwise 2.
    g_1(T)=1/4 if 3 belongs to T, otherwise -1, except g_1({2})=1/10.
    g_3(T)=-3 if 1 belongs to T, otherwise 1.
    Q_2=2P_2-3(1-H_2)+8q_0 q_3.

The last polynomial defines row 2 at the seven nonempty rival corners.
At H_2=1/2 both q_0,q_3<=1/2, so 4q_0 q_3<=q_0+q_3 and
q_0 q_3<=(1-H_2)/3. This gives Q_2-2P_2<=-(1-H_2)/3 and B_2>0.
With 2 silent, row 0 sees only negative singleton suppliers and its
gaps on all nonempty rival sets are 2. These rows give the reverse
existence test with a=2,b=0. On the common ray q=(t,t,t,0) as t
decreases to zero, P_i/t tend to (1,1,1,3/2) and g_i/t to
(-1,-9/10,-5,-1). Thus every nonempty M fails the joint positive-payoff
test, even along the same small-hazard ray.

This example also excludes every sure-quitter punishment opening. If
0 is sure, the induced gains of 1 and 3 are 5q_3/4-1 and 1-4q_1.
Their mutual best responses force q_3=4/5 and q_1=1/4. Row 2 then has
gain -4+2q_1+5q_3=1/2>0, so 2 is sure, giving 0 a negative gain.
If 1 is sure then 3 waits and 2 has gain -1-q_0<0. Then 0 strictly
joins, leaving 1 with gain -1. If 2 is sure then 0 waits and 1 has
positive gain against both {2} and {2,3}. Hence 1 is sure, 3 waits,
and 2 has negative gain against sure 1. If 3 is sure then 1 strictly
joins and 3 strictly prefers to withdraw.

A sole stationary mover j is blocked by owner 3,0,1,0 for j=0,1,2,3
respectively: its passive singleton is negative and joining improves
on that return, including at proper hazards. On a pair ij of proper
stationary movers one would need q_j Z_i({i,j})=Gamma_ij in both
directions. On 01,02,03,12 one required hazard is respectively
-1,-2,3,10/9. On 13 only q_1=1/7,q_3=4/5 can work and quiet 0 has
negative P_0 and positive joining gain. On 23 only q_2=7/9,q_3=1/3
can work and quiet 1 has P_1=-4/9 and gain 73/540>0. Thus a nonzero
stationary equilibrium needs at least three proper movers here.

The two-unrestricted-row test permits only first scheduled/free choices
0/{1,3}, 1/{2,3}, 3/{0,2}. For the second row respectively put 1
sure on its scheduled date and 0,3 sure on its passive date; put 2
sure then 1 sure; or put 0 sure then 3 sure. In these limits its
(A,B) equals (1,-1), (3,-2), (1,-1/4), so each choice fails also at
proper hazards. On cyclic triple 012 the phase-0 outsider reward is
-1/2 above A=-1 with eta=1; on 123 the phase-2 outsider joining
reward is -1 above A=-35/11, even at the largest allowed eta.
The native vector at coalition 02 is (-1,-1,-5,-1), excluding all
normalized nonnegative weights requiring nonnegative proper-coalition
sums. The existence conclusions use the stationary and punishment
endpoints under their stated source hypotheses.

For a formal handoff the new arguments are the joint selection, the
semialgebraic continuation of the smoothed minimum map, and the
deleted-coordinate product degree. The original-game declarations for
the local index, punishment and terminal characterization are named in
the [one-recipient proof](ONE_RECIPIENT_JOINING_PAYOFF_UNIFORM_EQUILIBRIUM.md).
These results are ordinary mathematics.
