# Uniform equilibrium for additive four-player quitting games without a mutually positive pair

Let the four players use independent behavioral stopping laws on the positive
integer dates and Never. The live payoff and the payoff if everyone plays
Never are zero. Let ell be an arbitrary real four-vector, let Gamma be a
real hollow four-by-four matrix and let u>0. At any nonempty first quitting
coalition S the reward to i is ell_i plus

    Z_i(S) = sum_{j in S} Gamma_ij        if i is outside S,
           = -u sum_{j in S} Gamma_ij     if i is in S.

**Theorem.** If every unordered pair ij satisfies
min(Gamma_ij,Gamma_ji)<=0, the game has a uniform-equilibrium payoff.
The conclusion uses one payoff target for all accuracies, against arbitrary
unilateral behavioral replacements, for every sufficiently long finite
average horizon. All magnitudes, zero comparisons and signed own levels are
included.

The [reciprocal-sign census, section 28](../notes/CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md#28-reciprocal-signs-for-proportional-additive-rewards)
reduces the strict case to a directed three-cycle with a fourth player
pointing into it. The proof here closes that entire remaining case. It also
gives a producer on the strict feeder whenever the necessary inverse column
is positive and the two adverse magnitude comparisons hold.

## Reducing to the feeder

A counterexample has an open neighborhood of counterexamples in the reward
entries. This follows from the equivalence between existence of a uniform
payoff and terminal Nash profiles at every accuracy, and the fact that each
deviation gain changes by at most twice the entrywise reward distance.
See the [limiting-return proof](NONMATCHING_PAIR_LIMIT_RETURN_UNIFORM_EQUILIBRIUM.md).
Every matrix in the stated closed sign set can be approximated by strict
matrices in the same set, by replacing its zero entries by small negatives.
It suffices to argue on strict matrices, with u and ell fixed.

The cited census covers all but the following matrix up to a relabeling,
where every displayed letter is positive.

    Gamma = [ 0 ,-a,-c, A ]
            [-b, 0,-d, B ]
            [ l,-m, 0,-k ]
            [-e,-f, h, 0 ].

It already covers l<=m or Ad<=Bc. Suppose l>m and Ad>Bc. By the
[unrestricted-reward column test, section 29](../notes/CODEX_ROOT__FIN4_METHOD_BOUNDARIES.md#29-a-named-inverse-column-for-unrestricted-higher-rewards),
absence of UE here implies det Gamma>0 and v=Gamma^(-1)e2 strictly
positive. Write e2 for the player-2 coordinate vector. Define

    A'=A/a, B'=B/b, C=c/a, D=d/b, r=l/m,
    U=1+u, theta=u/U, L=h+eD+fC, I=eB'+fA', tau=I/L.
    G=l(B'-D tau)-m(A'-C tau).

The inverse-column equations give tau=v2/v3, B'-D tau=v0/v3>0,
A'-C tau=v1/v3>0 and G=k+1/v3>k. Also A'D>B'C. The ratio
(A'-Ct)/(B'-Dt) strictly increases from t=0 to tau, and is less than r
at tau. Hence rB'>A' and d0=rD-C>0. These inequalities will control
every subsequent contact.

The construction also proves the following raw-table extension on this
strict feeder with l>m and Ad>Bc. Normalize all nonempty original rewards
by subtracting ell_i=r_i({i}) from row i. For some common u>0 assume only

    Z0(01)=ua, Z1(01)=ub, Z2(01)=l-m,
    E=Z3(01)+e+f <= U(e+f),
    Z2(02)<=-ul, Z2(12)<=um, Z2(012)<=-u(l-m),
    Z3(03)<=ue,  Z3(13)<=uf, Z3(013)<=u(e+f).

All remaining nonsingleton rewards are arbitrary. These raw inequalities
give UE even without assuming a positive inverse column, since failure
of that necessity already gives UE. On the positive-column branch we
will produce the target ell+T e2. The common additive table has E=0.

## A continuous family of return payoffs

Until the last step use the native rewards Z. In the additive case, for any construction-order
prefix with next annotation w and independent Quit probabilities q, forced
Quit pays -u (Gamma q)_i and Continue pays (Gamma q)_i+H_i w_i, where
H_i is the product of 1-q_j over j different from i. This identity uses
the additive payoff on the absorbing event and zero on an empty event in
the passive sum. Construction order prepends rows. Calendar order is its
reverse.

For 0<p<1 put T=kp/(1-p) and start at T e2. Prepend a solo3 aggregate
of probability p, giving (Ap,Bp,0,0). Subsequently write X=w0/a,
Y=w1/b. Every round first prepends a solo2 aggregate of some probability
s when w2=0, then prepends a mixed 01 row. Later rounds may have s=0.
A solo2 transforms the active coordinates into

    X_s=(1-s)X-Cs,       Y_s=(1-s)Y-Ds.

It sends w3 to (1-s)w3+hs and leaves w2 zero. When s=0 the identity
map also applies for w2>0. The 01 row uses

    q0=Y_s/(U+Y_s),      q1=X_s/(U+X_s).

The prescribed payoffs equal the Continue payoffs at all four players.
Both mixers are indifferent, with new coordinates X'=u q1, Y'=u q0.
For a quiet player i=2,3 write b_i=(Gamma q)_i. Its new annotation is
b_i+H w_i with H=(1-q0)(1-q1) and incoming w_i measured after the
solo. In the raw extension player 3 also receives E q0q1 in that update.
Its Quit offer is at most u(e q0+f q1), and the player-2 offer is at most
-u(l q0-m q1). The three raw guards for each owner and its zero singleton
give these bilinear inequalities at each vertex of the probability square,
hence everywhere on it. The raw active-player updates and the player-2
passive update are identical to the additive ones. For now these recursions
define the annotations before checking the quiet players' Quit inequalities.

At the start of the first round X=A'p, Y=B'p. At each later round
following a full contact X=rY. In either case X/Y>C/D and X<=rY.
As s rises from 0 to Y/(Y+D), the expression

    U(X_s-rY_s)-(r-1)X_s Y_s

strictly increases from a negative value to a positive one. Indeed
X_s-rY_s has strictly positive derivative d0-(X-rY), and the
nonnegative product decreases to zero while X_s remains positive.
The unique zero s_* is continuous in X,Y at these states by strict
monotonicity and compactness. At s_* one has q1=rq0. At any
0<=s<=s_* one has q1<=r q0.

A full round takes s=s_*. Its row has b2=l q0-m q1=0 and its outgoing
w2 stays zero. At any chosen round one can instead take a fraction of
s_* and then set every following solo2 probability to zero. Call this
choice a release. A release and its first 01 row have b2>=0. Their new
pair ratio is at most r. All subsequent 01 rows preserve this upper
bound because z -> z/(U+z) moves each positive ratio toward one. Thus
every quiet-2 row has nonnegative passive increment and a nonpositive
forced Quit offer. Together with incoming w2>=0 this proves all its caps.

Use the parameter z in [0,1] as follows. For 1-2^(-n)<=z<=1-2^(-n-1),
take n full rounds and release in the next round at fraction
2^(n+1)(z-1+2^(-n)). At z=1 take full rounds forever. At neighboring
endpoints a full round followed by immediate release reproduces the same
sequence as a release at fraction one. At every round X',Y' are bounded
by theta X,theta Y. The solo probability is at most Y/D and q0,q1 are
bounded by Y/U,X/U. All probabilities used after round n sum to at most
a fixed constant times p theta^n. Here and below constants can depend on
the fixed reward parameters and u. The individual quiet annotations stay
bounded, as their passive updates average a bounded terminal reward and
their old coordinate. The total subsequent change of each of them tends
uniformly to zero by the hazard bound. Thus the limiting quiet payoffs
R2(p,z),R3(p,z) are continuous, also at z=1. At that endpoint R2=0.
The other two limiting coordinates are zero.

## Finding both return coordinates at once

We seek F=(R2-T,R3)=0. On z=0 all rounds are pair-only and R3<0.
Indeed M=w3-eY-fX starts at -Ip<0 and each such row sends it to
H M+[E-U(e+f)]q0q1 by (1) below. The total pair survival is strictly
positive since its hazards are summable and proper. Hence the limit is
strictly negative.
On z=1 one has R2-T=-T<0. For p sufficiently close to one R2-T<0
uniformly in z, since R2 is bounded by the absolute passive rewards and
T tends to infinity.

For the remaining side take p small. Let V be the sum of the solo2
aggregate probabilities and S0,S1 the sums of the two pair hazards.
The total is O(p) uniformly over z. After the first solo3, all coordinates
remain O(p) by the passive increments and the active contractions.
Telescoping the Continue identities for each coordinate to the limiting
endpoint gives, uniformly in z,

    S1=A'p-CV+O(p^2),         S0=B'p-DV+O(p^2),
    R2=l S0-m S1+O(p^2),     R3=-e S0-f S1+hV+O(p^2).

For example an update contributes its linear passive increment and an
error bounded by (1-H_i)|w_i|. Summing the latter gives O(p^2). The raw correction E times the sum of
q0q1 is also O(p^2).
Let lambda=L/(lD-mC)>0. Since T=kp+O(p^2), these identities give

    R3+lambda(R2-T) = p lambda(G-k)+O(p^2)>0

on the whole small-p side. Fix p0,p1 strictly between zero and one giving
the small and large side bounds respectively, with p0<p1. Set
P=(p-p0)/(p1-p0). Compare F on the rectangle with the affine map

    (1-2P-2z, 3 lambda z-lambda/2).

The second component is negative at z=0, the first component is negative
at z=1 and P=1, and the second plus lambda times the first is positive at
P=0, for both maps. Their straight-line homotopy avoids zero on the
boundary. The affine map has exactly one simple zero, at (P,z)=(1/3,1/6).
Homotopy invariance of Brouwer degree therefore gives an interior zero of
F. Fix any such zero. There are only finitely many full rounds before
release. The remaining infinite tail consists entirely of 01 rows.

## Every quiet-3 comparison at this return

At a 01 row define the margin after the row by M=w3-eY-fX in its
outgoing coordinates. This is a lower bound on prescribed payoff minus forced
Quit for player 3, since Y=u q0 and X=u q1 after that row. Denote the
same expression immediately before a solo2 aggregate by M_old. After
that solo and its pair row direct substitution gives

    M_new=H(1-s)M_old+HLs+[E-U(e+f)]q0q1.                         (1)

In a pure 01 tail the forcing term is nonpositive. The limiting M at
our return is zero. At every position in this tail, the product of
remaining pair survivals is strictly positive by summability. A negative
margin there would have strictly negative limit by (1). Consequently
every post-row margin in the pure tail, and the margin just before it,
is nonnegative. This includes the margin just after the release row.

After a full contact the next incoming pair coordinates satisfy X=rY.
The next solo and pair row then obey

    H d0 s=U [q1-rq0+(r-1)q0q1].

This follows by multiplying X_s-rY_s=d0 s by H. Put
B=L(r-1)/d0-(e+f)+E/U. Substituting in (1) makes the forcing term

    U [(L/d0)(q1-rq0)+B q0q1].                                 (2)

If B<=0 this is nonpositive in every full round after the first, and
also at the partial release. Working backwards from the nonnegative
post-release margin in (1) proves each preceding full-contact margin
nonnegative. All survival factors here are positive.

If B>0 every full contact following the first preserves a nonnegative
margin. For the first full contact the initial coordinates are
(A'p,B'p) and w3=0. Here X_s-rY_s=(1-s)p(A'-rB')+d0 s. At q1=rq0 the
same substitution gives

    M_first = H(1-s)p [ L(rB'-A')/d0-I ] + U B q0q1.

The square bracket is positive because r(B'-D tau)-(A'-C tau)>0 and
I=L tau. Thus all full contacts pass in this case too. A path with no
full contacts needs only the pure-tail argument above. This proves the
forced-Quit comparison at every 01 row. In particular w3>=0 there.
Every solo2 starts at w2=0 and at nonnegative other annotations, and all
its coordinates are nonnegative at the other endpoint as well. The same
holds for the solo3 aggregate from T e2. Subdividing any solo aggregate
into proper microhazards interpolates between those endpoints. At a solo
microhazard of size at most eta any quiet player's forced Quit gains at
most a fixed reward bound times eta over its nonnegative annotation.

## Ordinary profiles and the original uniform target

Take the finite initial segment of the construction through its release
and then N pure pair rows. Subdivide its finitely many positive solos to
mesh eta, reverse into physical play and repeat this finite word.
Its native tail was T e2 and its head tends to T e2 as N tends to
infinity. The prescribed and Continue recursions are exact inside the
word, and every Quit offer has the bound just proved. Each player other
than 3 faces the solo3 aggregate p as an opponent. Player 3 faces the
positive hazard q0 of the very first construction-order pair row. Thus
opponent survival per word is bounded by one fixed rho<1, independent
of N and eta.

For clarity, if the head error in the sup norm is delta_N, the prescribed
period map has Lipschitz constant at most rho and its fixed payoff
lies within delta_N/(1-rho) of T e2. For a unilateral deadline telescope
the Continue recursions until that date. Each crossed period boundary
costs at most its survival weight times delta_N and the single Quit
costs at most M0 eta for a fixed reward bound M0. The same geometric
bound covers literal Never by letting the number of periods increase.
All behavioral deviations are mixtures of these deadlines on the unique
live history. Hence the terminal regrets tend to zero. Every such profile
and deviation absorbs almost surely, so restoring the row offsets adds
exactly ell to the prescribed terminal payoff and ell_i to each deviator's
terminal outcome. For each chosen finite period of length n, cutting at
K periods gives a uniform terminal-to-horizon error of at most
2M1[(Kn+1)/H+rho^K] for bounded original rewards of magnitude at most M1
and horizon H. Choosing N, eta, K and then a sufficiently long horizon
proves the original uniform target ell+T e2 on the constructed branch.
This contradicts absence of UE there and completes the stated theorem.


## An exact table requiring more than the single solo2 block

Take u=4 and the common additive rewards with

    Gamma=[0,-1,-1,4; -1,0,-3,3; 4,-1,0,-1/8; -1,-1,6,0].

Here det Gamma=7/4 and the player-2 adjugate column is
(72,264,56,80)/8. Both adverse magnitude comparisons hold. The earlier
small-u bound would require 1/8>=16/5. The only positive arrows form the
three-cycle and feeder. Every negative pair excludes the earlier
no-mutually-negative theorem, and there is no directed positive
Hamiltonian cycle. Among triples only 023 can map a positive vector to a
strictly positive vector. Its passive row times its inverse is
(567,-264,-289)/767, failing the nonnegative-row criterion.

The earlier §28 producer prepends solo3, a single solo2 aggregate, and
then uninterrupted 01 rows. Its complete parameter set on this table
can be checked exactly. In its notation x=4-t, y=3-3t. The zero3
balance forces 7/10<t<1 and P=9(10t-7)/(10xy). In fact X=Px, Y=Py
are the positive pair inputs and P=p/(1+pt). Quiet2 at the first row
requires 4Y/(5+Y)>=X/(5+X), or

    5(4y-x)+3Pxy=(211-280t)/10>=0.

The required fixed return R2=T gives F(t)=0, where

    F=(4y-x+(5/3)Pxy)[1-(1+t)P]-(1/8)(1+Px)(1+Py)
     =-(6400t^3+16480t^2-32660t+12453)/[800(t-4)(t-1)].

At 7/10 and 211/280 its values are 7/40 and 7799/81305, both positive.
The cubic numerator inside the leading minus sign is strictly convex on
this interval and negative at both ends. Hence F>0 wherever the first
quiet comparison and the zero3 balance hold. No choice of the two
initial solo probabilities in that earlier construction gives the return.

The actual stationary and sure-quitter alternatives can also be checked
over every hazard vector q. Put b=Gamma q. A positive stationary Nash
or any sure-quitter Nash head at a genuine continuation has b_i>=0 at
quiet players, b_i=0 at proper mixers and b_i<=0 at sure quitters. The
stationary safety hazard 1/(1+u) guarantees native zero against every
opponent strategy, so the continuation response cap needed for a sole
sure owner is nonnegative. These necessity arguments, including signed
restoration, are proved in the
[stationary and sure-head comparison](NONMATCHING_PAIR_LIMIT_RETURN_UNIFORM_EQUILIBRIUM.md#a-separating-nonmatching-proportional-family).

No nonzero q passes the sign test here. Every singleton has a negative
outsider. Of the pairs only 01 and 12 can have both active rows
nonpositive. Both owners must be sure, leaving respectively 3 and 0
with a strictly negative passive sum. On 012, rows 0 and 1 must be
sure and row 2 is then positive. On 013, row 3 must be sure and row 0
is positive. On 123, row 2 must be sure and row 3 is positive. On 023,
the active block has positive inverse, incompatible with active payoffs
all nonpositive and q positive on the block. Finally

    8 adj Gamma=[-147,199,72,75; -567,767,264,289;
                 -119,161,56,63; -168,232,80,88].

If all players are active, b<=0 and q=Gamma^(-1)b strictly positive
requires b0<0 by the signs of the last three columns. Thus q0=1 and
b2>=4-1-1/8>0, again impossible. A nonzero homogeneous singleton
complementary solution could be scaled down to give a nonzero box
solution, so Gamma is R0. The vanishing stationary hazard argument in
the same reference also rules out terminal regret tending to zero along
stationary profiles whenever at least one original own level is positive.
The new construction supplies actual private profiles on this table.
