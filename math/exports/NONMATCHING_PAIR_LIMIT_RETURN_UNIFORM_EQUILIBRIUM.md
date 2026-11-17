# A four-player singleton sign pattern with uniform payoffs and an open set without exact equilibria

This is an ordinary mathematical proof. The general four-player quitting conjecture
remains open.

## Raw family

Four players independently choose Continue or Quit at each live date. The first
nonempty Quit coalition absorbs at its finite original reward r_i(S). Live and
AllNever pay zero. Write ell_i=r_i({i}), Z_i(S)=r_i(S)-ell_i for nonempty S, and
Gamma_ij=Z_i({j}), with zero diagonal. All own singleton levels ell_i are arbitrary
signed reals.

Choose a labeling with

    Gamma=[ 0,-a,-c, A;
           -b, 0,-d, B;
            l, m, 0,-k;
            e,-f, h, 0 ],

where all twelve displayed letters are strictly positive. In this packet A,B denote
singleton entries, and T denotes a scalar target. Set

    U=f A/a-e B/b, L=h+f c/a-e d/b.

Also set V=AL-cU and W=BL-dU=Bh+f(Bc-Ad)/a. These quantities are used to choose a
proof branch. They impose no numerical restrictions on the twelve positive singleton
magnitudes. The two pair premiums are

    u0=Z0(01)/a>0, u1=Z1(01)/b>0,
    K_i=[Gamma_i0 u1+Gamma_i1 u0+Z_i(01)]/(1+u0+u1), i=2,3.

The following inequalities concern only the displayed nonsingleton rewards.

    Z2(01)>=0,    Z2(02),Z2(12),Z2(012)<=0,
                  Z3(03)<=-e u1,       Z3(13)<=f u0,
                  Z3(013)<=f u0-e u1-u0 u1 K3.                   (P)

Every other nonsingleton coordinate is unrestricted. All displayed conditions are
finite raw reward tests.

**Theorem.** Every table with this singleton sign pattern and the participant/passive
inequalities (P) has an original uniform-equilibrium payoff. When K3<=0, det Gamma>0
and Gamma^(-1)e2 is strictly positive in all four coordinates, the proof produces the
fixed target ell+T e2, T>0, through finite-period private profiles. Deviations may
replace the entire behavioral law. Before absorption there is only one live history
at each date, so the full response supremum runs over every deadline and literal
Never. The additive example below also gives a nonempty open set in all sixty
coordinates on which no exact original terminal Nash profile exists although the
uniform payoff exists. On that open set each fixed upper bound on the
period of the live hazards leaves a positive terminal regret gap.

If K3>0, let 0 and 1 quit surely at the first date. This gives an exact
equilibrium. Their joint payoffs are positive and withdrawing pays a negative
singleton. Player 2 stays quiet by (P), and player 3's passive reward
exceeds its joining reward by at least (1+u0)(1+u1)K3. This follows by
substituting the definition of K3 into the last bound in (P). All deviations
absorb against this pair. Hence assume K3<=0 in the constructions below.

The theorem also settles a complete subclass using only the singleton signs
above. For each coalition S let Z_i(S) equal the sum of Gamma_ij over j in S
when i is outside S and minus v_i times that same sum when i belongs to S.
Allow every v_i>0 with v1<=v3<=v0, including a common arbitrary v>0.
If f<=e, the sure pair 01 works directly. The two passive singleton sums
are l+m>0 and e-f>=0, and joining would multiply either by a negative
number. If f>e, (P) holds with u0=v0,u1=v1. In fact K3=
[e(1+v1)-f(1+v0)]/(1+v0+v1)<0, and v3(f-e)<=f v0-e v1.
Thus every choice of the twelve positive magnitudes and all the indicated
row factors in this subclass admits a uniform-equilibrium payoff.

## Why the singleton magnitudes impose no additional raw restrictions

For the literal sign pattern above, any hypothetical signed game without UE,
regardless of all nonsingleton rewards, must have

    det Gamma>0,       Gamma^(-1)e2 strictly positive.             (N)

We prove this same-table necessity first. We use the tracked unconditional no-UE
consequence finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff
(UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean). It
gives R0 and integer degree +1 for the actual singleton complementarity matrix Gamma.
Here a complementary vector at offset -y is x>=0 with Gamma x-y>=0 and x_i(Gamma
x-y)_i=0. R0 means that the homogeneous system has only zero. The normal-map degree
at -y is the same as at zero because R0 implies all complementary solutions for
bounded offsets are uniformly bounded, by scaling an unbounded sequence and taking a
homogeneous limit. Homotopy of offsets therefore preserves the Brouwer degree on a
sufficiently large bounded domain. A nonzero degree gives a solution. At a unique
full-support solution with nonsingular Gamma the local index is sign(det Gamma),
since the normal map x -> min(x,Gamma x-y) has derivative Gamma there. This is also
the sign convention used by the cited source.

First take a generic table, so all principal blocks of sizes at least two are
nonsingular and all four entries of adj(Gamma)e2 are nonzero. This condition is open
and dense within the sign pattern. Indeed the determinant of each hollow principal
block of these sizes is a nonzero polynomial (a derangement exists), and the four
cofactor polynomials are explicitly nonzero below. Consider offsets y with y0,y1,y3
fixed and strictly positive, and y2=Y tending to infinity. For any proper support
omitting 2, its active block gives a bounded vector independent of Y. A singleton
cannot match a positive active target. Thus such a support fails the required row2
for large Y. Pairs containing 2 cannot map a positive vector to a strictly positive
vector on both rows because at least one active off-diagonal coefficient is negative.
Triple 012 has nonpositive row0. On triple 023 the relation e x0+h x2=y3 bounds both
coordinates, and -c x2+A x3=y0 also bounds x3. Hence row2 cannot pay Y.

The final proper support is 123, with cyclic block C and passive row O=(-a,-c,A).
Direct multiplication gives

    Delta=det C=Bhm-dfk,
    adj(C)=[[hk,Bh,dk],[fk,Bf,Bm],[hm,df,dm]],
    (O adj(C))_2=Adf-Bah-Bcf=-aW,                               (2)

where the marked column is labeled by player 2, the middle column in this block. A
positive solution to Cx=y_123 forces Delta>0. At large Y the exterior constraint O
x>=y0 fails if W>0. Genericity excludes W=0. If W<0 and Delta>0, the following
three-player calendar already yields an original UE even with arbitrary other
entries, contradicting the assumed no-UE.

In construction order, from active values (0,T,0) at players 123 apply solo3 with
cumulative probability p=T/(k+T). Their values become (Bp,0,0). Then apply solo2 with
s=Bp/(d+Bp), reaching (0,0,hs), and solo1 with r=hs/(f+hs), reaching (0,mr,0). As T
tends to zero, mr/T tends to Bhm/(kdf)>1. This function of T is continuous and mr is
bounded, so there is a T>0 with mr=T. For quiet0 choose the periodic passive value by
its affine recursion, whose per-period survival (1-p)(1-s)(1-r)<1. Its constant
numerator divided by (1-r)(1-s) equals

    p[A-B(c+ah/f)/d] = -apW/(df) >=0.

Indeed s/(1-s)=Bp/d and r/(1-r)=hs/f. Thus its boundary value z is nonnegative. Its
other two values are nonnegative as well. Just after the solo3 update it is
(1-p)z+Ap, and just before the last solo1 update it is (z+a r)/(1-r). All active
values listed above are nonnegative and the mover's value is zero throughout each
solo aggregate. Subdivide each solo aggregate into hazards of size at most eta. Every
owner has at least one active opponent and a per-cycle opponent-survival bound
strictly below one independent of subdivision. The prescribed payoff recursions and
Continue values are exact, while a forced Quit at any date can exceed its annotated
nonnegative value by at most M eta. The finite-word argument below (now with seam
defect zero) proves signed original UE.

This eliminates 123 in the contrary case. The unique solution at every sufficiently
large Y is therefore the full solution Gamma^(-1)y>0. The local degree is then +1, so
det Gamma>0. Dividing by Y yields Gamma^(-1)e2>=0, and the generic cofactor condition
makes every component strictly positive.

For the exact table without genericity, failure of UE is open in all sixty reward
entries because a fixed terminal exploitability gap against all profiles stays
positive after any uniform reward perturbation smaller than half the gap, since each
deviation gain changes by at most twice the reward distance. The fixed-target
characterization in
quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors supplies
this positive gap under no UE. Vary just the twelve off-diagonal singleton entries in
a small open box preserving signs and no UE. The native pair values need not vary. By
density and continuity, det Gamma and the four cofactor entries are nonnegative
everywhere in this box. Each polynomial is multi-affine in these twelve entries, and
each is nonzero as a polynomial. If such a polynomial vanished at the box center, its
center value would equal the average of the values at all vertices of any smaller
axis-aligned box centered there. Nonnegativity would force every one of those
vertices to be a zero. As the side lengths vary this includes an open set, impossible
for a nonzero polynomial. Thus all five values are strictly positive at the literal
point, giving (N) without any genericity assumption.

The exact symbolic identities needed by the main construction are

    adj(Gamma)e2=(aW,bV,abU,abL),
    det Gamma=l aW + m bV - k abL.                              (3)

These follow by expanding the four minors and then row2. Under (N), W,V,U,L are
positive, so tau=U/L is defined, B-d tau=W/L and A-c tau=V/L. In particular

    [l(B-d tau)/b+m(A-c tau)/a]/k
         =1+det Gamma/(abLk)>1.                                 (4)

We now construct UE under (N). This contradicts the only possible contrary branch and
proves the unrestricted-magnitudes theorem.

## Two solo blocks, then a pair block in reverse construction order

An annotated row with next value w and playing hazard q has natural payoff recursion.
A player who Continues faces passive numerator P_i plus opponent survival H_i times
w_i. Its forced Quit offer is Q_i. Weak local caps at an annotated row mean
Q_i<=current_i+error and Continue is exactly current_i (all mixers are indifferent
when error=0). In the following construction annotations are propagated by prefixing
rows, so physical play traverses them in reverse.

Start at w=T e2. A solo3 aggregate of total hazard probability p=T/(k+T) gives
(Ap,Bp,0,0). A solo2 aggregate of probability s then gives x with

    x0=Ap(1-s)-cs, x1=Bp(1-s)-ds, x2=0, x3=hs,
    X=x0/a, Y=x1/b,      0<s<s0=min(Ap/(c+Ap),Bp/(d+Bp)).

These aggregates may be divided into finitely many solo microhazards as small as
desired, e.g. equal hazards 1-(1-p)^(1/n). Continue interpolates from the next to the
singleton payoff and gives the exact accumulated transformation. The mover's own
continuation and offer are both zero throughout its block. Every quiet owner's
interpolation is nonnegative because both endpoints are. Thus at each such subdate
the forced-Quit offer is at most M times the microhazard, where M bounds the absolute
native rewards. Every prescribed and Continue identity is exact.

At a 01 row with next coordinates a X_n,b Y_n, use

    q1=X_n/(1+u0+X_n), q0=Y_n/(1+u1+Y_n),
    X_(n+1)=u0 q1, Y_(n+1)=u1 q0, X_0=X,Y_0=Y.

Indeed Q0=a u0 q1,P0=-a q1, and Q1=b u1 q0,P1=-b q0, so each active owner is exactly
indifferent. Set theta_j=u_j/(1+u_j), D_(j,n)(z)=1+z(1-theta_j^n). Induction gives

    X_n=theta_0^n X/D_(0,n)(X), Y_n=theta_1^n Y/D_(1,n)(Y),
    1-q1=D_(0,n)(X)/D_(0,n+1)(X), 1-q0=D_(1,n)(Y)/D_(1,n+1)(Y).

The hazards are strictly proper, nonempty and summable in construction order. The
quiet annotation propagates by P_i+H_i w_i, where

    P_i=Gamma_i0 q0+Gamma_i1 q1+[Z_i(01)-Gamma_i0-Gamma_i1]q0q1.

If the block starts with passive coordinate z, the limit of this coordinate after n
prefix operations is

    [z+Gamma_i0 Y+Gamma_i1 X+K_i XY]/[(1+X)(1+Y)].               (1)

To see this, divide the passive recurrence by the joint survival through the current
row. The normalized increments have weights D_(0,n+1)(X)D_(1,n+1)(Y). The three
weighted sums are

    sum q0 =Y+XY(1+u1)/(1+u0+u1),
    sum q1 =X+XY(1+u0)/(1+u0+u1),
    sum q0q1=XY/(1+u0+u1).

For instance, the q0 weight times q0 is Y(1-theta_1)theta_1^n [1+X(1-theta_0^(n+1))].
Summing the geometric series proves the first formula. The other two follow
similarly. Substitution gives (1). The limiting transform is only used to select
parameters and approximate seams. Physical play below uses finite blocks.

## Closing the cycle

Choose s in (0,s0) to solve

    F(p,s)=hs+eY-fX+K3XY=0.

At s=0, F=-U p+K3 ABp²/(ab)<0. At s=s0, if X=0 first then Y>=0 and F>=hs0>0. If Y=0
first, F=pW/(d+Bp)>0. This endpoint argument permits either order and uses the actual
named cofactor W. Throughout [0,s0], both X,Y are nonnegative and decreasing. The
derivative of hs+eY-fX is L+pU>0, and the derivative of K3XY is nonnegative. Hence
there is a unique root s(p) in (0,s0), continuous in p (uniqueness and compactness
give this directly), extending by 0 at p=0. This enforces the zero3 endpoint in (1).
It also ensures the quiet3 inequality at every pair row. Applying the same terminal
formula to the construction-order suffix starting at n+1 gives

    w3_(n+1)=fX_(n+1)-eY_(n+1)-K3 X_(n+1)Y_(n+1)
             =f u0 q1-e u1 q0-u0 u1 K3 q0q1.

At each of the four vertices of the (q0,q1) square this is at least the forced-Quit
payoff Q3 by (P). The difference is bilinear, hence nonnegative everywhere. The
owner2 passive annotation starts at zero and remains nonnegative by its passive
entries. Its forced Quit offer is nonpositive by the three participant caps in (P).
Thus every pair row has all prescribed and Continue identities and every forced-Quit
inequality exactly.

The infinite-block limiting output is R(T)e2, where

    R(T)=(lY+mX+K2XY)/[(1+X)(1+Y)].

It is continuous and bounded by max(l,m,Z2(01)), since each finite passive recurrence
starts at zero and averages only these three bounded rewards and its old
continuation. Since s=O(p) and p~T/k, the balance equation gives

    s/p -> tau,
    R(T)/T -> [l(B-d tau)/b+m(A-c tau)/a]/k >1.

Indeed X=(Ap-cs)/a+O(p²), Y=(Bp-ds)/b+O(p²), and K3 is fixed. For large T one has
R(T)<T. The intermediate value theorem supplies one fixed T>0 with R(T)=T. All
ensuing probabilities are fixed before any accuracy request. By the explicit
recurrences and (1), the pair annotations w^(N) approach T e2 in all coordinates.

## Finite ordinary profiles and complete unilateral responses

Use the first N>=1 construction-order pair rows, preceded in construction order by
the two subdivided solo aggregates. Repeat this whole finite word in physical reverse
order. Its p and s are fixed and strictly positive. For every player i, even if that
player always Continues, at least one of the two distinct solo owners 2,3 remains an
opponent. Opponent survival per period is thus <=lambda=max(1-p,1-s)<1 independently
of N and the subdivision mesh eta. Prescribed and all deviating profiles absorb
almost surely. All local prescribed and Continue recursions hold exactly along the
annotated period with tail T e2 and head w^(N). Every immediate Quit offer is <=the
annotation at that date+M eta on solo rows and <=the annotation exactly on pair rows.
Put delta_N=||w^(N)-T e2||_infinity. The only periodic seam defect has size delta_N.

For the actual repeated word, the prescribed Bellman map over a period contracts by
joint survival <=lambda in the tail value. Its fixed prescribed value at the head
consequently differs from T e2 by at most delta_N/(1-lambda) (iterate affine map from
T e2). For any fixed player and any pure deadline, telescope the dated Continue
recursions before this deadline, then use the single immediate-Quit bound there. A
seam crossed after k periods incurs at most lambda^k delta_N if the first crossing is
indexed k=0. Summing seams gives at most delta_N/(1-lambda), with no accumulation of
M eta because the player uses Quit only at the final deadline. Always Continue has
the same cap bound by taking an unbounded number of full periods and using lambda^k
times a bounded remaining annotation. Thus every deadline/Never payoff is <=
w_i^(N)+M eta+delta_N/(1-lambda). Every complete behavioral replacement is a mixture
of these deadlines on the unique live history. Sending N to infinity and eta to zero
gives arbitrarily accurate terminal Nash and convergence to the one target T e2.

On every prescribed or deviating profile just constructed absorption is almost sure,
so restoring ell adds exactly ell_i to its terminal payoff. This applies also to
literal Never deviations. For a fixed finite period at each accuracy, opponent
survival after k periods is uniformly <=lambda^k for every unilateral replacement.
Bounded rewards and the tail estimate on absorption time (including the payoff's
one-stage onset) show uniformly over these profiles that the finite-average expected
payoff tends to the terminal payoff. For example cut after K whole periods. The error
is <=2M_orig[(K period+1)/H+lambda^K] for every sufficiently large H. Together these
bounds yield the requested fixed target ell+T e2 and uniform inequalities at all
sufficiently large horizons.

## A separating nonmatching proportional family

Take

    Gamma=[0,-2,-5,4; -6,0,-4,6; 1,3,0,-5; 1,-g,4,0],    1<g<89/68.

Here the only pair negative in both singleton directions is 01. Here Bc>Ad reads
30>16, U=2g-1>0, and L=10/3+(5/2)g>0, so the return balance has positive endpoints as
above. From the formula above, R(T)/T tends to (189+7g)/(100+75g)>1. Use the finite
native table

    Z_i(S)=sum_(j in S) Gamma_ij         if i not in S,
    Z_i(S)=-v_i sum_(j in S) Gamma_ij   if i in S,

with arbitrary v_i>0 satisfying v1<=v3<=v0 and no restriction on v2. Then
u0=v0,u1=v1, Z2(01)=4, and all three owner2 participant caps hold. One has Z3(01)=1-g
and K3=[v1-gv0+1-g]/(1+v0+v1)<0. The owner3 vertex guards hold because v3>=v1,
v3<=v0, and v3(g-1)<=g v0-v1. Thus the growth and return tests work throughout these
unbounded unequal row ratios. In particular every common negative ratio is included.
A small neighborhood with sixty independent directions is possible by choosing the
raw guards strictly, for example 1<g<89/68 and 0<v1<v3<v0. All singleton inequalities
are strict, the three owner2 caps are strictly negative, and all owner3 bounds are
strict in this interior. Recipient shifts of all nonempty rewards preserve these
native tests. The proof of the eighty-nine over sixty-eight boundary only uses strict
growth. No claim of failure of UE beyond that threshold is made.

Throughout 1<g<89/68 this explicit additive family also gives a full-menu separation.
With at least one positive own level it admits neither a stationary approximate-Nash
sequence with error tending to zero nor a sure-quitter cap-Nash root at any genuine
continuation. Here is a direct check against all supports.

In native coordinates let b_i(q)=(Gamma q)_i. The passive current numerator is
exactly b_i(q) and the forced-Quit offer is -v_i b_i(q), for all q including the
boundary. In the actual game the stationary hazard 1/(1+v_i) guarantees zero native
payoff against any opponent calendar, because at each reached stage its expected
absorbing reward contribution is zero. It guarantees absorption and original payoff
ell_i as well. Consequently every actual native response cap is nonnegative and every
actual original cap is at least ell. These properties pass to cap limits.

At a cap-Nash head containing a sure owner, a player facing a sure opponent has only
the two current offers. Its sign rules are b_i>=0 if quiet, =0 if proper active, <=0
if sure. A sole sure owner facing proper opponents must have -v_i b_i>=b_i+H_i
B_tail, with B_tail>=0, implying b_i<=0. For original rewards, relative caps
B_tail-ell_i>=0 give the identical comparisons. Any positive stationary Nash likewise
satisfies these three sign rules. When opponents have positive joint stopping hazard,
the Never payoff is b_i/(1-H_i) and the prescribed stationary value obeys its one-row
renewal identity. A quiet player needs b_i/(1-H_i)>=-v_i b_i, a mixer equality, and a
sure player the reversed inequality. If an active player faces all-Never opponents
its b_i is already zero. For an absorbing stationary profile, restoring ell_i affects
no finite response or prescribed payoff, and whenever the Never comparison above is
used, the opponents absorb surely.

Here is the box sign census. Every active row must have b_i<=0. The strictly positive
left tests (190,34g+58,68g+186,340) on the whole matrix and (37,34,50) on principal
block 123 exclude all four and 123. Their products are respectively (178-136g) times
the all-ones row and (102-50g,52,52), all positive on the stated g interval. Each of
02,03,12,13,23,012,023 has an active row which is strictly positive against its
entire positive support, by inspection of Gamma. Thus the only nonsingleton supports
left are 01 and 013. Every singleton has a negative outsider. On support 01 the two
strictly negative active comparisons force both owners sure, so quiet owner3 faces
b3=1-g<0. On 013, b0<=0 yields q1>=2q3, so 0<q3<1 and b3=0, i.e. q0=gq1. This implies
0<q1<1 and hence b1=0, i.e. q0=q3, contrary to q1>=2q3. Thus the box complementarity
system has no nonzero solution. Gamma is R0, since a nonzero nonnegative vector
complementary to Gamma with nonnegative slack could be scaled into the box to give
just such a solution.

## Every fixed upper bound on the period fails

On this additive example choose any own levels with at least one positive
coordinate. For every fixed integer N>=1 the infimum of original terminal
exploitability over periodic hazard profiles with period at most N is
strictly positive. The same holds on the open family proved below, upon
shrinking its neighborhood so its singleton matrix remains R0. This
statement concerns the conditional Quit probabilities on the live history.

Suppose a sequence of such profiles had regret tending to zero. Pass to a
fixed period length and to limits of all its hazards. AllNever itself has
a fixed profitable deviation by a player with positive own level. Hence
we may assume every profile in the sequence has some positive hazard.
Its periodic repetition absorbs almost surely. Every finite unilateral
deadline also absorbs surely, so row offsets cancel when testing each
such deadline. In a native table the limit of deadlines tending to infinity
is the Never payoff by bounded convergence, since the own singleton pays
zero. Thus native terminal regret tends to zero as well.

If some hazard has a positive limit, the limiting finite period absorbs
almost surely. Its prescribed payoff is continuous there by summing the
geometric series of whole periods. Each finite deadline is continuous as
it only queries finitely many rows. Passing to the limit gives an absorbing
exact native Nash, excluded in the next two sections. If all hazards tend to
zero, write beta for the sum of all hazards in one period. Pass to a limit
x in the unit simplex of the four per-player sums divided by beta. The
one-period absorption probability is beta+O(beta^2), and the unnormalized
vector of expected one-period rewards from absorption is beta Gamma x_n
+O(beta^2), where x_n is the normalized vector before taking the limit.
The constants are fixed by the reward bound and period bound. These
estimates follow by expanding the finite products, including simultaneous
quits. Dividing gives limiting prescribed payoffs Gamma x. The first-date
Quit offer tends to zero, hence Gamma x>=0. When 0<x_i<1, deleting
player i's clock gives opponent absorption beta(1-x_{n,i})+O(beta^2)
per period. Its Never value tends to (Gamma x)_i/(1-x_i), using the zero
diagonal. Since this cannot exceed (Gamma x)_i, that coordinate vanishes.
If x_i=1 it vanishes by the zero diagonal. This gives a nonzero homogeneous
complementary vector, contrary to R0. For the open perturbation, R0 persists
because a sequence of nonzero homogeneous complementary vectors can be
normalized to the compact unit simplex and passed to the limit. These two
cases prove the positive lower bound.

## AllNever is the unique actual native exact Nash

For the explicit additive table at 1<g<89/68, this claim holds for arbitrary positive
row factors v_i. Ordering the factors is only needed for the sufficient raw UE guards
above. Consequently every absorbing approximate native Nash sequence furnished by the
theorem is separated from the entire actual exact native Nash set by its joint Never
mass. This conclusion concerns actual independent strategies. The payoff/cap/Never
closure does contain zero-debt absorbing points.

Suppose an actual native profile is exact Nash. A first reached sure row would obey
the box sign constraints proved above, so all hazards at every reached date are
proper. Hence every finite date is reached with strictly positive probability. At
each such date its actual conditional tail is exact Nash, because any profitable
change conditional on that reached history would give a profitable complete
deviation. Let w(t) be its vector of conditional expected payoffs, q(t) its current
hazards, and b(t)=Gamma q(t). Every w(t) is nonnegative by the constant-hazard
guarantee. Since Continue is used with positive probability by every owner, exact
optimality on the unique surviving history gives

    w_i(t)=b_i(t)+H_i(t)w_i(t+1)>=-v_i b_i(t),

with equality to the right-hand side for every active owner i. If w_i(t)=0 then
b_i(t)>=0, and the equality plus H_i(t)>0 forces w_i(t+1)=b_i(t)=0. Thus a zero
coordinate remains zero at every later date. Every active row satisfies b_i<=0, as
w_i=-v_i b_i>=0. The active-row support eliminations already proved therefore leave,
at each date, only empty, singleton, 01 or 013 support (the static mixed/sure
endpoint rules are not used in this last reduction).

Put V=(1,1,0,1), W=(1,10,14,0). The three estimates below hold throughout the
interval for g.

    (V Gamma) on columns 0,1,2 = (-5,-2-g,-5),
    (V Gamma-(11/8)Gamma_0-(19/24)Gamma_1) on 0,1,3 = (-1/4,3/4-g,-1/4),
    (W Gamma+43 Gamma_3) on 0,1,3 = (-3,40-43g,-6).

While w3(t)>0, singleton3 cannot occur because then the active row3 would have b3=0
and hence w3=0. The first line covers the remaining singleton rows and the empty row.
The second covers 01 and 013 using b0,b1<=0. Thus V Gamma q<=-sum(q)/4 throughout
this initial interval. The exact recursion and nonnegativity give w(t)-w(t+1)<=Gamma
q(t) coordinatewise. Consequently

    V w(t+1)-V w(t)>=sum_i q_i(t)/4  while w3(t)>0.

Throughout the possible final interval w3(t)=0, the persistence already proved gives
b3=0 at every row. Each singleton except 3 would make b3 nonzero, so every surviving
support is contained in 013. The third line therefore gives

    W w(t+1)-W w(t)>=sum_i q_i(t)/4  while w3(t)=0.

Both weighted payoffs are nonnegative and uniformly bounded by the table, and there
is at most one switch of intervals. Summing on each shows that sum over all dates and
owners of q_i(t) is finite. Since every native nonzero payoff requires some future
Quit, the conditional probability union bound gives

    ||w(t)||_infinity <= M sum_(j) sum_(k>=t) q_j(k) -> 0.

If w3 were positive forever, the nonnegative, nondecreasing Vw would tend to zero,
contradicting its strict positivity. Thus there is a first zero3 date. From that date
the nonnegative, nondecreasing Ww tends to zero and the last growth bound forces no
further hazards. All w coordinates are zero at this first zero3 date. If an earlier
positive3 interval existed, its nonnegative, nondecreasing Vw would end at zero
despite its positive start. Hence w3 is zero from the beginning and all the original
hazards vanish. Conversely AllNever is exact native Nash because every own singleton
is zero. This proves the claim without assuming periodicity, finite support or a
stationary deviation.

For arbitrary signed ell_i, an absorbing exact original Nash would give an absorbing
exact native Nash. For any complete native deviation truncate its first-Quit time by
forcing it to Quit by date n. Its payoff converges to that of the original native
deviation by bounded convergence. When the first nonempty coalition is finite the
outcomes eventually agree samplewise, and on AllNever a forced solo gives native
zero. Every truncated law absorbs surely, so comparing in the original game subtracts
the same ell_i from both prescribed and deviating expected payoff. This gives the
native exact inequalities, a contradiction. On a nonabsorbing original profile with
some ell_i>0, forcing that owner's own prescribed clock by n instead has limiting
original gain ell_i times the positive joint Never mass. Each finite first outcome is
eventually unchanged and the previously all-Never event pays ell_i. Hence with a
positive own level there is no exact original terminal Nash. When every ell_i<=0,
AllNever is exact original terminal Nash. Thus in the additive example exact original
terminal Nash existence is characterized by max_i ell_i<=0, even though every
ordered-ratio member has a UE payoff for all signed ell.

## The exact obstruction persists on an open set in all sixty coordinates

Fix any base additive matrix Gamma* in 1<g<89/68 and any strictly ordered factors
0<v1<v3<v0, v2>0. Let Z* be its additive native completion. All raw positive UE
guards are strict at Z*, so they persist in a neighborhood. There exists epsilon>0
depending only on this base point so the following open native subfamily has AllNever
as its unique exact behavior on live histories under the following strict
inequalities.

* ||Z-Z*||_infinity<epsilon, native own singletons still zero.
* For every i and every nonempty subset S of opponents, Z_i(S union {i})+v_i Z_i(S)>0.

This open set is nonempty. From Z* increase every native participant reward on every
nonsingleton coalition by the same sufficiently small positive amount, with passive
and singleton rewards fixed. Each of the 28 strict comparisons holds and all original
raw UE guards still hold. All original reward offsets can then vary freely. Nonempty
open subsets with at least one positive own singleton have UE while no exact terminal
Nash exists. The original linear decomposition (native 56 free coordinates, four own
offsets) makes this genuinely 60-dimensional. The individual base factors v_i are
used only to specify this open subfamily.

For actual per-date hazards q and opponent survival H_i, write P_i,Q_i for passive
absorption and forced-Quit offers, b_i*=(Gamma* q)_i, beta=sum q. Independent product
expectations give

    |P_i-b_i*|<=epsilon sum_(j != i) q_j,
    |Q_i+v_i b_i*|<=epsilon sum_(j != i) q_j.

Indeed the empty opponent coalition contributes zero in either comparison and the
probability opponents are nonempty is bounded by that sum. The strict guards imply
Q_i+v_i P_i>=0, strictly when any opponent hazard is positive. Stationary personal
hazard 1/(1+v_i) then guarantees at least zero against every calendar by geometric
survival and nonnegative expected stage contributions.

A sure row of an exact profile is excluded uniformly near Z*. For a sure owner h,
deviation to Continue and then use that guarantee would yield P_h+H_h
nonnegative_tail, so it is necessary that Q_h>=P_h. Each i!=h faces guaranteed
immediate absorption, and its prescribed action is a best response in the two literal
offers Q_i,P_i. These requirements on (Z,q), q_h=1, are closed, since for i!=h they
require both q_i(P_i-Q_i)<=0 and (1-q_i)(Q_i-P_i)<=0. If such rows existed
arbitrarily close to Z*, a subsequence with the same h and convergent q would supply
a forbidden nonzero additive box-sign solution at the limit. Choose epsilon small
enough to exclude all four choices of h for the new family. Only this necessity,
which uses the weak security guard, is asserted. Arbitrary nearby tables outside the
guarded subfamily need not have nonnegative caps.

Every finite date is consequently reached and all hazards are proper. In any actual
exact Nash, each conditional w_i is nonnegative and w_i=P_i+H_i w_i'>=Q_i. At active
i, w_i=Q_i. Thus active coordinates satisfy

    b_i* <= epsilon sum_(j != i)q_j/v_i.

The support catalog remains valid with this slack. On 02,03,12,13,23,012,023 there is
an i having Gamma*_ij>0 for every other j in the support. If epsilon/v_i is smaller
than the minimum of these finitely many strict coefficients, that support is
impossible. On full support and 123 there is a strictly positive left multiplier y
for the relevant submatrix with product strictly positive. Multiplication of the
active upper bounds implies (min_j (y Gamma*)_j) beta <= epsilon (sum_i y_i/v_i)
beta, impossible for epsilon sufficiently small for each of these two multipliers.
This leaves only empty, singleton, 01 and 013 supports.

If w3(t)=0, then Q3<=0 and P3<=0 by nonnegativity of w3'. Thus Q3+v3 P3<=0, forcing
q0=q1=q2=0 by the strict guard. P3=Q3=0, H3=1 and w3'=0. The entire subsequent tail
therefore has no active owner except possibly 3. Player2's prescribed terminal value
on that tail would be Z2(3) times the probability of a player3 exit. This singleton
reward is still negative at our perturbations. Nonnegative security forces the exit
probability (and all future 3 hazards) to be zero. Hence a zero3 payoff makes that
whole tail empty.

While w3(t)>0, singleton3 cannot occur because its own forced offer is zero. For
V=(1,1,0,1), on empty or singleton0,1,2 the strict base estimate V Gamma* q<=-beta/4
holds. On 01,013 the coefficient bound

    (V Gamma*-(11/8)Gamma*_0-(19/24)Gamma*_1)q<=-beta/4

and the two active upper bounds imply

    V P <= [-1/4+epsilon(3+11/(8v0)+19/(24v1))] beta.

The same displayed bound also holds on empty and the allowed singleton supports by
the comparison |P_i-b_i*| above. Choose epsilon small enough that the bracket is
<=-1/8. The nonnegative future payoff and the flat Continue recursion yield
Vw(t)-Vw(t+1)<=V P, so Vw(t+1)-Vw(t)>=beta(t)/8. Summing over the initial positive3
interval bounds its total hazards. If this interval is infinite, bounded future
rewards give ||w(t)||<=M sum_(s>=t)beta(s)->0, contradicting Vw(t)>0 and
monotonicity. If it ends, its first zero3 date has an empty tail and hence w=0. The
positive initial interval cannot telescope upward to zero. Thus w3 is zero from the
start and the full prescribed live behavior is AllNever. It is indeed exact native
Nash because native own singletons and AllNever pay zero. The actual original-offset
conclusions follow from the same sure deadline truncation argument as in the additive
proof.

For an exact test of the two endpoint orderings in the scalar construction,
take Gamma=[0,-1,-1,2 / -1,0,-1,1 / 1,1,0,-1 / 1,-2,3,0], with slashes
separating rows. Here Bc=1<2=Ad, det Gamma=2 and
Gamma^(-1)e2=(1/2,5/2,3/2,2). One has U=3, L=4 and tau=3/4. Both endpoint
orderings are therefore needed even with a strictly positive inverse column.

## Source correspondence and formalization

The full-cap identity for a row followed by a genuine continuation is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
The fixed-target terminal characterization is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The degree input and its exact hypotheses were identified above.
The finite-period estimates here also prove the uniform payoff bounds directly.

The strategic distinction can be checked on the additive subfamily.
Earlier pair constructions that require both outsiders' three joining offers
against the pair to be nonpositive cannot apply under any relabeling.
The sole mutually negative pair is 01 and Z3(13)=g v3>0. A construction
using two disjoint mutually negative pairs has no eligible second pair.
On the explicit g interval, every actual exact terminal profile at positive
own levels and every vanishing-regret stationary sequence has already been
excluded. The limiting payoff formula for the passive player who might join,
and its use at every finite pair row, are essential to the present return.

For formalization, the four cofactor identities and the sole possible
proper support at a large player-2 offset give a finite matrix lemma.
The scalar recurrences for X_n,Y_n and the passive limit give a separate
finite-period approximation lemma. The one-period errors and opponent
survival estimates then supply the actual behavioral profiles. The claims
about uniqueness and its open set use exact conditional Nash behavior at
all reached histories and are independent of the matrix degree.
