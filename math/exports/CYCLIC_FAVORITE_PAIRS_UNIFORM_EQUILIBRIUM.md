# Uniform equilibrium for cyclic favorite-pair games

This ordinary mathematical theorem resolves a continuous family of four-player
quitting games through its actual payoff domain. Bad triple roots are replaced
by opposite-pair roots, and bad opposite pairs by good triple or adjacent-pair
roots at the SAME continuation. The complete compact-domain argument below
then supplies absorbing approximate equilibria with every behavioral deviation
priced. Neither stationary play nor an individual root-index sign is assumed.
This is not a proof for arbitrary Fin4, and no new Lean check is claimed.

## 1. Complete raw class and conclusion

Fix a parameter0<=T<=1/4.
Players are0,1,2,3 modulo4. Their private Continue/Quit choices are independent
at each live history. The first nonempty quitter coalition S absorbs at its
finite reward; live play and Never give zero. One player may replace its whole
behavioral law. Define native rewards Z by the cyclic singleton and
participant-pair rows

    Gamma_0=(0,-1,3,-1),       J_0=(0,-3/2,2,1/4).

Thus Z_i({j})=Gamma_ij and Z_i({i,j})=J_ij. Every nonparticipant in a pair
or triple receives T+1. Every participant in a triple or grand coalition
receives T. These rules specify all60 entries. Native own singletons vanish.
The opposite pairs02 and13 will be called favorites. All pair joining gaps
d=J-Gamma have cyclic first row(0,-1/2,-1,5/4), and all higher joining
differences equal-1.

Original rewards are r_i(S)=Z_i(S)+s_i on nonempty S, for arbitrary fixed
s_i>=0. The theorem gives ONE original uniform-equilibrium payoff target,
fixed before the accuracy, against ALL unilateral behavioral replacements.
In particular it covers r=Z+one. The stronger native conclusion is

    A_Z=inf{sum_i(B_i(P)-U_i(P)): P actual and absorbing}=0,       (A)

where U is prescribed terminal payoff and B_i is the full unilateral cap.
Literal native AllNever already has equilibrium payoff0; that alone would
not imply(A) or the stated conclusion for positive original own levels.

Write H=conv({0} union {Z(S):S nonempty}). Every coordinate of H is at
least-3/2. Coalition sums are1 on singletons,2T+3/4 on adjacent pairs,
2T+6 on favorites,4T+1 on triples, and4T on the grand coalition. For T>=0,

    H subset C={v: v_i>=-3/2 for every i, sum_i v_i>=0}.          (C)

The proof will produce a good root at every v in C with min v<=0.
We first prove the complete strategic implication of that finite claim.

## 2. Complete compact-payoff-domain argument

This argument applies to any finite four-player native table. Let K be a
compact set containing0 and invariant under every product prefix payoff map.
Assume every v in K with min v<=0 has a good root as defined below. We prove
(A), including the production of all required actual source points.

For a product prefix q, let the independent opponent quitter set for owner i
be A_i, and define literal reward expectations

    H_i=product_(j!=i)(1-q_j), h=product_i(1-q_i),
    Q_i=E[Z_i(A_i+i)], P_i=E[Z_i(A_i)1_(A_i nonempty)],
    E_i=q_i Q_i+(1-q_i)P_i, F_q(v)=E+h v.

For an actual profile write U_i for its prescribed payoff, B_i for its full
behavioral cap, nu for ORIGINAL joint Never, d_i=B_i-U_i>=0, and D=sum d_i.
The exact prefix recurrences are

    U'_i=E_i+h U_i,
    B'_i=max(Q_i,P_i+H_i B_i), nu'=h nu.                       (1)

There is only one live public history. Every complete behavioral replacement
disintegrates into finite first-Quit dates and Never, so(1) prices all
deviations, rather than only one-stage deviations. It also defines virtual
data initialized at U=B=v,nu=1. Such a virtual initialization is NOT asserted
to be realized by an actual profile. The identity

    d'_i=q_i(B'_i-Q_i)+(1-q_i)(B'_i-P_i-H_i B_i)+h d_i>=0       (2)

preserves nonnegative debt under arbitrary product prefixes. The U and B
maps are coordinatewise1-Lipschitz in their respective initial annotations,
uniformly over every finite word. Choose M>=1 bounding rewards and K; all
resulting payoff and cap coordinates remain bounded by M.

A root at v is a mixed Nash equilibrium of the finite game with choices
Quit,Continue and offers Q_i,P_i+H_i v_i. It uses only maximizing actions.
Prefixing such a root to U=B=v preserves zero debt. Call the root good if
some q_i=1 OR min_i F_q(v)_i<=0. Finite-game Nash existence gives a root;
the root graph and good-root graph are closed.

Every actual U lies in K. Indeed censoring all finite Quit dates after N
to Never gives a finite product word from0 whose payoff is in K, and the
censored payoff converges to U. Thus K also contains payoff projections
of actual-data closure points. Arbitrary positive-debt caps need not lie in K.

We prove a local assertion. Suppose v in K satisfies v>=0,min v=0 and
AllContinue is its ONLY good root. Write S={i:v_i=0}. For any positive
hazard bound and eta in(0,1), there are finite words of S-supported PRODUCT
prefixes below that bound, with survival in[1-eta,1-c] for a fixed c>0,
whose debt from U=B=v tends to0 and whose payoff minimum has limsup<=0.
The words may be approximate; they are not assumed to be exact Nash roots.
The proof is induction on |S|.

If Gamma_SS has a nonzero nonnegative kernel vector x, normalize sum x=1.
Repeat q=delta*x for floor(tau/delta) prefixes, where tau>0 is fixed and
sufficiently small and delta tends to0. For core owners, P_i=O(delta^2),
Q_i=O(delta),E_i=O(delta^2). Iterating(1) bounds every core payoff and cap
error by O(delta). Positive outsiders retain strict Continue buffers for
small tau, so their cap and payoff updates coincide. Survival tends to
exp(-tau) in(1-eta,1), proving the assertion, including singleton S.

Otherwise0 is outside the convex hull of the columns of Gamma_SS. Strict
separation supplies a signed row w with w Gamma_SS strictly positive in
every coordinate. For all sufficiently small S-supported product q,

    w E_S(q)>=gamma*sum_i q_i>=0                           (3)

for some gamma>0. Choose delta below this bound, the requested hazard
bound, and eta/16. Closedness of the good-root graph implies that all good
roots at nearby K-points with min<=0 are arbitrarily small; otherwise a
convergent subsequence would give a nonzero good root at v. At small roots
all formerly positive owners strictly Continue. Choose rho>0 so every
good root at such a point within rho of v is S-supported with hazards
below delta, and every formerly positive coordinate remains positive. Fix

    c0=min(eta/4,rho/(8M),1/4)>0.

For j in S and small t>0 the solo-j prefix payoff is
z=(1-t)v+t Gamma[:,j]. It lies in K, has z_j=0, satisfies ||z-v||<rho/4,
and w z_S=t w Gamma_Sj>0. Initialize virtual U=B=z,nu=1; these are not
the actual caps of that solo prefix. Take the compact closure of outputs
of ALL finite S-supported product words with hazards at most delta and
survival h>=1-eta. Minimize h on its nonempty closed subset

    B=U, min U<=0, w U_S>=h w z_S.                         (4)

The empty word is feasible, and every such U is in K. Every word obeys
||U-v||<=||z-v||+2M(1-h). If a minimum has h>1-c0, its U is within rho/2
of v. A nonzero good root there is small and S-supported. By(3) it
preserves zero debt, the nonpositive minimum and(4), while its new survival
is greater than(1-4delta)(1-c0)>1-eta and strictly smaller than h. This
contradicts minimality. Only good AllContinue can remain, so U>=0. Its
zero set S0 is nonempty and a proper subset of S, because w U_S>=h w z_S>0.

Apply induction at U with hazard bound delta and a survival budget eta1
small enough that h(1-eta1)>1-eta. Its arbitrary S0-supported words preserve
the ORIGINAL w inequality through(3). A compact endpoint has zero debt,
nonpositive minimum and strictly smaller survival in the same minimizing
set. Approximate the minimizing point by seed-generated words, append each
finite extension, and use continuity and the uniform Lipschitz bound.
Strict survival slack puts the endpoint in the original closure, again a
contradiction. Every seed minimum therefore has h<=1-c0. Let t tend to0
and apply its approximating words to v instead of z. Uniform Lipschitz
control gives debt tending to0 and limsup min U<=0, with survival at most
1-c0/2 eventually. This proves the local assertion with original survival
retained throughout; no conditional-tail reset has been made.

Now let C_actual be the compact closure of ALL actual data(U,B,nu).
Every finite product prefix acts continuously and preserves this closure.
For an actual profile move a smallest original marginal Never mass,
at most nu^(1/4), to a finite date. The profile becomes absorbing. All
four prescribed payoffs and the three other full caps change by at most
2M times that mass; its owner's cap is unchanged. Thus, also by closure,

    A_Z<=D+14M nu^(1/4).                                  (5)

Minimize nu on B=U,min U<=0 in C_actual. AllNever makes this set nonempty:
its native prescribed payoffs and all full caps are0. If A_Z>0, (5) makes
the minimum m positive. Its payoff/cap pair U=B=v belongs to K. A sure
good root would absorb with zero debt; a nonzero proper good root would
retain min U<=0 and lower Never. Both contradict(5) or minimality. Only
good AllContinue remains, so v>=0,min v=0. The local assertion, applied
through finite prefixes of the actual closure, gives a zero-debt endpoint
with nonpositive minimum and ORIGINAL Never at most m(1-c)<m. This final
contradiction proves(A).

For our table, K=H is compact, contains0 and is prefix invariant:
F_q(v) is a convex combination of v and the absorbing reward vectors.
The selector constructed next therefore verifies every hypothesis just
used. No actual continuation, full-cap certificate or favorable root is
an additional strategic input.

An absorbing prescribed profile gains s_i under a nonnegative recipient
row raise; any deviator gains at most s_i. Hence original regret is at
most native regret. Terminal approximate Nash profiles at every accuracy
select one fixed original uniform payoff by
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The full-cap recurrence corresponds to
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
Finite root existence is `exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`.
The domain argument and the raw selector below are ordinary mathematics;
these citations do not assert a new Lean certification of them.

## 3. Exact selector on the whole source region C


At proper odds(x,y,z,t), active indifference uses the following map,
independent of T:

    Phi0=-y/2-z+5t/4-yz-yt-zt-yzt,
    Phi1=5x/4-z/2-t-xz-xt-zt-xzt,
    Phi2=-x+5y/4-t/2-xy-xt-yt-xyt,
    Phi3=-x/2-y+5z/4-xy-xz-yz-xyz.

Active equations are Phi_i=v_i and quiet inequalities Phi_i<=v_i.
Indeed Q_i-P_i-H_i*v_i=H_i*(Phi_i-v_i), with Q_i,P_i the expectation
quantities defined above. An active output has the sign of its forced-Quit
odds numerator R_i;
a quiet output has the sign of P_i+v_i, with P_i now its odds numerator.
Call a root bad if it is proper and every output is positive.

When v>=0,min v<=0, AllContinue is good. Otherwise AllContinue is not
Nash. A singleton root is good by active output0; an adjacent pair root
is good by one negative participant payoff. Sure roots are good by
principle. Full proper roots are impossible because

    sum Phi=-sum odds/4-2sum pair products-sum triple products<0.

Nash existence therefore leaves only bad opposite pairs or triples.
Cyclic rotation reduces them to02 and012. The next two replacements
preserve the source annotation v and produce a good root.

### Bad triples supply their opposite pair

On012, high outputs require

    -3y/2+2z+Tyz>0, x/4-3z/2+Txz>0.

Write v=(-A,b,-B,d), where

    A=z+y/2+yz, B=x(1+y)-5y/4, b=5x/4-z/2-xz.

The source floor gives B<=3/2 and hence x<=3/2. The high inequalities
then give

    z<1/[4(1-T)]<=1/3, y<8/17,
    x>6z/(1+z), z>6y/(8+y).

Moreover x>9y/(2+7Ty), so B>0: its lower-bound numerator is
9(1+y)-(5/4)(2+7Ty)>0. Thus A,B are both in(0,3/2].

The opposite pair02 with odds(B,0,A,0) has the right active coordinates;
its quiet thresholds are

    F=5B/4-A/2-AB, G=-B/2+5A/4-AB.

The exact first difference is

    b-F=y[16xyz+8xy+32xz-12x-20yz-10y-12z+29]/16>=11y/16>0.

Indeed the bracket is affine in x on[0,3/2]. At x=3/2 it is
11+2y+36z+4yz; at x=0 it is at least875/51 on the stated y,z box.

For the other quiet coordinate, define

    P3=-x+3y-z+(T+1)(xy+xz+yz+xyz),
    Q_T=-P3-G, Hstar=A+B-b-G.

Badness gives d>-P3, while the source half-space gives d>=A+B-b.
It suffices to prove max(Q_T,Hstar)>0. Since Q_T decreases with T,
we can bound it below by Q_(1/4).

If y<=1/4, Q_(1/4) increases in x on the whole box: its derivative is
3/2+y^2/2+yz+y^2z-(y+z+yz)/4>=257/204>0. After replacing x by
6z/(1+z), its derivative in z is

    [19y^2z^2+38y^2z+7y^2+3yz^2+6yz-21y-7z^2-14z+35]
        /[4(1+z)^2]>0,

because the bracket is at least875/36 when y<=1/4,z<=1/3. Replacing z
by6y/(8+y) therefore gives the strict lower bound

    Q_(1/4)>y(1417y^3+78y^2-4596y+1184)/[8(y+8)(7y+8)]>0.

The last numerator is positive since1184-4596/4=35.

If y>=1/4, Hstar increases in x. At x=6z/(1+z) it becomes

    [(38y^2+84y+98)z^2+(9y^2+68y+14)z-5y^2-16y]/[8(1+z)],

which strictly increases in z. Hence

    Hstar>y(1417y^3+3768y^2+6300y-352)/[8(y+8)(7y+8)]>0,

because6300/4-352=1223. Thus d>G in both cases. The replacement pair
is Nash; if it is bad, apply the following replacement.

### Bad pairs have good replacements

At a bad02 pair the source is(-A,b,-B,d), A,B in(0,3/2], and
b>=F,d>=G. Its positive quiet outputs give

    b,d>K_T=A+B-(T+1)AB>=(A+B)/16>0.

Rotate by2 to arrange B>=A. Then
K_T-G=3B/2-A/4-TAB>=7B/8>0, so d>G.
For0<=t<=2B set

    x=(B-t/2)/(1+t), z=(A+5t/4)/(1+t), g(t)=-x/2+5z/4-xz.

The023 equations at owners0,2 hold identically, g(0)=G, and
 g(2B)=5z(2B)/4. If d<g(2B), continuity gives an interior t with g(t)=d.
The remaining quiet inequality follows from the unchanged exact identity

    Phi1=F-t[(28-8A)B+9t+18]/[8(1+t)]<F<=b.

This triple is good. Otherwise positive R2=2x-3t/2+Txt would imply

    2B+(TB-5/2)t-(3/2+T/2)t^2>0,
    t<2B/(5/2-TB)<=16B/17.

But z<=3/2 and positive R3=-3x/2+z/4+Txz imply z>(9/2)x.
Since A<=B, the fiber formulas then imply t>B, a contradiction.

If d>=g(2B), use adjacent pair23 with odds z=4d/5,t=2B. The two active
coordinates are correct. The first quiet inequality Phi0<=-A is exactly
d>=g(2B); the other is Phi1=-z/2-t-zt<0<b. This pair is good because
R2=-3t/2<0. Equality at the endpoint is included.


## 4. Boundary tests: stationarity and short-support periodic play

Every result in this section holds for EVERY fixed T>=0, evaluating the
same literal table also outside the proved UE interval. These architectural
obstructions do not imply a positive debt gap over unrestricted profiles.

There is no sure root at any annotation. With at least three sure owners,
a sure owner has joining gap-1. With exactly two, one has a negative
reciprocal pair gap and only negative higher gaps. With one sure owner h,
every other owner except h+1 has negative conditional gap and must be
quiet. Owner h+1 then has gap5/4 and must also be sure, a contradiction.
All these comparisons face a sure opponent and are annotation-independent.

### A strict gap for all original stationary profiles


For a proper stationary support define opponent odds numerators R_i,P_i
for forced Quit and passive rewards, and D_i=product_{j!=i}(1+z_j).
Every active owner must satisfy

    E_i=(D_i-1)R_i-D_i P_i=0.

Sure profiles were excluded above. A singleton h is defeated by h+1,
whose Never payoff is -1 and immediate Quit payoff q_h/4>0. On an
adjacent pair the positive participant has E=z(1+5z/4)>0. On a favorite
pair either owner has E=z(-3-z)<0. Thus no nonzero stationary pair exists.

Every triple is a cyclic copy of012. There

    E0=y-y^2/2-3z-z^2-(T+5/2)yz-(3/2)y^2z-2yz^2-y^2z^2,
    E1=x+z+5x^2/4-z^2/2+x^2z/4-3xz^2/2
                                  -(T+1/4)xz-x^2z^2.

E0=0 implies3z<y-y^2/2<=1/2, so z<1/6. But

    4(yE1-xE0)=x^2y(5+z-4z^2)+2yz(2-z)
       +xy^2(4z^2+6z+2)+xyz(2z+9)+4xz(z+3)>0.

For full support let C(m) sum the DISTINCT cyclic rotations of monomial m.
The complete positive identity is

    -4 sum E_i=4C(x)+C(x^2)+(13+8T)C(xy)
      +7C(xy^2)+14C(x^2y)+8C(x^2y^2)
      +(2+8T)C(xz)+5C(xz^2)+(17+4T)C(xyz)
      +7C(xyz^2)+16C(xy^2z)+14C(x^2yz)
      +8C(xy^2z^2)+8C(x^2yz^2)+8C(x^2y^2z)
      +8C(x^2z^2)+4C(x^2y^2z^2)>0.

It follows by expanding and rotating
D0=(1+y)(1+z)(1+t), W0=yz+yt+zt+yzt,
R0=-3y/2+2z+t/4+T W0, P0=-y+3z-t+(T+1)W0,
E0=D0(R0-P0)-R0. All74 coefficients, also counting T as a variable,
are positive integers. Thus every nonzero stationary support is excluded.

The exclusion includes approximation. At a nonzero limiting hazard the
prescribed stationary payoff is continuous. Full caps are lower
semicontinuous, being suprema of continuous finite-deadline responses.
Vanishing debt would therefore give an excluded stationary Nash profile.
At zero hazards normalize to p=q/sum q. The limiting payoff is w=Gamma p;
immediate Quit gives w>=0. A singleton p is impossible because its column
has negative entries. For p_i<1 the Never response tends to w_i/(1-p_i),
forcing p_i w_i=0. But

    Gamma inverse=(1/15)[2,3,7,3;3,2,3,7;7,3,2,3;3,7,3,2]>0.

If w!=0 then p is strictly positive and complementarity forces w=0;
if w=0 then p=0. Both contradict sum p=1. Hence nonzero native stationary
debt has a strictly positive infimum for each fixed T. Every nonzero stationary profile absorbs. Its prescribed payoff in Z+1
increases by1; every finite-deadline payoff does too. Native Never is a
limit of finite deadlines, so full original caps also increase by1.
Their regrets are identical. Original AllNever has total debt4. Therefore
Z+1 has a strict gap over ALL stationary profiles.
No uniform lower bound over unbounded T is asserted.


### Exact periodic play needs a triple phase


Suppose a nontrivial finite periodic product profile were exact native
Nash. The same applies to an original Z+1 equilibrium, since every such
prescribed profile absorbs and its native/original debts agree as above.
It absorbs almost surely; its native phase payoffs have nonnegative sum.
Every reached phase satisfies Nash with the actual prescribed continuation.
The sure-root exclusion makes every hazard proper, so every phase is
reached with positive probability. Delete idle phases. A proper full phase
would have its actual continuation equal Phi, contradicting sum Phi<0.
It remains to exclude calendars using only singleton and pair phases.

After a proper favorite02 phase, active indifference requires

    v0=-q2/(1-q2)<0, v2=-q0/(1-q0)<0.

Every singleton offers one of owners0,2 a nonnegative Quit payoff. Same02
offers both positive payoffs. On01 or23 the opposite anchor has a strictly
positive Quit offer; on12 or03 an active anchor has a strictly positive
Quit offer. (The extra T terms are nonnegative.) Thus the only next pair
or singleton support is favorite13. Rotation gives13->02. Once a favorite
is reached, periodicity forces the entire calendar into favorite alternation.

After an adjacent01 phase, the required labels are
v0=-(1/2)q1/(1-q1)<0 and v1=(5/4)q0/(1-q0)>0.
The negative label forces owner1 to be active at the next phase; otherwise
owner0 has a nonnegative Quit offer. Solo1 and pair12 make owner1's value
nonpositive. Only same01 or favorite13 remain. A favorite cannot return
to an adjacent pair without a triple. Therefore an adjacent-only periodic
calendar must repeat the same pair. But its positive owner's next value
is more than five times its current value q0/4, impossible around a cycle.

For favorite alternation let the hazards at phase n be a_n,b_n>0, and put
s_n=a_n+b_n,p_n=a_n b_n,h_n=(1-a_n)(1-b_n),
k_n=-s_n+(T+3)p_n, f(r)=r/(1-r). Passive recursion and the preceding
pair's indifference give, up to exchanging coordinates,

    -f(a_(n-1))=k_n+2h_n a_(n+1),
    -f(b_(n-1))=k_n+2h_n b_(n+1).                    (*)

Choose the largest hazard x in the finite period. Since T>=0,
-f(x)>min_{0<=y,z<=x}(-y-z+3yz)=min(-x,-2x+3x^2).
If x>=1/3 this contradicts f(x)>x. Otherwise f(x)<2x-3x^2.
The inequality4x(1-x)<=1 gives f(x)>=4x^2, hence x<2/7 and
every h_n>25/49>1/2. Summing(*) yields

    sum_n[f(a_n)+f(b_n)]+2 sum_n h_n s_(n+1)
                    =2 sum_n s_n-2(T+3) sum_n p_n.

The left side exceeds2 sum s_n and the right side is smaller. This rules
out every finite favorite-only period, with unequal hazards and any length.

Finally suppose every phase is solo. After solo i the required coordinate
i is zero. If j is the next distinct owner, Nash at its first phase gives
q_j J_ij<=0, forcing j=i+1. A one-owner calendar is defeated by its
successor. Otherwise the distinct-owner blocks follow the whole cycle.
At the last solo(i-1) phase before the next solo i block, owner i's
prescribed value is -q_(i-1), because its following value is zero.
Quitting instead gives q_(i-1)/4>0. This final contradiction exhausts
all calendars of supports at most two. Triple phases are necessary.

This is an exact finite-period obstruction. No maximum over an infinite
calendar or bound away from zero on its hazards has been assumed.


## 5. Strict comparison with earlier explicit raw admissions

It suffices to compare the ORIGINAL table r=Z+one at T=0. All failures
below persist under every owner permutation and positive recipient scale.
This is a comparison of complete explicit raw tests, not merely of their
published example tables; the compact-domain consumer itself remains usable.

Reciprocal singleton signs agree, each row has one positive singleton entry,
and positive singleton pairs are exactly02,13. Joining gaps on favorites
are(-1,-1), and on adjacent pairs(-1/2,5/4): no pair has both nonnegative.
Every owner has a negative participant pair-3/2 and positive favorite2;
no pair is mutually negative. Thus premium peeling, protected owners,
proper premium-core reductions, opposed-singleton/cyclic-child entrances,
positive-joining matching criteria and negative favorite-pair templates fail.
The singleton matrix has det45 and inverse

    Gamma^(-1)=(1/15)[2,3,7,3;3,2,3,7;7,3,2,3;3,7,3,2]>0.

It is R0: if Gamma x=y>=0,x>=0,x_i y_i=0, a nonzero y would make x>>0,
a contradiction, while y=0 gives x=0. At offset -one the only complementary
solution is x=one, with index+1. This excludes negative-degree/determinant
inverse exits. Every principal triple inverse has a negative diagonal;
on012 it is

    [-1/6,-1/2,1/6; -1/2,-3/2,-1/2; 1/6,-1/2,-1/6].

The projective complementary-offset test also fails there at offset -one:
singletons fail their zero diagonal, negative pairs require negative active
values, the positive pair has outside value-2/3<1, and the full solution is
(-1/2,-5/2,-1/2). Pair and triple principal nonsingularity and negative
outside singleton entries exclude a nonzero homogeneous branch.

At common odds u>0 all forced-Quit numerators are3u/4, while

    Phi_i=-u/4-3u^2-u^3,
    det D Phi=(1/4+3h)(7/4-h)[(1+h)^2+49/16], h=2u+u^2.

For small u the full root is high and has positive index. Thus full Low,
Upper and negative Orientation fail. At every positive charge weight lambda,
the four singleton charge coefficients sum to(3/4)sum lambda>0, so full
Charge fails. This defeats all old supportwise Low/Upper/Charge/Orientation
assignments. The paired-support option still requires an unpaired full
support gate, and its triple also requires a positive participant triple
entry, absent here. Shared-anchor rectangles require one sole mutual-positive
participant pair, whereas there are two; their positive-depth capture also
fails on the full high sources tending to0.

On012 use odds delta*(7,1,1). Then

    R=(delta/2,delta/4,57delta/4),
    Phi=(-3delta/2-delta^2,33delta/4-7delta^2,-23delta/4-7delta^2),
    det D Phi=-(1+delta)(224delta^2-96delta+29)/16<0.

Set the quiet source coordinate to10delta. For0<delta<=1/100 this source
is in H: its positive singleton convex weights are

    Gamma^(-1)v=(delta/60)(46,259,131,224)
                     -(delta^2/15)(72,38,42,73),

summing to11delta-15delta^2<1; put the remainder on Never. This negative-input
source defeats projected-hull individual weak orientation. Every open
first-action kernel collar also contains the symmetric full sources above,
since0 satisfies its first-action inequalities via AllContinue. Thus that
open individual-orientation test fails, even if the kernel is refined while
retaining0. A conditional compact-domain consumer is not a previous raw
admission: this packet produces its previously missing selector.

Equal-weight whole-payoff and joining ledger signs pass, but their remaining
premises fail. Every nonzero w>=0 with w Gamma>=0 is strictly positive by
Gamma inverse positivity. Hence every support-filtered ledger in any finite
family has full support and inherits the failed proper product-low test.
Rotating the high triple above meets every nonempty marked set; its original
annotations1+Phi are positive and above all permitted unmarked floors<=0,
so marked proper orientation fails too. In an ordered marked-block test,
the first block meeting a favorite pair has strictly positive participant
sum. No marks, order or positive block weights fix this. Global inserted-floor
weights require w_(j+1)>=6w_j around the cycle, forcing w=0; inserted-upper
weights fail since their singleton coefficients sum to3(sum w)/4.
For arbitrary positive-matrix coalition or product-cover cones, Z(I\{i})=e_i
forces their outside guard eta>=P_ii/(sum_k P_ki)>=rho, while their parameter
guard requires eta<rho, or eta<rho_star<=rho. Here rho is the minimum of
ALL positive entry-to-column-sum ratios P_ij/(sum_k P_kj), so each displayed
diagonal ratio is at least rho. No positive matrix or cover works.

Every universal quiet-child extension fails. In any proper nonempty child,
choose retained h with successor h+1 omitted. Sole-h sure stopping is exact
absorbing child Nash: all retained nonowners have negative joining gaps.
Child debts and Never are0, but omitted h+1 gains5/4 by joining. No finite
weights, security floors or Never price repair a child-debt-plus-Never bound.
For singleton persistent base h, induced Nash and outsider no-join force
h+1 sure and other nonowners quiet. Owner h then gains1/2 by leaving
(native Quit gives-3/2, Continue gives-1), and opponents' survival is0. No punishment
cap repairs this. Larger bases contain a member with a negative conditional
leave gap of magnitude at least1/2. Thus every base/free/induced-root/cap
selection and its raw arbitrary-completion subclasses fail.

The stationary proof excludes ALL stationary-output producers, including
signed/boundary inverse columns, coalition bonuses, polynomial row weights,
collision-dominance, conditional faces and odd-blocker outputs. Literal
odd-blocker passive equalities also fail because each row has both-1 and3.
The exact finite-period proof excludes every promised exact calendar with
phase supports at most two, at every period and hazard choice. It is not
used against diffuse approximate or larger-support calendars.

The signed solo/triple entrance, in roles(r,j,k,o), solves
[ J_rk,J_rj; Gamma_rk,Gamma_rj ](u,v)=(-Z_r(rjk),-Z_r(jk)).
Up to cyclic rotation its three unordered choices give
(-3/5,-4/5),(6/7,1/7),(8/11,-1/11); swapping j,k swaps u,v. The sole
positive case has hazards7/13,7/8 and requires
1077b^2-5339b+4280=0 on(0,1), impossible since the polynomial decreases
to18 on[0,1]. This exhausts all24 roles. Three-owner joint return requires
Gamma03>0,Gamma23<0,Z2(23)>0, leaving four cyclic roles. In one representative
its e=Gamma32=-1,d=-Gamma30=-3,w=Z3(02)=1,v=Z3(23)=-3/2,
a3=Z3(03)=2,t3=Z3(023)=0,omega=w+d-e=-1. Its necessary root
b=-(e*a3+d*v)/[e*(t3-a3)-(omega+e)*v] is5/2, not in(0,1).
Recipient scales cancel from both role computations.

Fixed collision, wedge, cyclic-child and diffuse-flow families require an
opposed reciprocal singleton pair or two positive singleton entries in one
row. Funded/mixed-passive pair entrances require a positive joining gap on
a positive singleton pair. Neither occurs. Four-solo/mixed-pair caps fail
on positive crossing or favorite premiums; below-singleton phases require
two negative scheduled premiums, absent here. Their qualitative below-own
variant requires those same signs. The positive-gain toggle cycle
0->01->1->12->2->23->3->03->0 excludes an ordinal toggle potential: adding
the successor gains5/4, and removing its predecessor gains1/2, at every step.
The componentwise affine potential condition also fails: row0's gap against
opponents12 is-1, whereas its original own level and singleton gaps predict-5/2.

Spectral/Jordan/crossing literal families have no negative participant pair;
passive/ten-phase families have a negative favorite pair. The three-parameter
passive family and its explicit tiny tube retain unequal negative singleton
comparisons in each row, unlike T0 under any permitted recipient scale.
The paid-return visible cube requires Gamma_ij>0 and d_ij>0 in one visible
pair; here positive Gamma implies d=-1. Earlier balanced and candidate
singleton fibers have opposed/zero signs; the integer period-three center
has two positives in some row. The E1 visible-affine box has favorite
|J/Gamma|<10^(-7), versus2/3 here. Its generic interval-face verification
interface requires supplied boxes and is not a raw arbitrary-table producer.

This comparison exhausts the prior explicit raw conditions and all their
finite roles and continuous proof parameters. Source reductions, and compilers
requiring supplied roots, boxes, child laws or potentials, are not automatic
admissions. An unspecified continuity neighborhood is not a certified T0
membership test; no claim about its maximal continuation domain or every
longer-period architecture is made. The proof establishes the complete
interval0<=T<=1/4 through global payoff geometry. It does not provide an
exact stationary or finite-periodic witness, or settle arbitrary Fin4.

## 6. Implemented source correspondence and Lean handoff

The semantic dependencies and their exact files are stated in Section2.
The implementation-overlap checks in Section5 correspond in particular to
these existing definitions and theorems; their hypotheses are tested by the
explicit reward calculations above, rather than inferred from file labels:

* `HasSupportwiseQuittingPremiumBalanceAt` in
  `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumBalanceAt.lean`,
  and `HasProtectedParticipantPremiums`, `HasSupportSpecificQuittingLeavers` in
  `UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`
  are the participant-weight and protected/leaver tests. Weights fail on
  favorites; every nonempty protected set fails on a negative adjacent
  participant entry, while the empty set fails the favorite-trap leaver test.
* `HasWeightedQuittingTrapLeavers` in
  `UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`
  includes the inserted-premium conditions; passing whole-payoff ledger signs
  does not imply these stronger hypotheses.
* `exists_uniformEquilibriumPayoff_of_pairPremiumCore_weakLeave` in
  `UniformEquilibrium/Quitting/Classification/Existence/QuittingPremiumCoreUniformPayoff.lean`
  needs a proper pair core; the present premium core is all four owners.
* `exists_stationary_uniformEquilibriumPayoff_of_participantOnly` in
  `UniformEquilibrium/Quitting/Classification/Existence/ParticipantOnlyStationary.lean`
  and `quittingGame_exists_uniformPayoff_of_componentwiseWeightedPotential` in
  `UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`
  have stationary outputs, independently excluded by Section4.
* `quietLift_gain_gt_weighted_childDebt_add_never_of_exact_child` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/PureAbsorbingChildDebtObstruction.lean`
  is precisely the universal-child obstruction instantiated in Section5.
* `quittingSingletonBaseOwnerFloorExcess_nonpos_iff` and
  `quittingPersistentLargeBaseExcess_nonpos_iff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
  expose the failed base-leave gates. Their semantic consumer is
  `exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.
* `integerTableTarget_isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockIntegerTablePeriodThree.lean`
  applies to its literal integer table; the singleton signs differ here.
* `exists_periodThreeClearedGapData_and_uniformPayoff_of_visible_affine_reward` in
  `UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreePositiveAffineCylinder.lean`
  is the visible-affine cylinder excluded by the favorite-premium ratio.

For formalization, define the literal parameterized native reward table and
the polyhedral region C from Section1. The first new theorem should produce
a good root for every0<=T<=1/4 and every v in C with min v<=0. Its proof
needs the finite support split, the explicit triple-to-pair inequalities,
the two cubic bounds, and the pair-to-triple/adjacent-pair replacements.
All divisions have their positive denominators displayed; endpoint equality
must use the adjacent-pair branch.

A separate compact-domain theorem should take the exact prefix recurrences,
compact prefix-invariant K containing0, and a good-root theorem on its
singleton sublevel. Its conclusion is absorbing full-debt infimum zero.
Its local lemma must PRODUCE arbitrary finite product words with vanishing
debt and strict original-survival loss, through zero-set induction; it must
not assume that descent or an actual virtual-seed realization as a field.
Instantiate it with the literal reward hull, then apply the existing fixed
uniform-payoff endpoint. Narrow finite checks are the displayed polynomial
identities, the74-coefficient stationary identity, and the exact role solves.
These proofs are ordinary mathematics, not newly checked Lean declarations
or an assertion of arbitrary Fin4 closure.
