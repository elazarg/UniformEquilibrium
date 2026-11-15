# Cyclic two-matching games: a concrete unresolved construction target

Status: internal research, not an export or a counterexample. For every fixed
T>=0 the family below has a strict stationary gap after raising own levels
to one. Moreover every nontrivial exact finite periodic equilibrium, if one
exists, must use a triple phase. The native AllNever profile already gives
native UE0; the unresolved issue is absorbing native debt zero, or UE for
the original table Z+1. T=0 is the immediate construction target.

The old-admission checks below are PARTIAL. Nonnegative coalition sums do
not establish a complete old UE admission. No positive least-Never value,
positive unrestricted exploitability gap, or necessity of periodic play is
claimed. Exact periodic exclusions do not exclude approximate, diffuse or
nonperiodic constructions.

## 1. Complete raw family and actual semantics

There are four owners, indexed modulo four, with independent private
Continue/Quit behavior and unrestricted unilateral behavioral deviations.
The first nonempty quitter coalition receives the finite table reward;
live and Never reward are zero. Define native singleton rows by

    Gamma=[0,-1,3,-1;-1,0,-1,3;3,-1,0,-1;-1,3,-1,0].

The participant-pair matrix J is circulant with first row(0,-3/2,2,1/4):
J_ij=Z_i({i,j}). Every nonparticipant pair or triple reward is T+1;
every participant triple and every grand reward is T. Together with
Z_i({j})=Gamma_ij these rules specify all60 entries. Original rewards
in the main target are r_i(S)=Z_i(S)+1 on nonempty coalitions only.

Pair joining differences d=J-Gamma have first row(0,-1/2,-1,5/4);
every higher joining difference is -1. The opposite pairs02 and13 are
called favorites. All native coalition reward sums are nonnegative:
singletons1, adjacent pairs2T+3/4, favorites2T+6, triples4T+1, grand4T.
Thus every actual native prescribed payoff has nonnegative coordinate sum.

For an actual profile let U be its native prescribed payoff, B its full
unilateral cap, and nu its joint Never probability. Total debt is
D=sum_i(B_i-U_i). Let A_Z be its infimum over absorbing profiles.
Finite-deadline and Never deviations determine B because there is only
one live public history. Native own singleton zero makes each Never
response a limit of finite deadlines. Hence every nonzero stationary
profile has the same debt in Z and Z+1: it absorbs, and all its payoffs
and full caps increase by one. Original AllNever instead has total debt4.

## 2. Exact auxiliary geometry near actual AllNever

With odds(x,y,z,t), proper active indifference requires continuation Phi,
whose coordinates are

    Phi0=-y/2-z+5t/4-yz-yt-zt-yzt,
    Phi1=5x/4-z/2-t-xz-xt-zt-xzt,
    Phi2=-x+5y/4-t/2-xy-xt-yt-xyt,
    Phi3=-x/2-y+5z/4-xy-xz-yz-xyz.

These maps are independent of T. No sure Nash root exists at ANY
annotation. With at least three sure owners a sure owner has joining gap
-1. With exactly two, one has a negative reciprocal pair gap and only
negative higher gaps. With one sure owner h, every other owner except
h+1 has negative conditional gap and must be quiet. Owner h+1 then has
gap5/4 and must also be sure, a contradiction.

At annotation0, singletons are blocked by their cyclic successor; pairs
cannot solve the two zero joining equations. Every triple has an owner
whose sole positive joining opponent is absent. Full support is excluded by

    sum Phi=-(x+y+z+t)/4-2(xy+xz+xt+yz+yt+zt)
               -(xyz+xyt+xzt+yzt)<0.

Thus AllContinue is the unique root at0. Native AllNever is actual full-law
Nash with U=B=0,nu=1. Nevertheless at v=-epsilon*one,0<epsilon<=1/1000,
the unique Nash root is full with common odds u determined by

    u/4+3u^2+u^3=epsilon, 0<u<4epsilon.

The only candidate pairs02/13 have both odds epsilon; a quiet owner has
Phi=3epsilon/4-epsilon^2>-epsilon. On012 the active equations would give
y/2+z+yz=epsilon and x(5/4-z)=z/2-epsilon, impossible. Rotation handles
all triples. For a full root the sum identity bounds each odds by16epsilon.
Opposite-coordinate differences form an invertible two-by-two system,
forcing x=z,y=t. The remaining difference is
(x-y)(-7/4+x+y+xy)=0; smallness forces equality of all four odds.

Every active Quit numerator is R=u[3/4+T(3u+u^2)]>0. Writing h=2u+u^2,

    det D Phi=(1/4+3h)(7/4-h)[(1+h)^2+49/16]>0.

Consequently these sources have only a proper, positive-output root of
positive index. A good-root neighborhood of actual AllNever fails, but
AllNever has not been shown to minimize original Never on the actual
zero-debt carrier. That missing minimum claim is decisive.

## 3. Strict stationary gap for every fixed T>=0

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
debt has a strictly positive infimum for each fixed T. By the row-raise
observation, original Z+1 has a strict gap over ALL stationary profiles.
No uniform lower bound over unbounded T is asserted.

## 4. Every exact finite periodic equilibrium needs a triple phase

Suppose a nontrivial finite periodic product profile were exact Nash.
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

## 5. Partial T0 admission audit: no complete old admission yet

The positive coalition sums verify H>=0, and all-one inserted joining
sums are -1/4 on singletons,-2 on pairs,-1 on triples. These are only
PART of the hypotheses in the old ledger producers. For012, odds
delta*(7,1,1) have active numerators delta*(1/2,1/4,57/4)>0 and

    det D Phi012=-(delta+1)(224delta^2-96delta+29)/16<0.

The positive ambient triple index defeats higher-support product-lowness
and marked proper orientation, for every marked selection by rotation.
Small annotations lie above every allowed passive floor. Singleton H
inequalities plus Gamma inverse positive force any ledger weight to have
full support, so sparse or multiple support-filtered ledgers do not repair
the missing proper-support premise.

Full Low and negative Orientation fail at the symmetric small full root.
For arbitrary positive recipient scales lambda, full-charge singleton
coefficients sum to(3/4)sum lambda>0, so they cannot all be negative.
The frozen sole-anchor rectangle requires one mutual-positive pair, but
this game has two. Every positive-depth capture chart also fails because
the symmetric full high annotations approach zero.

Both new payoff-domain tests fail. Every open first-action collar contains
the all-bad sources near actual AllNever. For the hull test complete the
triple annotation above with v3=10delta. Then

    Gamma inverse v=(delta/60)(46,259,131,224)
                         -(delta^2/15)(72,38,42,73)>0

for0<delta<=1/100, and its sum11delta-15delta^2<1. These are singleton
hull weights, with the remainder on Never. The active triple has positive
index at a negative-input source in the hull, so projected-hull orientation
fails. This does not imply failure of either theorem's conclusion.

Complete signed solo/triple role enumeration reduces by cyclic symmetry
to r=0 and(j,k)=(1,2),(1,3),(2,3), giving
(u,v)=(-3/5,-4/5),(6/7,1/7),(8/11,-1/11). Only the middle case survives;
its hazards7/13,7/8 require1077b^2-5339b+4280=0. This polynomial decreases
on[0,1] and equals18 at1, so all24 roles fail. The broader three-owner
joint-return entrance has four cyclic survivors, each forcing b=5/2.
Positive recipient scales do not change either failure.

Reciprocal singleton signs rule out the opposite-sign singleton/core
entrances. Every matching has a negative joining gap, excluding the
positive-joining two-pair and invariant-cone entrances. Every crossing
pair has a positive participant entry, excluding the old four-solo raw
caps; the stronger periodic theorem above excludes that architecture
without restricting its period. These are checks of the stated families,
not an exhaustive census of all old producers or maximal neighborhoods.

## 6. Next concrete task

Construct actual absorbing approximate equilibria for T0, starting with
calendars that mix triple phases with adjacent or favorite pairs. Any exact
finite-period candidate must pass EVERY quiet-owner comparison and price
the complete deviation cap. Alternatively find a global actual-source
descent that resolves the remaining triple interactions. The meaningful
negative alternative is a positive gap over all behavioral profiles;
failure of stationary or finite-controller searches is insufficient.
