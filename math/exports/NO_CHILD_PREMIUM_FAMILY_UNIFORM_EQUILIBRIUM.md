# Uniform equilibrium on the entire cyclic premium family and unbounded raw completions

## 1. Raw tables and exact conclusions

Players are0,1,2,3. At the unique live state each privately chooses Continue
or Quit. The first nonempty quitter coalition D absorbs at its reward;
live play and literal AllNever pay zero. Prescribed randomization is private
and independent. Deviations may replace one player's entire behavioral
strategy, with no restriction on dates or private randomization.

Write O={0,1,3}. Define the canonical native table Z^M, for any real M, by

    Gamma=[0,-1,-1,2; -1,0,1,1; 1,2,0,-1; 1,-1,1,0],
    J(M)=[0,-5,M-1,-5; M-1,0,-5,-5;
          -5,-5,0,M-1; -5,M-1,-5,0].

Singleton rewards are Z_i({j})=Gamma_ij, including own singleton0.
Participant rewards in a pair{i,j} are J_ij. Every passive nonsingleton
reward is0. Every participant reward in a coalition of size at least3 is-5.
These rules specify all60 native coordinates.

For M>=11 allow the following broader raw class Z. Keep Gamma fixed and,
for observers i in O and coalitions D contained in O, keep Z_i(D)=Z_i^M(D).
The remaining nonsingleton coordinates obey:

1. Z0(02), Z1(12) are arbitrary finite real numbers; Z3(23)<=1.
2. For every observer i, all rewards on coalitions containing2 other than
   singleton2 and own pair{i,2} are arbitrary finite real numbers. There
   are eighteen such coordinates.
3. For D=01,03,13,013 put delta_D=Z2(D). These four numbers are arbitrary
   nonnegative finite numbers.
4. Z2(02)<=-5, Z2(12)<=-5, Z2(23)<=M-1.
5. For D=01,03,13,013, require Z2(D union{2})<=delta_D-5.

Thus32 nonsingleton coordinates vary under explicit unrestricted or
one-sided raw conditions; no strategy or return is a class hypothesis.
All rewards are finite, with no common magnitude bound across the class.
Put B=max(2,delta_01,delta_03,delta_13,delta_013).

**Theorem.** For every such Z with M>=11 there are actual finite independent
hazard profiles followed by Never whose four full native unilateral debts
and EACH player's marginal Never probability tend to zero. Their payoffs
have a subsequence converging to b_*e2, with b_* in[3/16,B]. Consequently
its augmented native semantic carrier contains an absorbing full Nash point;
its absorbing observer-exact pivot minimum is zero.

For arbitrary real row offsets kappa_i and positive row scales sigma_i,
the absorbing rewards

    r_i(D)=kappa_i+sigma_i Z_i(D), live/Never0,

have uniform-equilibrium payoff kappa+sigma_2 b_*e2. The target is fixed
before accuracy. For every positive accuracy one actual private behavioral
profile delivers the target within that accuracy and bounds every unilateral behavioral deviation
on every sufficiently long finite horizon.

**Canonical corollary.** The table r=4+Z^M has a uniform equilibrium for
EVERY real M. For M>=11 the theorem supplies a target(4,4,4+b_*,4), with
b_* in[3/16,2]. Section8 supplies the remaining M<=11. The arbitrary signed
row-offset conclusion above is asserted only in the M>=11 raw class.

## 2. Finite proxy words and actual behavioral caps

At a proper root let q_i<1 be the independent quit probabilities,
x_i=q_i/(1-q_i), H_i=prod_(j!=i)(1-q_j), and c=prod_i(1-q_i).
Let P_i be the passive expected absorption reward from opponents quitting
while i Continues, and Q_i the immediate-Quit reward. A finite root word
with terminal payoff annotation u and response-cap annotation v has recursion

    u'_i=q_i Q_i+(1-q_i)P_i+c u_i,
    v'_i=max(Q_i,P_i+H_i v_i).                            (1)

The cap prices every complete quitting deadline in the word and continuation
to the terminal annotation. Mixing complete responses cannot improve their
maximum. Along the unique live history, fixing a player's private random
bits determines such a deadline or Never; thus these are full behavioral
caps. The annotations need not represent an actual continuation.

For zero own singleton rewards define C_i=(Q_i-P_i)/H_i. A diagonal
annotation u=v stays diagonal exactly when

    C_i<=v_i, with equality whenever x_i>0.               (2)

At such a root v'_i=H_i(v_i+P_i/H_i), including quiet players. The maps in(1)
are separately1-Lipschitz in their terminal annotations for the sup norm;
finite compositions are also1-Lipschitz. The cap map is monotone.

For a fixed diagonal seed v take the closure of all finite-word tuples
(U,full cap,N0,N1,N2,N3) with terminal annotation(v,v), terminal survivals1.
It is compact: payoffs and caps lie between finite reward/annotation bounds.
Every fixed finite prefix preserves this closure continuously. Hence a
sequence of exact Nash prefixes whose annotations and marginal survivals
converge has its diagonal limit in the same closure. Further prefix phases
may begin at that point. This is finite-word approximation, never execution
of a continuation after infinitely many physical dates. Approximants retain
both payoff and full cap; they need not be exactly Nash at phase switches.
All constructions below are in backward prefix order.

## 3. An explicit prefix from every positive pivot seed

Take b>=1/10 and start at diagonal seed b e2. Only singleton or O-supported
roots will be used. Therefore the eighteen coordinates in item2 never enter
any prescribed payoff or any unilateral deviator's own payoff: at an O root
an observer deviator's coalition is contained in O, and at a singleton root j the
only additional coalition relevant to deviator i is{i,j}.

First use only owner3, with odds x=v2/M. Its quiet increments for observers0,1
are-7,-6; the pivot increment is at most M. Its target coordinate follows
v2'=(M-1)v2/(M+v2), tending to zero. The phase limit is

    (2b,b,0,0)/(1+b), owner3 survival1/(1+b).

Next use only owner2, putting

    K=2+max(0,Z0(02)+1,2*(Z1(12)-1)), x=v0/K.

Quiet0 is priced by K>Z0(02)+1. Throughout this phase v1/v0>=1/2, so
quiet1 is priced by K>2*(Z1(12)-1). The quiet3 increment is Z3(23)-1<=0.
All coordinates stay nonnegative, v0 follows(K-1)v0/(K+v0), and the limit is

    (0,3b,0,2b)/(1+3b), owner2 survival(1+b)/(1+3b).

Use only owner0 with x=v1/M. Its quiet observer1 increment is M; its other
quiet increments are nonpositive. The target recurrence is again geometric,
and the limit is

    (0,0,3c0,5c0), c0=b/(1+6b),
    owner0 survival(1+3b)/(1+6b).

These affine phase endpoints depend on singleton rewards, not on phase speed.
Their combined survival is1/(1+6b). Their limits and switches are justified
by Section2.

After owner1 cumulative quit probability p, its value vector is

    (-p,0,3c0+(2-3c0)p,5c0-(1+5c0)p).

The next owner1 odds x are legal exactly when

    p/4<=x<=[5c0-(1+5c0)p]/M.

The pivot comparison is automatic because its joining increment is at most-7
and its continuation is positive. The lower bound expressly prices negative
observer0 caps. For y=p/(1-p), the minimal odds p/4 send y to(5/4)y. The
lower and upper bounds agree at

    p*=20c0/(M+4+20c0), y*=20c0/(M+4).

Take first odds(4/5)^7 y*, seven minimal-odds roots to reach y*, and one
further minimal-odds root at p*. The first is admissible because
(4/5)^7<1/4<(M+4)/(4M); all later roots are admissible by p<=p*.
There are exactly nine atoms. Their final cumulative probability is
25c0/(M+4+25c0). The complete prefix therefore reaches

    lambda(-25,0,3M+62,5M-5),
    lambda=b/[(M+4)+(6M+49)b].                            (3)

Its joint survival is at most theta=5/8, and its marginal survivals obey

    N3<=10/11, N2<=11/13, N0<=13/16,
    N1<=16(M+4)/(16M+89)<1.                              (4)

Indeed the exact owner1 survival is(M+4)/(M+4+25c0); c0>=1/16. These
bounds hold uniformly over every b>=1/10 for each fixed finite M.

## 4. A complete observer process with supports01 and013

Write observer odds as(a,t,z), in order0,1,3. Their fixed singleton matrix
and joining polynomials are

    G=[[0,-1,2],[-1,0,1],[1,-1,0]],
    C0=-4t-7z-5tz,
    C1=(M-5z)a-6z,
    C3=Mt-(6+5t)a.                                      (5)

Suppose the current observer annotation is(-S,v,w), where S>0,v,w>=0.
Set V=3S+5v+4w. At(3),

    V=(20M+55)lambda<Vbar=(20M+55)/(6M+49)<10/3.           (6)

Choose t0=S/4,a0=v/M. If Mt0-(6+5t0)a0<=w, take the face root
(a,t,z)=(a0,t0,0). Otherwise, on w/M<d<S/4 define

    a(d)=(Md-w)/(6+5d), z(d)=(S-4d)/(7+5d),
    F(d)=(M-5z(d))a(d)-6z(d)-v.

The interval is nonempty by failure of the face inequality. Here a increases,
z decreases, and M-5z>0 since z<=S/7<10/63. Thus F increases strictly;
its left endpoint value is negative and its right endpoint value positive.
Its unique zero gives a positive013 root. In both selections

    C0=-S, C1=v, C3<=w, with equality if z>0.              (7)

Every chosen root initially obeys the coarse bounds

    t<5/18, z<10/63, a<=102/643.

For the last bound use a=(v+6z)/(M-5z), v<2/3, M>=11. Thus all odds are
below5/18 and M-6-5 max(a,t,z)>0.

The observer outputs are v'_i=H_i(v_i+G_i x). They stay in the same orthant.
For0, the numerator is-5(t+z+tz)<0. For1 it is v-a+z: nonnegative if z>=a;
otherwise substitute(7) to obtain a strict lower bound(M-6-5z)a>0.
For3 it is w+a-t: nonnegative if a>=t; otherwise(7) gives the strict lower
bound(M-6-5t)t>0. This covers the quiet observer on a face root; its output
need not equal its immediate-Quit offer.

### 4.1. Lyapunov descent and size bounds

Let d=(-3,5,4). Then dG=(-1,-1,-1). Since each product d_i v'_i is
nonnegative, the exact recurrence gives

    V'-V=-sum_j x_j-sum_i d_i(1-H_i)(v_i+G_i x)
          <=-(a+t+z).                                   (8)

Therefore the process continues forever in the same orthant, with V<Vbar,
and the total sum of its odds is finite.

The stronger bounds Ma<1 and Mt<5/6 hold without assuming any cone. From(7),

    V>=(5M-24-20t-25z)a+(4M+12)t-9z+15tz.

Since t<=V/12,z<=V/21 and C1>=0 gives z<=Ma/6,

    V>=[(7/2)M-24-(20/7)V]a+(4M+12)t.

The coefficient of a is at least209/42>0 at M>=11,V<10/3. Thus
Mt<V/4<5/6. Furthermore 5v+21z<=V, so

    a<=[(2/7)V]/[M-5V/21]=6V/(21M-5V)<1/M.               (9)

The last inequality with Vbar is exactly6M^2+599M-275>0, valid for M>=11.

### 4.2. Observer values converge to zero

Equation(8) gives a,t,z->0. Equations(7) then give S,v->0. The remaining w
converges, because |w'-w|<=(1+5/6)(a+t) and the latter series converges.
If its limit were positive, eventually w>MS/4, forcing every later root
to be a face01 root. There S'=5S/(4+S), which strictly increases positive S
once S<1. This contradicts S->0. Thus w->0 as well.

## 5. An exact invariant upper cone

Put U=min(1,1/2+7/M). The following lemma closes the pivot comparison.

**Lemma.** If0<=a<=1/M,0<t<=1/M,0<=z<=Ut, then the next root selected
in Section4 satisfies z'<=Ut'. The inequality is strict when z'>0.

The first root enters this cone: at(3) the face test fails, so C3=w and
w<=Mt. Using S=25lambda, w=(5M-5)lambda in C0=-S gives

    z/t<=(M+4)/[7(M-1)]<1/2.                             (10)

Here is a complete algebraic proof of the lemma with a finite rational sign
certificate. For the old root put

    S=5(t+z+tz)/[(1+t)(1+z)],
    v=[(M-1)a-5z-5az]/[(1+a)(1+z)],
    w=[(M-1)t-5a-5at]/[(1+a)(1+t)].                     (11)

The actual next annotation has first two coordinates(-S,v) and third
coordinate wbar>=w, because an old face root may give its quiet observer3
more than immediate Quit. The possibly negative w in(11) is only a baseline.
A new face root has z'=0. For a full root use the increasing function
F_wbar of Section4. Let d_U>0 solve

    S=(4+7U)d_U+5U d_U^2.

Then z(d)<=Ud exactly when d>=d_U. If d_U<=wbar/M this is immediate.
Otherwise it suffices to prove F_wbar(d_U)<0. The function decreases with
wbar, so it suffices to use the baseline w. Put

    K=M^2+4M+24+U(7M+6)+5Uw-5v,
    R=(M+6)S+Mw+6v.

The exact identity is(6+5d_U)F_w(d_U)=d_U K-R. One has K>0 because
v<=Ma<=1 and w>=-5/M. For R>0, substitute h=1/M,A=Ma,T=Mt,u=z/(Ut).
Its positive denominator is h(1+Ah)(1+Th)(1+TUhu), and its numerator is

    Ah(1-6h)+T+24ATh^3+6ATh^2+4T^2Uh^2u
                  +T^2Uhu+5TUhu+30Th^2+4Th>0.

Thus the inequality

    E=(4+7U)RK+5UR^2-SK^2>0                              (12)

implies d_U<R/K and proves the lemma.

Appendix A reconstructs E from(11), with denominator
h^3(1+Ah)^2(1+Th)^3(1+TUhu)^3>0. For11<=M<=14 use U=1 and
h=1/14+(3/154)H, H in[0,1]. Its numerator has degrees(11,2,6,3) in
(H,A,T,u); all1008 tensor Bernstein coefficients are nonnegative, and every
coefficient with positive T-index is positive. For M>=14 use U=1/2+7h
and h=H/14, H in(0,1]. There are1428 coefficients of degrees(16,2,6,3);
all are nonnegative, and every coefficient with positive H- and T-indices
is positive. Since T>0 and finite M implies H>0 in the second box, these
strict coefficients prove(12), including all A,u endpoints. No infinite-M
game is asserted. Every acceptance test is exact rational arithmetic.

For completeness, the Bernstein coefficient of p=sum_m c_m x^m at index k,
with coordinate degrees d, is sum_(m<=k)c_m prod_i binom(k_i,m_i)/binom(d_i,m_i).
The inline verifier performs this conversion successively in each coordinate,
checks all coefficients and the strict-index conditions, and verifies the
scalar identity and R numerator. It stores no table of sampled roots.

## 6. Every pivot comparison and a returned diagonal seed

At the initial ray beta=(3M+62)lambda>w/2. At any later root the pivot's
actual joining expression is bounded above, by the raw reward conditions, by

    C2=-6a-7t+Mz-5(at+az+tz+atz).

For a full013 root, the cone and(7) give

    C2-w/2=Mz-(M/2+7)t-3a-(5/2)at-5az-5tz-5atz<=0.

A face01 root has C2<=0. Thus beta>=w/2 ensures the pivot is quiet.
This inequality is preserved. Put D=(1+a)(1+t)(1+z) and

    Delta=delta01*at+delta03*az+delta13*tz+delta013*atz>=0.

The pivot and observer3 outputs are

    beta'=[beta+a+2t-z+Delta]/D,
    w'=(1+z)(w+a-t)/D.

On a face, D(beta'-w'/2)>=a/2+5t/2>0. On a full root w=C3, and
w+a-t=(M-1)t-5a-5at<=Mt<=1. Therefore

    D(beta'-w'/2)>=a/2+5t/2-z-(z/2)(w+a-t)
                  >=a/2+5t/2-3z/2>0.

This prices every pivot response, including all multiple-quitter coalitions.

The pivot values also stay in a fixed positive interval. Let A=a+2t-z.
By the cone A>=a+t; by(9) and z<=t every odds coordinate is <=1/11. Thus

    A/(D-1)>=121/288>3/16,
    (A+Delta)/(D-1)<=B.

The first follows from D-1<=(a+t+z)(12/11)^2<=288(a+t)/121.
For the second use A<=2(a+t+z), and each higher monomial has coefficient
at most B. The update beta' is a convex combination of beta and
(A+Delta)/(D-1). Initially beta>=3/16 and beta<1: for b>=1/10 its minimum
is at b=1/10, giving(3M+62)/(16M+89)>3/16. Hence beta stays in[3/16,B].
Its absolute increments are bounded by a fixed table-dependent constant
times a+t+z. Equation(8) makes them summable, so beta converges to some
b' in[3/16,B]. Observer values tend to zero by Section4.

Thus every b in I=[1/10,B] has a returned b' in I. It is one fixed endpoint,
independent of approximation accuracy. The finite-proxy closure of Section2
provides, for every eta>0, a finite word W whose payoff and full cap at input
b e2 are within eta of b'e2, with joint survival<=theta+eta and every
marginal survival<=rho+eta, where theta=5/8 and

    rho=max(10/11,11/13,13/16,16(M+4)/(16M+89))<1.         (13)

All roots are produced from raw entries by the explicit phases and scalar
selection; no strategic input is left assumed.

## 7. Actual profiles, arbitrary signed offsets, and uniform horizons

Choose b0=1/10 and one infinite return orbit b_j in I. For fixed K select
finite words W_j with error eta at their ideal diagonal inputs. Prepend W_K
before W_(K-1),...,W_1 to terminal proxy b0 e2. Nonexpansiveness in(1) gives

    ||U*-bK e2||, ||B*-bK e2||<=K eta,
    nu<=(theta+eta)^K, N_i<=(rho+eta)^K.                 (14)

This controls all finite phase-switch errors; there is no exact finite
attainment of an intermediate zero cap assumed. Word lengths and hazards
are fixed before play.

Replace the native terminal proxy by actual Never. Its prescribed payoff
and full response cap are both zero because own native singleton rewards
are zero. Monotonicity and the payoff recursion give

    U=U*-nu*b0 e2, B<=B*,
    0<=d_i=B_i-U_i<=2K eta+b0(theta+eta)^K.              (15)

Choose eta_K with K eta_K->0 and both geometric factors in(14) tending
to zero. Compactness selects a subsequence bK->b_* BEFORE any requested
accuracy. Actual native payoffs converge to b_*e2, all native full debts
tend to zero, and each marginal Never mass tends to zero. Bounded augmented
payoff/cap/Never tuples then have an absorbing zero-debt limit. Additional
bounded Never-payoff coordinates may be included in the same subsequence.

For r_i=kappa_i+sigma_i Z_i, prescribed terminal payoff is
sigma_i U_i+kappa_i(1-nu). A unilateral deviation changes its joint Never
probability only when every opponent chooses Never, an event of probability
h_i=prod_(j!=i)N_j. Its terminal gain is therefore bounded by

    sigma_i d_i+abs(kappa_i)h_i.                          (16)

This covers complete behavioral deviations and their mixtures, and tends
to zero. The fixed target is kappa+sigma_2 b_*e2.

Here is the direct all-large-horizon passage, including negative kappa_i.
Fix one finite word, its last possible prescribed Quit date T, and let R0
bound the absolute original absorbing rewards. Prescribed average payoff
and terminal payoff differ by at most R0(T+1)/H over H stages. Under any
unilateral deviation, absorption by an opponent occurs by T. Later absorption
can only be the deviator's solo reward kappa_i; if negative, delaying it
can improve the H-stage average above its terminal payoff by at most
abs(kappa_i)h_i. All earlier discrepancies are at most R0(T+1)/H. Thus
H-stage unilateral gain is at most

    sigma_i d_i+2abs(kappa_i)h_i+2R0(T+1)/H.

Choose one profile making target error and the first two terms small, then
one horizon threshold making the remainder small. The same profile works
at every larger horizon, with the target already fixed.

## 8. The canonical remaining range M<=11

This section concerns only r=4+Z^M. Own singleton rewards are4. At any finite
root game with continuation v and an exact Nash root q, let A be its active
players. If some v_i<4, the all-Continue root is not Nash, so A is nonempty.
If M<=1, every native participant reward is nonpositive. Hence every
active player's forced-Quit payoff Q_i is at most4, and its Nash successor
payoff W_i equals Q_i.

If1<M<=11 and A is proper, some i in A lacks its premium predecessor in A:
otherwise closure under the four-cycle would force A to be all players.
Every participant reward relevant to that player's forced Quit is then
native nonpositive, so again W_i=Q_i<=4.

If A is full, use the exact inserted-reward identity

    sum_i(Q_i-4)=sum_(S subset I) mass_q(S) H(S),
    H(S)=sum_i Z_i^M(S union{i}).

It follows simply by averaging each forced-Quit payoff over the full product
root; inserting i removes any dependence on i's own root draw. Direct
enumeration gives H(empty)=0, H(singleton)=M-11, H(cycle pair)=M-16,
and H(other pair)=H(triple)=H(full)=-20. All are nonpositive for M<=11.
Thus some Q_i<=4, and because all players are active its successor W_i<=4.

Finite-game Nash existence supplies such an exact root at every continuation.
We have therefore produced the predicate HasBoxedSelectedSingletonSublevelReturn
for every sufficiently large finite box: every boxed continuation with some
coordinate below its own singleton has an exact Nash successor with some
coordinate at most its own singleton. The checked theorem
exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_on_subbox
in UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean
applies with bound=quittingRewardBound reward+1. Its hypotheses are own
singleton nonnegativity, this produced predicate, and the stated strict
reward-bound inequality. This proves the canonical corollary for M<=11.

## 9. Source correspondence, boundary checks, and handoff

The finite proxy calculus is the algebraic interface
quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash and literal splicing
quittingTerminalSemanticPair_rootThenContinuation in
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean. Full response
recursion is quittingContinuationBestResponseValue_rootThenContinuation_eq_max
in UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean. The stopping-law
payoff/cap correspondences are in
UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean.
The fixed-target consumer is
quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto in
UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean.
Section7 also supplies the required behavioral finite-horizon proof directly.

Section8 uses exists_isZeroQuittingRootNash in
UniformEquilibrium/Quitting/Root/NashExistence.lean and the exact averaging
identity quittingWeightedQuitPremium_eq_fullCoalitionAverage in
UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean.
These are existing semantic/finite-game interfaces, not a Lean proof of the
new M>=11 raw producer.

The coverage increment is an entire unbounded premium range, together with
its stated raw completions. For example M=13 lies beyond the elementary
upper-average criterion: its singleton tests sum to2 sum(w)>0 for every
nonzero nonnegative weight vector. Its cycle-forced anchor caps would require
12^4<=5^4, and every candidate pair has a negative participant-premium
endpoint. The new producer does not assume those criteria or an equilibrium
continuation. The canonical M<=11 boundary is included by its actual adapter,
not inferred from continuity or from failure of a competing construction.

Negative observer0 annotations, nonattainment of singleton phase endpoints,
face01 switches, potentially negative hypothetical Q3 in the cone test,
arbitrarily large passive pivot rewards, and signed row offsets are all
explicitly treated. The upper-cone certificate covers its boundary faces
and every finite M>=11. No sampled orbit or numerical eigenvalue is used.

A formalization should encode the raw support restrictions, finite proxy
closure and nonexpansiveness, the explicit prefix, scalar01/013 selection,
Lyapunov bounds, rational polynomial sign certificate, and the full consumer.
No return, rate, continuation strategy, or source realization belongs among
its assumed fields. This is ordinary mathematics with an exact finite
certificate; no new Lean theorem or compilation is claimed. Singleton
geometry and the displayed observer rewards remain restricted. Arbitrary
four-player quitting games remain open.

## Appendix A. Complete upper-cone certificate

The standalone Python program below needs only SymPy. It reconstructs all
rational polynomials and all2436 Bernstein coefficients from the formulas;
no external data, sampled roots, floating arithmetic, or stored coefficient
payload is used. Run it with Python3 to check every asserted sign.

```python
"""Exact upper-cone certificate for every real premium M>=11.
Requires SymPy only. No sampled data, floating arithmetic or external files.
"""
import sympy as s
from itertools import product
from math import comb
h,A,T,u,U=s.symbols('h A T u U')
M=1/h;a=h*A;t=h*T;c=U*u*t
S=5*(t+c+t*c)/((1+t)*(1+c))
v=((M-1)*a-5*c-5*a*c)/((1+a)*(1+c))
w=((M-1)*t-5*a-5*a*t)/((1+a)*(1+t))
K=M*M+4*M+24+U*(7*M+6)+5*U*w-5*v
R=(M+6)*S+M*w+6*v
E=(4+7*U)*R*K+5*U*R*R-S*K*K
n,d=s.fraction(s.factor(E))
assert d==h**3*(1+A*h)**2*(1+T*h)**3*(1+T*U*h*u)**3
rn,rd=s.fraction(s.factor(R))
assert s.expand(rn-(A*h*(1-6*h)+T+24*A*T*h**3+6*A*T*h**2
 +4*T*T*U*h*h*u+T*T*U*h*u+5*T*U*h*u+30*T*h*h+4*T*h))==0
assert rd==h*(1+A*h)*(1+T*h)*(1+T*U*h*u)
# The scalar-root upper-bound comparison is algebraic, not numerical.
b,SS,V,W,MM,UU=s.symbols('b SS V W MM UU')
KK=MM*MM+4*MM+24+UU*(7*MM+6)+5*UU*W-5*V
RR=(MM+6)*SS+MM*W+6*V
Fnum=(MM-5*UU*b)*(MM*b-W)-(6*UU*b+V)*(6+5*b)
assert s.expand(Fnum-(b*KK-RR)-(MM+6)*(SS-(4+7*UU)*b-5*UU*b*b))==0

def bernstein(poly,variables):
 p=s.Poly(poly,*variables);degrees=p.degree_list();values=dict(p.terms())
 for i,dd in enumerate(degrees):
  new={}
  rest=[range(dj+1) if j!=i else [0] for j,dj in enumerate(degrees)]
  for ix in product(*rest):
   coeff=[]
   for m in range(dd+1):
    idx=list(ix);idx[i]=m
    coeff.append(values.get(tuple(idx),s.Integer(0))/comb(dd,m))
   for k in range(dd+1):
    idx=list(ix);idx[i]=k
    new[tuple(idx)]=sum(coeff[m]*comb(k,m) for m in range(k+1))
  values=new
 return degrees,values

for mode in (0,1):
 # mode0: 11<=M<=14, U=1; mode1: 14<=M<infinity, U=1/2+7/M.
 expr=n.subs(U,1 if mode==0 else s.Rational(1,2)+7*h)
 expr=s.expand(expr.subs({h:s.Rational(1,14)+s.Rational(3,154)*h
                         if mode==0 else h/14,
                         T:T},simultaneous=True))
 degrees,values=bernstein(expr,(h,A,T,u))
 assert degrees==((11,2,6,3) if mode==0 else (16,2,6,3))
 assert len(values)==(1008 if mode==0 else 1428)
 assert all(vv>=0 for vv in values.values())
 # These indices guarantee strict positivity whenever M is finite and t>0,
 # including all endpoints of A,T,u and the finite-M parameter interval.
 assert all(vv>0 for ix,vv in values.items() if ix[2]>0 and (mode==0 or ix[0]>0))
 assert sum(int(bool(vv==0)) for vv in values.values())==(48 if mode==0 else 94)
 print('PASS upper-cone mode',mode,'degrees',degrees,'coefficients',len(values),flush=True)
```
