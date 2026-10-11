# Macroscopic periodic roots on the four-active negative-triple table

Status: complete ordinary proof with a passing exact-integer interval
certificate and two bounded independent ordinary checks. Not Lean checked.
The construction gives a236-date exact terminal Nash profile at the displayed
four-active table and a raw56-coordinate neighborhood with four upper-only
grand-coalition rewards. Its center and a smaller neighborhood times those
grand rays are ALREADY covered by the implemented boxed-charge producer.
The positive-grand calibration in Section8 also has a simple rational
sure-quitter equilibrium. This remains an explicit internal strategy construction, not a newly excluded
counterexample class and not an arbitrary-Fin4 existence theorem.

## 1. Self-contained question and fixed table

Let I=Z/4Z. Never pays0. A singleton{i} pays1 to i,4 to i+2,
and0 to the other two players. An adjacent pair{i,i+1} pays-1 to i,
2 to i+1, and1 to each outsider. An opposite pair pays0 to members
and1 to outsiders. Each triple pays-1 to its members and1 to its
outsider. The grand coalition pays(-10,-11,-12,-13).

Does this fixed table admit an actual proper periodic terminal Nash profile,
against every independent private behavioral replacement, including Never?
The proposed mechanism is a macroscopic 59-root return with one label rotation,
giving a236-date profile. It does not use uniformly small hazards or fictitious
terminal continuation values.

**Theorem.** Let r* denote the fourteen proper nonempty coalition rows just
specified. There exists delta>0 such that EVERY finite raw reward table r with

    |r_i(S)-r*_i(S)|<delta for every nonempty proper S and every i,
    r_i(I)<=-10+delta for every i                         (1)

has an exact terminal Nash equilibrium against every complete unilateral
behavioral deviation, including all finite deadlines and Never. The profile
uses the fixed236-date support calendar specified below, with independent
private randomization, and repeats forever. Its actual initial terminal
payoff is a fixed original uniform-equilibrium payoff; this SAME profile
works for every accuracy and all sufficiently long finite horizons.

The source inputs in(1) are only the56 proper reward coordinates and the four
finite grand rewards. No continuation value, root, strategy, Nash row or
strategic witness is supplied. The radius is existential. There is no lower
bound on any grand reward. In particular(1) contains a full60-dimensional
open neighborhood of the specific table above.

## 2. Root map and discovered support word

For a tail value u, a root Nash point has Quit endpoint Q_i, Continue stopping
term B_i, opponent survival alpha_i, and satisfies
Q_i=B_i+alpha_i*u_i for active i, with <= for inactive i. The new value
is v_i=B_i+alpha_i*u_i. All roots below are nonsure.

Write x=u_i,y=u_(i+1),z=u_(i+2),w=u_(i+3).
For an adjacent pair P_i, use

    a=(y-1)/(y+1), b=(1-x)/(2-x), s=(1-a)(1-b),
    v=(1-2b,1+a,4a-3ab+sz,4b-3ab+sw).

Its two inactive margins are v2-(1-a+b-2ab) and
v3-(1-2a-b+ab), in these rotated coordinates.

For a consecutive triple T_i, the quadratic elimination and its chosen
positive-square-root branch are implemented below. The three active values are

    v0=1-2b-c+bc, v1=1+a-2c-ac, v2=1-a+b-2ab,
    v3=4b-3ab+ac-3bc+2abc+(1-a)(1-b)(1-c)w.

The passive endpoint is bounded ABOVE by
1-2a-b+c+ab-ac-2bc-7abc, since every grand reward is<=-10.
Thus checking this upper bound checks all four rotated grand coordinates.

Let h=(2,3,2,3,2,3,3,2,3,2,3,2,3). For k=0,...,12,
apply h_k copies of P_(3+k), followed by two copies of T_(3+k), labels modulo4.
This gives59 root prefixes. Denote their value-map composition F.
Let R(u)_i=u_(i-1). The return equation is F(u)=R(u), or
G(u)_i=F(u)_(i+1)-u_i=0.

Floating-point discovery gives a root near

    (1.08629059985249,2.23838565117317,.727718995681476,.855085839403447).

Along that candidate word, the minimum positive hazard is approximately
0.0000842053, the maximum approximately0.275609, and the minimum inactive
margin approximately0.0266699. These decimals are discovery data only.

## 3. Exact fixed-denominator interval certificate

The following Python uses integer arithmetic only. Every interval endpoint is
an integer divided by S=10^P; each arithmetic operation rounds outwards.
Jets enclose the four first derivatives. The assertions certify an invariant
contraction box for u-BG(u), together with all root inequalities. The code
passes as printed. Floating-point conversion occurs only in diagnostic print
statements, never in an assertion or arithmetic used to prove a bound.

```python
from math import isqrt
P=400
S=10**P
class I:
    def __init__(self,a,b=None): self.a=int(a); self.b=int(a if b is None else b)
    @staticmethod
    def cast(x): return x if isinstance(x,I) else I(x*S)
    def __add__(a,b): b=I.cast(b); return I(a.a+b.a,a.b+b.b)
    __radd__=__add__
    def __neg__(a): return I(-a.b,-a.a)
    def __sub__(a,b): return a+-I.cast(b)
    def __rsub__(a,b): return I.cast(b)+-a
    def __mul__(a,b):
        b=I.cast(b); v=[a.a*b.a,a.a*b.b,a.b*b.a,a.b*b.b]
        return I(min(v)//S,-((-max(v))//S))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=I.cast(b); assert not b.a<=0<=b.b
        v=[(x*S,y) for x in [a.a,a.b] for y in [b.a,b.b]]
        return I(min(x//y for x,y in v),max(-((-x)//y) for x,y in v))
    def __rtruediv__(a,b): return I.cast(b)/a
    def sqrt(a):
        assert a.a>0
        lo=isqrt(a.a*S); hi=isqrt(a.b*S)
        return I(lo,hi+(hi*hi<a.b*S))
    def absup(a): return max(abs(a.a),abs(a.b))
class J:
    def __init__(self,v,d=None): self.v=I.cast(v); self.d=[I(0)]*4 if d is None else d
    @staticmethod
    def cast(x): return x if isinstance(x,J) else J(x)
    def __add__(a,b):
        b=J.cast(b); return J(a.v+b.v,[x+y for x,y in zip(a.d,b.d)])
    __radd__=__add__
    def __neg__(a): return J(-a.v,[-x for x in a.d])
    def __sub__(a,b): return a+-J.cast(b)
    def __rsub__(a,b): return J.cast(b)+-a
    def __mul__(a,b):
        b=J.cast(b); return J(a.v*b.v,[x*b.v+a.v*y for x,y in zip(a.d,b.d)])
    __rmul__=__mul__
    def __truediv__(a,b):
        b=J.cast(b)
        return J(a.v/b.v,[(x*b.v-a.v*y)/(b.v*b.v) for x,y in zip(a.d,b.d)])
    def __rtruediv__(a,b): return J.cast(b)/a
    def sqrt(a):
        r=a.v.sqrt(); return J(r,[x/(2*r) for x in a.d])
def decimal(s):
    neg=s.startswith('-'); s=s.lstrip('-')
    left,_,right=s.partition('.')
    n=int(left or '0')*S+int((right+'0'*P)[:P])
    return I(-n if neg else n)
centers=[
'1.08629059985249275099943327358833605592927849191530885646586433594508185321523866980632042886835964991124258076776200279739754465426898668779937035025573942270943647639095167252421884735994579476076408012315869267116347399552199684232201088140959502990417191525037065124196717715044396173384991948151795534611796062813554128487466',
'2.23838565117316515326075040160815511380856822701039481321241277556510328647454738261824308871138609203868138290510767505617927951480801810788404598766838738956004296941973342303213084087773928619538326590020465509123872763107470624460320452715661177405193064560512017441176474411794608307213807466750704690362964741808053082154416',
'.727718995681475659759047296469390516133065216658115049730312204178794927187814430964748217485002171501864920382857366237209592675692384190116260012688101650609243146505464641141660646374115046300463372973834627625589979748689064405533315193053897941522217573269466639328374777402189664568433124325730437575945656561454468941566723',
'.855085839403447116532561920047082501364123945565572813004112668253446695775611327522827751622062969822760710872132558845300796330411261905449023002631677851236668905763231121621248329199549185286406013197546702993430819902928369228017920752011188306952743217576895939480074669106441687082008974169195610405792252517056514666472379']
Braw=[
['-1.342728178208689076458183','-.1322531276726558335327251','-.04084837373279354020352394','-1.457139738362339561718967'],
['-.4160241052954299750115279','-1.160536828408923620517768','-.04958424722942012381838405','-1.768764043900329266736153'],
['1.085145485323764399887203','.4187396726610971960289535','-.870665932084366711436374','4.613593832748951454993156'],
['-.3144059869786936135797174','-.1213240517417353957537857','-.03747274883077457016855847','-2.33672537064907839965611']]
center=[decimal(s) for s in centers]
B=[[decimal(s) for s in row] for row in Braw]
lengths=[2,3,2,3,2,3,3,2,3,2,3,2,3]
word=[]
for k,h in enumerate(lengths):
    word += [('P',(3+k)%4)]*h+[('T',(3+k)%4)]*2
assert len(word)==59
def mul(a,b):
    return [a[0]*b[0],a[0]*b[1]+a[1]*b[0],a[1]*b[1]]
def step(u,tag):
    kind,i=tag; ix=[(i+j)%4 for j in range(4)]
    x,y,z,w=[u[j] for j in ix]
    if kind=='P':
        a=(y-1)/(y+1); b=(1-x)/(2-x); c=J(0)
        v=[1-2*b,1+a,4*a-3*a*b+(1-a)*(1-b)*z,
           4*b-3*a*b+(1-a)*(1-b)*w]
        margins=[v[2]-(1-a+b-2*a*b),v[3]-(1-2*a-b+a*b)]
    else:
        na=[y-1,2-y]; da=[1+y,-2-y]
        nb=[x-1,5-x]; db=[x-2,4-x]
        ts=[mul(da,db),mul(na,db),mul(nb,da),mul(na,nb)]
        fac=[1-z,z-5,1+z,1-z]
        p=[sum(f*t[j] for f,t in zip(fac,ts)) for j in range(3)]
        c=(-p[1]+(p[1]*p[1]-4*p[0]*p[2]).sqrt())/(2*p[2])
        a=(na[0]+na[1]*c)/(da[0]+da[1]*c)
        b=(nb[0]+nb[1]*c)/(db[0]+db[1]*c)
        v=[1-2*b-c+b*c,1+a-2*c-a*c,1-a+b-2*a*b,
           4*b-3*a*b+a*c-3*b*c+2*a*b*c+(1-a)*(1-b)*(1-c)*w]
        margins=[v[3]-(1-2*a-b+c+a*b-a*c-2*b*c-7*a*b*c)]
    out=[None]*4
    for j,k in enumerate(ix): out[k]=v[j]
    return out,[a,b] if kind=='P' else [a,b,c],margins
def evaluate(rad):
    u=[J(I(v.a-rad,v.b+rad),[I(S if j==k else 0) for k in range(4)])
       for j,v in enumerate(center)]
    old=u; minq=S; maxq=0; mingap=100*S; maxwidth=0
    for tag in word:
        u,q,gaps=step(u,tag)
        minq=min(minq,*[x.v.a for x in q])
        maxq=max(maxq,*[x.v.b for x in q])
        mingap=min(mingap,*[x.v.a for x in gaps])
        maxwidth=max(maxwidth,*[x.v.b-x.v.a for x in u])
    return [u[(j+1)%4]-old[j] for j in range(4)],minq,maxq,mingap,maxwidth
rad=10**(P-180)
G,mq,Mq,gap,width=evaluate(rad)
G0,*_=evaluate(0)
rowbound=[sum((I(S if i==j else 0)-sum(B[i][k]*G[k].d[j]
           for k in range(4))).absup() for j in range(4)) for i in range(4)]
res=max(sum(B[i][k]*G0[k].v for k in range(4)).absup() for i in range(4))
print('theta',max(rowbound)/S,'residual',res/S,'radius',rad/S,
      'minq',mq/S,'maxq',Mq/S,'mingap',gap/S,'maxwidth',width/S)
assert max(rowbound)*10**20<S
assert res*10**300<S
assert mq*100000>S and Mq*2<S and gap*100>S
K=[[G[i].d[j]+(1 if i==j else 0) for j in range(4)] for i in range(4)]
A=[[I(S if i==j else 0) for j in range(4)] for i in range(4)]
for unused in range(4):
    A=[[sum(A[i][k]*K[k][j] for k in range(4))
        for j in range(4)] for i in range(4)]
assert 5*max(sum(x.absup() for x in row) for row in A)<3*S
print('EXACT INTEGER CERTIFICATE PASS')
```

The exact asserted bounds are

    ||I-B DG(X)||_infinity<10^-20,
    ||B G(center)||_infinity<10^-300,
    10^-5<every positive hazard<1/2,
    every inactive margin>1/100,
    ||(D(R^-1 F)(X))^4||_infinity<3/5.             (2)

Here X is the closed infinity-norm box of radius10^-180 about the printed
rational center. The power enclosure in(2) contains every fourth power of
an enclosed derivative matrix; it does not assert that four arbitrary
derivatives along different off-center iterates have that norm.

### 3.1 Why the integer code certifies real inequalities

An I(a,b) represents[a/S,b/S]. Addition and negation are exact. Product
endpoints are the minimum and maximum of the four endpoint products,
rounded down/up after division by S. Quotient endpoints are the four endpoint
ratios, rounded down/up after multiplication by S, and the denominator is
asserted not to straddle0. Python integer division rounds down, including
negative numerators and denominators. The formula -((-x)//y) therefore rounds
x/y up. Square root bounds follow from integer square root of a*S,b*S,
adding1 exactly when the upper radicand is not a perfect square. Every
constant decimal denotes an EXACT rational with denominator S; excess zeros
are appended. The center strings have fewer than P fractional digits, so
there is no center truncation.

The J operations are the sum, product, quotient and positive-square-root
chain rules with interval bounds on values and derivatives. Starting with
the identity derivative therefore encloses DG on the ENTIRE box X. Every
denominator and discriminant used by the59-step composition has its domain
checked during evaluation. Thus each selected branch is continuously
differentiable on X and all intermediate root values are enclosed there.
The polynomial elimination is exact: defining Na,Da,Nb,Db as in the code,
the first two active equations give a=Na/Da,b=Nb/Db; the last equation,
multiplied by Da*Db, is p0+p1*c+p2*c²=0. The selected positive-square-root
branch solves it exactly. No approximate root equation is being accepted.

Put T(u)=u-BG(u). By(2), T has Lipschitz constant<10^-20 on X, and its
displacement at the center is<10^-300. Consequently it maps X strictly
inside itself. Banach's theorem gives a unique fixed point u* in X.
At this point BDG(u*) is invertible, since its distance to identity is<1;
hence the square matrix B is invertible. The fixed point therefore satisfies
G(u*)=0. This proves an EXACT twisted return and all associated strict
root inequalities, not just a numerically small residual.

## 4. Genuine periodic private clocks and their unrestricted caps

Let q1,...,q59 be the roots selected successively by the word in Section2,
starting at u*. Their value maps give u_j=f_(qj)(u_(j-1)) and
u59=R u*. These are PREFIX maps: the physical order of their roots is
q59,q58,...,q1, followed by the continuation with value u*.

The prescribed root coalitions have size at most3. Thus the original grand
rewards never occur in their prescribed payoff evaluation. Every active
recipient sees at most two quitting opponents, so its own immediate-Quit
endpoint also uses only proper coalitions. All the active value maps commute
with the cyclic rotation of the table's proper rows. The one inactive
recipient at a triple root may create the grand coalition by quitting;
its margin is checked against the largest possible grand reward-10.
This is why the table's asymmetric grand row does not invalidate rotation.

Append, in PREFIX order, the rotated copies Rq1,...,Rq59, then their
R² copies, then their R³ copies. Each root is Nash against its actual
assigned next value, every inactive test still holds, and the assigned
values close after236 steps at R⁴u*=u*. The genuine physical calendar is
the REVERSE of this236-root prefix list, repeated forever. Each player
uses the specified independent coin at each date; there is no public lottery
or conditioning on a common seed.

Every root has at least two positive hazards, each>10^-5. Therefore for
every recipient i and every date, the probability all its opponents Continue
is at most1-10^-5. In particular the prescribed profile and every full
unilateral replacement absorb almost surely, with a uniform geometric tail.
Each player's own clock is proper as well, since every label is active in
the periodic calendar.

At a given physical date write v for its assigned value and w for the next
one. The verified conditions say

    v_i=B_i+alpha_i*w_i,       Q_i<=v_i,
    q_i>0 implies Q_i=v_i.                           (3)

The prescribed expected one-stage absorption contribution plus joint
survival times w equals v: if the player Quits with positive probability
its Quit and Continue endpoints agree, and otherwise it Continues.
Iterating this vector Bellman equality and letting the joint-survival
remainder tend to0 proves that every assigned value is the ACTUAL terminal
payoff of the constructed periodic private-clock profile. No phantom
continuation remains.

For an arbitrary pure finite deadline, iterate the scalar inequality(3)
against the fixed opponents until that deadline; its forced-Quit endpoint
is bounded by v there. This gives terminal payoff at most the assigned
initial value. For Never, the same recursion through N dates has a remainder
bounded by a fixed reward bound times(1-10^-5)^N, so its limit gives the same
upper cap. A complete behavioral replacement before absorption specifies an
independent distribution on finite first-Quit dates and Never: the only live
public history at date t is universal Continue at every earlier date.
Integrating these pure-deadline/Never bounds covers EVERY such replacement,
with no finite-memory or stationary-deviation restriction. The prescribed
profile attains its assigned payoff, so the terminal Nash debt is exactly0.

If M bounds the absolute finite rewards of the particular input table,
the expected absorption delay under every one-player replacement is at most
10^5 up to an inessential choice of indexing. The difference between its
terminal payoff and its N-stage average payoff is consequently at most
M*10^5/N (or twice this bound if the selecting-date convention is counted
separately). This holds uniformly over all replacements. Hence the same
profile and one fixed actual initial target give original uniform equilibrium
over all sufficiently long finite horizons.

## 5. Raw56-coordinate neighborhood and four unbounded lower rays

At each adjacent-pair root, the two active equations have nonzero cross
derivatives x-2 and y+1; their2x2 Jacobian is invertible. At a triple root,
the first two equations solve for b and a using nonzero Db and Da. The
last equation has nonzero derivative in c after substitution, since its
quadratic discriminant is strictly positive. Its derivative is
p'(c)/(Da*Db), and p'(c) equals the selected nonzero square root of the
discriminant. Thus the full3x3 active-root Jacobian is invertible.
All these domain facts are certified in Section3, rather than assumed from
small numerical residuals.

The implicit-function theorem therefore supplies a unique nearby active
root on each prescribed support, smoothly in its incoming continuation and
all proper raw rewards near r*. Call the four rotated59-step compositions
F_r, r=0,1,2,3, and their236-step composition H=F_3 F_2 F_1 F_0.
At r*, F_r=R^r F R^(-r). Writing K=R^-1 F gives

    H=K^4,     H(u*)=u*,     DH(u*)=(DK(u*))^4.

The last bound in(2) gives ||DH(u*)||_infinity<3/5. Thus DH(u*)-I is
invertible. A second application of the implicit-function theorem produces
the closed actual value u(r) and all236 roots for EVERY sufficiently small
perturbation of the56 proper reward coordinates. Rotation symmetry is NOT
imposed on those perturbations. The four quarters are solved using their
literal perturbed rows, not by falsely rotating a nonsymmetric table.

There are finitely many strictly positive active hazards and inactive
margins. Continuity preserves their positivity, all hazards<1, and all
deleted contractions after shrinking the raw neighborhood. For inactive
triple recipients, evaluate the proxy grand row(-10,-10,-10,-10), or the
nearby proxy(-10+delta,...,-10+delta). Continuity again preserves every
strict margin for sufficiently small delta. No active equation, prescribed
value or root depends on the grand row. Replacing any proxy grand reward
by a smaller finite input reward can only LOWER its immediate-Quit endpoint.
It cannot change prescribed payoff or any other row. This proves the four
upper-only bounds in(1), with NO lower bound and without a compactness
assumption on those four rewards. The full-agency and uniform-payoff proof
of Section4 then applies to the same profile. This completes the theorem.

## 6. Bounded source lookup and meaning of the result

Inspected consumer:
`quittingTerminalDeviationDebt_cyclicBehaviorProfile_le_card_mul_error_div_opponentAbsorption`
in `UniformEquilibrium/Quitting/Cycles/PeriodicApproximateNashDeviationCap.lean`.
It caps unrestricted terminal debt of supplied actual periodic roots by
period length times local error divided by actual opponent absorption.
Our construction supplies its error0 hypotheses and positive denominators.
The ordinary argument in Section4 also proves the complete cap directly.
No claim is made that the new236-root producer is already formalized.

The fixed table has no sure-quitter root Nash point for ANY continuation:
if i is sure, its mate must Continue (joining<=0 versus withdrawing>=1),
its predecessor must Continue (joining negative versus withdrawing>=0),
then its successor must surely join (2 rather than0), and i withdraws
(0 rather than-1). This excludes all sure-owner and persistent-base exits.

The four already-exported named phase sources do not supply their profiles
here. The first four-joint source has favorite-pair rates in(1/4,3/4).
At a favorite-pair root with other hazard b, Quit is1-b<3/4, while
Continue>=4b>1: its next actual Nash value is nonnegative, since Never
earns only nonparticipant rewards0,1,4. The rectangle source requires
favorite-pair participant rows5,9/2, and the passive-ray source requires
their reward A>(5+sqrt(5))/2; here both favorite-pair participants get0.
The proper four-singleton source requires cross-pair participant caps below
the corresponding singleton floors, whereas a directed successor gets2.
The full owner-root uniqueness check for the paired singleton matrix is
needed if comparing the ENTIRE named singleton architecture, not just its
displayed rates. No unquantified IFT radius is being treated as numerically
known. These comparisons are bounded source tests, not universal novelty.

Negative triples alone do NOT exclude the positive-inverse coalition-jackpot
theorem, because that theorem also permits selected pairs. The independently
checked all-support stationary exclusion in
`CODEX_TURING_BOX__STATE_INFORMATION_AND_RELAXATION.md`, Section25.1,
instead excludes any source whose conclusion is exact stationary Nash at
this center. This is not an exclusion of a uniform equilibrium.
The new mathematical operation is a macroscopic support-changing periodic
return, not a rescaled dilute calendar or an exact-source preprocessing step.

There is decisive EXISTENCE-CLASS overlap. The only premium trap is I.
For the actual outsider-insertion charges P and leave sums L, every singleton
has(P,L)=(-2,-3), every pair(-4,-4), and a triple missing i has
(P,L)=(-11-i,-11-i). The boxed coefficients d=2,g=3,ell=11,tau=1 give
threshold100sqrt(2)>56=sum_i s_i+4*13. Thus
`exists_uniformEquilibriumPayoff_of_boxedQuittingNashCharges` in
`UniformEquilibrium/Quitting/Classification/Existence/BoxedQuittingNashChargesUniformPayoff.lean`
already covers the fixed center. The independent coverage check also gives
an explicit proper-coordinate radius1/10 times every grand reward<=-99/10,
using table-dependent tau=1/(M+1), d=1,g=2,ell=10. An unknown larger IFT
radius is not evidence of new coverage. Changing only grand coordinate0
upward does not repair the separation: weights(0,1,1,1) satisfy the entire
upper-average arm of the accepted mixed-support raw producer, at every finite
value of that coordinate. Zero weights are allowed by that statement.

## 7. Independent check and remaining mathematical question

The frozen source at SHA256
`bbe0c087476a57d9f110d71b5980fa5bd98b8af9b80068b108f379a1cf90b2e4`
received the separate bounded checks in
`../feedback/CODEX_EMMY_BOX__MACROSCOPIC_PERIODIC_ROOT_RETURN__BY_CODEX_TURING_BOX.md`
and
`../feedback/CODEX_EMMY_BOX__MACROSCOPIC_PERIODIC_ROOT_RETURN__BY_CODEX_NASH_BOX.md`.
The former executed the exact certificate and independently recomputed all
236 policy payoffs and complete caps; the latter checked full agency and
fixed-target transport and found the decisive boxed-charge overlap above.
No export as a new raw-table existence class is requested.

The remaining global research question is whether a macroscopic return can
be PRODUCED throughout a substantive class of negative-triple completions,
rather than validated near one fixed table. This236-step component is a
concrete positive calibration, not a finite-calendar completeness theorem.

## 8. Exact positive-grand calibration: a sure-quitter shortcut appears

**Ordinary exact calculation, not independently reviewed.** Keep every
proper coalition row fixed and replace the grand row by

    (95,96,100,-9).                                  (3)

This is not an uncovered-table claim. Although three positive grand entries
remove the previous boxed and upper-average comparisons, a simple exact
sure-quitter equilibrium now exists.

Let the private clocks be Quit0 with probabilities

    q=(1/8,1/3,1,1/10),

and Never otherwise. In particular these are one-date/Never laws, NOT
stationary geometric laws off the reached root. To test recipient i, use the
binary root Quit-minus-Continue difference, with its own singleton1 as the
empty-opponent Continue value: after an empty root an arbitrary finite late
Quit earns1, and Never earns0. Exact enumeration of the eight opponent
coalitions gives

    D=(0,0,103/240,0).                               (4)

Here is an exact reproducible computation, with no numerical root input:

```python
from fractions import Fraction as F
from itertools import product
q=[F(1,8),F(1,3),F(1),F(1,10)]
def reward(S,i):
    if not S:return F(1)  # root Continue followed by own finite late Quit
    if len(S)==1:
        j=next(iter(S))
        return F(1 if i==j else 4 if i==(j+2)%4 else 0)
    if len(S)==2:
        adj=[j for j in range(4) if S=={j,(j+1)%4}]
        if adj:
            j=adj[0]
            return F(-1 if i==j else 2 if i==(j+1)%4 else 1)
        return F(0 if i in S else 1)
    if len(S)==3:return F(-1 if i in S else 1)
    return F([95,96,100,-9][i])
def difference(i):
    O=[j for j in range(4) if j!=i]
    total=F(0)
    for bits in product((0,1),repeat=3):
        S={j for j,b in zip(O,bits) if b}
        mass=F(1)
        for j,b in zip(O,bits):mass*=q[j] if b else 1-q[j]
        total+=mass*(reward(S|{i},i)-reward(S,i))
    return total
assert [difference(i) for i in range(4)]==[0,0,F(103,240),0]
```

For i!=2, sure opponent2 ends the game at the root under EVERY replacement,
so(4) checks the complete cap. For owner2, all opponents surviving the root
choose literal Never. Every finite late deadline therefore gives exactly the
Continue value used above; Never weakly lowers its empty-root contribution
from1 to0. The positive owner difference checks its full cap as well. Thus
these actual independent laws form exact terminal Nash. They are also exact
finite-average Nash at every horizon: every nonempty opponent root pays at
date0, while postponing the nonnegative own singleton1 cannot improve its
finite-average contribution. The same fixed profile is consequently UE.

The macroscopic calendar itself also retains strict passive caps at(3).
An exact extension of the Section3 certificate is to traverse its word at
the certified box, and at each triple root assert

    (old_inactive_margin-110*a*b*c).lower>0.

The factor110 replaces the old proxy grand reward-10 by the upper bound100;
active root equations never use the grand row. Executing this strengthened
integer inequality succeeds. This is merely a second, more elaborate
equilibrium for an already simply solved modified table. It does not rescue
existence-class separation. The mechanism lesson is that increasing several
unused grand coordinates can activate mixed sure-owner sources even when
every pure quitting coalition remains unstable.
