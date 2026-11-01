# Mixed pair and triple clocks exclude an asymmetric AllNever source

## Exact statement and model

There are four owners I={0,1,2,3}. Independent Continue/Quit choices on natural
dates determine the first nonempty quitting coalition D, which absorbs at
finite rewards Z_i(D). Live play and the event that no owner ever quits pay0,
and Z_i({i})=0. An individual Never reply can have nonzero expected payoff.
A unilateral deviation may replace the owner's entire behavioral strategy.
Before absorption there is one live history at each date, so strategies are
independent first-Quit laws on N union a separate Never point. Randomized
complete replies average the pure finite deadlines and literal Never.

Put Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}) for i!=j, with zero diagonals, and
L=J-Gamma. These24 entries are the only inputs to the finite test below.
For an actual profile let U be prescribed payoff, B the supremum over ALL
finite/Never replies, e its Never-reply payoff, and N its ORIGINAL marginal
Never masses. Write C=closure{(U,B,e,N)}, D=sum_i(B_i-U_i), nu=product_i N_i,
E=C intersect{D=0}, and mu=min_E nu. The carrier is compact and E contains
AllNever. Escaping finite mass is not relabeled Never.

**Theorem.** If the pair data pass the test in Section1, then EVERY finite
completion of the other rewards has an actual infinite full Nash profile
with U=B=e and0<nu<1. Thus mu<1: the global AllNever-only source is excluded.
The result does not prove absorption, vanishing absorbing debt, or UE for
positive own levels, and does not exclude an all-positive global minimum.

**Produced class.** Fix

    Gamma=[0,-2,-5,4; -6,0,-4,6; 1,3,0,-5; 1,-1,4,0].           (G)

For EVERY fixed zero-diagonal K satisfying

    K_23<0, 31K_30+55K_31<0,                                  (RAY)

there is epsilon0(K)>0 such that J=epsilon K passes the test whenever
0<epsilon<epsilon0(K). All higher rewards remain arbitrary finite numbers.
The exact example in Section6 also gives an open neighborhood in all24 pair
coordinates. Its Gamma has positive inverse but only one mutually negative
pair, so a negative perfect matching is not being assumed.

## 1. A finite algebraic test on the mixed word

Use construction-order supports S1={2,3}, S2={0,2}, S3={0,1,3}. Require each
L_SS invertible. Put C_S=L_SS^-1 and define a4x4 linear map A_S by

    (A_S w)_i=(J_iS C_S w_S)              if i in S,
    (A_S w)_i=w_i+Gamma_iS C_S w_S        if i notin S.

Let H=A_S3 A_S2 A_S1. For each real eigenvalue rho>1 of H, test its real
eigenspace for a vector V. Set W0=V and, successively for r=1,2,3,

    h_r=C_Sr (W_(r-1))_Sr, W_r=A_Sr W_(r-1).

Accept precisely when all twelve strict scalar inequalities hold:

    h_r>0 on Sr, (W_r)_i-J_i,Sr h_r>0 for every i notin Sr.    (WORD)

These are seven hazard and five quiet-response inequalities. They are raw
finite algebraic tests, not supplied roots, strategies or continuation data.
For rational inputs, isolate the real roots of the quartic characteristic
polynomial, solve linear feasibility in each real algebraic eigenspace, and
normalize sum(h_1)=1. Simplicity or dominance of rho is not required.

## 2. Exact root maps from the raw data

For a root q let H_i(q)=product_(j!=i)(1-q_j), and define

    P_i(q)=sum_(empty!=D subset I minus{i}) Z_i(D)
                 product_(j in D)q_j product_(j notin D,j!=i)(1-q_j).

The forced-Quit offer Q_i has the same expectation with Z_i(D union{i}),
including empty D with reward0. Continue at tail w pays P_i(q)+H_i(q)w_i.
For each support S, set all outside hazards0 and define on S

    z_i(q_S)=(Q_i(q)-P_i(q))/H_i(q).

This is analytic near zero, z(0)=0 and Dz(0)=L_SS. The inverse function
theorem therefore supplies a unique local analytic q_S(w_S) with z(q)=w_S
and derivative C_S. Every active owner is exactly indifferent. The resulting
output map Phi_S(w) has active coordinates Q_i(q) and quiet coordinates
P_i(q)+H_i(q)w_i. It is analytic, fixes0, and D Phi_S(0)=A_S.
For a pair {i,j}, the same inverse is explicit:

    q_j=w_i/(L_ij+w_i), q_i=w_j/(L_ji+w_j).

The construction also permits signed tail values and signed internal L.
Proper hazards and quiet comparisons are established by(WORD), rather than
assumed from positivity of the entire continuation vector. The triple inverse
uses the actual higher rewards, not only their linearization.

Set F=Phi_S3 composed with Phi_S2 composed with Phi_S1. Then DF(0)=H.
All higher-reward contributions enter the Taylor remainders beyond these
displayed derivatives. Their finite sizes affect the chosen amplitude below,
not the raw pair test or the quantified completion class.

## 3. A signed backward orbit and the actual infinite clock

We use the following elementary lemma. If F:R^d->R^d is C^2 near0, F(0)=0,
A=DF(0), and AV=rho V with real rho>1 and V!=0, then for some
rho<sigma<rho^2 and every sufficiently small a>0 there is an orbit

    F(w_n)=w_(n+1) for n<0,
    w_n=a rho^n V+O(a^2 sigma^n), n<=0.                       (B)

Here is a proof, including repeated or nondominant eigenvalues. Write
F(x)=Ax+R(x), where |R(x)|<=C|x|^2 and
|R(x)-R(y)|<=C' max(|x|,|y|)|x-y| nearby. Choose sigma avoiding eigenvalue
moduli and split real invariant spaces into E_s,E_f below/above sigma.
Equivalent norms give ||A_s||<=alpha_s<sigma<alpha_f and
||A_f^-1||<=1/alpha_f. These norms follow from convergent weighted sums of
powers whenever the chosen bound exceeds the spectral radius.
On sequences n<=0 use ||x||_sigma=sup sigma^-n|x_n|. For forcing f_k, k<0,

    (Gf)^s_n=sum_(k=-infinity)^(n-1) A_s^(n-1-k)f^s_k,
    (Gf)^f_n=-sum_(k=n)^(-1) A_f^(n-1-k)f^f_k.

Omit empty blocks. The operator bound is
1/(sigma-alpha_s)+1/(alpha_f-sigma), and cancellation gives
(Gf)_(n+1)-A(Gf)_n=f_n. Put y_n=a rho^n V. On ||x||_sigma<=Ba^2,
x->G(R(y+x)) has norm<=C0a^2 and Lipschitz constant<=C1a for small a.
The estimates follow from rho^(2n)<=sigma^n<=rho^n for n<=0, which bounds
|y_n+x_n| by a constant times a rho^n. Choose B>2C0 and then a small.
Banach contraction gives x=G(R(y+x)); w=y+x proves(B). No state sign was used.

Apply(B) to F and a mode passing(WORD). Every intermediate state, hazard
and quiet gap has its displayed linear coefficient times a rho^n, plus
O(a^2 sigma^n). Since(sigma/rho)^n<=1 for n<=0, small fixed a makes all
scheduled hazards positive and proper, and every quiet gap positive, uniformly
along the orbit. The choice of a may depend on all finite higher rewards.

Play actual chronological blocks n=-1,-2,... . Within block n play S3 first,
then S2, then S1, using the roots constructed from w_n. Its tail value is w_n
and its output w_(n+1). Thus the first output is w_0. At each date Continue
equals the stated value, active Quit ties it, and quiet Quit is below it.
Unrolling to any finite deadline and sending the tail remainder to zero proves
that every supported deadline and literal Never pay w_0, and every other
finite deadline pays at most w_0. The remainder is bounded by the vanishing
state norm because the corresponding survival coefficient is at most1.
Averaging prices every complete randomized deviation, and prescribed play
averages its supported deadlines and Never. Hence U=B=e=w_0 exactly.

The scheduled hazards have a finite, nonzero total geometric sum. Each owner
acts in the word, so each original Never product lies strictly between0 and1.
These are independent natural-date laws; no action is executed after an
infinite prefix. Their joint Never lies in(0,1), proving the main theorem.

## 4. Automatic production on the asymmetric rays

For(G) at J=0, direct multiplication gives

    H_0=e_2[6/5,1/2,39/25,2], rho_0=39/25, V_0=e_2.

The eigenvalue rho_0 is simple; the other three eigenvalues are0. The leading
hazards and quiet margins, evaluated on V_0, are

| Support | Hazards in support order | Quiet margins in increasing owner order |
|---|---|---|
|23|(0,1/5)|(4/5,6/5)|
|02|(0,4/25)|(14/25,16/25)|
|013|(62/75,110/75,55/75)|(39/25)|

These are coefficients, not probabilities. The two zero hazards are the only
missing strict inequalities. Along J=epsilon K, the simple real eigenmode
continues analytically; normalize(V_epsilon)_2=1. The last output row gives

    (V_epsilon)_3=2(31K_30+55K_31)epsilon/117+O(epsilon^2).

Consequently the first phase's owner2 hazard coefficient is

    h_(1,2)=-(31K_30+55K_31)epsilon/234+O(epsilon^2).

The first phase's owner2 output is J_23 h_(1,3). Since h_(1,3)->1/5
and L_20->-1, the second phase's owner0 hazard coefficient is

    h_(2,0)=-K_23 epsilon/5+O(epsilon^2).

Both become strictly positive under(RAY); all other margins persist by
continuity. This proves the automatic ray class for arbitrary higher rewards.
The smallness threshold depends on the fixed K. No uniform radius is claimed
for directions approaching either boundary in(RAY).

## 5. Actual-data adapter, source comparison and scope

A signed Fin4 counterexample supplies native positive absorbing-gap data.
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`
produces a no-UE table with own singleton1 at one pivot and0 elsewhere.
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean` gives positive
full sum-debt infimum. Subtract1 from the pivot recipient row on all nonempty
coalitions. Finite deadlines dominate Never for nonnegative own singleton:
their limit is Never plus own singleton times opponents' Never product, by
`quittingTerminalPayoff_update_finiteTime_tendsto_of_profile` in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`.
Thus this subtraction preserves every debt on absorbing profiles, giving
native A=inf{D(P):nu(P)=0}>0. If M>=1 bounds native rewards, moving the
smallest original Never mass to one finite date changes four payoffs and
three caps by at most2M nu^(1/4) each. Hence A<=D+14M nu^(1/4), also on C,
and mu>0. Whenever the resulting pair data pass(WORD), this packet adds mu<1.

The unrestricted cap recursion is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`. The proof above
constructs its root inputs and handles the actual infinite limit directly.
No Nash selector, supplied clock, source realization or favorable strategic
witness is assumed. This is ordinary mathematics, not new Lean certification.

The backward-orbit mechanism and pair roots are reused. The added ingredient
is the mixed pair/triple word with two previously vanishing hazards activated
by actual pair rewards. The exact example below passes the whole-pencil test
and fails EVERY two-pair word test, so this is a further global AllNever
source exclusion. It does not descend from an all-positive minimum or assert
a new raw UE class; any proof of arbitrary Fin4 still needs those missing steps.

## 6. Exact witness, separation and reproducibility

Use(G) and

    J=(1/10000)[0,2,3,1; -2,0,1,-3; 2,-1,0,-2; -4,1,-2,0].

The mixed return has a simple eigenvalue in(155/100,157/100), and all twelve
strict tests hold throughout that isolating interval for an adjugate
eigenvector. They persist under sufficiently small independent pair-data
perturbations. No higher-reward bounds are used.

The same data fail the test for every partition into two pairs, using the
identical hazard/quiet criterion for its two-phase product. Two partitions
have one expanding real eigenvalue, but its one-dimensional eigenspace gives
opposite signs among the tests; the remaining partition has no real eigenvalue
above1. Reversing two phases is a cyclic shift: an accepted mode for one order
would give an accepted mode for the other, so the three partitions suffice.

Nevertheless every Gamma-tJ,0<=t<=1, is R0, has degree1 and is standard Q.
Here R0 means no nonzero v>=0 has Mv>=0 and v_i(Mv)_i=0. Negative columns
exclude singleton supports; the inverse-norm bounds below exclude every
larger principal kernel throughout the pencil. At offset-minus-ones Gamma
has exactly one complementary root, on full support, with index detGamma>0.
The R0 lower bound for min(x,Mx) on the unit sphere is uniform along the
compact pencil; Brouwer homotopy preserves degree1. Standard Q means that
for every b in R^4 there is x>=0 with Mx+b>=0 and x_i(Mx+b)_i=0 for all i.
Adding a fixed offset and using a sufficiently large sphere gives this
property. The code also checks
nonzero reciprocal cross ratios, principal J determinants of sizes3,4 and
principal/full determinant resultants. Thus the separation is generic, not
an artifact of a singular omitted parameter or unavailable inverse.

There is also no proper literal response-invariant quotient, for any higher
completion, even after positive recipient scaling. The necessary condition
`quittingSingletonBlockRowSum_eq_of_responseInvariant` and its sum identity
`sum_quittingSingletonBlockRowSum_eq_totalRowSum` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`
require equal singleton row sums into every source block for recipients in
the same block. The singleton comparison matrix subtracts the recipient's
own singleton; hence it is Gamma both natively and before the pivot row
subtraction in Section5. Its total row sums are(-3,-4,-1,4). Positive row
scaling preserves their signs, so owner3 must be a singleton block. Among
owners0,1,2, the internal sums for possible merged blocks02,12,012 have
opposite signs: respectively(-5,1),(-4,3), and(-7,-10,4). The only remaining
merge01 would require the same positive scaling to equalize both total and
internal sums. But the internal/total ratios are2/3 and3/2, respectively.
Thus no merge works. These strict sign and ratio failures persist near(G).
This rules out that implemented quotient mechanism, not every conceivable
strategy aggregation or every UE theorem for individual higher completions.

Run the following standalone Python3/SymPy program. All checks are exact.

```python
import sympy as s
from itertools import combinations
G=s.Matrix([[0,-2,-5,4],[-6,0,-4,6],[1,3,0,-5],[1,-1,4,0]])
J=s.Matrix([[0,2,3,1],[-2,0,1,-3],[2,-1,0,-2],[-4,1,-2,0]])/10000
L=J-G
I=range(4)
def phase(S):
    C=L.extract(S,S).inv(); H=s.eye(4)
    for i in I:
        if i in S:
            for j in I:H[i,j]=0
            coeff=J.extract([i],S)*C
        else: coeff=G.extract([i],S)*C
        for j,v in zip(S,coeff):H[i,j]=v
    return H,C
word=[[2,3],[0,2],[0,1,3]]
H=s.eye(4)
for S in word:H=phase(S)[0]*H
x=s.symbols('x'); f=H.charpoly(x).as_expr()
a,b=s.Rational(155,100),s.Rational(157,100)
assert s.Poly(f,x).count_roots(a,b)==1
assert s.gcd(f,s.diff(f,x))==1
V=(x*s.eye(4)-H).adjugate()[:,2]
if V[2].subs(x,s.Rational(156,100))<0:V=-V
W=V
for S in word:
    P,C=phase(S); q=C*W.extract(S,[0]); U=P*W
    vals=list(q)+[U[i]-(J.extract([i],S)*q)[0] for i in I if i not in S]
    for e in vals:
        e=s.factor(e)
        assert s.Poly(e,x).count_roots(a,b)==0,(S,e)
        assert e.subs(x,a)>0,(S,e.subs(x,a))
    W=U
print('PASS hybrid eigenvalue and 12 strict hazard/quiet tests on whole isolating interval')

# Exactly exclude every preceding two-pair eigencone test.
intervals=[(s.Rational(114,100),s.Rational(115,100)),None,(s.Rational(750,100),s.Rational(751,100))]
for T,interval in zip(([0,1],[0,2],[0,3]),intervals):
    S=[i for i in I if i not in T]
    P,_=phase(S); Q,_=phase(T); A=Q*P
    f=s.Poly(A.charpoly(x).as_expr(),x)
    assert s.gcd(f.as_expr(),s.diff(f.as_expr(),x))==1
    if interval is None:
        assert f.count_roots(1,s.oo)==0
        continue
    left,right=interval
    assert f.count_roots(1,s.oo)==f.count_roots(left,right)==1
    V=(x*s.eye(4)-A).adjugate()[:,0]
    W=V; tests=[]
    for Z in (S,T):
        B,C=phase(Z); q=C*W.extract(Z,[0]); U=B*W
        tests+=list(q)+[U[i]-(J.extract([i],Z)*q)[0] for i in I if i not in Z]
        W=U
    signs=[]
    for t0 in tests:
        t0=s.factor(t0)
        if t0==0: signs.append(0); continue
        assert s.Poly(t0,x).count_roots(left,right)==0
        signs.append(s.sign(t0.subs(x,left)))
    assert 1 in signs and -1 in signs
    print('PAIR excluded:',S,T,signs)
print('PASS: all three previous two-pair tests rejected exactly')
# Generic pencil conditions
for n in (2,3,4):
    for S in combinations(I,n):
        A=G.extract(S,S); B=J.extract(S,S)
        assert A.det()!=0
        norm=lambda A:max(sum(abs(A[i,j]) for j in range(A.cols)) for i in range(A.rows))
        assert norm(A.inv())*norm(B)<1
assert all(any(G[i,j]<0 and abs(J[i,j])<-G[i,j] for i in I) for j in I)
t=s.symbols('t'); full=(G-t*J).det()
for i,j in combinations(I,2):assert G[i,j]*J[j,i]-G[j,i]*J[i,j]!=0
for S in combinations(I,3):
    assert J.extract(S,S).det()!=0
    assert s.resultant((G-t*J).extract(S,S).det(),full,t)!=0
assert J.det()!=0
print('PASS generic whole-pencil R0 conditions')

roots=[]
for n in (2,3,4):
    for S in combinations(I,n):
        z=G.extract(S,S).inv()*s.ones(n,1)
        if all(a>0 for a in z):
            q=s.zeros(4,1)
            for i,a in zip(S,z):q[i]=a
            if all(a>=0 for a in G*q-s.ones(4,1)):
                roots.append((S,s.sign(G.extract(S,S).det())))
assert roots==[((0,1,2,3),1)]
assert G.det()==42 and all(a>0 for a in G.inv())
assert [(i,j) for i,j in combinations(I,2) if G[i,j]<0 and G[j,i]<0]==[(0,1)]
print('PASS: inverse-positive degree-one singleton matrix without negative perfect matching')

totals=G*s.ones(4,1)
assert list(totals)==[-3,-4,-1,4]
for S,expected in (([0,2],[-5,1]),([1,2],[-4,3]),([0,1,2],[-7,-10,4])):
    assert list(G.extract(S,S)*s.ones(len(S),1))==expected
assert G[0,1]/totals[0]==s.Rational(2,3)
assert G[1,0]/totals[1]==s.Rational(3,2)
print('PASS: no proper response-invariant quotient, even after positive row scaling')
```

## Lean handoff

Formalize the active-support inverse map, its derivative, the signed
backward-orbit lemma, and the chronological complete-response telescope.
The raw finite-word test should produce the mode and all strategies, not
assume them as input fields. The source-facing conclusion is an actual full
Nash law with0<nu<1 and therefore exclusion of mu=1. No absorption or closure
of the all-positive source is claimed.
