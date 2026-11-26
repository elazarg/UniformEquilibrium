# Alternating pairs exclude the global AllNever source

## Exact statement and model

There are four owners I={0,1,2,3}. On each natural date, independently
randomized Continue/Quit actions are observed publicly; the first nonempty
coalition D absorbs at a finite reward Z_i(D). Live play and literal Never
pay zero, and Z_i({i})=0. A deviation replaces one owner's entire behavioral
strategy. Before absorption there is only one live history per date, so
these strategies are exactly independent first-Quit laws on N union {Never}.
Set Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}) for i!=j, with zero diagonals.

For an actual profile let U_i be its payoff, B_i the supremum over ALL pure
finite-deadline and Never replies, e_i its Never reply, and N_i its ORIGINAL
Never mass. Every randomized complete reply averages these pure replies.
Define C=closure{(U,B,e,N)}, D=sum_i(B_i-U_i), nu=product_i N_i,
E=C intersect{D=0}, and mu=min_E nu. These are compact bounded Euclidean
sets; E contains AllNever. Finite mass escaping dates is never relabeled Never.

**Theorem.** Every pair table passing the finite algebraic test in Section3
has an actual independent infinite full Nash profile with

    U=B=e, 0<nu<1.

This holds for EVERY finite completion of all higher-coalition rewards.
In particular mu<1, excluding the global AllNever-only zero-debt carrier.

**Produced open class.** 
Let Gamma be a zero-diagonal4x4 matrix with Gamma^-1 strictly positive
entrywise, admitting a partition S,T into two mutually negative pairs.
There exists eta(Gamma,S,T)>0 with this property. For EVERY zero-diagonal
participant-pair matrix J with max|J_ij|<eta(Gamma,S,T), and EVERY finite native
completion of Gamma,J (own singletons0, arbitrary other rewards, Never0),
there is a nonempty ACTUAL countable full Nash profile with positive
original Never. Consequently the GLOBAL minimum mu of original joint Never
over the zero-full-debt compact carrier is strictly less than1.

All twelve J entries vary independently, including both scheduled-pair
participant rewards. The admissible J ball depends only on Gamma; the
actual clock amplitude may depend on the unrestricted higher rewards.
This does not prove mu=0, absorbing Nash or UE for these completions.
It excludes the AllNever alternative on an open pair-data neighborhood,
including constant pencils J=0 that pass the entire-pencil test.
In particular this applies to EVERY standard-Q singleton matrix whose
positive entries are exactly01,10,23,32, with all eight crossings negative.
The matching inverse fact below supplies the stronger inverse hypothesis.

## 1. Existing matching inverse fact, with a direct proof

The matching standard-Q => Gamma^-1>>0 implication is a reused matrix
fact. Here is its direct proof. Standard Q means every offset z admits
x>=0 with Gamma x+z>=0 and x_i(Gamma x+z)_i=0.
Q at offset-one supplies x>=0 with Gamma x>=one. Each row has its only
positive coefficient at its positive mate, so x>>0. Let P be the permutation
matrix for(01)(23), and D=diag(x). The matrix H=Gamma D P has positive
diagonal, nonpositive offdiagonal, and strict row diagonal dominance.
Write H=D0(I-K), K>=0 with ||K||_infinity<1. The crossing graph is strongly
connected, so sum_(n>=0)K^n is strictly positive. Hence H^-1>>0 and
Gamma^-1=D P H^-1>>0. No new inverse criterion is claimed.

## 2. A forced expanding two-phase mode at J=0

For the supplied negative-pair partition S,T write C=Gamma_SS and
E=Gamma_TT. Both are invertible, with strictly negative offdiagonals.
Put W=-diag(C,E), a positive weighted mate-permutation matrix. Therefore
Gamma^-1 W is strictly positive. Perron--Frobenius gives a simple positive
eigenvalue lambda and an eigenvector x>>0. With tau=1+1/lambda>1,

 Gamma_ST x_T=-tau C x_S,
 Gamma_TS x_S=-tau E x_T.

The two payoff-transfer matrices are

 A=-Gamma_ST E^-1, B=-Gamma_TS C^-1.

The strictly positive vector v=-C x_S satisfies

 Bv=Gamma_TS x_S=-tau E x_T>>0,
 ABv=tau² v.

This expanding eigenvalue rho=tau²>1 is SIMPLE. Indeed

 det(Gamma-tW)=det Gamma det(I-t Gamma^-1 W)
             =det C det E det((1+t)² I-AB).

The first expression has a simple zero at t=1/lambda; the derivative of
(1+t)² there is nonzero. Thus rho is a simple eigenvalue of AB. This
argument imposes NO signs on the cross-pair blocks Gamma_ST,Gamma_TS.
The positive expanding mode and both intermediate positive faces are
forced by the inverse-positive/negative-matching data, not strategic inputs.
All inequalities needed for the construction are strict.

## 3. Exact pair Nash update, including arbitrary higher rewards

For a root q, put H_i(q)=product_(j!=i)(1-q_j), and

 P_i(q)=sum_(empty!=D subset I minus{i}) Z_i(D)
          product_(j in D)q_j product_(j notin D,j!=i)(1-q_j).

Thus P is the passive offer on nonempty opponent coalitions and H the
opponents' Continue probability. The forced-Quit offer Q_i replaces Z_i(D)
by Z_i(D union{i}) in this expectation and includes the empty D term,
whose native reward is0. Continue at a tail value w pays P_i+H_i w_i.

Put L=J-Gamma and suppose its two offdiagonals inside each scheduled
pair are nonzero. For any small continuation vector w (possibly signed),
choose a root supported on S by

 q_j=w_i/(L_ij+w_i), i,j in S, i!=j.

The two active indifference equations are EXACT, because

 Quit_i-Continue_i=(L_ij+w_i)q_j-w_i.

Its active output is J_ij q_j. The quiet output is
P_k(q)+H_k(q)w_k. Call this analytic four-coordinate map Phi_S(w), and
define Phi_T analogously. The displayed hazards are proper whenever w_i/L_ij>0 and w is small;
the numerator and denominator may both be negative. Quiet owners
are checked separately; no sign of a nonactive continuation is presumed.

Let C_S=L_SS^-1, C_T=L_TT^-1 and set

 D_S=J_SS C_S, D_T=J_TT C_T,
 B_J=Gamma_TS C_S, A_J=Gamma_ST C_T.

The linear pair maps, in(S,T) coordinates, are

 D Phi_S(0)=[[D_S,0],[B_J,I]],
 D Phi_T(0)=[[I,A_J],[0,D_T]].

Their return map F=Phi_T composed with Phi_S has derivative

 H_J=[[D_S+A_J B_J,A_J],[D_T B_J,D_T]].

At J=0 this is [[AB,A],[0,0]]. Its simple expanding eigenvalue rho from
Section2 has eigenvector V=(v,0). The other eigenvalues are the other
eigenvalue of AB and two zeros, none equal to rho. Therefore, for all
sufficiently small independent perturbations of J, a real simple eigenvalue
rho_J>1 and eigenvector V_J continue continuously. Normalize so V_J->V.

The active S input (V_J)_S remains positive. The intermediate T input
(D Phi_S(0)V_J)_T remains positive, converging to Bv. The leading quiet
comparison at the S root is

 (D Phi_S(0)V_J)_T-J_TS C_S(V_J)_S,

and at the T root it is

 (H_J V_J)_S-J_ST C_T(D Phi_S(0)V_J)_T.

At J=0 these are respectively Bv and rho v, both strictly positive.
All these strict finite-dimensional conditions persist on a J ball depending
only on Gamma. This chooses eta(Gamma). The FULL eigenvector V_J may have
negative coordinates in T; that is harmless. Only active inputs and actual
quiet comparisons are required positive.

### A finite raw pair-data test

The same construction gives a directly checkable criterion, not merely an
unspecified small neighborhood. Given Gamma,J and a partition S,T, require
L_ij!=0 inside both pairs, form the explicit rational matrix H_J above,
and enumerate its real eigenvalues rho>1. For each eigenvalue, test its
real eigenspace for a vector V; put Z_T=B_J V_S+V_T. Accept if

 C_S V_S>>0, C_T Z_T>>0,
 Z_T-J_TS C_S V_S>>0,
 rho V_S-J_ST C_T Z_T>>0.                         (PAIR)

This is a finite algebraic calculation in the24 pair coordinates; hazards,
profiles, tails and strategic source annotations are not supplied inputs.
For rational pair data one isolates roots of a quartic and solves strict
linear feasibility over each real algebraic eigenspace, normalizing
sum(C_S V_S)=1. Eigenvalue simplicity is NOT required for this test.
The inequalities compare actual hazards and quiet offers, not the signs
of unused continuation coordinates. Section2 proves that every inverse-positive
Gamma with a negative perfect matching passes this test for ALL sufficiently
small independent J. The construction below consumes every accepted pair.

## 4. A genuine infinite full Nash clock

Apply the signed backward-orbit lemma proved below to the analytic return
map F and an eigenvector V_J passing(PAIR).
For some rho_J<sigma<rho_J² and every sufficiently small a>0 it gives

 F(w_n)=w_(n+1) for n<0,
 w_n=a rho_J^n V_J+O(a²sigma^n), n<=0.

The scheduled hazards and quiet gaps just checked are positive to first
order, uniformly in n, since(sigma/rho_J)^n<=1. Nonlinear terms are
O(a²sigma^n); their constants may depend on any of the finite higher rewards.
Choose a small relative to these constants. Then BOTH roots in EVERY block
are genuine exact Nash roots, all four scheduled hazards are positive and
proper, and their total sum over n<=-1 is finite and nonzero.

Physical chronological play consists of blocks n=-1,-2,... . In block n,
first use the T root computed at Phi_S(w_n), then the S root at w_n.
The block has tail value w_n and output w_(n+1). Thus the first output is
w_0. Each active response ties and each quiet comparison favors Continue.
Since w_n->0, unrolling through any finite deadline and sending the terminal
remainder to zero proves that literal Never and all supported deadlines have
value w_0, and every other deadline is bounded by w_0. Boundedness then prices
all randomized complete deviations. These are independent natural-date laws
with literal marginal Never products in(0,1), not a virtual infinite append.
Consequently U=B=e=w_0 and nu<1, proving the stated global source exclusion.

## 5. Signed backward-orbit lemma

Let F:R^d->R^d be C^2 near zero, F(0)=0, A=DF(0), and AV=rho V
with real rho>1 and V!=0. No sign, simplicity or dominance condition is
imposed. There are sigma with rho<sigma<rho^2 and, for every sufficiently
small a>0, a backward orbit

    F(w_n)=w_(n+1) for n<0,
    w_n=a rho^n V+O(a^2 sigma^n), n<=0.

Here is a complete construction. Write F(x)=Ax+R(x), with
|R(x)|<=C|x|^2 and |R(x)-R(y)|<=C' max(|x|,|y|)|x-y| nearby.
Choose sigma avoiding every eigenvalue modulus of A, and split into real
invariant spaces E_s,E_f below/above sigma. Equivalent norms give
||A_s||<=alpha_s<sigma<alpha_f, ||A_f^-1||<=1/alpha_f.
Such norms follow from the convergent series sum_(k>=0)c^-k||A^k x||
when c exceeds the spectral radius; apply it to A_f^-1 for the fast block.
Omit empty blocks. On sequences n<=0 use norm sup_n sigma^-n|x_n|.
For forcing f_k, k<0, define

 (Gf)^s_n=sum_(k=-infinity)^(n-1) A_s^(n-1-k) f^s_k,
 (Gf)^f_n=-sum_(k=n)^(-1) A_f^(n-1-k) f^f_k.

Both geometric series converge. The operator norm is at most
1/(sigma-alpha_s)+1/(alpha_f-sigma), and cancellation gives
(Gf)_(n+1)-A(Gf)_n=f_n. Put y_n=a rho^n V. On the ball
||x||_sigma<=Ba^2, the map x->G(R(y+x)) has norm at most C0 a^2
and Lipschitz constant at most C1 a, for a sufficiently small depending on B.
Indeed rho^(2n)<=sigma^n<=rho^n for n<=0, so |y_n+x_n|<=C2 a rho^n;
the quadratic and difference estimates give the stated uniform bounds.
Choose B>2C0 and then a small enough. Banach contraction gives x=G(R(y+x)),
and w=y+x is the desired orbit. This proves the lemma for signed states
and repeated eigenvalues as well as positive or simple ones.

## 6. Conjecture-facing change and source correspondence

The output is a genuine change of complete stopping laws from AllNever to
nontrivial zero debt. It uses the global unmarked minimum: any point of E
with nu<1 contradicts mu=1 regardless of its payoff signs. There is no
supplied clock, favorable root selection, source realization or payoff-fibre
repair hypothesis. The finite test produces the expanding direction; the
lemma and exact pair formulas produce every hazard and every response cap.

A hypothetical signed Fin4 counterexample supplies native positive absorbing
gap data as follows. The declaration
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`
produces a no-UE table with own singleton1 at a pivot and0 elsewhere. By
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`, its full sum-debt
infimum is positive. Subtract1 from every nonempty reward in the pivot
recipient row to get a native table Z.

Finite deadlines dominate Never when the own singleton is nonnegative:
their limiting payoff is Never plus the own singleton times opponents'
Never product. This is
`quittingTerminalPayoff_update_finiteTime_tendsto_of_profile` in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`.
On absorbing profiles the subtraction shifts prescribed payoff and every
finite reply equally, hence preserves all debts. Thus the native absorbing
infimum A=inf{D(P):nu(P)=0} is positive. For M>=1 bounding the native rewards,
move the smallest original Never mass n<=nu^(1/4) to a finite date. Four
payoffs and three caps change by at most2Mn each; the mover's cap is unchanged.
Consequently A<=D+14M nu^(1/4), including on C, and mu>0.
Whenever these native pair data pass(PAIR), this packet further forces mu<1.
It closes the AllNever global alternative on that raw region; it gives no
contradiction to positive A or to the remaining minimizing sources.

The exact complete cap recursion used here is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`: a response either
quits at the current date or continues with the full tail cap. Its repeated
finite form, followed by the vanishing virtual-tail limit in Section4, prices
all complete deviations. These declarations were inspected statically;
this packet makes no new Lean-certification claim.

The positive-inverse matrix fact and alternating negative-pair architecture
are reused. The implemented `GameTheory.PairedCycle.CrossedMatching.RawSource`
in `UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`
retains `cap_favorite`, `cap_other` and `cap_joint`, consumed by
`exists_exact_cycle_of_standardQ_all_initial` in the same file. These
absorbing pair conclusions impose quiet participant-triple or passive-pair bounds. Here strict linear quiet margins absorb every
fixed finite higher reward by choosing the initial amplitude small. This
removes those higher-reward bounds for the weaker positive-Never conclusion.
It is a source-mode exclusion, not an additional raw uniform-equilibrium class.

## 7. Exact tests and strictness of the new source restriction

Take

 Gamma=[0,3,-1,-1;3,0,-1,-1;-1,-1,0,3;-1,-1,3,0],
 J=(1/1000)[0,1,-2,3;-1,0,4,-2;3,-4,0,1;2,3,-1,0],
 S={0,2}, T={1,3}.

The inverse of Gamma is strictly positive and det Gamma=45. At J=0,
A=B=[-1,3;3,-1], AB=[10,-6;-6,10], and V=(1,1,0,0) has rho=4.
For the displayed nonzero J the return matrix has a simple real eigenvalue
in(399/100,401/100). An adjugate column passes all eight strict(PAIR)
inequalities throughout that interval, by exact polynomial root counts.

Nevertheless EVERY Gamma-tJ,0<=t<=1, is R0 of degree+1 and standard Q.
Here R0 means there is no nonzero v>=0 with Mv>=0 and v_i(Mv)_i=0.
Each column retains a negative entry. Each principal block of size at least2
stays invertible because ||Gamma_SS^-1||_infinity ||J_SS||_infinity<1.
These two facts exclude every homogeneous complementary support.
At offset-minus-ones Gamma has exactly one complementary root, on full
support, with index sign(det Gamma)=+1. The usual homogeneous complementarity
map min(x,Mx) has a positive uniform lower bound on the unit sphere along
this compact R0 pencil. Brouwer homotopy therefore preserves degree1.
Adding a bounded offset and taking a large sphere proves the Q property.

The example also has nonzero det L_SS for all sizes2,3,4, nonzero reciprocal
ratios Gamma_ij J_ji-Gamma_ji J_ij, nonzero det J_SS for sizes3,4, and
nonzero resultant of det(Gamma-tJ)_SS with det(Gamma-tJ) for every triple S.
Thus neither degeneracy nor an omitted singular pencil parameter explains
its escape. The new actual clock excludes its AllNever source even though
the whole-pencil condition holds. All higher-coalition completions are allowed.

The negative perfect matching is a genuine restriction on the open-class
corollary. The matrix

 [0,-2,-5,4;-6,0,-4,6;1,3,0,-5;1,-1,4,0]

has determinant42 and strictly positive inverse, but its only mutually
negative pair is01. It has no negative perfect matching. This is a boundary
of the stated producer, not evidence of a positive gap or absence of clocks.
The unrestricted higher-reward quantifier does not give one common clock
amplitude as those rewards grow without bound.

The following standalone Python3/SymPy program checks the algebraic example
and the negative-matching boundary using exact arithmetic only.

```python
import sympy as s
from itertools import combinations
G=s.Matrix([[0,3,-1,-1],[3,0,-1,-1],[-1,-1,0,3],[-1,-1,3,0]])
J=s.Matrix([[0,1,-2,3],[-1,0,4,-2],[3,-4,0,1],[2,3,-1,0]])/1000
L=J-G
S=[0,2]; T=[1,3]
DS=J.extract(S,S)*L.extract(S,S).inv(); DT=J.extract(T,T)*L.extract(T,T).inv()
B=G.extract(T,S)*L.extract(S,S).inv(); A=G.extract(S,T)*L.extract(T,T).inv()
H=(DS+A*B).row_join(A).col_join((DT*B).row_join(DT))
x=s.symbols('x'); f=H.charpoly(x).as_expr()
a,b=s.Rational(399,100),s.Rational(401,100)
assert s.Poly(f,x).count_roots(a,b)==1
assert s.gcd(f,s.diff(f,x))==1
v=(x*s.eye(4)-H).adjugate()[:,0]
vs=v[:2,0]; vt=v[2:,0]
u=B*vs+vt
qs=u-J.extract(T,S)*L.extract(S,S).inv()*vs
qt=x*vs-J.extract(S,T)*L.extract(T,T).inv()*u
if vs[0].subs(x,4)<0:
    v=-v; vs=-vs; vt=-vt; u=-u; qs=-qs; qt=-qt
for vec in [L.extract(S,S).inv()*vs,L.extract(T,T).inv()*u,qs,qt]:
    for e in vec:
        p=s.Poly(e,x)
        assert p.count_roots(a,b)==0
        assert e.subs(x,a)>0
print('PASS: simple expanding eigenvalue and all eight strict pair-clock inequalities')
for k in [2,3,4]:
    for ss in combinations(range(4),k):
        assert L.extract(ss,ss).det()!=0
        gg=G.extract(ss,ss); jj=J.extract(ss,ss)
        norminv=max(sum(abs(gg.inv()[i,j]) for j in range(k)) for i in range(k))
        normj=max(sum(abs(jj[i,j]) for j in range(k)) for i in range(k))
        assert norminv*normj<1
print('PASS: every principal size>=2 nonsingular throughout [0,1] by inverse norm bound')
t=s.symbols('t')
full=(G-t*J).det()
for i,j in combinations(range(4),2):
    assert G[i,j]*J[j,i]-G[j,i]*J[i,j]!=0
for ss in combinations(range(4),3):
    assert J.extract(ss,ss).det()!=0
    assert s.resultant((G-t*J).extract(ss,ss).det(),full,t)!=0
assert J.det()!=0
assert all(any(G[i,j]<0 and abs(J[i,j])<-G[i,j] for i in range(4)) for j in range(4))
roots=[]
for k in [2,3,4]:
    for ss in combinations(range(4),k):
        z=G.extract(ss,ss).inv()*s.ones(k,1)
        if all(a>0 for a in z):
            w=s.zeros(4,1)
            for i,a in zip(ss,z): w[i]=a
            if all(a>=0 for a in G*w-s.ones(4,1)):
                roots.append((ss,s.sign(G.extract(ss,ss).det())))
assert roots==[((0,1,2,3),1)]
assert G.det()==45 and all(a>0 for a in G.inv())
K=s.Matrix([[0,-2,-5,4],[-6,0,-4,6],[1,3,0,-5],[1,-1,4,0]])
assert K.det()==42 and all(a>0 for a in K.inv())
assert [(i,j) for i,j in combinations(range(4),2) if K[i,j]<0 and K[j,i]<0]==[(0,1)]
print('PASS: generic pair clock, whole R0 degree-one pencil, and matching boundary')
```

## Lean handoff and remaining scope

Formalize the pair update and its derivative from the literal root offers;
then the signed backward-orbit lemma, the finite(PAIR) producer and its
complete-deviation telescope. Perron--Frobenius and the block determinant
identity give the open-neighborhood corollary. The source-facing conclusion
is an actual full Nash law with 0<nu<1, hence exclusion of mu=1. No strategy
or favorable eigenmode should be a field of the raw-game input.

The packet does not prove absorption, vanishing native absorbing debt, or
uniform equilibrium for positive own levels. The all-positive global branch
and pair data failing(PAIR) remain unresolved.
