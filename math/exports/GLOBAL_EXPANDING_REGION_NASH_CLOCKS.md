# A global expanding region produces actual Nash clocks

## Exact statement and semantic endpoint

Let n>=2. Each owner independently chooses Continue or Quit on each natural
date until the first nonempty quitting coalition S absorbs at a finite real
reward Z_i(S). Live play and the event that nobody ever quits pay zero.
Own singleton rewards Z_i({i}) are zero. Before absorption there is one live
history per date. Independent behavioral strategies are therefore independent
first-Quit laws on the natural dates together with a separate Never point.
A unilateral deviation may replace the owner's entire law; no public
randomizer or correlation between owners is assumed.

Put Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}) for i!=j, with zero diagonals, and

    M=Gamma^-1, K=Gamma-J, T=M K,
    rho=min_(i,j) M_ij / sum_l M_lj, tau=max_(i,j)|T_ij|.

Assume the following finite raw matrix conditions:

    M>>0, K^-1>>0,
    one^T T>=0 coordinatewise, tau<=rho^2/8.                    (RAW)

The inverses in(RAW) exist, >>0 means strict entrywise positivity, and all
remaining inequalities are coordinatewise. Invertibility gives tau>0;
0<rho<=1/n<1. No strategic witness is part of(RAW).

**Theorem.** For EVERY finite completion of the remaining rewards there is
an actual infinite Nash profile whose prescribed payoff U, complete unilateral
response cap B and literal unilateral Never payoff e satisfy

    U=B=e, 0<nu=product_i N_i<1,

where N_i are the ORIGINAL marginal Never probabilities. The constructed
hazards are proper, nonempty and geometrically summable. The conclusion also
holds on an open neighborhood of J in all participant entries, depending
only on Gamma,J. Higher rewards affect only the allowed clock amplitude.

In particular let C be the Euclidean closure of actual tuples(U,B,e,N),
D=sum_i(B_i-U_i), E=C intersect{D=0}, and mu=min_E product_i N_i.
These are compact bounded carriers and AllNever belongs to E. The theorem
proves mu<1, excluding the global AllNever-only source. It does not prove
mu=0, an absorbing equilibrium, or uniform equilibrium for a table with
positive own singleton rewards. Fin4's strictly positive global-minimum
branch remains open. This is ordinary mathematics, not new Lean certification.

The region contains J=Gamma(I-diag(beta_j)) whenever
0<beta_j<=rho^2/8, independently for each column. More generally T may have
signed entries; diagonality and proportionality are not assumptions.
The proof produces roots by local degree, an invariant region by explicit
estimates, and the actual chronological profile by a limit of finite chains.
No support word, continuous root selector, periodic return or supplied
recurrent set is required.

For the root calculations define H_i(q)=product_(j!=i)(1-q_j), and let
P_i(q) be the expected reward Z_i(S) over nonempty opponent quitting
coalitions S, with their independent product probabilities. Let Q_i(q) be
the analogous expectation of Z_i(S union{i}), including S empty; its empty
term is zero. Continue at continuation w pays C_i(q,w)=P_i(q)+H_i(q)w_i.
A proper root means 0<=q_i<1 for every i. It is Nash exactly when
C(q,w)-Q(q)>=0 and
q_i(C_i(q,w)-Q_i(q))=0. All error bounds below use the maximum norm.
The product formulas extend these polynomials to a neighborhood of zero
for the degree argument; its resulting roots lie in the actual probability cube.

## 1. Uniform expansion on a projective collar

For a homogeneous Nash root at w, write

    q>=0, s=w+Kq>=0, q_i s_i=0, w'=w+Gamma q.

Use y=Mw and normalize sum y=1. Then

    z=Ms=y+Tq, y'=y+q.

Suppose y>=0 and min y<=e=rho/2. The nonnegative column sums give

    sum z=1+one^T T q>=1.

Thus s!=0 and positivity of M gives z_i>=rho sum z>=rho for every i.
Choose i with y_i<=rho/2. Then

    rho/2 <= (Tq)_i <= tau sum_j q_j,
    sum y'=1+sum q >= g0=1+rho/(2tau) >=1+4/rho.

Some quiet j has s_j>0, so q_j=0. Therefore

    min_i y'_i/sum y' <= y_j/sum y' <=1/g0<rho/4=e/2.

Also y'=y+q>=0. Every homogeneous root over the collar has the same
strict expansion and upper collar margin. Neither a continuous selector
nor a uniform positive lower bound on individual output coordinates is
required. The latter will be replaced by a quadratic thickening.

## 2. Uniform small exact roots and their estimates

K^-1>>0 implies K is R0. If Kq>=0,q>=0 were complementary and Kq!=0,
then q=K^-1 Kq>>0 would force Kq=0, a contradiction. Invertibility
handles Kq=0. The homogeneous normal map min(q,Kq) therefore has a
positive norm lower bound on the unit sphere.

Its degree is nonzero. At offset -one its only complementary root is
q=K^-1 one>>0: every feasible root satisfies
q=K^-1(one+slack)>>0, hence slack=0. Its determinant index is
sign(det K). The R0 bound allows bounded-offset homotopy on a sufficiently
large sphere, proving that this is also the homogeneous normal-map degree.

At an exact small root against continuation w, the Continue-minus-Quit
comparison is

    C(q,w)-Q(q)=w+Kq+O(|q|^2+|w||q|).

Take w=a Gamma p and q=a h. On bounded h the rescaled normal map is

    min(h,Gamma p+Kh+O(a(|h|^2+|h|))).

First fix the enlarged compact box

    sum p=1, p_i>=-1 for every i.

Choose R so large that the homogeneous R0 lower bound dominates all offsets
Gamma p on |h|=R. For uniformly small a>0, the nonlinear normal map has
the same nonzero boundary degree. Thus there is a root |h|<R. Taking
aR<1/2 makes q=a h a proper exact finite-game Nash root.

Because proper Nash output equals the Continue offer for every owner,

    y'=Mw'=y+q+E, |E|_infinity<=C a^2,                    (3)

uniformly on this enlarged p-box and the fixed root bound. Fix C here,
before introducing any cone-thickening constant. It depends on the fixed
finite table, which is permitted. Also fix

    1<g=(g0+1)/2<g0, G=2+nR.

These have strict margins relative to the homogeneous collar bounds.
No selection continuity is used.

## 3. Quadratically thickened invariance and actual chronological limit

Choose L>0 with L(g^2-1)>=C, and only afterward shrink the amplitude
cutoff so L a<=1. Use the varying collar

    a=sum y>0, y_i>=-L a^2, min_i y_i/a<=e.

For all sufficiently small a, every degree-produced root in this varying
collar satisfies

    g a<=a'=sum M w'<=G a, min_i (Mw')_i/a'<e.          (4)

Here is the uniformity argument. If it failed along a_n->0, the bounded
rescaled roots and input p_n would have a convergent subsequence. Since
p_n,i>=-L a_n, its limit is in the closed nonnegative collar. The limit
root is a homogeneous root there. Section1 and the strict margins in g,G
then contradict the failure. This fixes the remaining amplitude cutoff
after R,C,g,G,L, without a circular choice of constants.

From (3), q>=0 and a'>=g a,

    y'_i>=-(L+C)a^2>=-L(a')^2.

The upper collar condition is preserved by (4). Thus every selected exact
root stays in this quadratically thickened cone and increases amplitude
by a factor between g and G. This replaces the unnecessarily strong
requirement that every exact output coordinate be positive.

Choose a small target A>0 with G A inside the local range. Start at
w_0=epsilon Gamma p_0 for a fixed simplex collar point p_0, for example
a coordinate vector. Repeatedly select exact small Nash roots and prefix
them until the first amplitude a_l reaches A. Then

    A<=a_l<=G A, g a_k<=a_(k+1)<=G a_k.

As epsilon->0, the length l tends to infinity. Reverse the finite roots
into physical chronological order. For each fixed chronological index j,

    A/G^j <= a_(l-j) <= G A/g^j.

A diagonal subsequence gives an infinite sequence of proper exact Nash
roots (q^0,q^1,...) and compatible continuation values (w^0,w^1,...).
The tails tend to zero geometrically, and sum_j |q^j|<infinity by the
uniform q bound. The first root is nonzero: a zero root would have equal
input/output amplitude, contradicting the surviving growth factor g>1
and the positive lower bound A/G on its input amplitude. Choosing A small
makes every quit probability at most1/2. Consequently joint original
Never mass is strictly between zero and one.

All root equations are closed finite polynomial equations/inequalities.
No action is placed after an infinite prefix, and no periodic word is
assumed. The finite reversed chains converge on every fixed chronological
initial segment, while their remainder values vanish geometrically.

For open robustness in J, retain the same root radius and the strict
homogeneous expansion/collar margins. R0 degree and these uniform bounds
persist under small changes of K, by compactness of bounded root graphs.
The inequalities defining (RAW) need not themselves persist: their role
was to supply strict output margins at the central table. The exact
coordinate estimate (3) remains true and again supplies the quadratic
thickening. The participant neighborhood is determined entirely by linear
pair data; higher rewards affect only C and the final small amplitude.

## 4. Complete-response verification

Each limit root is exact Nash against its next tail w^(j+1). Every root
is proper. Thus for each owner its prescribed value equals its Continue
offer and dominates its Quit offer:

    w_i^j=P_i(q^j)+H_i(q^j) w_i^(j+1)>=Q_i(q^j).

Since w^j->0, unrolling these equalities gives the actual prescribed and
literal Never payoffs. Unrolling the inequalities bounds every pure finite
quit deadline by w_i^0. Every behavioral deviation averages finite deadlines
and literal Never, so the full cap is also w_i^0. Hence U=Bcap=eNever.

This is a direct nonperiodic clock producer. It avoids the requirement to
close any finite support word across its folds. The threshold is deliberately
coarse; the substantive mechanism is the invariant projective collar plus
uniform degree-produced exact roots and reversed-chain compactness.

## 5. An exact Fin4 witness beyond the prior finite word tests

Take

    Gamma=[0,-20,-5,40; -60,0,-4,60; 10,30,0,-50; 10,-10,4,0],
    D0=diag(1/4096,1/11264,1/2048,1/30720), J=Gamma(I-D0).

Then det Gamma=42000, M>>0, rho=17/146, T=D0 and
K^-1=D0^-1 M>>0. Each diagonal of D0 is at most rho^2/8, so(RAW) holds.
The pair03 has both participant rewards strictly positive. Small hazards
on that pair have positive Quit offers for both active owners, regardless
of higher rewards. Thus even proper-support local product-lowness fails.

The entire scalar pencil Gamma-uJ, 0<=u<=1, equals Gamma times the positive
diagonal matrix (1-u)I+uD0. Its inverse stays strictly positive. Its determinant
is positive, so the R0 and degree calculation in Section2 gives degree one
and standard Q throughout. This example therefore survives the whole-pencil
necessary condition as well.

For a self-contained comparison, the finite word tests being exhausted here
use L=J-Gamma and an ordered sequence of supports S. For each support define

    C_S=L_SS^-1, A_S w=w+Gamma[:,S] C_S w_S.

For a real expanding eigenpair H v=lambda v, lambda>1, where H is the product
of the A_S in construction order, put w_0=v and w_r=A_Sr w_(r-1).
The strict test requires, at every phase,

    C_Sr(w_(r-1))_Sr>>0,
    (w_r)_i-J_i,Sr C_Sr(w_(r-1))_Sr>0 for every i outside Sr.   (WORD)

The three prior templates are all ordered complementary pairs, all words
(pj,pk,I minus p) for distinct p,j,k,l, and all words
(pj,I minus j,I minus p) for p!=j. These give6,24,12 orders respectively.
The displayed data fail(WORD) for every expanding eigendirection in all42
orders. For column-deficit data the quiet guard is the input linear form
w_O-Gamma_OS Gamma_SS^-1 w_S, which is used below.

The exact checker isolates all real eigenvalues above one using Sturm counts.
Every characteristic polynomial is squarefree. At each real eigenvalue it
finds a nonzero adjugate column and certifies both positive and negative guard
signs, so neither orientation of that one-dimensional eigenspace can pass.
This checks every selectable mode and relabeling in the named templates.
It does not exclude longer words or other strategy classes. All remaining
rewards are still arbitrary finite numbers; this is a source-branch exclusion,
not a claim that one chosen completion escapes every known UE theorem.

The following is complete Python/SymPy code, with no sampled inequalities.


```python
"""Exact audit of the listed word templates. No floating-point claims."""
import sympy as s
from itertools import permutations,combinations
G=s.Matrix([[0,-20,-5,40],[-60,0,-4,60],[10,30,0,-50],[10,-10,4,0]])
cs=[4096,11264,2048,30720]
D=s.diag(*[s.Rational(1,c) for c in cs]); J=G*(s.eye(4)-D)
x=s.symbols('x'); I=range(4)
words=[]
for S in combinations(I,2): words.append(('PAIR',(S,tuple(i for i in I if i not in S))))
for p,j,k,l in permutations(I): words.append(('PP3',((p,j),(p,k),tuple(i for i in I if i!=p))))
for p,j in permutations(I,2): words.append(('P33',((p,j),tuple(i for i in I if i!=j),tuple(i for i in I if i!=p))))
words=list(dict.fromkeys(words)); subsets=list(dict.fromkeys(S for _,word in words for S in word))
phases={}
for S in subsets:
 C=(J-G).extract(S,S).inv(); A=s.eye(4)
 for i in I:
  for j,b in enumerate(S): A[i,b]+=(G.extract([i],S)*C)[0,j]
 O=tuple(i for i in I if i not in S)
 Q=s.eye(4).extract(O,list(I))
 for i,a in enumerate(O):
  for j,b in enumerate(S): Q[i,b]-=(G.extract([a],S)*G.extract(S,S).inv())[0,j]
 phases[S]=(A,C,Q)

def sign_at(f,g,interval):
 g=s.Poly(g,x).rem(f)
 if g.is_zero:return 0
 lo,hi=interval
 if lo==hi:return s.sign(g.eval(lo))
 common=s.gcd(f,g)
 if common.degree()>0 and common.count_roots(lo,hi):return 0
 while g.count_roots(lo,hi)>0 or g.eval(lo)==0 or g.eval(hi)==0:
  lo,hi=s.polys.polytools.refine_root(f,lo,hi,steps=1)
 return s.sign(g.eval(lo))
counts={k:[0,0] for k in ['PAIR','PP3','P33']}
for ix,(kind,word) in enumerate(words):
 H=s.eye(4)
 for S in word:H=phases[S][0]*H
 f=s.Poly(H.charpoly(x).as_expr(),x).clear_denoms()[1].primitive()[1]
 assert s.gcd(f,f.diff()).degree()==0,(kind,word,'multiple eigenvalue')
 intervals=f.intervals(eps=s.Rational(1,100))
 for (lo,hi),mult in intervals:
  if hi<=1:continue
  while lo<=1<hi:
   assert f.eval(1)!=0,(kind,word,'unit eigenvalue')
   lo,hi=s.polys.polytools.refine_root(f,lo,hi,steps=1)
  if hi<=1:continue
  assert lo>1
  counts[kind][1]+=1
  adj=(x*s.eye(4)-H).adjugate()
  for col in range(4):
   w=adj[:,col]
   if all(sign_at(f,e,(lo,hi))==0 for e in w):continue
   tests=[]
   for S in word:
    A,C,Q=phases[S]; tests+=list(C*w.extract(S,[0]))+list(Q*w);w=A*w
   signs=[sign_at(f,e,(lo,hi)) for e in tests]
   assert 1 in signs and -1 in signs,(kind,word,(lo,hi),signs)
   break
  else:raise AssertionError('No nonzero adjugate column')
 counts[kind][0]+=1
print('Exact rejections:',counts)
M=G.inv();rho=min(M[i,j]/sum(M[:,j]) for i in I for j in I)
assert G.det()==42000 and all(z>0 for z in M)
assert rho==s.Rational(17,146)
assert all(D[j,j]<=rho**2/8 for j in I)
assert all(z>0 for z in (G-J).inv()) and M*(G-J)==D
assert J[0,3]>0 and J[3,0]>0
print('PASS: one collar witness fails every PAIR, PP3 and P33 order')
```

At the opposite boundary J=Gamma, K is singular and(RAW) fails. Nevertheless
every pure solo-j profile at the first date is an absorbing native Nash
profile: j is indifferent at its own singleton zero, and any other owner's
unilateral join gives J_ij=Gamma_ij, exactly its Continue payoff. Thus the
raw criterion is sufficient, not necessary. The numerical threshold is
also only a sufficient margin for the invariant-region proof.

## 6. Actual-source consumer and formalization handoff

For Fin4, an original signed counterexample yields a table R with own
singleton vector one at a pivot p and zero elsewhere, still without UE,
by `nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`.
The theorem `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
in `UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean` supplies
Delta=inf D_R>0 over all actual profiles. Define the native table
Z_i(S)=R_i(S)-1_(i=p) on nonempty coalitions, leaving literal Never zero.

For nonnegative own singleton rewards, late finite deadlines dominate the
Never reply in the limit. This is
`quittingTerminalPayoff_update_finiteTime_tendsto_of_profile` in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`.
Hence the full cap equals the supremum of finite replies before and after
the subtraction. Every finite pivot reply loses exactly one. On an absorbing
prescribed profile its payoff also loses one, so every debt is preserved.
Writing A=inf{D_Z(P): P actual, product N_i(P)=0}, we obtain A>=Delta>0.

Let B0>=1 bound the absolute native rewards. Moving the smallest marginal
Never mass n to one finite date forces absorption. Coupling changes four
payoffs and three other-owner caps by at most2B0 n each; the mover's own
cap is unchanged. Thus, on actual profiles and their closed carrier,

    A<=D_Z+14B0 nu^(1/4), hence mu>=(A/(14B0))^4>0.

Whenever this native table satisfies(RAW), the constructed actual Nash
profile additionally gives mu<1. This removes the AllNever-only alternative
without requiring a selected source or a realization of a carrier minimum.
It does not show that the remaining positive minimum is impossible.

The linear ingredients are already represented by
`isR0Matrix_of_strictlyPositiveInverse` in
`MathUE/LinearProgramming/PositiveInverseR0.lean` and
`r0Degree_eq_sign_det_of_nonnegative_inverse` in
`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`.
The complete cap recursion is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
The summable-hazard positivity result is
`exists_pos_le_jointSurvivalPrefix_of_summable_marginalHazard` in
`UniformEquilibrium/Quitting/Paths/SummableRootSurvival.lean`.
The actual stopping-law payoff identity is
`quittingRootSequenceHazardTerminalValue_eq_expect_stoppingLaw` in
`UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`.

The missing implementation is the all-root collar estimate, uniform local
degree lifting to exact proper roots, quadratic thickening, and reversal of
expanding finite chains into a compatible infinite chronological law. A
handoff can first formalize these finite-dimensional statements, then combine
their geometric tail bounds with the complete-response calculation in
Section4. No structure field should assume a recurrent orbit or an infinite
Nash law: both are outputs here. No new Lean proof or build is claimed.
