# Marked support orientation and actual-cap ledger chambers

## 1. Exact raw theorem

Let I be finite with at least two players. At each live date, the players
independently choose Continue or Quit. The first nonempty quitter set S
absorbs with the finite real vector r(S); live play and Never give zero.
All past actions are public. Profiles use independent private behavioral
randomization, and one player may replace its complete behavior law.
Write s_i=r_i({i})>=0. Fix a nonempty marked set M subset I.

Let W be a finite nonempty family of nonnegative normalized weights a,
so sum_i a_i=1. Define, for nonempty proper S,

    H_a(S)=sum_i a_i[r_i(S)-s_i],
    J_a(S)=sum_(i outside S)a_i[r_i(S+i)-r_i(S)],
    f_a(z)=sum_(empty!=S proper) z_S J_a(S),
    z_S=product_(i in S)z_i.

Assume:

1. Every H_a(S)>=0. Moreover H_a({h})>0 whenever a_h<1.
2. For every z in (0,infinity)^I, some a in W has f_a(z)<=0.
3. Some j in M has a_j<1 for every a in W.

The scalar proper H/J signs are a special case after normalizing one
nonzero a>=0. The singleton strictness is retained here; no arbitrary
orientation-preserving reward perturbation is asserted.

For each unmarked i choose a physical floor ell_i<=0 with ell_i<s_i,
and require r_i(S)>=ell_i whenever i is outside the nonempty coalition S.
For a finite table such a floor always exists; its numerical strength
matters in the two raw conditions below.

For every nonempty proper support D, let z in (0,infinity)^D and
q_i=z_i/(1+z_i) on D, q_i=0 outside. Define the odds indifference map
Phi_D:(0,infinity)^D -> R^D by

    Phi_i^D(z)=s_i+sum_(empty!=S subset D-i)
                       z_S[r_i(S+i)-r_i(S)].                 (1)

Let Q_i(q) be the forced-Quit endpoint, b_i(q) the immediate absorbing
reward after forced Continue, and alpha_i(q) the probability every
opponent Continues. These finite product averages are defined explicitly
in Section 2. Require:

4. If D meets M, z satisfies Phi_i^D(z)>=ell_i for every unmarked
   i in D, and Q_k(q)>s_k for every k in D intersect M, then

       (-1)^|D| det D Phi_D(z)<=0.                            (O)

5. If D is disjoint from M and Phi_i^D(z)>=ell_i for every i in D,
   then EVERY marked k satisfies

       b_k(q)+alpha_k(q)s_k<=s_k.                            (P)

These conditions quantify only over finite raw reward polynomials and
positive odds. No annotation, Nash root, actual cap, strategy, derivative
of a selected root, or desired equilibrium is supplied as an input.
The restrictions Phi_i>=ell_i are raw polynomial inequalities whose
strategic availability is proved, rather than assumed.

**Theorem.** Under these hypotheses, the infimum of total unrestricted
terminal regret over actual independent ABSORBING profiles is zero.
Consequently there is one uniform-equilibrium payoff u: for every
epsilon>0, one behavioral profile and one threshold work at every larger
finite horizon, giving prescribed expected average payoff within epsilon
of u and capping every complete unilateral replacement at u_i+epsilon.
The vector u is fixed before accuracy.

Taking M=I makes (P) and the physical-floor conditions empty. Then (O)
is a raw proper-support nonpositive orientation condition on the region
where every active player has positive Quit premium. Proper product-low
supports satisfy it vacuously. On a pair with both participant premiums
positive it is precisely the weak same-sign joining-gap condition.
On a triple it asks det D Phi_D>=0 only on its relevant premium-positive
region, rather than requiring that region to be empty.

## Conjecture-facing change

The theorem supplies an actual-data equilibrium producer for reward tables
whose proper premium-high supports need neither be absent nor have uniformly
negative local Nash index outside the region allowed by actual response
floors. Only selected players must return to a low-cap face. Proper supports
disjoint from those players may instead preserve that face through their
passive Continue averages. This removes both the same-sign pair restriction
and the higher-support product-low restriction on the explicit four-player
rectangle in Section 6. At its joint witness both restrictions fail strictly,
and the complete stationary, persistent-base and raw producer exclusions in
Section 7 show that this is new class coverage under the named comparisons.

The main theorem permits finitely many simultaneous ledgers; the separating
rectangle uses one scalar ledger. General Fin4 remains open. The theorem
does not assert that every reward table satisfies its orientation, floor,
passive-average or ledger conditions.

## Strategic inputs

The inputs are finite rewards, a marked player set, finitely many numerical
ledger weights, numerical passive floors, and the raw inequalities in
Section 1. These contain no strategic witness. Every strategic object used
in the conclusion is produced:

- A sole-owner absorbing profile supplies the common seed and its full caps.
- The ambient degree argument selects a full finite Nash root at every
  annotation used in the proof, including source-floor boundaries.
- Exact prefix formulas and the compact chamber produce an actual-cap
  diagonal and actual absorbing profiles with vanishing full regret.
- A payoff-convergent subsequence fixes one target before accuracy; the
  truncation argument controls every behavioral replacement at every
  sufficiently long horizon.

No child equilibrium, outsider cap, punishment plan, selected continuation,
return map, attained best response, recursive strategy producer or rate of
convergence is assumed.

## 2. Actual semantic carrier and exact prefix accounts

Before absorption the only live public history is repeated all Continue,
so behavioral profiles are independent laws on finite quit dates plus
Never. A replacement payoff is affine in the replacing player's law;
its supremum is therefore the supremum over all pure deadlines and Never.
This is the full behavioral response cap, without an attained optimizer.

Let K be the closure of all actual absorbing payoff/full-cap pairs (U,B).
Finite rewards make K nonempty and compact, and B>=U. The literal Never
response gives B_i>=ell_i for every unmarked i: each finite outcome then
pays a passive reward at least ell_i, and Never pays 0>=ell_i. The bound
persists on K. An actual finite independent prefix preserves absorption;
the exact continuous prefix formulas therefore preserve K.

For q in [0,1]^I, put p_q(S)=product_(i in S)q_i times
product_(i outside S)(1-q_i), c=p_q(empty), and
alpha_i=product_(j!=i)(1-q_j). If A is the independently drawn opponent
quitter set, define

    Q_i=E[r_i(A+i)],    b_i=E[r_i(A)1_(A nonempty)],
    C_i(B)=b_i+alpha_i B_i,
    Delta_i=q_i(C_i-Q_i)_+ +(1-q_i)(Q_i-C_i)_+.

Prefixing yields

    U_i'=q_i Q_i+(1-q_i)(b_i+alpha_i U_i),
    B_i'=max(Q_i,C_i(B)),
    d_i'=c d_i+Delta_i,            d=B-U.

Set E=max_i d_i and L_a(B)=sum_i a_i(B_i-s_i). On a proper-support
prefix the exact ledger account is

    L_a(B')=c L_a(B)+sum_(S nonempty)p_q(S)H_a(S)
                                      +sum_i a_i Delta_i.    (2)

At a finite Nash root annotated by B, every Delta_i is zero. If the root
is Nash instead at x=B-delta e_h, delta>=0, its ORIGINAL-game defects obey

    Delta_i=0 for i!=h,
    Delta_h<=q_h alpha_h delta=p_q({h})delta.                 (3)

Indeed only the h Continue endpoint has been raised, by alpha_h delta;
a supported Continue action stays optimal. If w is the auxiliary Nash
successor, then B_i'=w_i for i!=h and B_h'<=w_h+alpha_h delta.
Thus a low marked auxiliary successor yields a true marked cap <=s+delta.
At a sure root, c=0 and (3) gives E'<=delta.

## 3. Generic annotations and a closed three-way selector

For any annotation x satisfying

    some x_i<s_i,   L_a(x)>0 for every a in W,
    x_i>=ell_i for every unmarked i,                          (4)

there is a nonzero full finite Nash root with at least one of these
three properties:

- some hazard is sure;
- its auxiliary successor has a marked coordinate w_k<=s_k;
- it is PASSIVE-SAFE: q_k=0 and
  b_k+alpha_k s_k<=s_k for every marked k.

The final alternative deliberately retains both closed conditions.
Merely retaining membership in a disjoint support, or a relaxed low value,
would obscure the original-cap bound at a lowered annotation.

### 3.1 One dense generic source set

For each nonempty proper D, exclude from source space the critical values
of Phi_D, times all outside annotation coordinates. These form a null
set. An elementary equal-dimension C1 argument suffices: exhaust the odds
domain by compact boxes; on sufficiently small cubes meeting the critical
set, uniform differentiability approximates the map by a rank-deficient
linear map. Its image lies in a rotated box with |D|-1 sides O(delta)
and the last side at most epsilon delta. O(delta^(-|D|)) cubes give
outer volume O(epsilon), which tends to zero. Countable exhaustion proves
the claim. Equivalently one may use Sard for the polynomial map.

Also exclude all sources where a nonsure root of support D can have an
inactive tie at some outsider k. At such a tie, active indifference fixes
x_D=Phi_D(z), while the kth equation fixes

    x_k=s_k+sum_(empty!=S subset D)
                  z_S[r_k(S+k)-r_k(S)].                     (5)

The remaining outside coordinates are free. Hence these sources lie in
the image of an explicit smooth map from |I|-1 dimensions into |I|.
On each compact box it is Lipschitz; a delta-cube covering gives total
|I|-dimensional image volume O(delta), proving nullity. There are finitely
many D,k and countably many boxes. Their union with the critical-value
sets is null, so its complement G is dense.

No rewards, participant signs, physical floors, or ledger weights are
perturbed here. At a source on an unmarked floor, first move the unmarked
coordinates slightly inward, making every x_i>ell_i. The strict-below-own
condition and all finitely many L_a>0 persist under sufficiently small
changes. Thus every source (4) can be approached by G while preserving
(4), with strict unmarked floors at each approximating source.

### 3.2 All bad roots have negative full ambient index

Fix a generic source and suppose every Nash root fails the three-way
alternative. All Continue is not Nash because some x_i<s_i. Sure roots
are good by definition, so every positive rate is interior.

Full support is impossible: active indifference and positive odds give

    x_i-s_i=sum_(empty!=S subset I-i)
                   z_S[r_i(S+i)-r_i(S)],
    L_a(x)=f_a(z) for every a in W,

contradicting the odds cover and simultaneous positivity of L_a.

A remaining root has nonempty proper support D. If D is disjoint from M,
active indifference gives Phi_i^D=x_i>=ell_i, so (P) makes the root
passive-safe, a contradiction. Hence D meets M. Every active marked k
has Q_k=w_k>s_k; active unmarked coordinates obey Phi_i^D=x_i>=ell_i.
Condition (O) therefore applies. Generic critical-value avoidance makes
det D Phi_D nonzero, so its signed inequality is strict.

Write the full endpoint gaps g_i(q)=Q_i-C_i(x), extended polynomially to
real hazards, and F(q)_i=min(1,max(0,q_i+g_i(q))). Fixed points of F
are exactly full Nash roots. At the root all inactive gaps are nonzero
by genericity and negative by Nash, so inactive rows of F are locally zero.
Active rows are unclipped. Since g_i=alpha_i(Phi_i^D(z)-x_i) on the
support face, its active derivative is

    D_q g_D=diag(alpha_i) D_z Phi_D diag((1-q_j)^(-2)).        (6)

Both diagonal factors are positive. The derivative of identity minus F
has active block -D_q g_D, inactive identity block and arbitrary upper
right block. Its determinant has sign
(-1)^|D| det D Phi_D<0. This is the FULL ambient index, not a face index.

Every bad root is thus isolated and has index -1. If every root is bad,
the compact root set consists entirely of isolated points; an infinite set
would have a limiting root, contradicting isolation there. Thus it is
finite and nonempty. On Omega=(-1,2)^I, the map F and its straight-line
homotopy to the cube center take values in [0,1]^I, avoiding the boundary
of Omega. Total degree is +1. Summing the finitely many local indices -1
contradicts +1. A good root therefore exists.

### 3.3 Closed restoration

Approach an arbitrary source (4) by generic sources as above and take a
convergent subsequence of selected roots. Nash inequalities are closed.
Each sure-coordinate set is closed; the successor is continuous; and the
passive-safe tag consists of finitely many closed equalities/inequalities.
Their finite union is closed, so one of the three alternatives survives.
The limit cannot be All Continue because the original source has a strict
singleton deficit. No active label is required to survive the limit.

## 4. The marked compact chamber

Choose the common marked seed owner j. The actual sole-j Quit0 profile has
B_j=s_j and B_i=max(r_i({j}),r_i({i,j})) for i!=j. Every ledger satisfies
L_a(B)>=H_a({j})>0. If the seed has no debt, we are done. Otherwise fix

    0<lambda<=min(1/2,min_(a in W)L_a(B)/E).

Suppose K has no diagonal; compactness gives g=min_K E>0. Choose
0<e<g sufficiently small that lambda e is below every positive singleton
H_a. The nonempty compact chamber is

    C_e={(U,B) in K: min_(k in M)(B_k-s_k)<=e,
                       L_a(B)>=lambda E for every a in W}.

Minimize E on C_e. Its value exceeds e. The following case split uses
m=min_ALL(B-s), although the chamber's low face is marked.

If m<0, apply the selector at x=B; physical floors hold on K. A sure
root gives E'=0. A nonsure root is proper by the odds cover. Its low
marked successor directly preserves the marked face. If it is passive-safe,
choose any original marked k with B_k<=s_k+e. Since q_k=0, Nash at
x<=B gives Q_k<=C_k(x)<=C_k(B), so the true cap is C_k(B). Thus

    B_k'=b_k+alpha_k B_k
          <=s_k+alpha_k(B_k-s_k)<=s_k+e.                     (7)

In this exact-source case x=B; the same argument applies to the lowered
source below because it too has x<=B. No raw bound on Q_k is needed in
the passive-safe condition.

Every defect is zero. Formula (2) preserves every ledger, and E'=cE<E
because the selected root is nonzero. This contradicts minimality.

If m=0, choose ANY tied owner h, marked or unmarked. For every a in W,
a_h<1; otherwise a=e_h and L_a(B)=0. Hence
h_*=min_(a in W)H_a({h})>0. Choose delta>0 with

    delta<=e, delta<g, delta<E, lambda delta<h_*,
    every L_a(B-delta e_h)>0,
    delta<s_h-ell_h if h is unmarked.

The last inequality preserves the physical source floor because B_h=s_h.
Apply the selector at x=B-delta e_h. A sure root has true E'<=delta<g,
impossible on K. A nonsure root is proper. A low marked auxiliary successor
gives a true marked cap <=s+delta<=s+e by (3). A passive-safe root uses
(7) at ORIGINAL B; no e+delta error is introduced. Finally

    E'<=cE+p_q({h})delta<=cE+(1-c)delta<E,
    L_a(B')-lambda E'>=c[L_a(B)-lambda E]
                         +p_q({h})[H_a({h})-lambda delta]>=0.

This is another original-game point in C_e with smaller debt, contradiction.

If m>0, choose h in M with smallest marked excess m_M. Then
0<m_M<=e<E. Give only h a sufficiently small hazard p>0. All other
Continue margins remain strict, the only defect is p m_M, and B_h stays
fixed. Thus the marked face is preserved and

    E'<=(1-p)E+p m_M<E,
    L_a(B')-lambda E'>=(1-p)[L_a(B)-lambda E]
                       +p[H_a({h})+(a_h-lambda)m_M].

For a_h<1, the bracket is positive by the choice of e. For a_h=1 it
equals (1-lambda)m_M>0. Every ledger is preserved, again a contradiction.
Thus K has a diagonal, and actual absorbing approximants have total full
terminal regret tending to zero.

To obtain one uniform target, take a payoff-convergent subsequence of those
actual approximants; their caps converge to the same vector u. For any fixed
profile, let T_-i be the first opponent quit date and
eta_i(t)=Pr(t<T_-i<infinity), which tends to zero. Truncate an arbitrary
deviator's quit plans after t to Never. The truncated terminal payoff is at
least its absorbed reward by t minus R eta_i(t), for a common absolute
reward bound R. Thus the N-stage deviation payoff is at most
B_i+(R/N)sum_(t<N)eta_i(t)+2R/N, uniformly over the entire replacement
law. The last term covers the possible one-stage timing boundary between
the quitting date and the first paid absorbing stage.
Prescribed averages tend to U by bounded convergence. Choose the profile
close to u first, then a common horizon threshold; this proves the fixed
target and all-horizon uniform deviation contract.

## 5. Finite raw corollaries

### 5.1 Marked participant certificates

If for a proper D meeting M there is b^D>=0, supported on D intersect M,
of sum one, with sum_(i in S)b_i^D(r_i(S)-s_i)<=0 for every nonempty
S subset D, then

    sum_(i in D)b_i^D q_i(Q_i-s_i)
      =sum_(S nonempty)p_q(S)sum_(i in S)b_i^D(r_i(S)-s_i)<=0.

Some active marked player is therefore low. Condition (O) is vacuous on
this support, without a derivative test. A single marked participant flat
on every containing subcoalition supplies a point-mass certificate.

### 5.2 A physical-floor rectangle for an unmarked pair

For Fin4, let A={i,j}, M=I\A and suppose the marked certificate above
holds for every proper support meeting M. Suppose an actual floor ell_j
has D_j=r_j({i})-r_j(A)>0, and put A_j=s_j-ell_j>0. For every k in M,
require

    r_k(i)<=s_k,   r_k(j)<=s_k,
    A_j[r_k(A)-s_k]<=D_j[s_k-r_k(j)].                        (8)

At positive pair odds with Phi_j>=ell_j, the negative joining gap gives
q_i<=(s_j-ell_j)/(s_j-ell_j+D_j)=rho. The marked certificate on A+k
has only k in its marked intersection, so Q_k<=s_k. The passive Continue
excess at own cap is bilinear on [0,rho] times [0,1]. Its four corners
are nonpositive by (8). Thus b_k+alpha_k s_k<=s_k. The same properties
for the unmarked singleton supports follow from (8) and their marked
two-player certificates. This proves (P), with no condition on the other
pair joining gap. The scalar case with all singleton H strictly positive
is a complete raw corollary.

### 5.3 Conditional triple orientation

For a triple D={i,j,k}, write d_ij=r_i(ij)-r_i(j) and
e_i=r_i(D)-r_i(D-i). Then

    Phi_i=s_i+d_ij z_j+d_ik z_k+e_i z_j z_k,
    partial_j Phi_i=d_ij+e_i z_k,
    det D Phi=(d_ij+e_i z_k)(d_jk+e_j z_i)(d_ki+e_k z_j)
             +(d_ik+e_i z_j)(d_ji+e_j z_k)(d_kj+e_k z_i).

Nonnegative determinant is sufficient only on the marked-premium-positive
region that also satisfies the active unmarked physical floors. This can
be much larger than a global sign-pattern theorem. If all d_ij are nonzero,
both directed cycle products are positive and e_i d_ij>=0 for every edge,
the determinant is strictly positive for every positive odds vector. This
recovers joining-attractive and several mixed-sign configurations without
requiring that the greatest premium core be the triple.

## 6. One table containing both former obstructions

Use unit scalar ledger weights, own singletons 1, and this two-parameter
table. Equivalently take W={(1/4,1/4,1/4,1/4)}. The complete rectangle
is -2<=T<=6 and -4<=t<=5.

| S | r(S), in order 0,1,2,3 |
| --- | --- |
| 0 | (1,0,4,0) |
| 1 | (0,1,0,4) |
| 2 | (4,0,1,0) |
| 3 | (0,4,0,1) |
| 01 | (-1,1,5/2,3/2) |
| 02 | (T,2,2,2) |
| 03 | (2,3/2,3/2,-1) |
| 12 | (3/2,-3,1,9/2) |
| 13 | (2,0,2,0) |
| 23 | (5/2,3/2,-1,1) |
| 012 | (-1,t,-1,10) |
| 013 | (-1,-1,10,-1) |
| 023 | (-1,10,-1,-1) |
| 123 | (10,-1,-1,-1) |
| 0123 | (9,9,9,9) |

All singleton H are 1. Pair H are zero except H(02)=T+2; triple H
are 3 except H(012)=t+4. Singleton J=(-2,-4,T-6,-3), pair J in
order 01,02,03,12,13,23 are (-6,t-5,-5,-8,-6,-6), and every triple
J is -1. Thus the displayed rectangle satisfies the ledger hypotheses.

Take M={1,3} and physical floors ell_0=ell_2=0; every relevant passive
reward is nonnegative. Marked flat owners cover every proper support
meeting M except possibly triple 012: pairs 01,03,12,13,23 have owners
1,3,1,1,3, and triples 013,023,123 have owners 3,3,1.

On triple 012, the unmarked owner-2 odds coordinate is

    Phi_2=1-2z_0+z_1-(7/2)z_0 z_1.

If z_0>1/2, both 1-2z_0 and 1-(7/2)z_0 are negative, contradicting
Phi_2>=0. Therefore q_0<=1/3. But

    Q_1-1=q_2[-4+(t+3)q_0]<=0

for every -4<=t<=5: if t+3<=0 this is immediate, and otherwise the
bracket is at most -4+8/3<0. Hence the antecedent of (O) is empty even
when the triple has all-premium product roots at unrealized annotations.

For the disjoint pair 02, Phi_2=1-2z_0>=0 gives q_0<=1/3. The same
Q_1 bound applies, while marked owner 3 is flat on triple 023. Both marked
owners have passive singleton rewards 0 on 0,2 and passive pair reward 2
on 02. Their own-cap Continue excess is

    -q_0(1-q_2)-(1-q_0)q_2+q_0 q_2
       =-q_0-q_2+3q_0 q_2<=0

on [0,1/3] times [0,1], by its four corners. The two disjoint singleton
supports are passive-safe as well. Thus (P) holds and the theorem proves
UE throughout the rectangle.

At T=t=5, pair 02 has positive participant premiums and joining gaps
(+1,-2), violating the previous pair sign condition. Triple 012 has all
active premiums positive at q=(9/10,1/10,1/10,0): the active premiums
are exactly (4/25,8/25,63/100). Hence higher proper product-lowness also
fails. This point is outside BOTH structural restrictions of the preceding
class.

The physical-floor restriction also does real work in the orientation
condition. On triple 012, take odds (z_0,z_1,z_2)=(11/10,1/10,1/10).
Every active premium is positive, with exact values
(18/121,4/231,8/21), but det D Phi=-759/400<0. Its unrestricted
triple index would be positive. The excluded actual coordinate is
Phi_2=-297/200<0. Thus the new theorem is not merely applying a globally
valid nonpositive orientation condition to the same table.

For comparison, at T=t=3 one may instead take M=I and use the orientation
test itself. The only positive-premium pair is 02, with joining gaps
(-1,-2); its determinant is -2 and its index is negative. On triple 012,
Q_1>1 forces z_0>2. Setting z_0=2+u gives

    det D Phi=4+(23/2)z_1+z_2+(25/4)z_1z_2
                 +u[11/2+(49/4)z_1+(17/2)z_2+(35/2)z_1z_2]>0.

The other triples are product-low, so this is a nonvacuous orientation
application. For example q=(3/4,1/10,1/2,0) has active Quit values
(17/10,5/4,61/40), all strictly above one, at T=t=3.
The single theorem includes both this determinant argument and the
opposite-sign pair region through its marked-floor conditions.

## 7. Complete named producer exclusions at T=t=5

All assertions in this section concern the single table in Section 6 with
T=t=5. They compare complete selections of the named producers, without
asserting an enumeration of every conceivable nonstationary certificate.

### 7.1 Protected, weighted, core and boxed raw entrances

A player i is protected when r_i(S)>=s_i for every coalition containing i.
A premium trap D is a nonempty set such that each i in D has some
S subset D containing i with r_i(S)>s_i. The greatest premium core is
the largest such set. A global inserted-premium floor uses a nonzero w>=0
and requires, for EVERY coalition S including empty and sets outside a trap,

    W_w(S)=sum_i w_i[r_i(S union {i})-s_i]>=0.

A weighted upper-average test uses nonzero nonnegative weights and
nonpositive weighted premium sums on every coalition of its support.
Both its inserted-premium and participant-only versions require, on the
full support, sum_i w_i[r_i(I)-s_i]<=0. These are distinct predicates
from the H_a lower ledgers of Section 1.

Every player has a proper-triple participant reward -1, so no player is
protected. The grand reward 9 makes I a premium trap, hence the greatest
premium core is all four players. This excludes hypotheses requiring that
core to have at most two members or exactly three members, including
joining-attractive and mixed-sign three-core entrances. Grand premiums
are all 8, defeating every nonzero full-support weighted upper-average
test and every global product-low test.

For a global-floor weight w, singleton 1 requires -2w_0-w_3>=0,
whereas singleton 3 requires w_0-w_1-2w_2>=0. Their sum is
-w_0-w_1-2w_2-w_3, at most -1 after sum w=1. Thus no nonzero
global-floor weight exists. This quantitative contradiction persists under
small reward perturbations, so it also excludes reward closure of that
raw entrance, including every full-trap weighted-leaver choice.

For the boxed full-trap entrance define

    P_I(S)=sum_(i outside S)[r_i(S+i)-s_i],
    J_I(S)=sum_(i outside S)[r_i(S+i)-r_i(S)].

Its positive coefficients D,G,tau,L require P_I({j})<=-D and
J_I({j})<=-G on singletons, P_I(S)<=0 and J_I(S)<=0 on every
two-player S, and P_I(I-j)<=tau and J_I(I-j)<=-L on triples,
before any further charge threshold can be considered. Here

    P_I(02)=(r_1(012)-1)+(r_3(023)-1)=4-2=2>0.

No coefficient choice satisfies the middle condition; the strict failure
persists in a reward neighborhood. Also P_I({2})=0 already contradicts
D>0. The full set is a trap, so choices for any proper trap cannot
repair this missing full-trap branch in a mixed boxed criterion. A mixed
upper-average-or-boxed criterion also fails on this same full trap, since
the grand row excludes its upper-average alternative.

The opposite pair 02 has two positive participant premiums and gaps
(+1,-2), while triple 012 has the strictly positive premiums displayed
in Section 6. Thus proper product-low criteria and the same-sign-pair
criterion with higher proper product-lowness fail. These strict failures
also exclude their reward closures. The same example violates the
unrestricted positive-premium orientation test by det D Phi=-759/400;
the actual physical floor is essential.

The singleton comparison matrix in Section 7.3 has mutually negative
entries Gamma_01=Gamma_10=-1, so a no-mutually-negative-entry screen
does not apply. This is only an exclusion of that explicit screen.

For completeness, consider the cyclic fixed participant template with own
singleton 1, two neighboring singleton rewards 0 and opposite singleton
reward P_i>=4, adjacent pair participants (-1,2), opposite pair
participants (0,0), and triple participants -1. Allow every other passive
reward and every grand reward to vary. Each recipient in the displayed
table has singleton values {0,0,1,4}. A positive recipient-affine
transformation matching these singletons must send the template's two
zero passive values to the two zeros, forcing shift 0, and its own value
1 to 1, forcing scale 1; this remains true under player relabeling.
The participant value
r_0(02)=5 is outside {-1,0,2}. Thus no such template or relabeling
produces this table. This comparison concerns that stated participant
template, not all monotone-cap constructions.

### 7.2 No exact stationary equilibrium

Every passive reward is nonnegative. The literal Never response therefore
guarantees nonnegative reward against every opponent behavior. At a
stationary equilibrium, values are nonnegative. Every active nonsure
player with an active opponent satisfies

    v_i=Q_i=N_i=b_i/(1-alpha_i),

where N_i is its Never payoff; in particular Q_i>=b_i.

First exclude sure owners 0,1,3. For these owners, respectively, the
opposite player's joining gaps over the four possible subsets of the
remaining players are

    (-2,-7/2,-5/2,-1),
    (-4,-5/2,-11/2,-1),
    (-4,-5/2,-5/2,-1).

Thus the opposite Continues. The predecessor's two remaining gaps are
(-1,-5/2) in each case, so it Continues too. The successor gaps are
1,1,2, respectively, forcing that successor to Quit surely. The original
owner's Quit payoff is -1,-3,-1, respectively; withdrawal gives 0.
This contradiction uses only the nonowners' full root best responses and
the owner's Quit-versus-Continue comparison.

For a sure owner 2, no other player can be sure by the preceding argument.
Let z_0,z_1,z_3 be their finite nonnegative odds. Owner 2's necessary
inequality Q_2>=b_2, after division by positive opponent survival, is

    1-2z_0+z_1-(7/2)z_0z_1
      -z_3-(5/2)z_0z_3-3z_1z_3-z_0z_1z_3>=0.

All terms involving z_3 are nonpositive. As in Section 6 this implies
q_0<=1/3. At q_2=1, player 1's endpoint gap is

    g_1=-3+6q_0+(1/2)q_3-(9/2)q_0q_3.

Its maximum on [0,1/3] times [0,1] is -1, by the four corners, so
q_1=0. The remaining two free endpoint gaps are

    g_0=1-(9/2)q_3,       g_3=1-4q_0.

Their Nash points are exactly (q_0,q_3)=(1,0),(0,1),(1/4,2/9):
the strict threshold comparisons give the two vertices or both equalities.
The first violates q_0<=1/3. At (0,1), owner 2 has Q_2=-1<b_2=0;
at (1/4,2/9), it has Q_2=3/4<31/36=b_2. Thus no sure owner is
possible, even with any nonnegative continuation value.

All-Never fails at own reward 1. A sole active player fails at its cyclic
successor, whose Never payoff is 0 and whose Quit payoff is positive.
On adjacent supports 01,12,23,30, the successor has Never payoff 0 and
Quit endpoint respectively 1,1,1,1+q_3. On opposite pair 02, active
player 2 has Never payoff 4 and Quit endpoint 1+q_0<2. On opposite
pair 13, active player 1 has Never payoff 4 and Quit endpoint 1-q_3<=1.
This excludes every nonsure support of size at most two.

On support 013 put (a,b,c)=(q_0,q_1,q_3). The inequality Q_3>=b_3
is 1-2a-5b+(7/2)ab>=0. It gives a<1/2 and b<=1/5. But
Q_0=1+c-2b-bc>=3/5, whereas N_0=2bc/(b+c-bc)<=2b<=2/5.
On support 123 put (a,b,c)=(q_2,q_3,q_1). The inequality Q_1>=b_1
is 1-4a-5b+(11/2)ab>=0, giving a<1/4 and b<=1/5. Then
Q_2=1-2b>=3/5, while N_2=2bc/(b+c-bc)<=2b<=2/5.

On support 012 put (a,b,c)=(q_0,q_1,q_2). The exact endpoints are

    Q_0=1-2b+4c-4bc,       b_0=4c-(5/2)bc,
    Q_1=1-4c+8ac,          b_1=2ac,
    Q_2=1+a-3ab,           b_2=4a-(3/2)ab.

The inequalities Q_2>=b_2 and Q_1>=b_1 give a<=1/3 and c<=1/2.
Since Q_1=N_1<=2c and Q_1>=1-4c, also c>=1/6. Finally
Q_0>=b_0 gives b<=1/2. Player 0's stationary residual is

    F_0=(b+c-bc)Q_0-b_0
       =b(1-2b)-c[3-(7/2)b+2b^2-4c(1-b)^2].

Because c<=1/2, the bracket is at least 1+b/2>=1. Therefore
F_0<=1/8-c<=-1/24<0, contradicting active indifference.

On support 023 put (a,b,c)=(q_0,q_2,q_3). Only players 2 and 3 are
needed:

    Q_3=1-2a,         b_3=2ab,
    Q_2=1+a-2c-ac,    b_2=4a-(5/2)ac.

The equality Q_3=N_3<=2a gives a>=1/4. The inequality Q_2>=b_2
gives a<=1/3 and c<=2/13. Player 2's stationary residual is

    F_2=(a+c-ac)Q_2-b_2
       =a^2-3a+c(1+a/2-2a^2)-c^2(2-a-a^2).

For a in [1/4,1/3], its constant term is at most -11/16, its c
coefficient is at most 1, and its c^2 coefficient is negative. Thus
F_2<=-11/16+2/13=-111/208<0.

Finally, a full nonsure support has strictly positive terminal singleton
masses. Every H(S)>=0, singleton H values are 1, and grand H is 32,
so the actual stationary value v has L(v)>0. Full-support indifference
instead gives L(v)=sum_(proper nonempty S)z_S J(S)<=0. This excludes
the final support and completes the exact stationary census.

### 7.3 Reward closure of the exact stationary entrance

The singleton comparison matrix Gamma_ij=r_i({j})-1 is

    Gamma=[ 0,-1, 3,-1;
           -1, 0,-1, 3;
            3,-1, 0,-1;
           -1, 3,-1, 0].

Its pair principal determinants, in order 01,02,03,12,13,23, are
(-1,-9,-1,-1,-9,-1). All four triple principal determinants are 6,
and det Gamma=45. Hence no nonzero p>=0 satisfies

    Gamma p>=0,       p_i(Gamma p)_i=0 for every i.            (9)

Indeed an active support of size at least two would give a nonzero kernel
vector of its invertible principal block. A singleton support fails at
an external entry -1. This is the R0 complementarity property needed here.

Suppose reward tables tending to this table have exact stationary Nash
hazards q^n, and pass to a convergent hazard subsequence. If the limit q
is nonzero, the stationary payoff is a continuous quotient with positive
total absorption probability. The root Bellman inequalities pass to the
limit. If at least two players remain active, every player faces an
opponent's eventual absorption; iterating those inequalities bounds every
deadline and Never, hence every full stopping law. If only player j remains
active, all other players still face that absorption, while owner j's own
singleton 1 is at least Never 0. Thus q would be an exact stationary Nash
of this table, contradicting Section 7.2.

If q^n tends to zero, put p^n=q^n/sum_i q_i^n and pass to a simplex
limit p. Own rewards near 1 exclude All-Never, so the normalization is
defined. Conditional terminal singleton masses tend to p and all larger
coalition masses tend to zero; the payoff limit is 1+Gamma p. Date-zero
Quit deviations imply Gamma p>=0. For p_i>0, player i is eventually
active with interior hazard, and active indifference gives
(Gamma p)_i=0. This contradicts (9). Therefore the table is outside
reward closure of the exact stationary producer. No positive gap for
arbitrarily accurate stationary approximate equilibria is asserted.

### 7.4 Every persistent-base induced-Nash punishment-tail selection

A persistent-base selection fixes a nonempty set of sure quitters, a
disjoint free set whose actions form an induced Nash point, and outsider
no-join inequalities. For a singleton base j, the latter two requirements
make every nonowner a full best response in the sure-j row, regardless of
which players were labeled free. Its owner-floor condition is

    Q_j>=b_j+alpha_j chi_j,

where chi_j is its punishment floor, the infimum over all opponent plans
of the supremum over all complete behavioral replies. Literal Never
guarantees nonnegative payoff against every plan, so chi_j>=0 for every
player of this table. Thus the necessary owner inequality is Q_j>=b_j.

For bases 0,1,3, the exact cascade in Section 7.2 forces a sure successor;
owner-deleted survival is zero and the owner's negative Quit payoff is
strictly below its immediate withdrawal payoff 0. For base 2, the same
Q_2>=b_2 assumption forces q_0<=1/3, then q_1=0, and the two-player
threshold calculation in Section 7.2 excludes every remaining root.
This proof covers every free set, every induced boundary or interior Nash
point, and every permissible punishment choice. It does not substitute
failure of stationary repetition for the owner-floor test.

For a base of size at least two, each withdrawing owner faces another sure
quitter. Owner-leave, free-player Nash and outsider no-join conditions
therefore give all the full sure-root Nash inequalities, independently of
the continuation tail. Section 7.2 excludes every such root. The separate
all-Never owner chamber requires an own singleton <=0, whereas all own
singletons here equal 1. Thus the full persistent-base and all-Never
owner-chamber selection sets fail at this table.

## 8. Boundary tests and exact scope of the hypotheses

The entire closed rectangle in Section 6 includes the raw boundaries
H(02)=0 at T=-2, J({2})=0 at T=6, H(012)=0 at t=-4, and
J(02)=0 at t=5. Singleton H remains strict throughout, so these equality
cases are genuine theorem instances. The nonvacuous orientation example
T=t=3 and the joint opposite-sign/high-triple example T=t=5 test different
parts of the same mechanism.

The selector explicitly permits singular support maps and zero signed
determinants: their critical values are excluded only at generic sources,
then restored by the closed alternative. Actual unmarked floors may be
attained; generic approximation is from their interior. Marked labels may
lose positive hazard in a limit; the successor-low and passive-safe tags
remain closed without an active-label assumption. Unit ledger vectors are
allowed and are handled separately in the positive-minimum case. The
common marked seed is still required.

The strict singleton-H requirement is intentional. Weak determinant
orientation and passive-average inequalities need not survive arbitrary
passive-singleton reward perturbations. Specialized same-sign pair classes
can admit a separate perturbation preserving their participant conditions;
no such general weak-H extension is claimed here. Likewise the proof does
not replace physical floors by arbitrary source inequalities: their
availability at every actual cap and every lowered annotation is essential.

## 9. Source correspondence

The following exact Lean declarations are correspondences and reusable
services. The combined marked raw theorem and its adapter above are ordinary
mathematics, not a claim that these new steps are already checked in Lean:

- `quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
  and `quittingRootContinuePayoff_update_add` in
  `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
- `exists_exactRoot_singletonSublevel_of_badRoot_negative_derivatives`
  in `UniformEquilibrium/Quitting/Root/NegativeBadRootSelectedReturn.lean`.
  This is a conditional derivative consumer. Sections 1 and 3 supply its
  new reward-only, floor-restricted data and adapt its good alternative.
- `tripleNash_hasFDerivAt_and_negative_det_fullClippedDisplacement`
  in `UniformEquilibrium/Quitting/Root/TripleFullClippedJacobian.lean`.
- `mixedSignTripleNash_hasFDerivAt_and_negative_det` in
  `UniformEquilibrium/Quitting/Classification/MixedSignTripleCoreJacobian.lean`,
  and `exists_uniformEquilibriumPayoff_of_mixedSignTriple_core` in
  `UniformEquilibrium/Quitting/Classification/Existence/MixedSignTripleCoreUniformPayoff.lean`.
  Its greatest-core-cardinality-three hypothesis is absent here; grand
  rewards make the displayed witness's greatest core the entire four-set.
- `IsSupportwiseQuittingPremiumWeightCertificate` in
  `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumBalanceAt.lean`.
- `HasProductLowQuittingPremium` in
  `UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`;
  `IsCommonQuittingPremiumLeaver` in
  `UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`;
  and `HasProtectedParticipantPremiums`,
  `HasSupportSpecificQuittingLeavers`, `quittingMaximalProtectedPlayers` in
  `UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`.
  Section 7.1 excludes every protected-set choice and the full-support
  product-low hypothesis, not merely a selected protected set.
- `quittingPremiumCore` in
  `UniformEquilibrium/Quitting/Classification/QuittingPremiumCore.lean`;
  `exists_exactRoot_singletonSublevel_of_signed_pair_core` in
  `UniformEquilibrium/Quitting/Classification/SignedPairCoreSelectedReturn.lean`;
  and `exists_uniformEquilibriumPayoff_of_joiningAttractive_core` in
  `UniformEquilibrium/Quitting/Classification/Existence/JoiningAttractiveCoreUniformPayoff.lean`.
  The explicit full premium trap violates their stated small-core premises.
- `HasGlobalQuittingWeightedFloor` and `HasWeightedQuittingTrapLeavers` in
  `UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`.
  Their full weight selection is excluded by the two singleton floor rows
  in Section 7.1.
- `QuittingTrapChargeCoefficients` and `quittingTrapInsertedPremiumSum` in
  `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`.
  Its middle-coalition field is impossible at P_I(02)=2, independently of
  all four positive coefficient choices. This defeats
  `HasBoxedQuittingNashCharges` in
  `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`.
- `quittingSingletonBaseOwnerFloorExcess`,
  `quittingSingletonBaseOwnerFloorExcess_nonpos_iff`,
  `nonempty_quittingSingletonBaseCertificate_of_inducedNash`, and
  `quittingPersistentLargeBaseExcess_nonpos_iff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`;
  `QuittingInducedOwnerChamber` and `QuittingInducedOwnerNeverChamber` in
  `UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`;
  and `exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.
  Section 7.4 excludes their entire base/free-set/Nash-point selection,
  using the actual punishment floor rather than a selected tail value.
- `quittingPunishmentValue` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean` is the infimum of
  full behavioral best-response values over all opponent profiles. Literal
  Never proves the nonnegative lower bound used in Section 7.4 directly.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The cap recursion in TerminalDebtPrefix has no Nash hypothesis. Its
neighboring debt theorem assumes a root at prescribed payoff U; Section 2
derives the B-annotated and lowered-source accounts directly instead of
silently changing that hypothesis. The generic orientation selector needs
the full ambient clipped index, including inactive identity directions,
and its closed passive-safe alternative is new data beyond a face-index
calculation or a supplied derivative consumer.

## 10. Actual-data adapter and semantic consumer

The adapter takes only the finite table and raw numerical witnesses from
Section 1. It produces actual Never floors, a common absorbing seed, and
a selected full Nash root at every source reached by the chamber. Those
are proved for the original reward table; no reward perturbation, child
game or supplied response optimizer is used. The closed three-way selector
supplies exactly the marked-face property required by the original-cap
prefix account, including the one-coordinate lowering at a tied source.

The compact minimization then produces absorbing profiles whose full
terminal regret tends to zero. In finite dimension, zero infimum of the
maximum nonnegative regret is equivalent to zero infimum of its sum.
The all-errors terminal conclusion supplies the hypothesis of
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
Section 4 also proves the fixed-target uniform endpoint directly, so the
probability, target-order and all-deviation contracts are explicit.

## 11. Lean handoff

State a raw marked-orientation predicate with finite reward data, the marked
set, finite normalized ledgers and passive floors. Its fields should be the
H inequalities, odds cover, common marked seed, and polynomial conditions
(O),(P); no selector, actual-cap diagonal or equilibrium should be a field.
An existential theorem may quantify over this finite raw data.

The main proof can be split into these reusable lemmas:

1. An odds indifference map and its full clipped displacement derivative,
   with positive diagonal factors as in (6).
2. Density of simultaneous critical-value and inactive-tie avoidance for
   the finitely many proper supports, including inward approximation at
   unmarked physical floors.
3. A full Nash selector returning the closed sure/marked-low/passive-safe
   alternative from the raw signed determinant conditions and odds cover.
4. The exact B-annotated cap/debt recursion and the one-owner lowering
   defect bound delta p_q({h}), using the existing full-cap recursion.
5. The simultaneous marked compact chamber, its three minimum cases, and
   actual absorbing approximation to a diagonal.
6. The complete rectangle adapter and the separate exact finite tests
   recording its class separation.

The finite determinant expansions, H/J table, physical-floor rectangle
corners, sure-owner endpoint comparisons and Gamma principal determinants
are suitable exact rational tests. The mathematical consumer must retain
all behavioral deviations and a target chosen before accuracy. No Lean
source or import refactor is prescribed by this packet.

## 12. Scope and nonclaims

This is a complete ordinary-mathematical existence theorem for the stated
raw class and a strict new class exclusion under the named comparisons.
It is not a proof or disproof of arbitrary Fin4, and does not classify all
possible nonstationary strategies or supplied certificate interfaces.
The exact stationary census and its reward-closure exclusion do not assert
a positive regret gap over approximate stationary profiles. The finite
ledger generality is part of one mechanism; the scalar rectangle supplies
the explicit new-coverage evidence. No Lean implementation or unrestricted
weak-singleton-H extension is claimed.
