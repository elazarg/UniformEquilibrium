# Original-reward completion classes from crossing transports and stationary contraction

This packet proves a uniform-equilibrium producer for a union of explicit
four-player quitting-game reward classes. The main unbounded class permits
eight independent crossing-passive rewards, four independent nonnegative
favorite increments, and sixteen wholly unrestricted higher raw rewards.
Its eight affine guards are

    alpha_k >= -3,   beta_k >= -3 - 5*tau_(w_k),   tau_i >= 0.

At zero increments this contains the entire independent orthant
[-3,infinity)^8 and, in particular, every completion with the eight tested
participant-triple premiums nonnegative. A separate flexible-contact
polyhedron permits perturbations of singleton and joining data. A signed
finite-box polyhedron admits additional points outside the simple orthant.

A stationary construction covers a sixteen-dimensional relative tube of
negative passive completions. Together these results solve the entire
common-passive line H in R for the exact fixed singleton/contact data
specified below. The sixteen free raw coordinates of the crossing producer
are not free in the stationary branch; the two scopes are stated separately.

Every branch produces an exact terminal Nash profile against all complete
behavioral replacements, including Never. Arbitrary finite signed own
singleton offsets are allowed. Each profile supplies one fixed uniform-
equilibrium target with an explicit O(1/N) finite-horizon bound.

The complete finite calibration in Section 6 has a positive stationary
exploitability gap, yet the periodic producer solves it and an explicit full
sixty-dimensional reward cube around it. Section 13 compares this calibration
with the named complete raw sufficient criteria, including all their stated
roles and scales, and lists the abstract certificate and qualitative
neighborhood domains left unclassified. The general Fin4 conjecture remains
open. The proofs and exact rational certificates here are ordinary
mathematics; no Lean formalization is asserted.

## 1. Model and finite raw hypotheses

There are four players I={0,1,2,3}. At every live date they independently
choose Continue or Quit. The first nonempty quitter coalition S absorbs at
the finite vector r(S). Live and Never rewards are zero. Strategies and
unilateral replacements are unrestricted behavioral strategies. The theorem
constructs one independent periodic profile and one fixed target, working
for every accuracy over all sufficiently long finite horizons.

For each owner i set s_i=r_i({i}) and z_i(S)=r_i(S)-s_i on nonempty S.
The native live and Never rewards remain zero. Define

    Gamma_ij=z_i({j}),       J_ij=z_i({i,j}),
    d_i(B)=r_i(B union{i})-r_i(B),  i notin B, B nonempty.

Own offsets s_i have arbitrary finite signs. Their use will be justified by
opponent-deleted absorption, rather than by a general translation claim.

Put f(i)=i xor 1 and use these PREFIX phases, with indices modulo four:

| k | S_k | w_k | v_k |
| --- | --- | ---: | ---: |
| 0 | 13 | 1 | 3 |
| 1 | 12 | 2 | 1 |
| 2 | 02 | 0 | 2 |
| 3 | 03 | 3 | 0 |

Set

    e=1/1000000, eta=1/2000,
    l=(7/10,73/100,3/5,3/4),
    W-=106/1000, W+=167/1000, c+=7/10+e.

The first raw tests are the following linear inequalities:

1. For both ordered directions i,j in each S_k,
   1/100-e <= J_ij <= 1/100+e.
2. With c_k=d_(w_k)({v_k}) and a_k=d_(v_k)({w_k}),
   7/10-e <= c_k <= 7/10+e and 1/20-e <= a_k <= 1/20+e.
3. Every favorite contact satisfies d_i({f(i)}) <= -1+e.
4. At every S_k, d_(f(w_k))(S_k) <= -1+e and
   d_(f(v_k))(S_k) <= 1+e.

For an outsider i of S_t, define the literal passive polynomial

    P_(i,t)(x,y)=Gamma_i,w_t y(1-x)
                 +Gamma_i,v_t x(1-y)+z_i(S_t)xy.       (1)

The remaining raw tests are **32 affine vertex inequalities**. For each k,
put i=w_k and require

    P_(i,k+2)(x,y) >= eta
      for x in {l_(k+2),1}, y in {W-,W+};              (2)

    P_(i,k+3)(x,y) >= c+ l_k/(1-l_k)+eta
      for x in {l_(k+3),1}, y in {W-,W+}.              (3)

All vertex coordinates are fixed rational constants. Thus (2)--(3) are
linear inequalities in the sixty original rewards, not inequalities on an
unknown strategy or a supplied continuation. No lower bound is imposed
separately on favorite passive singleton premiums or second-inactive passive
pair premiums. Coordinates absent from these tests are unrestricted.

**Theorem.** Every finite reward table satisfying tests 1--4 and (2)--(3)
has an exact terminal Nash profile, repeated in chronological order
03,02,12,13. Each active hazard is proper. Against every unilateral complete
replacement, the survival probability for t dates is at most (9/10)^t.
If M=max_(i,S nonempty)|r_i(S)|, there is one fixed target u with

    |prescribed N-stage expected average_i-u_i| <= 10M/N,
    deviating N-stage expected average_i <= u_i+10M/N.   (4)

The same profile works for every accuracy. This is a uniform-equilibrium
payoff conclusion, not merely a collection of terminal approximations.

## 2. A transparent larger subcone and strict inclusion

Let g=(3,4,2,5), indexed by k, so g_k=w_k+2. The vertex hypotheses follow
from the simpler additional bounds

    Gamma_(w_k),f(w_k) >= g_k-e,
    z_(f(w_t))(S_t) >= 1/2-e,
    z_(f(v_t))(S_t) >= -1-e.                          (5)

These replace the old theorem's bound 1-e for **both** outsider premiums.
The other tests are unchanged. In particular, the entire old literal raw
polyhedron is contained in the new one.

Here are exact bounds establishing this assertion. For x in D=product_k
[l_k,1], formula (6) below gives W-<y_k<W+. At the first inactive transport,
the favorite is the weak quitter, and the other singleton premium is at
least -1/25-2e. Dropping the nonnegative favorite term, (5) gives

    P_(w_k,k+2) >= x[(1/2-e)y+(-1/25-2e)(1-y)]
                 >= min(l)*8619053/500000000 > eta.

At the second inactive transport the favorite is the strong quitter.
The lower polynomial is

    (g_k-e)x(1-y)+(-69/100-2e)y(1-x)+(-1-e)xy.

It decreases in y and increases in x throughout the stated rectangle.
At x=l_(k-1), y=W+, its excess above c+ l_k/(1-l_k) is respectively

    521135999/6000000000,
    38925211973/135000000000,
    657778991/50000000000,
    315880333/1250000000.

All four exceed eta. The checker independently tests every vertex, so the
monotonic simplification is not required by the computational certificate.

Section 6 gives a full sixty-dimensional cube in the difference between
these classes and Section 7 gives a ray not bounded below in four passive
pair coordinates. These are finite original reward statements.

### 2.1 Complete closure of the fixed-contact participant sign class

Fix A,J,Gamma and every d_i(B) from Section 6. Let the twelve passive
opponent-pair values F_i(B) and four passive opponent-triple values T_i be
**arbitrary finite reals**, and define the native table by

    P_i(empty)=0, P_i({j})=Gamma_ij,
    P_i(B)=F_i(B) for |B|=2, P_i(I minus{i})=T_i,
    Z_i(S)=P_i(S minus{i})+1_(i in S)d_i(S minus{i}).

Require exactly these eight sign conditions:

    Z_i(S_k union{i})=F_i(S_k)+d_i(S_k)>=0
       for k in {0,1,2,3} and i notin S_k.             (SC)

If i=f(w_k), its contact is -1, so (SC) says F_i(S_k)>=1. If i=f(v_k),
its contact is +1, so it says F_i(S_k)>=-1. Both imply (5). Every favorite
singleton already has Gamma_i,f(i)=i+2, so all other hypotheses also hold.
Therefore every completion satisfying (SC) has the constructed uniform
equilibrium, with arbitrary own offsets.

The four F_i(B) with B a favorite pair and all four T_i never enter a
prescribed pair's endpoint or an outsider's joining comparison. They may
be positive, zero, or arbitrarily negative. In particular all completions
whose twelve participant-triple premiums and four grand-coalition premiums
are nonnegative are covered: they imply the eight tests (SC), and no extra
passive nonnegativity is assumed. The argument certifies the simultaneous
corner F_i(S_k)=-d_i(S_k) and the whole independent unbounded orthant above
it, not just a common scalar ray.

## 3. Producing a closed cap cycle by Brouwer

At prefix phase k let v_k quit with hazard x_k and w_k with hazard y_k.
All other hazards are zero. Write

    j_k=J_(v_k),v_(k-1),
    y_k=j_k x_(k-1)/(a_k+j_k x_(k-1)).                  (6)

The role identities v_k=w_(k-1), w_k=v_(k+1) show that j_k is one of the
tested crossing pair premiums. The exact bounds

    W- < (1/100-e)min(l)/(1/20+e+(1/100-e)min(l)),
    (1/100+e)/(1/20-e+(1/100+e)) < W+

prove W-<y_k<W+ on D. Thus all weak hazards are strictly positive and less
than one. All c_k and a_k are strictly positive.

Fix i=w_k. This owner is strong at phase k+1, first inactive at k+2, second
inactive at k+3, and weak at k. Its output at the strong phase is

    A_k=J_i,w_(k+1) y_(k+1)>0.

For an inactive phase define the literal Continue transport

    V_(i,t)(b)=P_(i,t)(x_t,y_t)+(1-x_t)(1-y_t)b.

Set

    E_k=V_(w_k,k+2)(A_k),
    B_k=V_(w_k,k+3)(E_k),
    F_k(x)=B_k/(c_k+B_k).                              (7)

A bilinear function on a rectangle is a convex combination of its four
vertex values. Consequently (2) gives E_k>=eta>0, and (3) gives
B_k>=c+ l_k/(1-l_k)+eta. Since c_k<=c+, this implies

    l_k < F_k(x) < 1.

The map F is continuous on the compact convex rectangle D. Its denominators
are bounded away from zero by the displayed inequalities. Brouwer supplies
a fixed point x*. Every x*_k and y*_k is proper. This is a raw-data producer:
the only existence theorem used is a fixed point of an explicit continuous
map on an explicitly specified rectangle.

## 4. Every root is fully Nash

At an active pair with partner j, a native active owner's forced-Quit
endpoint is J_ij q_j. Its Quit-minus-Continue gap at continuation b_i is

    d_i({j})q_j-(1-q_j)b_i.                            (8)

Equation (6) makes (8) vanish for v_k, whose preceding active output is
j_k x_(k-1). The fixed point in (7) makes it vanish for w_k, whose preceding
output is B_k. The active output is exactly the forced-Quit endpoint.

Define each cap coordinate at every phase by this active output or by E_k
and B_k in its successive inactive phases. All are positive, and inactive
coordinates satisfy their exact Continue recursion by (7). These definitions
cover every owner and phase once and cyclically close.

It remains to check both inactive actions; this cannot be omitted. Write
x=x*_t, y=y*_t and H=(1-x)(1-y). The inactive owners are ell=f(w_t)
and h=f(v_t). Their gaps have the exact form

    d_i({w_t})y(1-x)+d_i({v_t})x(1-y)+d_i(S_t)xy-Hb_i.

Since b_i>=0, the raw contact tests imply

    gap_ell <= (-1+e)y+(1/20+e)x(1-y)
             <= (-1+e)W-+(1/20+e)(1-W-) < -3/50,

    gap_h <= (7/10+e)y(1-x)-(1-e)x+2xy
           <= (7/10+e)W+-(1-e-2W+)min(l) < -7/25.      (9)

The first favorite contact is negative; ell's other crossing contact is the
small one. For h the other crossing contact is the large one. These role
facts follow directly from the displayed phase table. The negative
continuation term is discarded only after the produced cap is proved
positive. Thus every inactive owner strictly prefers Continue, and every
active owner is indifferent. At every phase the constructed output b'
satisfies both the full Bellman equation and prescribed policy equation:

    b'_i=max(Q_i,P_i+H_i b_i)
        =q_i Q_i+(1-q_i)(P_i+H_i b_i).                (10)

The prefix order is 13,12,02,03; physical play reverses it. This reversal
uses the meaning of prefix and continuation rather than a phase relabeling.

## 5. Shared compiler: actual laws, signed caps, and one uniform target

The following argument applies to every producer branch in this packet,
including the period-one stationary branch. Let a finite cyclic list of
independent hazard vectors q^t and finite native cap vectors b^t satisfy
at every phase and owner

    b^t_i=max(Q_i(q^t), C_i(q^t,b^(t+1)))
         =q^t_i Q_i(q^t)+(1-q^t_i)C_i(q^t,b^(t+1)).     (BC)

The first equality is the full one-step cap, and the second is prescribed
policy equality. Assume that, after deleting any owner, its opponents quit
with probability at least delta>0 at every phase. Caps may have either sign.

Repeat these hazards independently at each live history. Opponent-only
survival for n dates is at most(1-delta)^n under every complete unilateral
replacement, including Never. Iterating the inequality in (BC) bounds an
arbitrary replacement's value by the initial cap plus a bounded terminal
remainder times this survival probability. The remainder tends to zero
uniformly over replacements. Iterating prescribed equality gives equality.
Thus every b^t is the actual unrestricted behavioral cap and the prescribed
native value of the corresponding infinite suffix, rather than an unrealized
annotation. This proof applies also to nonperiodic unilateral responses.

Every prescribed or unilateral play absorbs almost surely. Adding the signed
constant s_i to all nonempty native rewards therefore adds exactly s_i to
every relevant terminal expectation. The original profile is exact Nash
with one fixed target u equal to its first native cap plus s. No strategic
translation assertion is made for profiles lacking deleted-opponent
absorption.

If M=max_(i,S nonempty)|r_i(S)| and T counts zero-paying live stages through
the absorbing decision, E[T]<=1/delta. Pathwise, the N-stage average differs
from its final absorbing reward by at most M min(T,N)/N. Consequently

    |prescribed expected N-average_i-u_i| <= M/(delta N),
    every deviating expected N-average_i <= u_i+M/(delta N),
    actual N-stage regret_i <= 2M/(delta N).             (UC)

The bounds are uniform over complete horizon-dependent deviations. Profile
and target are fixed before accuracy or horizon, proving a uniform-
equilibrium payoff.

For Sections 1--4, every deleted opponent set contains either a weak quitter
of hazard greater than W->1/10, a strong quitter of hazard at least min(l),
or both. Take delta=1/10. The construction there has positive caps, but the
compiler does not require that sign. It proves exactly (4). Section 9 uses
delta=2/27 and retains genuinely negative intermediate caps. Section 10
uses delta=7/82. Section 11 uses the positive deleted-opponent absorption of its full-support
stationary solution.

## 6. A concrete stationary-free calibration and a full reward cube

Here is a complete native table specified without a supplied strategy. Set

    A=[[0,1,-7/10,-1/20],
       [1,0,-1/20,-7/10],
       [-1/20,-7/10,0,1],
       [-7/10,-1/20,1,0]].

Let all crossing J_ij=1/100 and J_01,J_10,J_23,J_32=1,2,3,4. Put Gamma=A+J.
For each owner i and opponent set B define

    d_i(empty)=0, d_i({j})=-A_ij, d_i(I minus{i})=-1.

For opponent pairs B in order01,02,03,12,13,23, assign signs
(-1,-1,+1,+1,-1,-1) to the smaller outsider and the opposite signs to the
larger outsider. Define

    P_i(empty)=0, P_i({j})=Gamma_ij,
    P_i(B)=-d_i(B) if |B|=2,
    P_i(I minus{i})=1,
    Z_i(S)=P_i(S minus{i})+1_(i in S)d_i(S minus{i}).    (11)

This specifies all sixty native rewards. The actual calibration is
r_i(S)=Z_i(S)+1, with original live and Never still zero. All participant
native rewards are nonnegative. The singleton pattern is strict matching.
At every crossing pair the negative-contact outsider has passive premium1
and the positive-contact outsider has passive premium-1. Hence (5) holds
with room to spare, and the new theorem produces an equilibrium.

For direct comparison, the complete native table is:

| S | Z_0(S) | Z_1(S) | Z_2(S) | Z_3(S) |
| --- | ---: | ---: | ---: | ---: |
| 0 | 0 | 3 | -1/25 | -69/100 |
| 1 | 2 | 0 | -69/100 | -1/25 |
| 2 | -69/100 | -1/25 | 0 | 5 |
| 3 | -1/25 | -69/100 | 4 | 0 |
| 01 | 1 | 2 | 1 | -1 |
| 02 | 1/100 | 1 | 1/100 | -1 |
| 03 | 1/100 | -1 | 1 | 1/100 |
| 12 | -1 | 1/100 | 1/100 | 1 |
| 13 | 1 | 1/100 | -1 | 1/100 |
| 23 | 1 | -1 | 3 | 4 |
| 012 | 0 | 0 | 0 | 1 |
| 013 | 0 | 0 | 1 | 0 |
| 023 | 0 | 1 | 0 | 0 |
| 123 | 1 | 0 | 0 | 0 |
| 0123 | 0 | 0 | 0 | 0 |

All twelve participant-triple premiums are exactly zero, including the
eight defining the newly closed class. Four of the unused pair-passive
entries also have both signs. These entries permit the exact stationary certificate below and the
complete named-criterion coverage comparison in Section 13.

In fact the entire independent closed cube |r_i(S)-r0_i(S)|<=1/4000000 is
admitted. Each premium/contact changes by at most1/2000000=e/2, and all
tests in the simple subcone have margin at least e at the center.

Every representation of the calibration obtained by permuting owners,
positively scaling recipient rewards, and shifting own offsets still fails
the old raw polyhedron. Its required positive favorite and negative crossing
singleton signs force the same unordered favorite matching. Each crossing
pair has a negative passive outsider premium, preserved by every positive
recipient scale and offset normalization; the old bound1-e is positive.
The same separation holds throughout the displayed cube because those
premiums stay negative and the singleton matching signs stay unchanged. Section 13 gives the broader named-criterion comparison and its limits.

### 6.1 Exact exclusion of all stationary profiles

Appendix B recomputes all the following facts directly from (11), including
every elimination polynomial and exact root count.

Write Delta_i(q)=E[d_i(B)] and H_i=product_(j!=i)(1-q_j). Direct expansion
gives

    sum_i(1-q_i)Delta_i(q)
      =-(1/4)sum_j q_j product_(k!=j)(1-q_k)
       -sum_i(1-q_i)product_(j!=i)q_j.                (12)

All participant endpoints Q_i are nonnegative. At four proper active
hazards, stationarity requires Delta_i=H_i Q_i>=0, contradicting (12).
If four are active and some are sure, every mixed owner's Delta_i is zero
and every sure owner's factor1-q_i is zero, while the right side is strictly
negative. All-sure has Delta_i=-1. Thus full support always fails.

One-owner support fails at a crossing outsider with negative Gamma but
positive participant J. Favorite pair support fails because its joining
contact is negative and Q_i>=0. A proper crossing pair would require
-A_ij=(1-q_j)J_ij<J_ij, whereas -A_ij>J_ij. A sure crossing player forces
its partner sure, and the pure crossing pair has an outsider with positive
pair contact. Thus every support of size one or two fails.

On a three-owner support with one sure owner h, the other owners' comparisons
are the zero-input contacts, because they face a sure opponent. The complete
rational census leaves only

    support012: h=1, q0=7/17, q2=1/2;
    support023: h=2, q0=1/2, q3=7/17.

In both cases Delta_h=-27/68<0, and subtracting H_h Q_h cannot help. With
two sure and one mixed player, the mixed player's nonzero pair contact
cannot vanish. Every pure triple has a negative active contact. This
exhausts all sure faces.

For a proper triple list its hazards x,y,z in increasing owner order.
The three stationary active equations are

    R_i=100[(1-H_i)Q_i-P_i]=0.

They have the form F(y,z),G(x,z),K(x,y). The checker computes
E=Res_x(G,K) and Res_y(F,E), which is a nonzero constant times z times a
degree15 polynomial. Exact Sturm counts in (0,1), and admissibility after
reconstruction, are:

| Support | Number | z isolating intervals | Failed recovered coordinate |
| --- | ---: | --- | --- |
| 012 | 2 | (.100308,.100309);(.940418,.940419) | x>1; y<0 |
| 013 | 1 | (.959332,.959333) | x<0 |
| 023 | 3 | (.003020,.003021);(.045840,.045841);(.049250,.049251) | x<0; y<0; y<0 |
| 123 | 0 | none | none exists |

All decimal endpoints denote exact rationals. The actual isolating intervals
have width at most10^-35. Pseudodivision verifies
lead(F)^m E=QF+c(z)y+d(z), with remainder degree one. On every candidate
interval the checker proves c nonzero and recovers y=-d/c. Cancelling the
quadratic terms in G and K gives x as a rational expression; its denominator
is also certified nonzero. Rational interval evaluation proves every stated
failure. No leading-coefficient division is used to obtain the necessary
resultant equation, so its projection omits no proper root.

The actual lifted AllNever profile has unilateral gain1. Any other original
stationary profile with at least two active owners has opponent-deleted
absorption, so subtracting1 preserves its comparisons and the exclusions
apply. The one-owner case was excluded directly above. This proves no
stationary exact original Nash profile, including every boundary.

There is a positive infimum of original full-response exploitability over
all stationary profiles. For nonzero limits with at least two positive
hazards the complete payoff and cap formulas are continuous, contradicting
the exact exclusion; a one-positive-hazard limit is excluded by its crossing
observer. At q_n->0 normalize q_n by their total rate and pass to z in the
simplex. Vanishing gain against immediate Quit and Never forces

    Gamma z>=0, z_i(Gamma z)_i=0.

The checker verifies Gamma^{-1}>0 entrywise. If Gamma z=0 then z=0; otherwise
z=Gamma^{-1}(Gamma z)>>0 and complementarity again forces Gamma z=0. Both
contradict sum z_i=1. This closes the only discontinuous boundary. The
positive gap is restricted to stationary prescriptions and is consistent
with the four-phase equilibrium proved above.

## 7. An unbounded negative-passive family

Starting with the minimal nonnegative-passive variant of (11), in which
P_i(B)=max(0,-d_i(B)) on opponent pairs, choose any real t>=0. Raise each favorite passive
singleton Gamma_i,f(i) and its favorite participant J_i,f(i) by t, keeping
the favorite contact -1. At every opponent pair with positive owner contact
d_i(B)=+1, replace the passive premium0 by -t and participant premium1 by
1-t. Keep every other entry unchanged. Own offsets are arbitrary.

This remains strict matching at the singleton level. Along the prescribed
crossing pairs, the first inactive transport changes by

    t*y(1-x) >=0,

and the second inactive transport changes by

    t*x(1-2y) >0,

because y<=W+<1/2. Contacts and tested crossing participant premiums are
unchanged. Thus all32 affine guards remain satisfied for **every real t>=0**.
Four passive crossing-pair premiums and their associated participant triple
premiums tend to minus infinity. This is a whole produced raw family, not an
eventual bonus ray changing the base in an unproved direction.

The checker verifies these two coefficient signs on all vertices and an
exact finite member t=10^6. The coefficient argument proves the full ray;
the finite evaluation is only a reproducibility calibration. Section 13 records further comparisons that hold on this entire ray;
its center-specific complete census is not asserted for every ray point.

## 8. Exact certificate conventions

The six Python appendices are standalone programs. Save each code block to
a separate file and run it with Python 3; Appendices B--F require SymPy.
Appendix A checks the rational transport constants, all affine guards at
the calibration, the full reward cube, and compensation coefficients.
Appendix B supplies the complete stationary support and boundary exclusion.
Appendix C checks the signed finite-box polynomial identities and all its
Bernstein coefficients. Appendix D checks the unbounded compensated cone,
including absence of all sixteen unused raw coordinates. Appendix E checks
the full stationary interval certificate and its sixteen-parameter tube.
Appendix F checks the finite coverage invariants used in Section 13.

Every asserted computational inequality is rational, with no external data,
floating-point root assumption, or sampled-root inference. The use of
Brouwer, Banach, tensor Bernstein positivity, and the behavioral compiler is
proved in the prose; the programs certify their finite algebraic premises.

## 9. A second affine producer with signed intermediate caps

This is an alternative raw region, not an additional hypothesis on
Sections 1--4. Its A,J,Gamma and all contacts are fixed exactly as in
Section 6; its sixteen passive completion coordinates are the arbitrary
F_i(B),T_i of Section 2.1. The eight unused coordinates remain unrestricted.
The purpose of the new region is to allow an actual first-inactive cap to
be negative while retaining the complete second-inactive comparison.

Retain the same prefix phase roles. In this section use the different box

    L=(3/5,13/20,2/5,3/5),
    U=(17/20,87/100,4/5,9/10),
    D_s=product_k[L_k,U_k],
    y_k=x_(k-1)/(5+x_(k-1)),       g=(3,4,2,5).          (S1)

Define the eight independent crossing-passive coordinates

    alpha_k=F_(w_k)(S_(k+2)),
    beta_k =F_(w_k)(S_(k+3)).                            (S2)

Every crossing-pair outsider occurs exactly once in (S2). For owner w_k,
its strong-phase output, first inactive output, and second inactive output
are, respectively,

    a_k=y_(k+1)/100,
    e_k=g_k y_(k+2)(1-x_(k+2))
          -(1/25)x_(k+2)(1-y_(k+2))
          +alpha_k x_(k+2)y_(k+2)
          +(1-x_(k+2))(1-y_(k+2))a_k,
    b_k=-(69/100)y_(k+3)(1-x_(k+3))
          +g_k x_(k+3)(1-y_(k+3))
          +beta_k x_(k+3)y_(k+3)
          +(1-x_(k+3))(1-y_(k+3))e_k.                 (S3)

These are literal Continue transports for this fixed table. No sign is
assumed for e_k. Write C_k=(1-x_k)(1-y_k) and define sixteen expressions

    R_k^- = b_k-(7/10)L_k/(1-L_k),
    R_k^+ = (7/10)U_k/(1-U_k)-b_k,
    I_k   = y_k-(1/20)x_k(1-y_k)+C_k a_(k+2),
    O_k   = -(7/10)y_k(1-x_k)+x_k-2x_k y_k+C_k e_(k+1). (S4)

The last two expressions are the negatives of the full actual inactive
Quit-minus-Continue gaps. In particular the signed e term in O_k is kept.

### 9.1 Explicit finite affine membership tests

Let D0(x)=product_j(5+x_j)>0 on D_s. For each R in (S4), D0*R is a
polynomial of multidegree one in three variables and two in one variable.
For R_k^- and R_k^+ the doubled coordinate is k-1; for I_k and O_k it is k.
These degrees are fixed before any specialization and include zero leading
coefficients if a specialization cancels. The polynomial depends affinely
on all eight parameters (alpha,beta).

Substitute x_j=L_j+(U_j-L_j)t_j and expand D0*R as sum_n c_n t^n. If its
fixed multidegree is d, form, for every 0<=m_j<=d_j,

    B_m(R)=sum_(n<=m)c_n product_j
               [binom(m_j,n_j)/binom(d_j,n_j)].        (S5)

There are24 tensor Bernstein coefficients for each expression. Require all
384 rational affine tests B_m(R)>=0. Call their closed affine polyhedron
P_s in the eight original passive coordinates. The96 constant I tests may
be omitted without changing the class. These are finite raw arithmetic
tests; unknown hazards, roots, caps, or strategies are not input witnesses.

**Signed-region theorem.** Every completion whose eight values (alpha,beta)
belong to P_s has an exact terminal Nash profile with physical supports
03,02,12,13, and a uniform-equilibrium payoff for arbitrary finite signed
own offsets. Its other eight passive coordinates are arbitrary. The bounds
(UC) hold with delta=2/27, giving delivery error27M/(2N) and regret27M/N.

### 9.2 Brouwer construction and all actual root comparisons

Tensor Bernstein basis functions are nonnegative and sum to one on the
unit cube. Their conversion formula is (S5), so every expression in (S4)
is nonnegative throughout D_s. In particular

    (7/10)L_k/(1-L_k) <= b_k <= (7/10)U_k/(1-U_k).

The rational map F_k(x)=b_k/(7/10+b_k) is therefore continuous on D_s,
has positive denominators, and maps D_s into itself. Brouwer supplies a
fixed point x*. All strong hazards are proper because D_s is strictly
inside(0,1)^4. Moreover

    2/27 <= y_k <= 9/59 <1.                              (S6)

The strong owner's prior continuation at prefix phase k is x_(k-1)/100:
that owner was weak at phase k-1. Its active gap is

    (1/20)y_k-(1-y_k)x_(k-1)/100=0.

The weak owner's prior continuation is b_k, and its gap
(7/10)x_k-(1-x_k)b_k vanishes at the fixed point. Their outputs are
y_k/100 and x_k/100, respectively, exactly their forced-Quit endpoints.

The first inactive owner at phase k is w_(k+2)=f(w_k). Its prior cap is
a_(k+2)>0, its actual gap is -I_k<=0, and its output is e_(k+2), possibly
negative. The second inactive owner is w_(k+1)=f(v_k). Its prior cap is
e_(k+1), its actual gap is -O_k<=0, and its output is b_(k+1). The signed
term in (S4) is what makes this a full comparison when that prior cap is
negative. No favorable sign has been silently discarded.

These outputs give a cyclic vector at each phase. Formula (S3) is precisely
the prescribed Continue recursion, and the comparisons prove both Bellman
equalities (BC). Chronology reverses the prefix order. After deleting any
owner, a weak quitter of hazard at least2/27, a strong quitter of hazard
at least2/5, or both remains at every date. Section 5 applies with
delta=2/27 even for signed caps, proving the theorem.

### 9.3 Exact common-H certificate and strict signed behavior

On alpha_k=beta_k=H, every polynomial D0*R and each Bernstein coefficient
is affine in H. Appendix C checks all 768 coefficients at H=-3 and H=1. Their minimum, over both
endpoints and all multi-indices for that expression, exceeds the following
integer strictly:

| k | R_k^- | R_k^+ | I_k | O_k |
| --- | ---: | ---: | ---: | ---: |
| 0 | 121 | 1394 | 69 | 277 |
| 1 | 323 | 1549 | 68 | 330 |
| 2 | 226 | 1141 | 82 | 60 |
| 3 | 263 | 2715 | 32 | 314 |

These are coefficient bounds for D0 times the actual expressions, not
hazard bounds or direct bounds on the unmultiplied gaps. D0 is positive,
so the signs transfer. Affinity in H proves every intermediate H in[-3,1].
Strictness of finitely many affine tests puts this whole compact segment
inside the interior of P_s. The eight unused coordinates are still arbitrary;
in this statement only the eight active crossing-passive inputs equal H.

At H=-3 the construction really has a negative intermediate cap. For k=2,
its first inactive phase is0 and

    e_2=y_0(2-5x_0)-(1/25)x_0(1-y_0)+C_0 a_2.

On D_s, x_0>=3/5, y_0>=3/28, and a_2<=1/100. Consequently
e_2<=-3/28+1/100<0 at every point of the box and at every produced fixed
point. The positive-cap branch's test at x=1 would instead require a
positive value of -(1/25)(1-y)-3y, which is impossible. Thus this new branch
changes the actual signed-cap mechanism rather than rechecking a positive
transport condition with another numerical cutoff.

The checker also reconstructs all sixty native rewards with all sixteen
passive coordinates symbolic, verifies all active and inactive endpoint
identities, verifies the fixed multidegrees and affine dependence, and
proves the8 unused values are absent from every defining polynomial.

### 9.4 Independent eight-dimensional box

The entire independent parameter box [-3,1]^8 belongs to P_s, with strict
margins. This is stronger than the diagonal common-H statement. No equality
between different passive coordinates is required.

For each k the only nonzero passive derivatives of D0*b_k are

    d_(alpha_k)(D0*b_k)
      =5(1-x_(k+3))x_(k+2)x_(k+1)(5+x_k)(5+x_(k+3)),
    d_(beta_k)(D0*b_k)
      =x_(k+3)x_(k+2)(5+x_k)(5+x_(k+1))(5+x_(k+3)).    (S7)

The only nonzero passive derivative of D0*O_k is

    d_(alpha_(k+1))(D0*O_k)
      =5(1-x_k)x_(k+3)x_(k+2)(5+x_k)(5+x_(k+1)).      (S8)

These identities follow by cancelling the literal denominators in (S3)--
(S4). Every displayed polynomial is a product of affine factors
nonnegative on D_s. Each factor has nonnegative degree-one Bernstein
coefficients. Multiplication preserves this property: in one coordinate,
the product of a degree-m and degree-n basis function is a positive
constant times a degree-(m+n) basis function; apply this in every coordinate.
Degree elevation also preserves nonnegativity. The resulting multidegrees
are the fixed degrees in Section9.1.

Therefore every coefficient of D0*R_k^- and D0*O_k is nondecreasing in
every passive coordinate; every coefficient of D0*R_k^+ is nonincreasing;
and the I coefficients are constant. The minima of the first group on the
independent box occur when all eight entries are-3. The minima of the R^+
group occur when all are1. Those two vertices were already checked with
strict rational margins in Section9.3. This proves the complete box,
including its boundary and a neighborhood around it in all eight variables.
The other eight passive coordinates remain completely free.

Appendix C also verifies all twelve identities (S7)--(S8), replays the full original-data
and endpoint certificate, and checks all3072 generic coefficient derivative
signs. This checks Bernstein coefficient monotonicity, which is stronger
than pointwise monotonicity of the transported function and is the fact
used in the argument.

## 10. An unbounded compensated cone with sixteen free raw entries

This is an alternative input region. It strengthens the explicit independent
box consequence of Section 9, but need not contain every point of its
coefficient-defined polyhedron. It also keeps crossing data fixed, whereas
Sections 1--4 permit perturbations. Its support geometry is the same.

### 10.1. Complete family and eight raw inequalities

Let I={0,1,2,3}, f(i)=i xor 1, and

    A=[[0,1,-7/10,-1/20],
       [1,0,-1/20,-7/10],
       [-1/20,-7/10,0,1],
       [-7/10,-1/20,1,0]].

Choose four independent increments tau_i>=0. Let J_ij=1/100 on crossing
pairs and J_i,f(i)=i+1+tau_i. Put Gamma=A+J, with zero diagonal. In
particular Gamma_i,f(i)=i+2+tau_i and the favorite joining contact stays -1.
Set d_i(empty)=0 and d_i({j})=-A_ij. For crossing opponent pairs
B=02,03,12,13 assign contacts (-1,+1,+1,-1) to the smaller outsider and
their negatives to the larger outsider. The four contacts at opponent
favorite pairs 01,23 and the four contacts d_i(I minus{i}) are ARBITRARY
finite reals. Choose any twelve finite passive opponent-pair values
F_i(B) and any four finite passive opponent-triple values T_i. Set

    P_i(empty)=0, P_i({j})=Gamma_ij,
    P_i(B)=F_i(B) for |B|=2, P_i(I minus{i})=T_i,
    Z_i(S)=P_i(S minus{i})+1_(i in S)d_i(S minus{i}).      (C1)

This specifies every one of the sixty native rewards. All own singletons
are zero. The only additional hypotheses are

    F_i(S)>=-3           if d_i(S)=-1,
    F_i(S)>=-3-5*tau_i   if d_i(S)=+1,                  (C2)

for S in {02,03,12,13} and i notin S. These are eight affine raw
inequalities, with independent coordinates. The four passive rewards on
favorite pairs 01,23, their four participant-triple rewards, the four
passive opponent-triple rewards and the four grand-coalition rewards are
SIXTEEN independent unrestricted raw entries. Their passive/contact
parameterization in (C1) is invertible and imposes no relation on them.
Original rewards are r_i(S)=Z_i(S)+s_i on nonempty coalitions, with any
finite signed own offsets s_i; live and literal Never still pay zero.

**Theorem.** Every table (C1)--(C2), with arbitrary signed own offsets, has
an absorbing four-phase exact terminal Nash profile against every complete
behavioral deviation. It repeats the crossing pairs 03,02,12,13 and has
one fixed uniform-equilibrium payoff. Under any unilateral deviation,
survival for t stages is at most (75/82)^t. If
M=max_(i,S nonempty)|r_i(S)| and u is the constructed payoff, then

    |prescribed N-stage expected average_i-u_i| <= 82M/(7N),
    deviating N-stage expected average_i <= u_i+82M/(7N). (C3)

No boundedness uniform over the raw parameters is needed;
every particular original reward table is finite.

### 10.2. Explicit signed transport map

Use PREFIX phases with all indices taken modulo four:

| k | S_k | w_k | v_k |
|---|---|---:|---:|
| 0 | 13 | 1 | 3 |
| 1 | 12 | 2 | 1 |
| 2 | 02 | 0 | 2 |
| 3 | 03 | 3 | 0 |

Let v_k be strong with hazard x_k and w_k weak with hazard y_k. Define

    L=(31/50,24/35,7/15,2/3),
    D=product_k[L_k,1],
    y_k=x_(k-1)/(5+x_(k-1)),       g=(3,4,2,5),
    alpha_k=F_(w_k)(S_(k+2)),     beta_k=F_(w_k)(S_(k+3)). (C4)

The alpha and beta variables are exactly the eight coordinates in (C2):
alpha_k>=-3 and beta_k>=-3-5*tau_(w_k). They are independent conditional
on the four nonnegative increments. For owner w_k put

    a_k=y_(k+1)/100,
    e_k=(g_k+tau_(w_k))*y_(k+2)*(1-x_(k+2))
          -(1/25)*x_(k+2)*(1-y_(k+2))
          +alpha_k*x_(k+2)*y_(k+2)
          +(1-x_(k+2))*(1-y_(k+2))*a_k,
    b_k=-(69/100)*y_(k+3)*(1-x_(k+3))
          +(g_k+tau_(w_k))*x_(k+3)*(1-y_(k+3))
          +beta_k*x_(k+3)*y_(k+3)
          +(1-x_(k+3))*(1-y_(k+3))*e_k.                (C5)

These are its strong output and its two successive inactive Continue
transports. The intermediate e_k can be negative. With C_k=(1-x_k)(1-y_k),
define three tests for each phase:

    R_k=b_k-(7/10)*L_k/(1-L_k),
    I_k=y_k-(1/20)*x_k*(1-y_k)+C_k*a_(k+2),
    O_k=-(7/10)*y_k*(1-x_k)+x_k-2*x_k*y_k+C_k*e_(k+1). (C6)

I_k and O_k are the negatives of the ACTUAL first and second inactive
Quit-minus-Continue gaps. The e term in O_k is retained with its actual
sign. There is no upper-b constraint in this construction.

### 10.3. Exact worst-corner certificate and independent orthant monotonicity

Put D0(x)=product_j(5+x_j)>0. At the single worst passive corner
tau_i=0 and alpha_k=beta_k=-3, each polynomial D0*R_k, D0*I_k, D0*O_k has multidegree
one in three coordinates and two in the remaining coordinate. The degree-
two coordinate is k-1 for R_k and k for I_k,O_k. There are 24 tensor
Bernstein coefficients per polynomial on D.

The conversion is explicit. Substitute x_j=L_j+(1-L_j)t_j and expand the
polynomial as sum_n c_n t^n. For its fixed multidegree d, the Bernstein
coefficient indexed by m is

    B_m=sum_(n<=m)c_n product_j[binom(m_j,n_j)/binom(d_j,n_j)]. (C7)

Appendix D verifies all 288 rational coefficients. Their exact
minima are as follows; in particular every entry is strictly positive.

| k | minimum for D0*R_k | minimum for D0*I_k | minimum for D0*O_k |
|---|---:|---:|---:|
| 0 | 2326399/427500 | 8159/105 | 100710119/437500 |
| 1 | 930324403/48125000 | 25789/375 | 28866542/91875 |
| 2 | 12001889/918750 | 291397/3500 | 44608/3375 |
| 3 | 239768/16875 | 726947/17500 | 664003/2250 |

Tensor Bernstein basis functions are nonnegative and sum to one, so these
coefficient signs imply R_k,I_k,O_k>0 throughout D at that corner.

First keep tau=0. The passage to all independent alpha_k,beta_k>=-3 is
pointwise and exact.
The only nonzero passive derivatives of D0*b_k are

    d_(alpha_k)(D0*b_k)
       =5(1-x_(k+3))*x_(k+2)*x_(k+1)*(5+x_k)*(5+x_(k+3)),
    d_(beta_k)(D0*b_k)
       =x_(k+3)*x_(k+2)*(5+x_k)*(5+x_(k+1))*(5+x_(k+3)).

The only nonzero passive derivative of D0*O_k is

    d_(alpha_(k+1))(D0*O_k)
       =5(1-x_k)*x_(k+3)*x_(k+2)*(5+x_k)*(5+x_(k+1)).   (C8)

All factors are nonnegative on D, including its faces x_j=1. I_k is
independent of the passive coordinates. Since the tests are affine in
those parameters, increasing ANY subset of the eight coordinates from
-3 preserves all twelve strict inequalities. This proves the entire
independent unbounded orthant, not only a diagonal ray. It does not require
Bernstein coefficient monotonicity, although that stronger property also
holds for these factored derivatives.

Now allow all four favorite increments independently. For a fixed owner
w_k write tau=tau_(w_k), delta_alpha=alpha_k+3>=0 and

delta_beta=beta_k+3+5*tau>=0. Write a superscript 0 for the same transport
at the certified corner tau=0, alpha=beta=-3. Directly expanding (C5) gives

    e_k-e_k^0
      =tau*y_(k+2)*(1-x_(k+2))
         +delta_alpha*x_(k+2)*y_(k+2),

    b_k-b_k^0
      =tau*[x_(k+3)*(1-6*y_(k+3))
               +C_(k+3)*y_(k+2)*(1-x_(k+2))]
         +delta_beta*x_(k+3)*y_(k+3)
         +delta_alpha*C_(k+3)*x_(k+2)*y_(k+2).          (C8a)

Every term is nonnegative: x lies in [L,1], and

    1-6*y_j=5*(1-x_(j-1))/(5+x_(j-1))>=0.

The first inactive test I is unchanged, while
O_k-O_k^0=C_k*(e_(k+1)-e_(k+1)^0)>=0. Thus all twelve strict corner
inequalities hold on the WHOLE compensated cone (C2), including arbitrarily
large independent increments and arbitrarily negative compensated beta
coordinates. No common-parameter selection or diagonal inference is used.

### 10.4. Producing the cycle and checking all sixteen action comparisons

Equation (C6) now gives b_k>(7/10)L_k/(1-L_k)>0 throughout D. Therefore

    F_k(x)=b_k/(7/10+b_k)                                (C9)

is continuous and satisfies L_k<F_k(x)<1. The upper inequality follows
from b_k being a finite positive real number; no uniform upper bound over
all reward tables is needed. Thus F maps the compact convex D into itself.
Brouwer supplies a fixed point, and EVERY fixed-point coordinate is proper,
even though the box used for existence includes the sure boundary x_k=1.
Formula (C4) also gives

    7/82 <= y_k <= 1/6.                                 (C10)

At phase k the strong owner v_k=w_(k-1) has prior cap x_(k-1)/100, its weak
output in the preceding prefix phase. Its active gap is

    (1/20)y_k-(1-y_k)x_(k-1)/100=0.

The weak owner w_k has prior cap b_k. Its active gap is

    (7/10)x_k-(1-x_k)b_k=0

by (C9). Their prescribed outputs are exactly their forced-Quit endpoints,
y_k/100 and x_k/100 respectively.

The first inactive owner is f(w_k)=w_(k+2). Its prior cap is a_(k+2), its
actual Quit-minus-Continue gap is -I_k<0, and its output is e_(k+2). The
second inactive owner is f(v_k)=w_(k+1). Its prior cap is e_(k+1), its
actual gap is -O_k<0, and its output is b_(k+1). These identities follow
by direct independent expectation over the prescribed pair; Appendix D
reconstructs the entire table (C1) before verifying them.

The four outputs at each phase cyclically close because every owner is
successively weak, strong, first inactive, and second inactive in prefix
order. Equations (C5) are its literal Continue recurrences. Hence all sixteen
coordinates satisfy both identities

    output = max(Quit endpoint, Continue endpoint with prior cap)
           = prescribed action expectation with prior cap.       (C11)

Caps can be signed in (C11). The physical clock reverses the prefix order,
and therefore repeats 03,02,12,13.

### 10.5. Complete behavioral and uniform-horizon verification

Delete any one owner. At every physical phase its remaining opponents
include either a weak quitter with hazard at least 7/82, a strong quitter
with hazard at least 7/15, or both. Their per-stage survival is at most
75/82. These hazards remain the prescribed independent hazards at every
live history, whatever the deleted owner's complete behavioral replacement.

Iterating the inequality in (C11) for an arbitrary replacement leaves a
bounded signed continuation cap times at most (75/82)^t. This tends to
zero; positivity of the cap is unnecessary. It follows that every native
complete behavioral replacement earns at most the initial cap. The
prescribed equality in (C11) gives exactly that cap. This proves exact
terminal Nash, including all finite deadlines, literal Never, private
randomization, nonperiodic deviations, and accuracy-dependent choices.

The opponents alone absorb almost surely under every replacement. Adding
s_i to every nonempty reward therefore adds exactly s_i to every prescribed
and deviating terminal payoff, for arbitrary finite signed s_i. Hence the
same original profile is exact Nash at the raised table.

The expected number of live stages through the absorbing decision is at
most sum_(t>=0)(75/82)^t=82/7, uniformly over every unilateral deviation.
If M bounds original absolute terminal rewards, the expected N-stage
average differs from the corresponding expected terminal payoff by at most
82M/(7N). Together with terminal Nash this proves (C3). One profile and one
fixed payoff target work for every accuracy and all sufficiently large
horizons.

The sixteen unused higher raw entries are independent because no prescribed
crossing pair, or unilateral replacement against it, can sample an opponent
favorite pair or an opponent triple. Every one-step endpoint depends only
on the empty set, singleton opponents, and the prescribed crossing pair.
Appendix D retains sixteen distinct symbols and verifies their absence.

At tau=0 and alpha=beta=-3, e_2 is negative throughout the producer box:

    e_2=y_0(2-5*x_0)-(1/25)*x_0*(1-y_0)+C_0*a_2
        <=-3/28+1/100<0.

Thus the signed continuation in the second inactive comparison is needed
for this produced cycle. The complete sign class of Section 2.1 is a
subclass of the cone at tau=0; its crossing passive floors are +1 or -1,
both greater than -3. The independent increments give a stronger negative-
passive compensation than the ray in Section 7.

## 11. Negative-common-passive stationary branch

Here the fixed A,J,Gamma and contacts remain exactly those of Section6,
but EVERY one of the sixteen passive entries F_i(B),T_i equals the same
finite H<=-3. Thus passive higher coalitions pay H, participant triples pay
H plus their specified contact, and grand-coalition premiums are H-1.
The eight-free-coordinate extension of the pair branches is not asserted
here: a full-support stationary law samples every coalition.

**Negative-ray theorem.** Every such exact common-H table has a fully
mixed stationary exact Nash profile and a uniform-equilibrium payoff after
arbitrary signed own offsets. Writing t=-1/H in(0,1/3], its hazards satisfy

    (2/5)t < q_i < (7/5)t  for every i.                  (N1)

The following finite rational construction proves the statement on the
entire unbounded ray. Its complete-response conclusion uses Section 5.

### 11.1 Literal stationary equations and their nonsingular scaling

For independent stationary hazards q set

    h_i=product_(j!=i)(1-q_j), alpha_i=1-h_i,
    P_i=sum_B Pr_q(B)P_i(B),
    D_i=sum_B Pr_q(B)d_i(B), Q_i=P_i+D_i,

where the sums run over opponent subsets and the passive empty reward is0.
Here the same letter P_i on the left denotes an expected passive endpoint;
on the right P_i(B) is the raw passive datum from Section2.1. Full-support
stationarity is exactly

    R_i(q,H)=(1-h_i)Q_i-P_i=0.                           (N2)

It implies Q_i=P_i+h_i Q_i, so the forced-Quit and Continue endpoints agree
at constant continuation Q_i.

Put H=-1/t and q=t z. For owner i define

    p_i=product_(j!=i)(1-t z_j),
    e2_i=sum_(j<k; j,k!=i)z_j z_k,
    e3_i=product_(j!=i)z_j,
    Pbar_i=sum_(j!=i)Gamma_ij z_j product_(k!=i,j)(1-t z_k)
                          -e2_i+2t e3_i,
    Dbar_i=-sum_(j!=i)A_ij z_j product_(k!=i,j)(1-t z_k)
       +t sum_(B subset I\{i}; |B|=2)d_i(B)
             product_(j in B)z_j product_(k!=i; k notin B)(1-t z_k)
       -t^2 e3_i,
    E_i(z,t)=-p_i Pbar_i+(1-p_i)Dbar_i.                  (N3)

Literal expansion from all sixty rewards gives

    R_i(tz,-1/t)=t E_i(z,t).                             (N4)

In particular E is polynomial and extends to t=0 with
E_i(z,0)=e2_i-sum_(j!=i)Gamma_ij z_j. The endpoint t=0 is used only in
a compact certificate; it is not a finite-reward game or an asserted
absorbing strategy with zero hazards. All higher coalition terms are retained
in (N3). The exact checker reconstructs all sixty entries and verifies (N4)
by symbolic polynomial identity.

### 11.2 Finite exact contraction certificate on every parameter cell

Let N_c=512, rho=1/N_c, and for k=0,...,N_c-1 set

    I_k=[k/(3N_c),(k+1)/(3N_c)],
    mu_k=(2k+1)/(6N_c).

These closed intervals cover[0,1/3], including every cell boundary. Define
Round_D(x)=floor(Dx+1/2)/D coordinatewise. Start at the exact vector
c=(68/100,132/100,47/100,92/100). On cell k do six iterations for k=0
and three otherwise of

    c <- Round_(10^10)(c-[D_z E(c,mu_k)]^(-1)E(c,mu_k)). (N5)

For k>0 start from the previous final center. The new center is c_k. Set

    M_k=Round_(10^8)([D_z E(c_k,mu_k)]^(-1)).            (N6)

Every operation and inverse in this candidate-construction algorithm is
rational. A singular matrix terminates the certificate unsuccessfully.
No convergence theorem or numerical root assumption is attached to these
iterations. The mathematical evidence is the separate exact verification
on every B_k={z:|z-c_k|_infinity<=rho}:

    B_k subset(2/5,7/5)^4,
    sup_(z in B_k,t in I_k)|Id-M_k D_z E(z,t)|_infinity <1/4,
    sup_(t in I_k)|M_k E(c_k,t)|_infinity <(15/32)rho.    (N7)

The matrix norm is maximum absolute row sum. To check its bound, expand
every derivative entry as a rational polynomial in z,t. Each box coordinate
is nonnegative. Thus monomial intervals are obtained by multiplying endpoint
powers, followed by the signed coefficient; sum the intervals, multiply by
the exact M_k, subtract from Id, and bound row sums. This covers the whole
parameter-and-state box, not selected derivative samples.

For the centered residual, substitute c_k first and multiply its univariate
coefficient vectors by M_k before evaluating intervals. Translate to powers
of t-mu_k. If the resulting coefficients are a_d, then

    |sum_d a_d(t-mu_k)^d| <= sum_d |a_d|(1/(6N_c))^d.

The right side is rational. This procedure retains exact cancellations
without dropping terms. Appendix E verifies every inequality (N7) in all512 cells using no floating-point values,
external data, numerical solver, or claimed true root coordinates.

For any fixed t in I_k, T(z)=z-M_k E(z,t) has Lipschitz constant<1/4 on B_k,
and its centered image radius is at most

    (15/32)rho+(1/4)rho=(23/32)rho<rho.

Banach supplies a fixed point. Since |Id-M_k D_zE|<1, the product M_k D_zE
is invertible, hence M_k is invertible. Therefore the fixed point satisfies
E(z,t)=0 exactly. No compatibility of selected roots across neighboring
cells is required for existence. For t>0, (N1) follows from the box bounds,
and q_i<(7/5)(1/3)=7/15<1. The identity (N4) gives exact stationarity (N2)
for every finite H<=-3, including H=-3.

### 11.3 Original complete-behavior and uniform payoff conclusion

Take constant native cap v_i=Q_i(q). Equation (N2) says
v_i=Q_i=P_i+h_i v_i, so both Bellman equalities (BC) hold. Every deleted
opponent set contains a player with hazard>(2/5)t. Consequently one may
use delta=(2/5)t in Section5. Signed native caps present no obstacle.
The same stationary profile therefore caps every complete behavioral
replacement and produces one original uniform target after arbitrary
signed own offsets. The bounds (UC), for example, give delivery error
at most5M/(2tN) and regret at most5M/(tN). These bounds are table-dependent;
no rate uniform over H tending to minus infinity is claimed or needed.

### 11.4 A full sixteen-dimensional relative passive tube

The stationary producer is stable on an explicit relative neighborhood of
the entire negative ray. Retain the same singleton and contact data, but
now allow all sixteen passive entries F_i(B), |B|>=2, to vary independently.
Put eta_tube=1/32768 and let f_min,f_max be their minimum and maximum.
The finite raw guards are

    f_max<=-3(1-eta_tube),
    (1+eta_tube)f_max<=(1-eta_tube)f_min.                (N8)

These conditions are equivalent to existence of H<=-3 with
|F_i(B)-H|<=eta_tube|H| for all16 entries. Indeed its feasible interval is

    [f_max/(1-eta_tube), f_min/(1+eta_tube)]
        intersect(-infinity,-3].

When (N8) holds, choose H=min(-3,f_min/(1+eta_tube)) and t=-1/H.
This is an explicit reward computation; it supplies no strategic witness.
Each resulting actual reward table has a full-support stationary exact
Nash profile satisfying (N1) and the same original fixed-target conclusion.

To prove this, write F_i(B)=H+xi_i(B)/t, with |xi_i(B)|<=eta_tube. In the
stationary field (N2), the passive and Quit endpoints receive the same
passive perturbation. The exact scaled perturbation is therefore

    DeltaE_i(z,t)=-p_i W_i(z,t),
    W_i=sum_(B subset I\{i}; |B|=2)xi_i(B)
            product_(j in B)z_j product_(k!=i; k notin B)(1-t z_k)
         +t xi_i(I\{i})product_(j!=i)z_j.              (N9)

The checker derives this identity from the literal independent opponent
coalition law for every one of the sixteen separate perturbations.

On the certified boxes let b=7/5. All coefficients of xi in W_i are
nonnegative, and their sum is e2_i-2t e3_i<=3b^2. Since0<=p_i<=1,

    |DeltaE|_infinity <= C0 eta_tube, C0=147/25.

For one opponent coordinate z_l, the two pair terms containing l, the
pair term not containing l, and the triple term give
|partial_l W_i|<=eta_tube(2b+2t b^2). Also |partial_l p_i|<=t. Thus

    |partial_l DeltaE_i| <= (91/15)eta_tube,
    |D_z DeltaE|_infinity <= C1 eta_tube, C1=91/5.       (N10)

There are three opponent derivatives and the own derivative is zero.
These are uniform analytic bounds over all16 independent real parameters,
not sampled perturbation signs.

The same finite512-cell certificate checks in addition that every rational
preconditioner satisfies |M_k|_infinity<2. For the actual perturbed table,
T(z)=z-M_k(E+DeltaE) therefore has Lipschitz constant less than

    1/4+2C1 eta_tube < 1/2.

Its centered image radius on B_k is strictly below

    (23/32)rho+2eta_tube(C0+C1 rho)<(29/32)rho<rho.      (N11)

The last inequalities are exact rational calculations. Banach applies to
the same boxes; M_k is invertible by the base contraction, so the produced
root solves the perturbed stationary endpoint equations exactly. Bounds
(N1) persist because the entire state box is unchanged. Section5 supplies
the full-behavior, signed-offset and uniform conclusions using the ORIGINAL
perturbed table's reward bound M.

The standalone tube checker repeats the entire base certificate and all
512 cells, verifies (N9), the norm bound on every M_k, and constants
(N10)--(N11). Thus it contains the full common-ray certificate as well.
At each H<-3, the strict guards contain a neighborhood of its common
completion in the sixteen-dimensional passive space, with width
proportional to|H|. Participant triple and grand rewards vary with these
passive entries according to the fixed contacts; no additional coordinates
are declared free in this stationary branch.

## 12. Complete common-passive line and precise remaining scope

**Common-passive closure.** Fix the singleton and contact data of Section6.
For ANY finite real H, set all twelve passive opponent-pair entries and all
four passive opponent-triple entries equal to H. Retain any finite signed
own offsets. This original quitting game has a uniform-equilibrium payoff,
indeed one exact terminal Nash profile that serves every accuracy.

For H>=-3, the unbounded cone in Section 10 with tau=0 produces the
four crossing pairs. For H<=-3, Section 11 produces a full-support stationary
profile. These intervals cover all real H and agree in their literal
sixty-entry definition at the boundary. No continuous equilibrium selection
is required at an overlap.

The pair branches cover independent affine regions in the eight crossing-
passive coordinates. The strengthened cone also permits four independent
favorite increments and sixteen independent unused higher raw entries.
The stationary branch covers the sixteen-dimensional relative negative tube
(N8), with every contact fixed as specified. These results do not settle
arbitrary independently varying completions outside the stated union or
the general four-player quitting conjecture.

## 13. Coverage comparison and its exact limits

This appendix compares the literal calibration below with the complete named
raw sufficient criteria. Every role, positive recipient scale and free
parameter of those criteria is included in the stated exclusions. Arbitrary
supplied strategic certificates and maximal qualitative continuation
neighborhoods are explicitly left unclassified at the end.

The comparison establishes new raw-family coverage, not a new generic
periodic-equilibrium consumer and not a solution of the four-player
quitting-game conjecture.

### The complete calibration and its invariants

For nonempty coalitions S, put r_i(S)=1+Z_i(S), with zero live and Never
rewards, and use the following native table:

| S | Z(S) |
| --- | --- |
| 0 | (0,3,-1/25,-69/100) |
| 1 | (2,0,-69/100,-1/25) |
| 2 | (-69/100,-1/25,0,5) |
| 3 | (-1/25,-69/100,4,0) |
| 01 | (1,2,1,-1) |
| 02 | (1/100,1,1/100,-1) |
| 03 | (1/100,-1,1,1/100) |
| 12 | (-1,1/100,1/100,1) |
| 13 | (1,1/100,-1,1/100) |
| 23 | (1,-1,3,4) |
| 012 | (0,0,0,1) |
| 013 | (0,0,1,0) |
| 023 | (0,1,0,0) |
| 123 | (1,0,0,0) |
| 0123 | (0,0,0,0) |

Write Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}), and
d_i(B)=Z_i(B union{i})-Z_i(B) for nonempty B omitting i. Set d_i(empty)=0
when using native root polynomials. The following facts follow directly:

1. All four original own rewards are one. Every participant native reward
   is nonnegative, all twelve J_ij are strictly positive, and all twelve
   participant-triple premiums are zero.
2. Gamma has the unique positive favorite matching f=(01)(23). Each row's
   two negative magnitudes are {1/25,69/100}. Favorite contacts are -1 in
   both directions; crossing contacts are 1/20 and 7/10.
3. At each crossing pair, the two passive outsider premiums are -1 and +1.
   The pair-contact data are:

| B | Outsider contacts |
| --- | --- |
| 01 | d_2=-1, d_3=+1 |
| 02 | d_1=-1, d_3=+1 |
| 03 | d_1=+1, d_2=-1 |
| 12 | d_0=+1, d_3=-1 |
| 13 | d_0=-1, d_2=+1 |
| 23 | d_0=-1, d_1=+1 |

All four full-opponent contacts are -1. Positive recipient scaling preserves
the signs, within-row comparisons and ratios used below; relabeling merely
permutes the finite choices. Additive shifts of the original own rewards
are not invoked as strategic equivalences with Never held fixed at zero.

The stationary-exclusion proposition for this calibration supplies one
additional fact used here: its complete behavioral regret has a strictly
positive infimum over ALL stationary profiles, including every support,
sure face and the all-Continue boundary. This is the exact original-own-one
stationary exclusion, not a numerical search or an exclusion confined to
full-support stationary profiles.

### Crossing transport and the unbounded compensation ray

The previous four-crossing-pair polyhedron requires its favorite singleton
matching signs and strictly positive passive premiums at both outsiders of
every crossing pair. Among all 24 relabelings, only the eight preserving
the actual matching can satisfy its singleton signs. In every one, each
crossing pair has a passive premium -1. Thus every role and positive
recipient scale fails. The same obstruction excludes the entire positive
two-scale four-pair class, whose eight passive lower bounds are positive
numbers alpha*H^2 and beta*H.

The mixed-word contact-guard-removal class leaves only coalitions
{01,012,013,0123} outside its explicit tiny coordinate neighborhood. Every
crossing passive pair coordinate is still constrained near +1, so that
whole raw class is excluded by the same argument. No choice of its freed
coordinates affects this necessary condition.

The exclusion from the old crossing polyhedron persists throughout the full
sixty-coordinate cube of radius 1/(4*10^6) about the actual table. Native
coordinates change by at most twice that radius, including the movement of
the own coordinate. The negative passive signs and the unique singleton
matching therefore persist. Admission of this whole cube by the new
transport theorem gives a full-dimensional difference of the two classes.

There is also an unbounded comparison. In the compensation ray, start from
the nonnegative-passive completion, increase favorite Gamma and J by t>=0,
and set every passive pair coordinate with contact +1 to -t, changing its
participant-triple coordinate by the same amount. Every crossing pair has
a passive outsider premium -t<=0. Thus every t>=0 is outside all three
positive-passive crossing classes just described, under all their roles,
scales and positive numerical parameters.

This all-t assertion has its stated scope. It does not assert that the
whole ray is outside every earlier existence class. In particular, the
center's stationary gap, exact punishment calculation and universal-child
census below are not silently extended along the ray.

### Stationary-producing criteria, including all representations

The strict stationary regret gap rejects any raw theorem whose conclusion,
on these own-positive data, is stationary complete regret tending to zero.
This includes all choices of parameters and representations in the signed
passive-coalition, positive-inverse coalition-jackpot, signed single-column
jackpot including scale-thick completions, three-passive-pole, and
contact-preserving coalition-bonus producers. It also excludes the proper
triple three-weak, one-strong and critical bonus producers and the
contact-preserving negative-penalty producer.

The same argument rejects every stationary-response quotient satisfying
the full response identities, every polynomial-row-weight odds-order
certificate, and its constant-row and columnwise-hazard predecessors.
Here det Gamma is nonzero and all own rewards are positive, so the
polynomial-row theorem's weak negative-own exception cannot avoid its
exact stationary conclusion. Every partition, odds vector, positive row
scale and positive polynomial vertex-weight choice is covered.

The guarded crossed-response exact and stationary-approximate classes fail
as well. Its sole-active boundary has positive own reward here and also
gives a stationary equilibrium if admitted. Finally, all sure-exit,
toggle-potential, componentwise weighted-potential, strict blocker-switch
and odd-blocker interval-passive criteria fail, since each produces an exact
stationary equilibrium.

This is a conclusion-based exclusion of the complete criteria. It does not
merely reject one presentation as base plus bonus, one threshold, one
inverse column, or one selected stationary support.

### True punishment and every universal quiet child

Every player's actual punishment value is one. Immediate Quit guarantees
at least one because all participant rewards are at least the own reward.
All-Never opponents cap every complete response at one, proving equality.

At the actual punishment continuation the root field is
g_i(q)=E[d_i(B)]. If mu_q(S) is the full product coalition probability,
the exact multiaffine identity is

```text
sum_i (1-q_i) g_i(q)
 = -(1/4) sum_{|S|=1} mu_q(S) - sum_{|S|=3} mu_q(S).       (1)
```

There is no sure-quitter punishment root. Every nonempty pure coalition
fails a joining inequality. One sure and one mixed owner would require a
zero singleton contact; two sure and one mixed owner would require a zero
pair contact; none exist. With one sure and two mixed owners, solve the
two linear mixed-owner equations. Among all twelve support/sure choices,
the only two proper candidates are support012 with sure1 and support023
with sure2. The sure owner's g is -27/68 in each. With full support and
some mixed owner, (1) is strictly negative while every weighted root
coordinate must vanish. All-sure instead has four negative contacts -1.

This rejects the complete instant-punishment criterion and the corresponding
persistent-base inputs, including every induced mixed proper root. A base
with at least two sure owners leaves immediate absorption when any one is
deleted. For a singleton base, any actual continuation cap is at least its
punishment value one; raising that cap only strengthens the sure owner's
Continue alternative. The census therefore cannot be evaded by choosing a
different punishment continuation.

Every one of the fourteen nonempty proper child sets has a pure exact
child equilibrium with zero child debt and zero joint Never, but a profitable
omitted join. For the four triples, use respectively:

```text
child012: coalition02;   child013: coalition13;
child023: coalition03;   child123: coalition12.
```

In each case the inside nonquitter's contact is -1 and the omitted owner's
contact is +1. A crossing pair child uses both owners; its omitted owner
with positive pair contact gains. A singleton child uses its singleton
quitter. A favorite pair child uses one singleton quitter, whose other
child member has negative favorite contact and whose crossing outsider has
positive contact. All these profiles are exact against full child
behavioral deviations.

Consequently every universal comparison

```text
omitted-owner debt <= sum_i a_i child_debt_i + b child_joint_Never,
                     a_i>=0, b finite,
```

fails for every child selector and every choice of weights. This includes
the universal withdrawal/deadline, cancellation, evaluated-security,
terminal-security, advancing-only and singleton-Never quiet-lift tests.
An existentially selected quiet child law is a different input and remains
unclassified by this universal counterexample.

### Premium, leaver, marked and payoff-exclusion criteria

All six pairs are premium traps. All larger supports are traps too, because
each member already has a positive participant premium on one contained
pair. This gives the following complete-choice exclusions.

- Every weak-premium support peeling, proper premium-core and proper-flat
  participant-cap criterion fails. This includes the empty/pair-core
  same-sign branch and the monotone, sink-or-receiver and graph-free H/J
  chambers.
- For any nonempty marked set, ordered block partition and positive block
  weights, choose one owner in the first block and another owner. The
  earliest-block participant sum at their pair is strictly positive.
  Thus every marked-set, ordering and weight choice fails the raw cap of
  the ordered-anchor-block, passive-bound and calendar-polytope theorems.
- At a proper positive-hazard pair both active forced-Quit native values
  are positive, rejecting product-low. For a supportwise nonnegative upper
  average, its two singleton-coalition tests force both pair weights to
  vanish. Thus no nonzero allowed weight works, including support-dependent
  weights.
- The mixed upper-average/boxed-charge criterion cannot charge a pair when
  its charge alternative is restricted to size at least three; its upper
  alternative just failed. For the mixed-premium-trap criterion, a triple's
  singleton inserted sum is a sum of two positive J entries, contradicting
  its required upper bound -D<0. Every positive charge constant and every
  supportwise certificate assignment fails.
- A common leaver must belong to all traps, impossible for disjoint pair
  traps. Its separate global participant-nonnegativity premise DOES hold
  here. Every owner can likewise be protected, but a crossing-pair trap has
  two positive contacts, so none of its members is a weak or strict leaver.
  Positive weighted trap leavers fail at that pair's singleton-subset test:
  the leave sum is w_i d_i({j})>0. This does not falsely assert that the
  global weighted-floor premise fails; it is the leave comparison that
  fails for every allowed positive trap weight.

One actual finite word rejects all universal payoff-exclusion selectors
at once. Let each owner independently Quit with probability1/2 on one date,
then use Never. Every nonempty coalition has probability1/16 and

```text
U = (1929,1929,2329,2329)/1600 > (1,1,1,1).             (2)
```

Thus no strict-deficit margin PD, no nonempty weak-exclusion subset WE_J,
and no nonconcentrated weight/cap GE can hold. This covers all existential
choices in their finite-calendar raw predicates. It also rejects every
nonzero nonnegative social-weight upper chamber: if every weighted raw
surplus were nonpositive, no actual profile could exceed the positive own
levels in all four coordinates.

### Singleton and alternating-pair criteria

Here Gamma^-1 is strictly positive and det Gamma>0. One direct proof writes
Gamma F=D-NF, where F is the favorite permutation matrix, D is the positive
diagonal with entries2,3,4,5, and N consists of the positive crossing
magnitudes. Every row sum of N is73/100, so the geometric inverse of
I-D^-1 NF converges and is entrywise nonnegative. The crossing graph is
connected and contains all two-step within-block paths, making the inverse
strictly positive. Continuation from D to D-NF preserves nonsingularity and
the positive determinant; det F=+1.

Every principal pair is nonsingular since its reciprocal entries have the
same nonzero sign. Every principal triple has one positive favorite pair
and four negative crossings. Its determinant is the sum of two positive
three-cycle products, and the inverse diagonal belonging to the third owner
is the negative favorite-pair minor divided by that positive determinant.
Thus no deleted-triple inverse is nonnegative.

The homogeneous LCP has no nonzero root: supports of size at least two
have nonsingular principal matrices, and a singleton support has a negative
outside residual. At offset -1, every row needs its positive favorite
coordinate positive, so the only complementary solution is Gamma^-1*1>0.
Its index is positive. Therefore Gamma is R0, has integer LCP degree+1,
and is standard Q. All non-Q, non-R0, degree-not-one and negative-determinant
inverse-positive exits fail. A negative reciprocal principal pair fails
the projective-Q-bar test at offset -1. There is no nonnegative singleton
column. The positive favorite-pair principal inverses are not claimed
negative; their universal quiet extensions were separately excluded above.

Every raw role requiring an opposite-sign reciprocal singleton pair or a
positive directed triangle or four-cycle fails: the actual positive graph
is two disjoint two-cycles. This covers the fixed raw versions of the
attached-negative-pair, cyclic-child one-joint, arbitrary-one/two-joint,
negative/zero-premium child, repeated-solo-buffer, two-outsider-buffer,
diffuse-solo, global-two-joint-child, negative-chord, larger-eigenvalue
signed-cycle, scalar-singular-circuit, three-owner positive-passive-triple,
balanced-singleton-cycle and heterogeneous signed-four-cycle criteria.
The scalar-singular circuit's opposite-sign test precedes all of its finite
interval-coefficient choices. The no-mutually-negative-pair theorem fails
its explicit sign hypothesis.

The negative-pair-funded and mixed-pair-positive-passive producers instead
need a positive reciprocal singleton pair with J_ij>Gamma_ij. Every actual
favorite has J_ij=Gamma_ij-1. Every triple contains a favorite pair with
negative contacts, so all triple-singleton-collision-box selections fail.

For the arbitrary finite invariant-cone pair producer, a scheduled mate map
m with positive contacts must be one of the two crossing perfect matchings.
Its contacts c_i are1/20 or7/10, less than every favorite J_i,f(i)>=1.
For ANY positive invertible cone matrix V, let R_ab=max_l V_al/V_bl. The
favorite singleton joining cap implies

```text
J_i,f(i) <= c_i/(R_f(i),m(i)+R_k,m(i))
           ==> R_f(i),m(i)<1.
```

For i'=m(f(i)), its favorite and mate reverse those indices, forcing also
R_m(i),f(i)<1. This is impossible since every column has reciprocal positive
ratios. Therefore every positive proof matrix, normalization, partition
and coefficient certificate is rejected before any further polynomial test.
The positive-inverse alternating-pair criterion is a special case.

For bounded inverse corners, its computed kappa<=1/4 and r_min<=1 give
ell_i=c_i*kappa*r_min/2<=c_i/8<J_i,f(i), contradicting its joining cap.
The two-pair join-cap, crossed-matching and signed-inverse-column versions
impose nonpositive unscheduled participant caps; all actual J>0 rejects
them. The asymmetric scalar paired criterion has equal negative singleton
entries within a row, whereas the actual ratio is69/4. The implemented
raw paired-cycle region requires two positive singleton premiums per row;
the calibration has one. These arguments include all relabelings and
positive recipient scales.

### Remaining fixed periodic families and explicit boxes

The necessary conditions in this table are properties of the whole named
raw family, including all its stated continuous parameters. Their failures
are invariant under positive recipient scaling. For an explicit raw reward
cube, the native-premium error includes movement of the own coordinate.

| Earlier raw family | Necessary condition that fails |
| --- | --- |
| Repeated-pair slab AND its whole fixed-tube algebraic criterion | Singleton matching leaves eight roles. With scheduled pairs A=03,B=12, one A-owner has passive B=-1 below both available crossing singletons, contradicting the necessary lower monotonicity guard M0. This precedes every tube and scalar-root choice. |
| Ten-phase middle-reward cylinder | Its bounded participant pair has native premiums <=-1+2*10^-6<0. |
| Four-joint-phase local/upper-only/free cylinder | Its stated radius <=1/2 leaves designated upper-only participant-pair premiums strictly negative. |
| Four-joint-phase unbounded rectangle | A designated opposite-pair participant bound is below -24ML in own-one coordinates. |
| Unordered rotating mixed pairs, both alternatives | An opposite pair has participant premiums <=-b<0. |
| Full passive-parameter family, every M,N,T | Both pair01 participant premiums are -1. |
| Four-phase passive-reward ray, every A,B,K | Crossing raw participant rewards are bounded by B<1 at own level1, so native premiums are negative. |
| Negative-passive paired phases | Two crossing participant premiums have sum <=2c<0. |
| Monotone passive-cap chamber | Its participant caps include negative native pair bounds. |
| Global asymmetric pair-phase unbounded scalar class | Within each row its two negative singleton entries are equal. Its explicit full reward cube instead retains designated strictly negative native crossing participant premiums. |
| Four-singleton-phase raw completion family | Crossing participant premiums are capped at or below zero. |
| Below-singleton joint-phase and opposite-sign matching-phase raw families | A designated participant pair has strictly negative native premiums. |
| Thirty-three-phase and weak-crossing unbounded-period literal families | Each favorite J/Gamma ratio is below1/2; the calibration's ratios are1/2,2/3,3/4,4/5. |
| Jordan-reset and complex-spectrum literal parameter families, including endpoints | Their favorite J/Gamma ratio is1/101. |
| Actual marked-source printed centers, every permitted parameter | Pair01 has both participant premiums -1. |
| Two-joint-phase full-table-neighborhood printed center | Pair01 includes negative participant premiums. |
| Full-dimensional cyclic-child printed centers, every eta | Pair03 has two negative participant premiums. |
| Paired-collision reward disjunction, all literal parameters | Its two negative singleton entries in each row are equal. |
| Rational full-core deadlock block and integer period-three table | Their singleton positive graphs are not disjoint favorite matchings. |
| E1 overlapping period-three table, explicit full cube and structural cylinder | Its constrained negative singleton magnitudes lie in [1-2eta,1+2eta], eta=1/50000000. Their ratio is near1, not69/4. Its four freed coordinates are nonsingletons. |

For the long-period rows, singleton signs fix the favorite entries before
ratios are compared. On the compensation ray all favorite ratios remain at
least1/2, so those literal families are excluded for every t. Also, every
row excluded solely by a negative participant-pair premium remains excluded
along the whole ray, where all J stay positive. The repeated-pair M0 guard
fails immediately when t>69/100; no claim about its small-t segment follows
from this particular comparison.

### Precisely unclassified domains

No nonmembership claim is made for unspecified maximal qualitative local
continuations of the actual marked-source, two-joint-phase, full-dimensional
cyclic-child, below-singleton joint-phase, four-singleton-phase or asymmetric
scalar paired theorems, or of the long-period examples. Exclusion of their
printed centers or fixed parameter families does not determine the extent
of an unspecified neighborhood. Explicit numerical cubes have instead been
tested at their stated radii above.

The reusable interval-face criterion allowing an arbitrary finite phase
word, hazard box and preconditioner is also unclassified over all those
choices. A newly produced regular cycle might furnish such a previously
available certificate. That would not mean that the old verifier produced
this raw family and its certificate from the reward data.

Arbitrary supplied cycles, cap data, selected quiet child laws, finite-menu
strategies and favorable semantic source witnesses likewise remain outside
the nonmembership claim. Source exclusions restricted to full-zero faces,
least-Never sources or special minimum profiles can apply without being
unconditional original-game existence producers; they are not rejected as
though they were whole-game raw classes.

The comparison therefore supports the stated nonredundant raw transport
enlargement and complete fixed-contact sign branch. It does not assert
exclusion from every abstract sufficient predicate, nor does it extend the
center-specific complete census to every point of the compensation ray.

## 14. Source correspondence, actual-data adapter, and Lean handoff

### Existing semantic consumers and the new producer boundary

The following exact declarations are present in the tracked source
`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`:

- `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` consumes
  a finite cycle of product roots, a cyclic value vector, exact policy
  recursion, exact root Nash at each phase, and playerwise opponent-cycle
  contraction. It concludes exact terminal Nash against all behavioral
  replacements.
- `isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
  consumes the same data and concludes that the selected cyclic terminal
  vector is a uniform-equilibrium payoff, with the same cyclic profile at
  every accuracy.

The tracked source
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` contains:

- `quittingStationaryFullRateUnilateralCap_le_of_fixedPoint_endpointNash`,
  which bounds the complete behavioral unilateral cap from a stationary
  value fixed point, exact endpoint Nash, and the saturated-coordinate
  boundary condition;
- `isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`,
  which concludes exact terminal Nash from joint absorption, the value fixed
  point, endpoint Nash, and opponent contraction for every player; and
- `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`,
  which produces the uniform-equilibrium payoff from those same contracting
  stationary data.

These declarations are existing semantic consumers. They assume their
finite strategic certificates; they do not assert the new raw completion
classes or produce the needed roots from their reward inequalities. The
new mathematical content here is that production step, together with the
exact finite calibration and its scoped comparison. The source audit is
static; no new Lean compilation or formalization of this packet is asserted.
No paper-derived result beyond the standard fixed-point theorems is being
attributed as a new theorem here.

### Named adapter from original rewards

Call the construction in Sections 1--4, 9, and 10 the **crossing-completion
adapter**. Its only inputs are the sixty finite original rewards and the
stated raw region hypothesis. It subtracts the four own singleton rewards,
computes Gamma, J, contacts and passive entries, and then produces a
four-phase root and value cycle by the specified Brouwer map. Its phase
map reverses the prefix clock, giving chronological supports 03,02,12,13.
Every active coordinate becomes the Bernoulli PMF on Bool with its proved
hazard; inactive coordinates use pure Continue. The literal endpoint
identities prove exact root Nash and policy recursion. The deleted-opponent
bounds give the strictly contracting cycle product required by the periodic
consumer. Signed original offsets are restored to both the reward table
and phase values, as justified in Section 5.

Call Section 11 the **negative-completion adapter**. From a reward table
satisfying the sixteen-entry raw min/max test, it computes H and t, selects
a closed parameter cell containing t, and produces its exact root by the
certified contraction map. The resulting q=t*z lies strictly in (0,1)^4.
Set the native stationary value to its forced-Quit vector Q; equation (N2)
proves equality of both endpoints and the value fixed point. Proper hazards
give joint and playerwise opponent absorption, making the saturated-face
boundary condition vacuous. Restore the four own offsets and apply the
stationary contracting consumer.

No strategic input remains unproduced in either adapter: hazards, finite
caps, exact fixed points, phase roots, contraction rates and the fixed target
are conclusions of the raw hypotheses. In particular, none of the raw
classes is defined by assuming a successful equilibrium, a supplied cycle,
an invertible continuation certificate, or a favorable semantic source.

### Suggested definitions and theorem shapes

Define reward predicates on `Fin 4` for the flexible 32-test transport
region, the finite signed Bernstein region, the compensated eight-guard
cone, and the negative relative tube. Their fields should contain only the
explicit raw equalities and inequalities in this packet. Define the
transport maps and polynomial coefficients independently of existence.

A first producer theorem should have the shape: for every original reward
table in the union of the three periodic regions, there exist a four-phase
product-root cycle and phase values satisfying exact policy recursion,
exact root Nash, and playerwise contraction. Its proof uses the explicit
maps, tensor Bernstein positivity, and Brouwer. Apply the existing periodic
consumer to obtain the UE theorem; do not place the required cycle or its
properties in the input predicate.

A second producer theorem should state: every table in the negative tube
admits a proper stationary product root and a value satisfying the fixed
point, endpoint Nash, and joint/playerwise contraction. Its proof verifies
the polynomial identities and all 512 rational interval certificates, then
uses the contraction theorem. A corollary takes the union of this branch
and the cone at zero favorite increment to cover every real common H.
Separate corollaries state the eight-participant-sign completion class,
the explicit full reward cube, and the unrestricted sixteen higher raw
coordinates in the cone.

The Python appendices specify reproducible exact certificates, not trusted
Lean oracles. Formalization should reconstruct the polynomial identities,
finite rational inequalities, Sturm exclusion and interval bounds with
kernel-checked proofs. The strongest first target is the raw cone producer
plus the existing periodic consumer; the negative-tube producer can then
reuse its independent stationary consumer. Check each new declaration under
its narrow imports and the project's trust rules. The existing generic
semantic compilers should be reused, without adding duplicate behavioral
or uniform-equilibrium interfaces.

## Appendix A. Flexible raw transport constants

```python
'Flexible raw transport constants; exact rational arithmetic only.'
from fractions import Fraction as F
from itertools import combinations, product

I = tuple(range(4))
e = F(1, 10**6)
eta = F(1, 2000)
lo = (F(7, 10), F(73, 100), F(3, 5), F(3, 4))
Wlo, Whi = F(106, 1000), F(167, 1000)
w, v = (1, 2, 0, 3), (3, 1, 2, 0)
S = tuple(frozenset((w[k], v[k])) for k in I)
jlo, jhi = F(1, 100)-e, F(1, 100)+e
alo, ahi = F(1, 20)-e, F(1, 20)+e
chi = F(7, 10)+e
assert all(v[k] == w[(k-1)%4] and w[k] == v[(k+1)%4] for k in I)
assert all(w[(k+2)%4] == (w[k]^1) for k in I)
assert all(v[(k+3)%4] == (w[k]^1) for k in I)
assert Wlo < jlo*min(lo)/(ahi+jlo*min(lo))
assert jhi/(alo+jhi) < Whi
assert Wlo > F(1, 10)
assert (-1+e)*Wlo+ahi*(1-Wlo) < -F(3, 50)
assert chi*Whi-(1-e-2*Whi)*min(lo) < -F(7, 25)

# A transparent subcone implies all 32 affine transport guards.
# First-inactive pair floor 1/2-e; second-inactive pair floor -1-e.
g = (F(3), F(4), F(2), F(5))
first_lower = (F(1, 2)-e)*Wlo+(-F(1, 25)-2*e)*(1-Wlo)
assert first_lower > 0 and min(lo)*first_lower > eta
margins = []
for k in I:
    first = (k+2)%4
    for x, y in product((lo[first], F(1)), (Wlo, Whi)):
        P = (g[k]-e)*y*(1-x)+(-F(1,25)-2*e)*x*(1-y)+(F(1,2)-e)*x*y
        assert P > eta
    second = (k+3)%4
    required = chi*lo[k]/(1-lo[k])
    for x, y in product((lo[second], F(1)), (Wlo, Whi)):
        P = (g[k]-e)*x*(1-y)+(-F(69,100)-2*e)*y*(1-x)+(-1-e)*x*y
        assert P > required+eta
    x = lo[second]
    lower = (g[k]-e)*x*(1-Whi)+(-F(69,100)-2*e)*Whi*(1-x)+(-1-e)*Whi*x
    margins.append(lower-required)

A = [[F(t) for t in row] for row in
     [[0,1,'-.7','-.05'],[1,0,'-.05','-.7'],['-.05','-.7',0,1],['-.7','-.05',1,0]]]
J = [[F(0) if i==j else (F(i+1) if j==(i^1) else F(1,100)) for j in I] for i in I]
signs = dict(zip(combinations(I,2), (-1,-1,1,1,-1,-1)))

def build(mode, t=F(0)):
    """Minimal completion or unbounded negative-passive compensation ray."""
    Z = {}
    for mask in range(1,16):
        for i in I:
            B = tuple(j for j in I if j!=i and mask>>j&1)
            if not B:
                p=d=F(0)
            elif len(B)==1:
                j=B[0];p=A[i][j]+J[i][j];d=-A[i][j]
                if mode=='ray' and j==(i^1): p+=t
            elif len(B)==3:
                p,d=F(1),F(-1)
            else:
                d=F(signs[B]*(1 if i==min(j for j in I if j not in B) else -1))
                p=max(F(0),-d)
                if mode=='ray' and d>0:p=-t
                if mode=='participant_floor':p=-d
            Z[i,mask]=p+(d if mask>>i&1 else 0)
    return Z

def validate(Z):
    def gamma(i,j):return Z[i,1<<j]-Z[i,1<<i]
    def premium(i,mask):return Z[i,mask]-Z[i,1<<i]
    def contact(i,mask):return Z[i,mask|(1<<i)]-Z[i,mask]
    for k in I:
        a,b=w[k],v[k];mask=(1<<a)|(1<<b)
        for i in (a,b):assert jlo<=premium(i,mask)<=jhi
        assert F(7,10)-e<=contact(a,1<<b)<=chi
        assert alo<=contact(b,1<<a)<=ahi
        assert contact(a^1,mask)<=-1+e
        assert contact(b^1,mask)<=1+e
        i=w[k]
        assert contact(i,1<<(i^1))<=-1+e
        for shift in (2,3):
            phase=(k+shift)%4;mask=sum(1<<j for j in S[phase])
            for x,y in product((lo[phase],F(1)),(Wlo,Whi)):
                P=gamma(i,w[phase])*y*(1-x)+gamma(i,v[phase])*x*(1-y)+premium(i,mask)*x*y
                required=eta if shift==2 else chi*lo[k]/(1-lo[k])+eta
                assert P>=required

minimal=build('minimal')
assert len(minimal)==60
validate(minimal)
floor=build('participant_floor')
validate(floor)
assert all(floor[i,mask]==0 for mask in range(1,16) if mask.bit_count()>=3 for i in I if mask>>i&1)
assert all(minimal[i,mask]>=0 for mask in range(1,16) for i in I if mask>>i&1)
assert sum(minimal[i,sum(1<<j for j in S[k])]==0 for k in I for i in I if i not in S[k])==4
# The old raw class requires all eight passive crossing-pair premiums>=1-e.
assert any(minimal[i,sum(1<<j for j in S[k])]<1-e for k in I for i in I if i not in S[k])

# For the whole participant-nonnegative class, F>=-d at the eight
# crossing pair entries. Every transport vertex is increasing in F, so
# validation at the common floor above proves ALL such independent choices.
assert all(x*y>=0 for x,y in product((min(lo),F(1)),(Wlo,Whi)))

# On the ray, the first transport increases by t*y*(1-x), and the
# second transport increases by t*x*(1-2*y)>0. Thus EVERY real t>=0 works.
for phase in I:
    for x,y in product((lo[phase],F(1)),(Wlo,Whi)):
        assert y*(1-x)>=0 and x*(1-2*y)>0
validate(build('ray',F(0)))
validate(build('ray',F(10**6)))  # Exact calibration, not the all-t proof.
print('PASS: weak hazards in (106/1000,167/1000); inactive gaps<-3/50 and<-7/25.')
print('PASS: all32 transport vertices for the enlarged simple subcone; margins:',margins)
print('PASS: complete participant-nonnegative crossing-triple class, all8 other passive coordinates arbitrary.')
print('PASS: original zero-triple and minimal completions, strict separation from the old literal raw guards.')
print('PASS: coefficient proof of the whole negative-passive compensation ray t>=0.')
print('ALL EXACT TRANSPORT POLYHEDRON CHECKS PASS')
```

## Appendix B. All-support stationary exclusion

```python
'All-support stationary exclusion; exact rational arithmetic only.'
from itertools import combinations
import sympy as s

I=tuple(range(4))
x,y,z=s.symbols('x y z')
A=s.Matrix([[0,1,-s.Rational(7,10),-s.Rational(1,20)],
            [1,0,-s.Rational(1,20),-s.Rational(7,10)],
            [-s.Rational(1,20),-s.Rational(7,10),0,1],
            [-s.Rational(7,10),-s.Rational(1,20),1,0]])
J=(s.ones(4)-s.eye(4))/100
for i in I:J[i,i^1]=i+1
Gamma=A+J
L=-A
assert all(t>0 for t in A.inv()) and all(t>0 for t in Gamma.inv())
assert all(J[i,j]>0 for i in I for j in I if i!=j)
assert list(s.ones(1,4)*A)==[s.Rational(1,4)]*4
pair_contacts={}
for B,sign in zip(combinations(I,2),[-1,-1,1,1,-1,-1]):
    i,j=[k for k in I if k not in B]
    pair_contacts[i,frozenset(B)]=sign
    pair_contacts[j,frozenset(B)]=-sign


def subsets(items):
    items=tuple(items)
    return [frozenset(items[j] for j in range(len(items)) if mask>>j&1)
            for mask in range(1<<len(items))]


def delta(i,B):
    B=frozenset(B)
    if not B:return s.S.Zero
    if len(B)==1:return L[i,next(iter(B))]
    if len(B)==2:return s.Integer(pair_contacts[i,B])
    return -s.S.One


def passive(i,B):
    if not B:return s.S.Zero
    if len(B)==1:return Gamma[i,next(iter(B))]
    if len(B)==2:return -delta(i,B)
    return s.S.One


R={(i,S):passive(i,S-{i})+(delta(i,S-{i}) if i in S else 0)
   for i in I for S in subsets(I) if S}
assert len(R)==60
assert all(R[i,frozenset([i])]==0 for i in I)
assert all(R[i,S]>=0 for i in I for S in subsets(I) if i in S)


def endpoints(i,q):
    P=Q=s.S.Zero
    for B in subsets(j for j in I if j!=i):
        weight=s.prod(q[j] if j in B else 1-q[j] for j in I if j!=i)
        P+=weight*(R[i,B] if B else 0)
        Q+=weight*R[i,B|{i}]
    H=s.prod(1-q[j] for j in I if j!=i)
    return s.expand(P),s.expand(Q),s.expand(H)


def gap(i,q):
    P,Q,H=endpoints(i,q)
    return s.expand(Q-P)


qq=s.symbols('q0:4')
identity_left=sum((1-qq[i])*gap(i,qq) for i in I)
identity_right=-s.Rational(1,4)*sum(qq[j]*s.prod(1-qq[k] for k in I if k!=j) for j in I)
identity_right-=sum((1-qq[i])*s.prod(qq[j] for j in I if j!=i) for i in I)
assert s.expand(identity_left-identity_right)==0
assert all(gap(i,[1]*4)==-1 for i in I)
print('PASS: all 60 rewards, inverse-positive matching, nonnegative participants, full-support identity.')

# All proper three-support zero-input solutions and one-sure candidates.
# Together with the support and identity arguments in the note this is the
# complete frozen zero-input census, reproduced for the actual literal table.
one_sure=[]
for S in combinations(I,3):
    M,rhs=s.zeros(3),s.zeros(3,1)
    for row,i in enumerate(S):
        opp=[j for j in S if j!=i]
        for j in opp:
            M[row,S.index(j)]=L[i,next(k for k in opp if k!=j)]
        rhs[row]=-delta(i,opp)
    inverse_odds=M.inv()*rhs
    assert min(inverse_odds)<0
    pure=[int(i in S) for i in I]
    assert any(gap(i,pure)<0 for i in S)
    for h in S:
        j,k=[i for i in S if i!=h]
        dj=L[k,h]-delta(k,(h,j));dk=L[j,h]-delta(j,(h,k))
        if dj==0 or dk==0:
            assert L[k,h]!=0 and L[j,h]!=0
            continue
        qj,qk=L[k,h]/dj,L[j,h]/dk
        if 0<qj<1 and 0<qk<1:
            q=[s.S.Zero]*4;q[h]=1;q[j]=qj;q[k]=qk
            assert gap(h,q)<0
            one_sure.append((S,h,qj,qk,gap(h,q)))
assert one_sure==[((0,1,2),1,s.Rational(7,17),s.Rational(1,2),-s.Rational(27,68)),
                  ((0,2,3),2,s.Rational(1,2),s.Rational(7,17),-s.Rational(27,68))]
for S in combinations(I,2):
    outside=[i for i in I if i not in S]
    assert delta(outside[0],S)*delta(outside[1],S)<0
print('PASS: exact zero-input census and every possible three-support one-sure candidate.')


def add(a,b):return(a[0]+b[0],a[1]+b[1])


def mul(a,b):
    vals=[u*v for u in a for v in b]
    return(min(vals),max(vals))


def divide(a,b):
    assert b[0]*b[1]>0
    return mul(a,(1/b[1],1/b[0]))


def poly_interval(expr,ivs):
    result=(s.S.Zero,s.S.Zero)
    for powers,coefficient in s.Poly(expr,*ivs.keys()).terms():
        term=(coefficient,coefficient)
        for (_,iv),power in zip(ivs.items(),powers):
            for _ in range(power):term=mul(term,iv)
        result=add(result,term)
    return result


expected_counts=[2,1,3,0]
coarse_intervals=[[(100308,100309),(940418,940419)],
                  [(959332,959333)],
                  [(3020,3021),(45840,45841),(49250,49251)],[]]
for S,expected,coarse in zip(combinations(I,3),expected_counts,coarse_intervals):
    q=[s.S.Zero]*4
    for i,variable in zip(S,(x,y,z)):q[i]=variable
    equations=[]
    for i in S:
        P,Q,H=endpoints(i,q)
        equations.append(s.expand(100*((1-H)*Q-P)))
    F,G,K=equations
    assert not F.has(x) and not G.has(y) and not K.has(z)
    # Necessary elimination equation E(y,z)=0 at any common root of G,K.
    E=s.resultant(G,K,x)
    resultant=s.Poly(s.resultant(F,E,y),z)
    assert resultant.eval(0)==0
    p=s.Poly(resultant.as_expr()/z,z).primitive()[1]
    assert p.degree()==15 and p.eval(0)!=0 and p.eval(1)!=0
    assert p.count_roots(0,1)==expected
    # Explicit pseudodivision identity recovers y at each isolated z.
    quotient,remainder=s.pdiv(E,F,y)
    lead=s.Poly(F,y).LC()
    power=s.degree(E,y)-s.degree(F,y)+1
    assert s.expand(lead**power*E-quotient*F-remainder)==0
    assert s.degree(remainder,y)==1
    yc=s.expand(remainder).coeff(y);yd=remainder.subs(y,0)
    # An explicit cancellation of quadratic x terms recovers x.
    GP,KP=s.Poly(G,x),s.Poly(K,x)
    xc=s.expand(KP.nth(2)*GP.nth(1)-GP.nth(2)*KP.nth(1))
    xd=s.expand(KP.nth(2)*GP.nth(0)-GP.nth(2)*KP.nth(0))
    assert s.expand(KP.nth(2)*G-GP.nth(2)*K-xc*x-xd)==0
    intervals=[]
    for (lo,hi),multiplicity in p.intervals(eps=s.Rational(1,10**35)):
        if hi<=0 or lo>=1:continue
        assert 0<lo<=hi<1 and multiplicity==1
        assert p.count_roots(lo,hi)==1
        zi=(lo,hi)
        yi=divide(poly_interval(-yd,{z:zi}),poly_interval(yc,{z:zi}))
        xi=divide(poly_interval(-xd,{y:yi,z:zi}),poly_interval(xc,{y:yi,z:zi}))
        assert xi[1]<0 or xi[0]>1 or yi[1]<0 or yi[0]>1
        intervals.append((zi,xi,yi))
    assert len(intervals)==expected
    for ((lo,hi),xi,yi),(cl,ch) in zip(intervals,coarse):
        assert s.Rational(cl,10**6)<lo<=hi<s.Rational(ch,10**6)
    print('PASS: support',S,'degree15 projection,',expected,'interior z roots; all recovered hazards outside the cube.')
print('ALL EXACT ZERO-TRIPLE STATIONARY EXCLUSION CHECKS PASS')
```

## Appendix C. Signed finite-box certificate

```python
#!/usr/bin/env python3
"""Exact raw-table and Bernstein certificate for signed crossing transports."""
from itertools import combinations, product
from math import comb
import sympy as s

Q = s.Rational
I = range(4)
x = s.symbols('x0:4')
alpha = s.symbols('alpha0:4')
beta = s.symbols('beta0:4')
params = (*alpha, *beta)
lo = list(map(Q, ['.60', '.65', '.40', '.60']))
hi = list(map(Q, ['.85', '.87', '.80', '.90']))
phases = [frozenset(S) for S in ((1, 3), (1, 2), (0, 2), (0, 3))]
w = [1, 2, 0, 3]
v = [3, 1, 2, 0]
g = [3, 4, 2, 5]
y = [x[(k-1) % 4] / (5+x[(k-1) % 4]) for k in I]
D0 = s.prod(5+t for t in x)
active_out = [y[(k+1) % 4] / 100 for k in I]
E = []
B = []
for k in I:
    t = (k+2) % 4
    E.append(g[k]*y[t]*(1-x[t]) - Q(1, 25)*x[t]*(1-y[t])
             + alpha[k]*x[t]*y[t] + (1-x[t])*(1-y[t])*active_out[k])
for k in I:
    t = (k+3) % 4
    B.append(-Q(69, 100)*y[t]*(1-x[t]) + g[k]*x[t]*(1-y[t])
             + beta[k]*x[t]*y[t] + (1-x[t])*(1-y[t])*E[k])
checks = []
for k in I:
    C = (1-x[k])*(1-y[k])
    checks.append((k, 'lower', B[k]-Q(7, 10)*lo[k]/(1-lo[k])))
    checks.append((k, 'upper', Q(7, 10)*hi[k]/(1-hi[k])-B[k]))
    checks.append((k, 'first', y[k]-Q(1, 20)*x[k]*(1-y[k])+C*active_out[(k+2) % 4]))
    checks.append((k, 'second', -Q(7, 10)*y[k]*(1-x[k])+x[k]-2*x[k]*y[k]+C*E[(k+1) % 4]))


def zero(expr):
    assert s.cancel(expr) == 0


def subsets(S):
    S = tuple(sorted(S))
    return [frozenset(B) for k in range(len(S)+1) for B in combinations(S, k)]


# Independent reconstruction of every table entry, with all sixteen passive
# coordinates retained before any common-H substitution.
A = s.Matrix([[0, 1, -Q(7, 10), -Q(1, 20)],
              [1, 0, -Q(1, 20), -Q(7, 10)],
              [-Q(1, 20), -Q(7, 10), 0, 1],
              [-Q(7, 10), -Q(1, 20), 1, 0]])
J = (s.ones(4)-s.eye(4))/100
for i in I:
    J[i, i ^ 1] = i+1
Gamma = A+J
contacts = {}
for coalition, sign in zip(combinations(I, 2), [-1, -1, 1, 1, -1, -1]):
    pair = frozenset(coalition)
    left, right = [i for i in I if i not in pair]
    contacts[left, pair] = sign
    contacts[right, pair] = -sign
passive_pair = {}
for k in I:
    passive_pair[w[k], phases[(k+2) % 4]] = alpha[k]
    passive_pair[w[k], phases[(k+3) % 4]] = beta[k]
assert len(passive_pair) == 8
free_pair = []
for i in I:
    for pair in combinations(set(I)-{i}, 2):
        key = (i, frozenset(pair))
        if key not in passive_pair:
            z = s.Symbol('freeF'+str(i)+''.join(map(str, sorted(pair))))
            passive_pair[key] = z
            free_pair.append(z)
free_triple = s.symbols('freeT0:4')
assert len(free_pair) == 4 and len(passive_pair) == 12


def passive(i, opp):
    if not opp:
        return s.Integer(0)
    if len(opp) == 1:
        return Gamma[i, next(iter(opp))]
    if len(opp) == 2:
        return passive_pair[i, opp]
    return free_triple[i]


def contact(i, opp):
    if not opp:
        return s.Integer(0)
    if len(opp) == 1:
        return -A[i, next(iter(opp))]
    if len(opp) == 2:
        return contacts[i, opp]
    return s.Integer(-1)


Z = {}
for coalition in subsets(I):
    if not coalition:
        continue
    for i in I:
        opp = coalition-{i}
        Z[coalition, i] = passive(i, opp)+(contact(i, opp) if i in coalition else 0)
assert len(Z) == 60
assert all(Z[frozenset({i}), i] == 0 for i in I)


def endpoints(k, i):
    hazards = {w[k]: y[k], v[k]: x[k]}
    opponents = phases[k]-{i}
    P = Qv = s.Integer(0)
    for coalition in subsets(opponents):
        probability = s.prod(hazards[j] if j in coalition else 1-hazards[j]
                             for j in opponents)
        P += probability*(Z[coalition, i] if coalition else 0)
        Qv += probability*Z[coalition | {i}, i]
    H = s.prod(1-hazards[j] for j in opponents)
    return P, Qv, H


for k in I:
    # Strong active owner: actual prior weak output and exact indifference.
    P, Qv, H = endpoints(k, v[k])
    zero(Qv-y[k]/100)
    zero(Qv-P-H*x[(k-1) % 4]/100)
    # Weak active owner: the only equality deferred to the Brouwer fixed point.
    P, Qv, H = endpoints(k, w[k])
    zero(Qv-x[k]/100)
    zero((Qv-P-H*B[k])-(Q(7, 10)*x[k]-(1-x[k])*B[k]))
    # Both inactive roots, with signed intermediate continuation retained.
    ell = w[(k+2) % 4]
    h = w[(k+1) % 4]
    assert ell == (w[k] ^ 1) and h == (v[k] ^ 1)
    P, Qv, H = endpoints(k, ell)
    zero(P+H*active_out[(k+2) % 4]-E[(k+2) % 4])
    zero(Qv-P-H*active_out[(k+2) % 4]+checks[4*k+2][2])
    P, Qv, H = endpoints(k, h)
    zero(P+H*E[(k+1) % 4]-B[(k+1) % 4])
    zero(Qv-P-H*E[(k+1) % 4]+checks[4*k+3][2])


# Generic polynomial degrees and affine dependence, before specialization.
polychecks = []
for k, kind, expr in checks:
    poly = s.Poly(s.cancel(D0*expr), *x)
    degrees = tuple(2 if j == ((k-1) % 4 if kind in ('lower', 'upper') else k)
                    else 1 for j in I)
    assert poly.degree_list() == degrees
    assert all(s.Poly(c, *params).total_degree() <= 1 for c in poly.coeffs())
    assert not set((*free_pair, *free_triple)).intersection(poly.as_expr().free_symbols)
    polychecks.append((k, kind, poly, degrees))


def bernstein_coefficients(poly, degrees):
    transformed = s.Poly(poly.as_expr().subs(
        {x[j]: lo[j]+(hi[j]-lo[j])*x[j] for j in I}, simultaneous=True).expand(), *x)
    coeffs = []
    for m in product(*(range(d+1) for d in degrees)):
        value = 0
        for n, c in transformed.terms():
            if all(n[j] <= m[j] for j in I):
                value += c*s.prod(Q(comb(m[j], n[j]), comb(degrees[j], n[j])) for j in I)
        coeffs.append(value)
    return coeffs


certified_integer_lower = [[121, 1394, 69, 277], [323, 1549, 68, 330],
                          [226, 1141, 82, 60], [263, 2715, 32, 314]]
kinds = ['lower', 'upper', 'first', 'second']
count = 0
for k, kind, poly, degrees in polychecks:
    minima = []
    for H in (-3, 1):
        specialized = s.Poly(poly.as_expr().subs({z: H for z in params}), *x)
        coefficients = bernstein_coefficients(specialized, degrees)
        assert len(coefficients) == 24
        assert min(coefficients) > certified_integer_lower[k][kinds.index(kind)]
        assert all(c.is_Rational for c in coefficients)
        minima.append(min(coefficients))
        count += len(coefficients)
    print(k, kind, 'minimum exact coefficient', min(minima))
assert count == 768

# Uniform bounds and genuinely signed intermediate cap at H=-3.
assert min(lo)/(5+min(lo)) == Q(2, 27)
assert max(hi)/(5+max(hi)) == Q(9, 59)
zero(E[2].subs(alpha[2], -3)-(y[0]*(2-5*x[0])-Q(1, 25)*x[0]*(1-y[0])
                              +(1-x[0])*(1-y[0])*active_out[2]))
assert lo[0] == Q(3, 5) and lo[3]/(5+lo[3]) == Q(3, 28)
assert -Q(3, 28)+Q(1, 100) < 0
print('PASS: full 60-entry raw table; all 16 literal endpoint identities; generic affine passive tests; 768 exact Bernstein coefficients; H in [-3,1]; signed intermediate cap; deleted-clock geometric bound')

# The generic coefficient derivatives certify the independent box.
v = globals()
s, x, alpha, beta, B, D0 = (v[n] for n in ('s', 'x', 'alpha', 'beta', 'B', 'D0'))
for k in range(4):
    def z(j):
        return x[j % 4]
    expected_a = 5*(1-z(k+3))*z(k+2)*z(k+1)*(5+z(k))*(5+z(k+3))
    expected_b = z(k+3)*z(k+2)*(5+z(k))*(5+z(k+1))*(5+z(k+3))
    expected_o = 5*(1-z(k))*z(k+3)*z(k+2)*(5+z(k))*(5+z(k+1))
    v['zero'](s.diff(D0*B[k], alpha[k])-expected_a)
    v['zero'](s.diff(D0*B[k], beta[k])-expected_b)
    v['zero'](s.diff(D0*v['checks'][4*k+3][2], alpha[(k+1) % 4])-expected_o)
count = 0
for k, kind, poly, degrees in v['polychecks']:
    coefficients = v['bernstein_coefficients'](poly, degrees)
    sign = -1 if kind == 'upper' else 1
    for c in coefficients:
        for parameter in v['params']:
            derivative = s.diff(c, parameter)
            assert derivative.is_Rational and sign*derivative >= 0
            if kind == 'first':
                assert derivative == 0
            count += 1
assert count == 3072
print('PASS: all twelve positive-factor derivative identities; 3072 exact coefficient derivative signs; entire independent passive box [-3,1]^8')
```

## Appendix D. Compensated unbounded cone certificate

```python
#!/usr/bin/env python3
"""Standalone exact certificate for the compensated crossing-passive cone."""
from itertools import combinations, product
from math import comb
import sympy as s

Q = s.Rational
I = range(4)
x = s.symbols('x0:4')
alpha = s.symbols('alpha0:4')
beta = s.symbols('beta0:4')
tau = s.symbols('tau0:4')
params = (*alpha, *beta, *tau)
lo = [Q(31, 50), Q(24, 35), Q(7, 15), Q(2, 3)]
hi = [s.Integer(1)]*4
phases = [frozenset(S) for S in ((1, 3), (1, 2), (0, 2), (0, 3))]
w = [1, 2, 0, 3]
v = [3, 1, 2, 0]
g = [3, 4, 2, 5]
y = [x[(k-1) % 4] / (5+x[(k-1) % 4]) for k in I]
D0 = s.prod(5+t for t in x)
active_out = [y[(k+1) % 4] / 100 for k in I]
E = []
B = []
for k in I:
    t = (k+2) % 4
    E.append((g[k]+tau[w[k]])*y[t]*(1-x[t]) - Q(1, 25)*x[t]*(1-y[t])
             + alpha[k]*x[t]*y[t] + (1-x[t])*(1-y[t])*active_out[k])
for k in I:
    t = (k+3) % 4
    B.append(-Q(69, 100)*y[t]*(1-x[t]) + (g[k]+tau[w[k]])*x[t]*(1-y[t])
             + beta[k]*x[t]*y[t] + (1-x[t])*(1-y[t])*E[k])
checks = []
for k in I:
    C = (1-x[k])*(1-y[k])
    checks.append((k, 'lower', B[k]-Q(7, 10)*lo[k]/(1-lo[k])))
    checks.append((k, 'first', y[k]-Q(1, 20)*x[k]*(1-y[k])+C*active_out[(k+2) % 4]))
    checks.append((k, 'second', -Q(7, 10)*y[k]*(1-x[k])+x[k]-2*x[k]*y[k]+C*E[(k+1) % 4]))


def zero(expr):
    assert s.cancel(expr) == 0


def subsets(S):
    S = tuple(sorted(S))
    return [frozenset(B) for k in range(len(S)+1) for B in combinations(S, k)]


# Independent reconstruction of every table entry, retaining sixteen unused
# higher raw-coordinate symbols and all active parameters before specialization.
A = s.Matrix([[0, 1, -Q(7, 10), -Q(1, 20)],
              [1, 0, -Q(1, 20), -Q(7, 10)],
              [-Q(1, 20), -Q(7, 10), 0, 1],
              [-Q(7, 10), -Q(1, 20), 1, 0]])
J = (s.ones(4)-s.eye(4))/100
for i in I:
    J[i, i ^ 1] = i+1+tau[i]
Gamma = A+J
contacts = {}
free_pair_contacts = []
for coalition, sign in zip(combinations(I, 2), [-1, -1, 1, 1, -1, -1]):
    pair = frozenset(coalition)
    left, right = [i for i in I if i not in pair]
    if pair in phases:
        contacts[left, pair] = sign
        contacts[right, pair] = -sign
    else:
        for i in (left, right):
            raw = s.Symbol('freeD'+str(i)+''.join(map(str, sorted(pair))))
            contacts[i, pair] = raw
            free_pair_contacts.append(raw)
passive_pair = {}
for k in I:
    passive_pair[w[k], phases[(k+2) % 4]] = alpha[k]
    passive_pair[w[k], phases[(k+3) % 4]] = beta[k]
assert len(passive_pair) == 8
free_pair = []
for i in I:
    for pair in combinations(set(I)-{i}, 2):
        key = (i, frozenset(pair))
        if key not in passive_pair:
            z = s.Symbol('freeF'+str(i)+''.join(map(str, sorted(pair))))
            passive_pair[key] = z
            free_pair.append(z)
free_triple = s.symbols('freeT0:4')
free_grand_contacts = s.symbols('freeGrandContact0:4')
assert len(free_pair) == 4 and len(passive_pair) == 12
assert len(free_pair_contacts) == 4
free_higher = (*free_pair, *free_triple, *free_pair_contacts, *free_grand_contacts)
assert len(set(free_higher)) == 16


def passive(i, opp):
    if not opp:
        return s.Integer(0)
    if len(opp) == 1:
        return Gamma[i, next(iter(opp))]
    if len(opp) == 2:
        return passive_pair[i, opp]
    return free_triple[i]


def contact(i, opp):
    if not opp:
        return s.Integer(0)
    if len(opp) == 1:
        return -A[i, next(iter(opp))]
    if len(opp) == 2:
        return contacts[i, opp]
    return free_grand_contacts[i]


Z = {}
for coalition in subsets(I):
    if not coalition:
        continue
    for i in I:
        opp = coalition-{i}
        Z[coalition, i] = passive(i, opp)+(contact(i, opp) if i in coalition else 0)
assert len(Z) == 60
assert all(Z[frozenset({i}), i] == 0 for i in I)


def endpoints(k, i):
    hazards = {w[k]: y[k], v[k]: x[k]}
    opponents = phases[k]-{i}
    P = Qv = s.Integer(0)
    for coalition in subsets(opponents):
        probability = s.prod(hazards[j] if j in coalition else 1-hazards[j]
                             for j in opponents)
        P += probability*(Z[coalition, i] if coalition else 0)
        Qv += probability*Z[coalition | {i}, i]
    H = s.prod(1-hazards[j] for j in opponents)
    return P, Qv, H


for k in I:
    for i in I:
        literal_P, literal_Q, literal_H = endpoints(k, i)
        assert not set(free_higher).intersection(literal_P.free_symbols | literal_Q.free_symbols)
    # Strong active owner: actual prior weak output and exact indifference.
    P, Qv, H = endpoints(k, v[k])
    zero(Qv-y[k]/100)
    zero(Qv-P-H*x[(k-1) % 4]/100)
    # Weak active owner: the only equality deferred to the Brouwer fixed point.
    P, Qv, H = endpoints(k, w[k])
    zero(Qv-x[k]/100)
    zero((Qv-P-H*B[k])-(Q(7, 10)*x[k]-(1-x[k])*B[k]))
    # Both inactive roots, with signed intermediate continuation retained.
    ell = w[(k+2) % 4]
    h = w[(k+1) % 4]
    assert ell == (w[k] ^ 1) and h == (v[k] ^ 1)
    P, Qv, H = endpoints(k, ell)
    zero(P+H*active_out[(k+2) % 4]-E[(k+2) % 4])
    zero(Qv-P-H*active_out[(k+2) % 4]+checks[3*k+1][2])
    P, Qv, H = endpoints(k, h)
    zero(P+H*E[(k+1) % 4]-B[(k+1) % 4])
    zero(Qv-P-H*E[(k+1) % 4]+checks[3*k+2][2])


# Generic polynomial degrees and affine dependence, before specialization.
polychecks = []
for k, kind, expr in checks:
    poly = s.Poly(s.cancel(D0*expr), *x)
    degrees = tuple(2 if j == ((k-1) % 4 if kind == 'lower' else k)
                    else 1 for j in I)
    assert poly.degree_list() == degrees
    assert all(s.Poly(c, *params).total_degree() <= 1 for c in poly.coeffs())
    assert not set(free_higher).intersection(poly.as_expr().free_symbols)
    polychecks.append((k, kind, poly, degrees))


def bernstein_coefficients(poly, degrees):
    transformed = s.Poly(poly.as_expr().subs(
        {x[j]: lo[j]+(hi[j]-lo[j])*x[j] for j in I}, simultaneous=True).expand(), *x)
    coeffs = []
    for m in product(*(range(d+1) for d in degrees)):
        value = 0
        for n, c in transformed.terms():
            if all(n[j] <= m[j] for j in I):
                value += c*s.prod(Q(comb(m[j], n[j]), comb(degrees[j], n[j])) for j in I)
        coeffs.append(value)
    return coeffs


certified_integer_lower = [[5, 77, 230], [19, 68, 314],
                          [13, 83, 13], [14, 41, 295]]
kinds = ['lower', 'first', 'second']
count = 0
for k, kind, poly, degrees in polychecks:
    specialized = s.Poly(poly.as_expr().subs({**{z: -3 for z in (*alpha, *beta)}, **{z: 0 for z in tau}}), *x)
    coefficients = bernstein_coefficients(specialized, degrees)
    assert len(coefficients) == 24
    assert min(coefficients) > certified_integer_lower[k][kinds.index(kind)]
    assert all(c.is_Rational for c in coefficients)
    count += len(coefficients)
    print(k, kind, 'minimum exact coefficient', min(coefficients))
assert count == 288

# Exact positive-factor derivatives extend the worst corner to the entire
# independent unbounded orthant. Every factor has known nonnegative sign
# on the box lo<=x<=1; no diagonal-inference shortcut is taken.
for k in I:
    def z(j):
        return x[j % 4]
    da = 5*(1-z(k+3))*z(k+2)*z(k+1)*(5+z(k))*(5+z(k+3))
    db = z(k+3)*z(k+2)*(5+z(k))*(5+z(k+1))*(5+z(k+3))
    do = 5*(1-z(k))*z(k+3)*z(k+2)*(5+z(k))*(5+z(k+1))
    zero(s.diff(D0*B[k], alpha[k])-da)
    zero(s.diff(D0*B[k], beta[k])-db)
    zero(s.diff(D0*checks[3*k+2][2], alpha[(k+1) % 4])-do)
    for parameter in params:
        if parameter not in (alpha[k], beta[k], tau[w[k]]):
            zero(s.diff(B[k], parameter))
        if parameter not in (alpha[(k+1) % 4], tau[w[(k+1) % 4]]):
            zero(s.diff(checks[3*k+2][2], parameter))
        zero(s.diff(checks[3*k+1][2], parameter))

# Independent favorite increments: compensate beta by FIVE times the
# increment. These literal rational identities have nonnegative factors
# on the entire expanded box because y<=1/6, including its sure faces.
for k in I:
    first = (k+2) % 4
    second = (k+3) % 4
    E_gain = y[first]*(1-x[first])
    B_gain = x[second]*(1-6*y[second])+(1-x[second])*(1-y[second])*E_gain
    zero(s.diff(E[k], tau[w[k]])-E_gain)
    zero(s.diff(B[k], tau[w[k]])-5*s.diff(B[k], beta[k])-B_gain)
    zero(s.diff(checks[3*k+2][2], tau[w[(k+1) % 4]])
         -(1-x[k])*(1-y[k])*y[(k+3) % 4]*(1-x[(k+3) % 4]))
    zero(1-6*y[k]-5*(1-x[(k-1) % 4])/(5+x[(k-1) % 4]))
    corner = {**{p: -3 for p in (*alpha, *beta)}, **{p: 0 for p in tau}}
    delta_alpha = alpha[k]+3
    delta_beta = beta[k]+3+5*tau[w[k]]
    zero(E[k]-E[k].subs(corner)-tau[w[k]]*E_gain
         -delta_alpha*x[first]*y[first])
    zero(B[k]-B[k].subs(corner)-tau[w[k]]*B_gain
         -delta_beta*x[second]*y[second]
         -delta_alpha*(1-x[second])*(1-y[second])*x[first]*y[first])

# Uniform deleted-opponent survival and genuinely signed intermediate cap.
assert all(0 < lo[j] < 1 for j in I)
assert min(lo)/(5+min(lo)) == Q(7, 82)
assert max(hi)/(5+max(hi)) == Q(1, 6)
zero(E[2].subs({alpha[2]: -3, tau[w[2]]: 0})-(y[0]*(2-5*x[0])-Q(1, 25)*x[0]*(1-y[0])
                              +(1-x[0])*(1-y[0])*active_out[2]))
assert lo[0] >= Q(3, 5) and lo[3]/(5+lo[3]) >= Q(3, 28)
assert -Q(3, 28)+Q(1, 100) < 0
print('PASS: full 60-entry raw table; all phase endpoint identities; 288 exact Bernstein coefficients; twelve positive-factor derivatives; independent favorite-increment compensation factor5; sixteen unused higher raw coordinates arbitrary; signed caps and deleted survival75/82')
```

## Appendix E. Stationary negative tube certificate

```python
"""Exact rational certificate for a sixteen-dimensional negative passive tube.

All 512 closed cells cover t=-1/H in [0,1/3]. Rational rounded Newton only
constructs candidate centers; independent whole-box contraction and residual
bounds certify each cell. Every passive higher reward may independently vary
by at most |H|/32768. No floating-point number is used anywhere.
"""
from fractions import Fraction as F
from itertools import combinations
from math import comb
import sympy as sp

N = 512
radius = F(1, N)
t=sp.symbols('t'); z=sp.symbols('z0:4'); q=sp.symbols('q0:4')
A=sp.Matrix([[0,1,-sp.Rational(7,10),-sp.Rational(1,20)],
             [1,0,-sp.Rational(1,20),-sp.Rational(7,10)],
             [-sp.Rational(1,20),-sp.Rational(7,10),0,1],
             [-sp.Rational(7,10),-sp.Rational(1,20),1,0]])
J=(sp.ones(4)-sp.eye(4))/100
for i in range(4): J[i,i^1]=i+1
Gamma=A+J
contact={}
for B,sign in zip(combinations(range(4),2),[-1,-1,1,1,-1,-1]):
    lo,hi=[i for i in range(4) if i not in B]
    contact[lo,frozenset(B)]=sign;contact[hi,frozenset(B)]=-sign
fields=[]
for i in range(4):
    other=[j for j in range(4) if j!=i]
    p0=sp.prod(1-t*z[j] for j in other)
    e2=sum(z[j]*z[k] for j,k in combinations(other,2))
    e3=sp.prod(z[j] for j in other)
    P=sum(Gamma[i,j]*z[j]*sp.prod(1-t*z[k] for k in other if k!=j) for j in other)-e2+2*t*e3
    D=sum(-A[i,j]*z[j]*sp.prod(1-t*z[k] for k in other if k!=j) for j in other)
    D+=t*sum(contact[i,frozenset(B)]*sp.prod(z[j] for j in B)*sp.prod(1-t*z[j] for j in other if j not in B) for B in combinations(other,2))-t*t*e3
    fields.append(sp.expand(-p0*P+(1-p0)*D))

# Independently reconstruct all sixty literal reward entries, including the
# passive partner-pair and triple coordinates actually used by this branch.
H=sp.symbols('H')
table={}
for mask in range(1,16):
    S=frozenset(i for i in range(4) if mask & (1<<i))
    for i in range(4):
        B=S-{i}
        passive=0 if not B else Gamma[i,next(iter(B))] if len(B)==1 else H
        delta=0 if not B else -A[i,next(iter(B))] if len(B)==1 else contact[i,B] if len(B)==2 else -1
        table[i,S]=passive+(delta if i in S else 0)
assert len(table)==60
for i in range(4):
    other=[j for j in range(4) if j!=i]
    P=Q=0
    for size in range(4):
        for chosen in combinations(other,size):
            B=frozenset(chosen)
            prob=sp.prod(q[j] if j in B else 1-q[j] for j in other)
            P+=prob*(table[i,B] if B else 0)
            Q+=prob*table[i,B|{i}]
    literal=(1-sp.prod(1-q[j] for j in other))*Q-P
    assert sp.cancel(literal.subs(dict(zip(q,[t*x for x in z]))).subs(H,-1/t)-t*fields[i])==0

# Independent perturbations of all three passive pairs and the passive
# triple for each owner. Exact endpoint-field difference is -p_i W_i.
for i in range(4):
    other=[j for j in range(4) if j!=i]
    coalitions=[frozenset(B) for size in (2,3) for B in combinations(other,size)]
    xi=sp.symbols(f'xi{i}_0:4')
    deltaP=0
    W=0
    for B,x in zip(coalitions,xi):
        prob=sp.prod(t*z[j] if j in B else 1-t*z[j] for j in other)
        deltaP+=prob*x/t
        W+=x*sp.prod(z[j] for j in B)*sp.prod(1-t*z[j] for j in other if j not in B)*(t if len(B)==3 else 1)
    p0=sp.prod(1-t*z[j] for j in other)
    assert sp.cancel(-p0*deltaP/t+p0*W)==0

eta=F(1,32768)
b=F(7,5); tmax=F(1,3)
C0=3*b*b
coordinate_derivative=tmax*C0+2*b+2*tmax*b*b
C1=3*coordinate_derivative
assert C0==F(147,25) and coordinate_derivative==F(91,15) and C1==F(91,5)
assert F(1,4)+2*C1*eta<F(1,2)
assert F(23,32)+2*eta*(C0/radius+C1)<F(29,32)<1

def terms(poly):
    return [(powers,F(int(c.p),int(c.q))) for powers,c in sp.Poly(poly,*z,t).terms()]

E=list(map(terms,fields))
DJ=[[terms(sp.diff(p,x)) for x in z] for p in fields]

def powers_at(values):
    return [[F(1)]+[v**k for k in range(1,6)] for v in values]

def evaluate(poly,powers):
    answer=F(0)
    for exponents,c in poly:
        for j,e in enumerate(exponents): c*=powers[j][e]
        answer+=c
    return answer

def inverse(a):
    b=[row[:]+[F(i==j) for j in range(4)] for i,row in enumerate(a)]
    for j in range(4):
        row=next(i for i in range(j,4) if b[i][j])
        b[j],b[row]=b[row],b[j]
        pivot=b[j][j];b[j]=[v/pivot for v in b[j]]
        for i in range(4):
            if i!=j:
                c=b[i][j];b[i]=[x-c*y for x,y in zip(b[i],b[j])]
    return [row[4:] for row in b]

def rounded(x,den=10**10):
    # Nearest rational on a fixed exact grid; no floating-point dependency.
    return F((x.numerator*den*2//x.denominator+1)//2,den)

def newton(center,mid,steps):
    for _ in range(steps):
        p=powers_at(center+[mid]);v=[evaluate(poly,p) for poly in E]
        jac=[[evaluate(poly,p) for poly in row] for row in DJ]
        R=inverse(jac)
        center=[rounded(center[i]-sum(R[i][j]*v[j] for j in range(4))) for i in range(4)]
    return center

def interval_powers(lower,upper):
    assert min(lower)>=0
    return [[(F(1),F(1))]+[(a**k,b**k) for k in range(1,6)] for a,b in zip(lower,upper)]

def interval_eval(poly,powers):
    lo=hi=F(0)
    for exponents,c in poly:
        a=b=F(1)
        for j,e in enumerate(exponents):
            p,q=powers[j][e];a*=p;b*=q
        if c>=0:lo+=c*a;hi+=c*b
        else:lo+=c*b;hi+=c*a
    return lo,hi

def interval_sum_scaled(coefficients,intervals):
    lo=hi=F(0)
    for c,(a,b) in zip(coefficients,intervals):
        if c>=0:lo+=c*a;hi+=c*b
        else:lo+=c*b;hi+=c*a
    return lo,hi

center=[F(68,100),F(132,100),F(47,100),F(92,100)]
maximum_lambda=F(0); maximum_defect=F(0)
for k in range(N):
    lo,hi=F(k,3*N),F(k+1,3*N);mid=(lo+hi)/2
    center=newton(center,mid,6 if k==0 else 3)
    p=powers_at(center+[mid]);R=inverse([[evaluate(poly,p) for poly in row] for row in DJ])
    R=[[rounded(x,10**8) for x in row] for row in R]
    assert max(sum(abs(x) for x in row) for row in R)<2
    # Full parameter-and-state box for the derivative contraction bound.
    lower=[x-radius for x in center]+[lo]
    upper=[x+radius for x in center]+[hi]
    assert min(lower[:4])>F(2,5) and max(upper[:4])<F(7,5)
    assert hi*max(upper[:4])<1
    box=interval_powers(lower,upper)
    jacbox=[[interval_eval(poly,box) for poly in row] for row in DJ]
    lam=F(0)
    for i in range(4):
        norm=F(0)
        for j in range(4):
            a,b=interval_sum_scaled(R[i],[jacbox[l][j] for l in range(4)])
            a,b=F(i==j)-b,F(i==j)-a
            norm+=max(abs(a),abs(b))
        lam=max(lam,norm)
    # Center residual as a univariate polynomial, preconditioned BEFORE
    # interval evaluation to retain cancellations.
    centered=[]
    for poly in E:
        coeff=[F(0)]*6
        for exponents,c in poly:
            for j in range(4):c*=center[j]**exponents[j]
            coeff[exponents[4]]+=c
        centered.append(coeff)
    defect=F(0)
    for i in range(4):
        coeff=[sum(R[i][j]*centered[j][power] for j in range(4)) for power in range(6)]
        # Translate around mid, then use the exact symmetric parameter radius.
        shifted=[sum(coeff[j]*comb(j,d)*mid**(j-d) for j in range(d,6)) for d in range(6)]
        bound=sum(abs(c)*((hi-lo)/2)**d for d,c in enumerate(shifted))
        defect=max(defect,bound)
    maximum_lambda=max(maximum_lambda,lam)
    maximum_defect=max(maximum_defect,defect/radius)
    assert lam<F(1,4), ('derivative contraction failed',k)
    assert defect<F(15,32)*radius, ('center self-map bound failed',k)
assert F(1,4)+F(15,32)==F(23,32)<1
print('PASS: all 60 literal rewards and four scaled-field polynomial identities.')
print('PASS: 512 closed parameter cells cover [0,1/3], radius = 1/512.')
print('PASS: every contraction norm < 1/4; every center defect/radius < 15/32.')
print('PASS: every state box lies inside (2/5,7/5)^4; q=t*z lies in (0,1)^4 for t>0.')
print('PASS: every preconditioner norm < 2 and all sixteen independent perturbation identities.')
print('PASS: relative passive tube radius 1/32768; perturbed contraction < 1/2 and image radius < 29/32.')
```

## Appendix F. Finite raw-coverage invariants

```python
"""Independent exact raw-coverage checks for the zero-participant-triple table.

This does not reconstruct or verify the new periodic producer. It checks
complete finite selectors and invariant necessary conditions of prior classes.
No numerical solver, Lean verification, or exhaustive UE classification.
"""
from itertools import combinations, permutations, product
import sympy as s

R = s.Rational
I = tuple(range(4))
U = frozenset(I)
f = lambda i: i ^ 1
rows = {
    (0,): (0, 3, -R(1,25), -R(69,100)),
    (1,): (2, 0, -R(69,100), -R(1,25)),
    (2,): (-R(69,100), -R(1,25), 0, 5),
    (3,): (-R(1,25), -R(69,100), 4, 0),
    (0,1): (1, 2, 1, -1),
    (0,2): (R(1,100), 1, R(1,100), -1),
    (0,3): (R(1,100), -1, 1, R(1,100)),
    (1,2): (-1, R(1,100), R(1,100), 1),
    (1,3): (1, R(1,100), -1, R(1,100)),
    (2,3): (1, -1, 3, 4),
    (0,1,2): (0, 0, 0, 1),
    (0,1,3): (0, 0, 1, 0),
    (0,2,3): (0, 1, 0, 0),
    (1,2,3): (1, 0, 0, 0),
    (0,1,2,3): (0, 0, 0, 0),
}
Z = {(i, frozenset(S)): s.Rational(row[i])
     for S, row in rows.items() for i in I}


def subsets(S, empty=False):
    return [frozenset(B) for k in range(0 if empty else 1, len(S)+1)
            for B in combinations(sorted(S), k)]


def d(i, B):
    return Z[i, B | {i}]-Z[i, B] if B else s.S.Zero


G = s.Matrix(4, 4, lambda i, j: 0 if i == j else Z[i, frozenset((j,))])
J = s.Matrix(4, 4, lambda i, j: 0 if i == j else Z[i, frozenset((i,j))])
assert len(Z) == 60
assert all(Z[i,S] == 0 for S in subsets(U) if len(S) == 3 for i in S)
assert all(Z[i,S] >= 0 for S in subsets(U) for i in S)
assert all(J[i,j] > 0 for i in I for j in I if i != j)
assert G.det() > 0 and min(G.inv()) > 0
assert all(G.extract(S,S).det() != 0 for S in combinations(I,3))
assert all(min(G.extract(S,S).inv()) < 0 for S in combinations(I,3))
assert all(G[i,f(i)] > 0 and all(G[i,j] < 0 for j in U-{i,f(i)}) for i in I)
assert all(sorted(-G[i,j] for j in U-{i,f(i)}) == [R(1,25),R(69,100)] for i in I)
print('PASS literal table, all twelve zero triple premiums, positive J,')
print('     inverse-positive matching and every proper triple inverse exclusion.')

# Exact all-role necessary tests. Positive recipient scaling preserves
# signs and the within-row comparisons used here.
role_count = old_rejected = tube_rejected = 0
for p in permutations(I):
    matching = all(G[p[i],p[f(i)]] > 0 and
                   all(G[p[i],p[j]] < 0 for j in U-{i,f(i)}) for i in I)
    if not matching:
        continue
    role_count += 1
    crossing = [frozenset((p[i],p[j])) for i,j in ((0,2),(0,3),(1,2),(1,3))]
    assert all(min(Z[k,B] for k in U-B) == -1 for B in crossing)
    old_rejected += 1
    # Repeated-pair Section4 M0: A=03 and B=12. One A owner sees
    # passive B=-1, below either crossing singleton (>=-.69).
    A, B = frozenset((p[0],p[3])), frozenset((p[1],p[2]))
    assert any(Z[i,B] < min(G[i,j] for j in B) for i in A)
    tube_rejected += 1
assert role_count == old_rejected == tube_rejected == 8
print('PASS all 24 roles: old four-crossing polyhedron and full repeated-pair')
print('     fixed-tube criterion fail; every positive row scaling is covered.')

# Every pair is a premium trap. No common owner belongs to all traps;
# no marked-block participant cap survives its earliest marked pair;
# no supportwise nonnegative upper average works even on one pair.
pairs = list(combinations(I,2))
assert all(all(J[i,j] > 0 for i,j in ((a,b),(b,a))) for a,b in pairs)
assert all(any(i not in B for B in map(frozenset,pairs)) for i in I)
crossing = [frozenset(B) for B in pairs if f(B[0]) != B[1]]
assert all(all(d(i,B-{i}) > 0 for i in B) for B in crossing)
print('PASS every premium-pair core/flat/marked/upper-average selector fails;')
print('     crossing pairs reject all protected and weighted leaver selectors.')

# Complete universal quiet-child refutation: one exact pure child
# equilibrium with zero joint Never and a strictly profitable outside join.
quiet_witnesses = []
for C in subsets(U):
    if C == U:
        continue
    found = []
    for E in subsets(C):
        member_ok = all((1+Z[i,E] >= 0 if len(E) == 1 else d(i,E-{i}) >= 0)
                        for i in E)
        outsider_ok = all(d(i,E) <= 0 for i in C-E)
        if member_ok and outsider_ok:
            found.extend((E,k) for k in U-C if d(k,E) > 0)
    assert found
    quiet_witnesses.append((C,*found[0]))
assert len(quiet_witnesses) == 14
print('PASS all 14 proper child sets: zero child debt/Never, positive outside debt.')

# Punishment values are exactly one: immediate Quit guarantees at least
# one, while all-Never opponents cap every possible response at one.
q = s.symbols('q0:4')
g = []
for i in I:
    g.append(s.expand(sum(s.prod(q[j] if j in B else 1-q[j] for j in U-{i})*d(i,B)
                          for B in subsets(U-{i}, empty=True))))
mu = {B: s.prod(q[j] if j in B else 1-q[j] for j in I) for B in subsets(U,True)}
negative = -R(1,4)*sum(mu[B] for B in subsets(U) if len(B)==1)
negative -= sum(mu[B] for B in subsets(U) if len(B)==3)
assert s.expand(sum((1-q[i])*g[i] for i in I)-negative) == 0


def endpoints_at(v):
    gv = [z.subs(dict(zip(q,v))) for z in g]
    return all((gv[i] <= 0 if v[i] == 0 else gv[i] >= 0 if v[i] == 1 else gv[i] == 0)
               for i in I)


assert not any(endpoints_at(v) for v in product((0,1), repeat=4) if 1 in v)
assert all(d(i,frozenset((j,))) != 0 for i in I for j in U-{i})
assert all(d(i,B) != 0 for B in subsets(U) if len(B)==2 for i in U-B)
sure_candidates = []
for C in combinations(I,3):
    for h in C:
        a,b = sorted(set(C)-{h})
        da = d(a,frozenset((h,)))
        db = d(b,frozenset((h,)))
        ca = d(a,frozenset((h,b)))
        cb = d(b,frozenset((h,a)))
        if db == cb or da == ca:
            assert db != 0 if db == cb else da != 0
            continue
        qa,qb = db/(db-cb),da/(da-ca)
        if 0 < qa < 1 and 0 < qb < 1:
            v = [s.S.Zero]*4
            v[h],v[a],v[b] = s.S.One,qa,qb
            gh = g[h].subs(dict(zip(q,v)))
            assert gh == -R(27,68)
            sure_candidates.append((C,h))
assert sure_candidates == [((0,1,2),1),((0,2,3),2)]
print('PASS punishment=1 and all sure-root supports, including both proper candidates.')

# A one-date independent row, then Never, lies in every finite-calendar
# payoff domain. Every nonempty coalition has probability 1/16.
# All four own-surpluses are positive: no choice of a nonempty subset,
# probability weights, strict margin, or nonconcentration cap can certify
# the universal payoff exclusions PD, WE_J, or GE.
one_date = [sum(1+Z[i,B] for B in subsets(U))/16 for i in I]
assert one_date == [R(1929,1600),R(1929,1600),R(2329,1600),R(2329,1600)]
assert min(one_date) > 1
print('PASS all finite-calendar payoff-exclusion selectors: one actual date')
print('     has payoff (1929,1929,2329,2329)/1600, strictly above own levels.')

# Cone-cap obstruction: positive contacts force a crossing schedule.
# Favorite J_i,f exceeds c_i for every owner, in every such partition.
for m in ((1,0,3,2),(2,3,0,1),(3,2,1,0)):
    c = [d(i,frozenset((m[i],))) for i in I]
    if min(c) <= 0:
        continue
    assert all(0 < c[i] < J[i,f(i)] for i in I)
    # Required R_{f(i),m(i)}<1 would give both opposite strict ratios.
    for i in I:
        j = m[f(i)]
        assert f(j) == m[i] and m[j] == f(i)
print('PASS all pair partitions and all cone weights: opposite ratio demands contradict.')

# Compensation ray: start with F=max(0,-d), increase favorite Gamma/J by t,
# and replace every passive entry with positive pair contact by -t.
t = s.Symbol('t', nonnegative=True)
for B in crossing:
    assert sorted(d(i,B) for i in U-B) == [-1,1]
    vals = {i: (1 if d(i,B)<0 else -t) for i in U-B}
    assert any(x == -t for x in vals.values())
for i in I:
    assert J[i,f(i)] >= 1
print('PASS compensation ray: each crossing pair has a passive -t<=0 for every t>=0;')
print('     old four-crossing and positive two-scale passive requirements always fail.')
print('No claim about unspecified local neighborhoods or arbitrary supplied certificates.')
```
