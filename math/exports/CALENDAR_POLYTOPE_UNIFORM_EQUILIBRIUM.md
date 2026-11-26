# Finite calendar polytopes fund positive passive rewards

## 1. Exact statement and conjecture-facing change

Let I be a finite set with n>=3 players. For each nonempty quitting coalition
A subset I and each recipient i, let r_i(A) be a finite real reward. Before
absorption the reward is zero; after absorption the coalition reward persists.
Each player privately chooses Continue or Quit on the unique live history.
Set s_i=r_i({i}) and assume s_i>=0. Define the native rewards
Z_i(A)=r_i(A)-s_i, so Z_i({i})=0. Native live and Never rewards are zero.

Choose distinct unmarked owners a,b, a nonempty marked set C=I minus{a,b},
an ordered partition B_1,...,B_k of C, and strictly positive real weights
lambda_i for i in C. Require the following finite raw participant caps:

    sum_(i in A intersect B_j) lambda_i Z_i(A) <= 0
    whenever B_j is the first block meeting A.                    (1)

Define Gamma_ij=Z_i({j}) and J_ij=Z_i({i,j}) for i!=j, with zero diagonals.
Put

    c_a=J_ab-Gamma_ab>0,       c_b=J_ba-Gamma_ba<0,
    b_ca=-Gamma_ca>=0,        b_cb=-Gamma_cb>=0,
    K_c=Z_c({a,b}),           c in C.                              (2)

The last raw condition is a finite polytope calculation. A deterministic
calendar is an ordered partition of any subset of I; remaining owners Never.
Record its prescribed native payoffs u_a,u_b and its counterfactual payoffs
m_a,m_b, where m_i is obtained by forcing just i Never while keeping every
other owner's date. A calendar with no finite owner pays zero. Let P be the
convex hull of these finitely many four-coordinate vectors and let

    R_Z={(x,y):(x,y,x,y) belongs to P},
    T_c=inf_( (x,y) in R_Z, x>0, y<0 )
              [b_ca*c_a/x + b_cb*(-c_b)/(-y)].                    (3)

An empty infimum is +infinity. Require K_c<=T_c for every c in C. The
quantities in (1)--(3) are computed from the finite reward table. They do not
include a strategy, continuation, Nash root, periodic word, minimum, or
punishment as an input. Ordered partitions are finite choices; their positive
weights satisfy ordinary linear inequalities. The polytope and its diagonal
slice are finite raw data, and (3) is a finite-dimensional semialgebraic test.

**Theorem.** The infimum A_Z of total native terminal deviation debt over
independent prescribed stopping laws that absorb surely is zero. The original
game consequently has one fixed uniform-equilibrium payoff, against every
complete unilateral behavioral replacement. The payoff target is fixed before
the accuracy; the prescribed profile and horizon threshold may depend on the
accuracy. The theorem includes weak singleton magnitudes and weak funding
inequalities exactly as stated.

The new producer uses correlations between two actual payoff coordinates and
their own-Never responses. It closes a raw class with an unbounded positive
passive reward parameter for which the previous separate passive-extrema
funding test fails under every labeling and every positive-weight block choice.
Section8 supplies the complete sixty-coordinate family and Section9 audits
other relevant selectors, including their full finite choices. Comparisons
with unspecified-threshold asymptotic theorems are explicitly at family level.
The full Fin4 conjecture remains open. This is ordinary mathematics, not a
new Lean-checked theorem.

## 2. Complete laws, root maps, and semantic debt

A complete prescribed strategy is a probability law on the finite dates and
Never, independently sampled by each player. Its conditional hazards give a
behavioral strategy. Conversely, before absorption the only live history is
that everyone Continued, so every unilateral behavioral replacement has a
complete first-Quit law. Against fixed opponents its payoff is a mixture of
pure finite-deadline and literal Never payoffs. Their supremum B_i is therefore
the unrestricted behavioral best-response value. Write U_i for prescribed
terminal payoff, N_i for original Never mass, nu=product_i N_i, d_i=B_i-U_i,
and D=sum_i d_i. In particular d_i>=0. No public correlating device is used.

For one product root with independent Quit probabilities q_i, define

    h(q)=product_i(1-q_i),       H_i(q)=product_(j!=i)(1-q_j),
    P_i(q)=sum_(A nonempty subset I minus{i}) Pr_(q_-i)(A) Z_i(A),
    Q_i(q)=sum_(A subset I minus{i}) Pr_(q_-i)(A) Z_i(A union{i}),
    E_i(q)=q_i Q_i(q)+(1-q_i)P_i(q).

At continuation u, Quit pays Q_i and Continue pays P_i+H_i*u_i.
A root Nash uses only maximizing actions. A root is proper if every q_i<1;
it may have zero coordinates. A nonzero root has positive absorption
probability. Finite mixed Nash existence supplies at least one root for every
u; the root correspondence has closed graph in the compact cube [0,1]^I.

The prescribed and full-cap prefix maps are exactly

    u'_i=h*u_i+E_i,
    b'_i=max(Q_i,P_i+H_i*b_i).                                  (4)

They preserve b>=u. When b=u and the root is Nash, b'=u'. Each map is
coordinatewise 1-Lipschitz in its terminal annotation. Hence any finite word
has the same Lipschitz bound, independent of its length. Comparing two
terminal payoff/cap vectors changes total debt by at most the sum of their
coordinatewise payoff and cap differences. This accounts for every deadline
and literal Never, not only one-step deviations.

A virtual finite word starts at (z,z) and applies (4). The terminal vector z
need not be the payoff of an actual game tail. It is removed at the end by
this length-independent comparison, or the word is applied to an actual
semantic point. Words are generated by successive prefixes; their physical
dates are read in the reverse order. No individual root is required to be
Nash unless the proof explicitly chooses it so.

If all rewards, the initial seed and a comparison vector v have absolute
values at most M, and the word has joint survival p, convexity gives

    ||u-v||_infinity <= ||z-v||_infinity+2M(1-p).                 (5)

All payoff, cap, and counterfactual annotations stay bounded. All finite
prefix maps are continuous, including their action on closures of actual
payoff/cap/Never data.

## 3. The finite calendar invariant and its diagonal identification

For clarity, P always denotes the four-coordinate projection in Section1;
other prescribed coordinates remain in the semantic state, not in P. There
are finitely many calendars because every owner appears at most once. Four
players have150 calendars, including AllNever.

For a pure attempted first coalition A, its map on an observed row i in{a,b}
is

    u_i -> Z_i(A) if A is nonempty, otherwise u_i;
    m_i -> Z_i(A minus{i}) if A minus{i} is nonempty, otherwise m_i. (6)

This sends every calendar vector to another calendar vector. Prepend A and
remove each member's old occurrence from the calendar. For the counterfactual
forcing i Never, remove i from both the new coalition and its old occurrence.
The construction works simultaneously for both observed owners, including
A={i}; no counterfactual deleting two owners is needed.

An arbitrary product prefix is the common convex mixture of (6) over A. Its
exact annotation map is

    u'_i=h*u_i+E_i,       m'_i=P_i+H_i*m_i.                       (7)

Thus P is invariant under every product prefix, Nash or otherwise. These maps
are sup-norm nonexpansive. For epsilon>=0, the closed sup-norm enlargement
P_epsilon is also invariant: compare a point to one in P and apply the same
prefix. This is a statement about the whole polytope, not about any isolated
supporting halfspace.

For actual independent laws, sample the private stopping-time vector once
and use it for every observed counterfactual. Compress its finite dates into
ordered tie blocks. Its annotated vector is a calendar vertex; averaging
shows that every actual annotation belongs to P. This also holds in the
compact semantic closure. P is a correlated outer relaxation; its points are
not asserted to be independently realizable or equilibria.

For a virtual word start b=u=z and m_i=z_i. The cap dominates m_i throughout.
Let n_i be owner i's survival through the word and p its joint survival.
Decomposing the prescribed own law into its finite deadlines and its terminal
Continue atom gives

    u_i <= (1-n_i)b_i+n_i*m_i,
    b_i-u_i >= n_i(b_i-m_i) >= p(b_i-m_i)>=0.                    (8)

This is continuous in the retained annotations and p, so it passes to every
bounded-survival closure. At b=u and p>0 it forces m_i=b_i=u_i. For actual
profiles the same argument with literal Never gives

    B_i>=m_i,        B_i-U_i>=N_i(B_i-m_i).                       (9)

It also passes to the actual closure. Thus zero debt and N_i>0 identify the
actual diagonal. Neither (8) nor (9) asserts equality at zero survival.

## 4. A restricted marked-root invariant from the raw table

First assume all b_ca,b_cb>0 and all K_c<T_c. There is epsilon>0 such that
for every diagonal point (x,y,x,y) in P_epsilon with x>0,y<0,

    K_c <= b_ca*c_a/x+b_cb*(-c_b)/(-y),  c in C.                 (10)

Otherwise take epsilon decreasing to zero and violating points, using one
fixed c along a subsequence. They stay bounded. A subsequential limit belongs
to the exact diagonal slice. Positive numerators force the reciprocal sum
to diverge on either relevant zero axis, so the limit has x>0,y<0. Continuity
then contradicts K_c<T_c. This includes T_c=+infinity.

We prove the following property for this fixed C,P,epsilon:

    If min_C u<=0 and (u_a,u_b,u_a,u_b) belongs to P_epsilon,
    every proper root Nash at u has min_C u'<=0.                 (NI)

If a marked owner is active, let B_j be the first active marked block.
Independence and (1) imply

    sum_(i in B_j) lambda_i*q_i*Q_i
      = E_q[sum_(i in A intersect B_j)lambda_i*Z_i(A)] <=0.

Earlier blocks have zero hazards, so each nonempty summand meets the first
relevant block. At least one active member of B_j has Q_i<=0, and its
prescribed Nash output equals Q_i. This proves (NI) in that case.

Otherwise only a,b may quit. With neither active the marked vector is
unchanged. With one active, each marked stopping term is nonpositive by (2),
so a previously nonpositive marked coordinate remains nonpositive. With both
active at a proper root, both mix. Set Y_a=q_a/(1-q_a),Y_b=q_b/(1-q_b).
The two exact mixing equations give

    u_a=c_a*Y_b>0,         u_b=c_b*Y_a<0.                        (11)

For each c in C its stopping contribution divided by h is

    E_c/h=-b_ca*Y_a-b_cb*Y_b+K_c*Y_a*Y_b <=0,                  (12)

by (10)--(11). Hence u'_c=h*u_c+E_c preserves every nonpositive marked
coordinate. This proves (NI) for all supports, including weak participant
caps. No root selector has been assumed.

## 5. Complete local escape with a strict calendar radius

The next lemma supplies the strategic words, including every recursive
stall. It uses (NI) only on diagonal observed annotations in P_epsilon.

**Local lemma.** Let v>=0, min_C v=0, and suppose AllContinue is the unique
whole-game root Nash at v. Assume

    dist_infinity((v_a,v_b,v_a,v_b),P)<epsilon.                  (13)

Given a hazard bound d>0 and total absorption budget eta>0, there are finite
words W_k supported on S={i:v_i=0}, with all hazards<=d, survival
p_k in[1-eta,1-c] for some c>0, full-cap debt tending to zero from (v,v), and
limsup_k min_C U(W_k)<=0. Positive coordinates outside S stay positive.
The same C,P,epsilon are retained at every smaller-face induction.

We may shrink eta to lie in(0,1), to protect positive outsiders using (5),
and to satisfy any further requested small absorption budget. Induct on|S|.
The nonempty set S meets C. Let Gamma_SS be the native singleton matrix on S.

### 5.1. Nonnegative kernel case

Suppose Gamma_SS*x=0 for x>=0 nonzero, normalized by sum x=1. Fix t>0 with
1-eta<exp(-t)<1 and repeat the supported root q=delta*x for floor(t/delta)
dates as delta decreases to zero. Its survival tends to exp(-t). For i in S,
passive and prescribed stopping contributions are O(delta^2), since their
linear term is Gamma_SS*x=0. Forced Quit values are O(delta). The total core
payoff is O(k*delta^2); the cap upper bound is O(delta+k*delta^2), by iterating
(4). Thus every core debt tends to zero, including rows not in supp(x).
Outsiders have zero hazard and positive Continue values protected by (5),
whereas their Quit values are O(delta). For sufficiently small delta their
caps equal prescribed payoffs exactly. Core payoffs tend to zero and S meets
C. The annotation stays within its starting strict radius by (7). The
survival interval and the hazard bound hold after discarding finitely many
terms. This proves the lemma in this case, including |S|=1 because Gamma_ii=0.

### 5.2. Strict signed separator and admissible seeds

If no nonnegative kernel exists, zero is outside the convex hull of the
columns of Gamma_SS. Its nearest point w gives the strict row separator

    w*Gamma_SS >= ||w||_2^2 * 1 >>0.                             (14)

Here w may have either sign. Uniformly for all sufficiently small supported
hazards q>=0, the singleton expansion E_S(q)=Gamma_SS*q+O((sum q)^2) gives

    w*E_S(q) >= gamma*sum q,   gamma>0.                          (15)

There are arbitrarily small seed vectors z_S with w*z_S>0 and
min_(C intersect S)z_i<0. Indeed, if no such vector existed, for every marked
zero index i the functional w would be nonpositive on the halfspace z_i<0.
That forces w to be supported on i alone. Two marked zero indices force w=0.
If there is just one, support on it contradicts the i-th strict inequality
in (14), since Gamma_ii=0. Keep z outside S equal to v. Choose z arbitrarily
close to v and initialize b=z,m=(z_a,z_b). By (13), its observed diagonal
has distance at most some r<epsilon from P. The value r can depend on z;
the strict inequality is all that is needed.

### 5.3. A bounded-prefix minimum

Choose delta<=d with delta<eta/(4n), with (15) valid, and small enough that
positive outsiders strictly Continue near(v,0). Uniqueness of the root at v
and compactness of the whole root graph give epsilon_0>0 such that every
root at ||u-v||_infinity<epsilon_0 is supported on S and has all hazards<delta.
Increase M to bound rewards and all nearby seeds. Fix

    c_0=min(eta/4,epsilon_0/(8M),1/4)>0                          (16)

BEFORE choosing the seed, then choose ||z-v||<epsilon_0/4 as well.

Let K_z be the compact closure of all outputs (u,b,m,p) of finite words from
(z,z,z_observed), supported on S, with hazards<=delta and survival p>=1-eta.
Include the empty word. Every such point satisfies dist((u_observed,m),P)<=r
by (7); this is inherited, not an artificial boundary constraint. A fixed
permitted finite prefix acts on K_z whenever the resulting survival has
strict slack above1-eta: apply it to defining approximants, use the strict
slack to keep them in the budget, and pass to the limit.

Minimize p on the nonempty closed subset

    F_z={ b=u, min_C u<=0, w*u_S>=p*w*z_S }.                     (17)

The empty word belongs to F_z. Let Y=(u,u,m,p) attain its minimum. Suppose
p>1-c_0. Equations (5) and (16) put u within epsilon_0 of v. All whole-game
roots at u are small, proper, supported on S. By (8), m=u_observed. The
annotation has distance<=r<epsilon, so (NI) applies. Any nonzero root
preserves cap equality, the marked cone, and the original weighted constraint
by (15). It has strict budget slack because

    h(q)*p >= (1-n*delta)*p >1-n*delta-c_0 >1-eta/2.

It would therefore lie in the SAME F_z with smaller survival, a contradiction.
AllContinue must be the unique root at u. In particular u>=0, since its
Quit payoff is zero and its Continue payoff is u_i. The signed constraint
w*u_S>=p*w*z_S>0 ensures u_S is not identically zero. Thus its zero set T
is a nonempty proper subset of S meeting C; every coordinate outside T is
positive.

### 5.4. Smaller faces retain the original carrier and weight

Apply the induction hypothesis at u with the SAME C,P,epsilon. It applies
because the observed diagonal is at distance<=r<epsilon. Request hazards
<=delta and choose eta'>0 so that p(1-eta')>1-eta. The resulting words V_k
have survival h_k in[1-eta',1-c'] for some c'>0, debt tending to zero, and
limsup min_C payoff<=0.

Apply these words to the unperturbed Y, whose terminal cap and payoff are
both u and whose terminal m is u_observed. Each endpoint lies in the original
K_z by strict-slack stability. Every added hazard is supported on T subset S
and bounded by delta, so the ORIGINAL signed row w satisfies

    w*U_S(V_k Y) >= h_k*w*u_S >= p*h_k*w*z_S.                    (18)

This follows by iterating (15), regardless of which separator was used inside
the smaller-face proof. A convergent subsequence has zero debt, nonpositive
marked minimum, and the original inequality in (17), but survival at most
p(1-c')<p. This contradicts the original minimum.

Temporary inner seeds may lie at a larger radius than r, still below epsilon.
There is no accumulation of those seed perturbations in K_z: their produced
words have just been reapplied to Y, so their endpoints recover the original
radius r. The same reasoning retains the original signed constraint, not a
new constraint imposed only inside the recursive proof.

Consequently the minimum of F_z is at most1-c_0. Approximate such a minimum
by finite defining words. Their debts tend to zero and their marked minima
have limsup<=0, with survival eventually<=1-c_0/2. Now take seeds z->v and
choose these approximants diagonally. Apply the same words to(v,v,v_observed).
The single terminal seam is nonexpansive in payoff, cap and m, independently
of word length. Total debt changes by at most2*sum_i|z_i-v_i|. Survival does
not change. This proves the local lemma with a positive loss independent of
the vanishing seed. No seed is asserted to be an actual strategy.

## 6. Actual source, original Never, and the global contradiction

Let H be the compact closure of actual bounded data (U,B,N,m_a,m_b) over all
independent complete stopping profiles. It retains original Never masses,
not conditional tail masses. Prefixes act continuously by (4),(7) and
N'_i=(1-q_i)N_i; hence nu'=h(q)*nu. The observed annotation lies in P and
(9) holds throughout H.

A simple absorption repair relates H to A_Z. For an actual profile choose
an owner with smallest Never mass, and move that Never atom to any one finite
date. The modified profile absorbs surely. Coupling changes every prescribed
payoff by at most2M*N_min. It changes each other owner's complete cap by at
most2M*N_min, uniformly over all deviations; the changed owner's cap is
unchanged because its opponents are unchanged. Therefore

    A_Z <= D+(4n-2)M*min_i N_i
        <= D+(4n-2)M*nu^(1/n).                                  (19)

Continuity extends (19) to H. Under the temporary assumption A_Z>0, every
zero-debt point of H has all N_i>0.

Minimize original nu on

    E_C={ X in H : B=U and min_C U<=0 }.

This compact nonempty set contains AllNever, with U=B=m=0 and N_i=1.
Its minimum nu_* is strictly positive by (19). At a minimizer, (9) identifies
m=U_observed, so its diagonal annotation lies exactly in P.

Choose any root Nash at U. If some owner is sure, the prefixed point has
zero debt and nu=0, contradicting (19), with no need for a marked condition.
Any nonzero proper root preserves the marked cone by (NI) and cap equality,
while strictly decreasing original nu, another contradiction. Thus the only
root is AllContinue. It follows that U>=0 and min_C U=0.

Apply the local lemma to v=U; its radius is zero<epsilon. Prefix its finite
words to the semantic minimizer. Each fixed word lies in H by applying it
to actual approximants first. The resulting sequence has debt tending to
zero, limsup marked minimum<=0, and original nu at most(1-c)nu_* for a fixed
c>0. Compactness yields a point in E_C contradicting the defining minimum.
This proves A_Z=0. Neither a minimum of a conditional tail nor any transfer
of a fixed nonvanishing payoff error is used.

## 7. Weak raw inequalities and the original uniform payoff

For weak K_c<=T_c and weak b_ca,b_cb>=0, perturb only marked recipient rows:
lower Gamma_ca and Gamma_cb by delta>0 and lower Z_c({a,b}) by delta.
These are passive coordinates for c. They change no participant cap (1),
no observed row a,b, and no coefficient c_a,c_b. In particular the projected
polytope P and R_Z are exactly unchanged. The new singleton magnitudes are
strictly positive. Their thresholds satisfy T_c(delta)>=T_c, so

    K_c-delta < T_c(delta).

Sections4--6 apply to every perturbed table. A sup-norm reward perturbation
of size delta changes any prescribed payoff and any full cap by at most
delta, hence total debt by at most2n*delta, uniformly over all complete laws.
Absorption is a property of the laws, so A_Z=0 passes to the original table.
This proves weak boundaries without assuming that a zero numerator provides
reciprocal divergence at an axis.

For the original rewards r_i=Z_i+s_i with s_i>=0, take any prescribed native
profile that absorbs surely. Its original payoff is U_i+s_i. Every finite
Quit deadline absorbs surely and gains exactly s_i; the Never endpoint gains
at most s_i. Thus the original complete cap is at most B_i+s_i and its debt
is at most native debt. Native absorbing profiles with D->0 give original
terminal epsilon-Nash profiles for every epsilon>0 against all behavioral
replacements. The fixed-target semantic theorem then supplies one original
uniform-equilibrium payoff. Negative own offsets are not included in this
adapter.

Every strategic object has been produced: raw calendar enumeration produces
P, strict funding produces a radius, finite Nash existence produces roots,
the singleton matrix produces a kernel direction or signed separator, the
zero diagonal produces the signed seeds, bounded prefix minima and finite
zero-face induction produce words, and the actual compact minimum plus (19)
consume them. No strategic witness remains assumed.

## 8. A complete unbounded sixty-coordinate calibration

Let I={0,1,2,3}, C={0,1}, ordered singleton blocks0 then1, and a=2,b=3.
For every real R>=3, the following table specifies all sixty native entries,
with recipients in order0,1,2,3. Put kappa=12/5.

    0:   (0,3,-1,-1)             1:   (3,0,-1,-1)
    2:   (-1,-1,0,3)             3:   (-1,-1,3,0)
    01:  (-1,-1,R,R)             02:  (-2,-1,-1/10,-1)
    03:  (-1/10,-1,-1,-2)        12:  (-1,-1/10,-2,-1)
    13:  (-1,-2,-1,-1/10)        23:  (12/5,12/5,4,1)
    012: (-6,-41/10,-11/10,-1)
    013: (-41/10,-6,-1,-11/10)
    023: (-11/10,-1,9/10,-4)
    123: (-1,-11/10,-1,-21/10)
    0123:(-17/2,-17/2,-1/10,-31/10).                              (20)

Adding1 to every coordinate gives a concrete original table with all own
levels1; any other nonnegative own levels are also permitted by the theorem.
All participant caps (1) hold. The marked singleton magnitudes are all1,
and c_2=1,c_3=-2. The literal passive extrema are

    max(0,max_(A nonempty,2 notin A)Z_2(A))=R,
    max(0,max_(A nonempty,3 notin A)(-Z_3(A)))=1.                  (21)

Nevertheless, every one of the150 deterministic calendars satisfies

    40*u_2-21*u_3-147*m_3<=267,       m_3>=-1.                   (22)

The complete exact enumeration is in Section12. It proves (22) uniformly
already for R>=1: each calendar's functional is affine in R, its value at
R=1 is at most267, and its slope is nonpositive. The lower bound follows
also directly from all passive row3 rewards being at least-1. This is an
exact affine certificate, not a bounded numerical sample in R.

On the diagonal slice, write x=u_2>0 and s=-u_3 in(0,1]. Equations (22) give
40x+168s<=267. Therefore

    1/x+2/s >= 40/(267-168s)+2/s >=238/99>12/5.                   (23)

The second difference has numerator (1-s)(52866-39984s) and positive
denominator99s(267-168s). The strict margin is2/495. Thus (20) satisfies
the raw theorem for EVERY R>=3, although its positive passive extremum
diverges. No positive-gap or counterexample status is asserted for this
family: the theorem proves its absorbing approximate equilibria and UE.

The singleton joining matrix L=J-Gamma is

    [0,   -4,   -1,  9/10]
    [-4,   0, 9/10,  -1 ]
    [9/10,-1,    0,   1 ]
    [-1, 9/10,  -2,   0 ].                                     (24)

At zero continuation let Delta_i=Q_i-P_i. Literal expansion of (20) gives

    Delta_0=L_0 q-(kappa+1)q_2 q_3,
    Delta_1=L_1 q-(kappa+1)q_2 q_3,
    Delta_2=L_2 q-(R+1)q_0 q_1(1-q_3),
    Delta_3=L_3 q-(R+1)q_0 q_1(1-q_2).                          (25)

The Continue factors in the last two rows are essential: only the passive
pair01 coordinates were raised. Section12 checks every literal opponent
coalition, rather than taking (25) as an input. Every reciprocal sum
L_ij+L_ji is strictly negative; all extra terms in sum_i q_i Delta_i are
nonpositive. Thus q dot Delta(q)<0 whenever at least two owners are active,
contrary to root Nash. With just one active owner, its column of L contains
a positive entry, so some inactive owner strictly prefers Quit. Hence the
whole zero-continuation root game has unique AllContinue throughout the ray.

## 9. Complete finite comparisons and qualified asymptotic comparisons

These comparisons identify the new raw class relative to specific existing
producers. They do not claim that every conceivable supplied periodic word
fails, nor that individual finite tables violate unknown eventual thresholds.
All original-reward comparisons below use own levels1.

### 9.1. All passive-extrema roles and all weighted blocks

The separate-extrema criterion replaces (3) by

    K_c<=b_ca*c_a/R_a+b_cb*(-c_b)/H_b,

where R_a is the maximum nonnegative passive reward of a and H_b is the
maximum nonnegative negative passive reward of b. It permits the same
arbitrary ordered positive-weight marked blocks as (1).

For (20), any marked set meeting{2,3} fails (1) at coalition23: every
participant in its first intersecting marked block receives either4 or1,
so every positive-weight sum is strictly positive. With exactly two unmarked
owners this forces C={0,1}. Its one-block version and both ordered singleton
versions share the same per-owner funding inequalities. The opposite joining
signs then force the ordered unmarked roles(2,3). For both marked recipients,
the old threshold is2+1/R<=7/3<12/5. Thus the entire weighted-block extension
fails for every labeling and every R>=3, not merely the24 singleton-order
role permutations. The24-role enumeration is included as an additional check.

The unbounded nonpositive-anchor-block criterion is still stronger in its
passive sign demand: all marked recipients must be nonpositive on every
nonempty coalition wholly outside the marked set. It fails for every
nonempty marked set, every block ordering and every positive weight choice.
If the set meets23, use the preceding positive participant obstruction. If
it is contained in01, the disjoint coalition23 gives every marked recipient
12/5>0. This covers all149 ordered-subset/block choices in Fin4.

### 9.2. All fourteen quiet-child weight alternatives

For a proper nonempty child S and outsider o, any nonnegative capped-clock
weight vector lambda must satisfy, even at its singleton rows,

    sum_(i in S)lambda_i*(-Gamma_ij)>=-Gamma_oj,
    sum_(i in S)lambda_i*L_ij>=L_oj,       j in S.                 (26)

For the following(S,o,j), the second inequality has a positive right side
and all nonpositive left coefficients:

    (0,2,0),(1,3,1),(2,1,2),(3,0,3),
    (01,2,0),(02,1,2),(03,2,0),(12,3,1),(13,0,3),(23,1,2),
    (012,3,1),(013,2,0),(023,1,2).

For S=123 and o=0 add its future rows j=2,3 and twice its joining row j=3.
The resulting left coefficients in child order1,2,3 are(0,-1,-3), while
the right side is19/5>0. Thus every nonnegative weight vector fails in all
fourteen children. The table changes no entry of Gamma or L. The complete
full-clock LP, including its relaxed Never row, cannot pass these necessary
rows. This excludes all its choices, not just one stationary child.

The exact interfaces are `rawChild_future_delta`, `rawChild_future_base`,
`rawChild_joining_delta`, `rawChild_joining_base` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockOriginalCoalitionRows.lean`
and `nonempty_cappedClockParentRewardCertificate_iff` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockExactLPAlternative.lean`.

### 9.3. Entire sure-owner correspondences, including punishment tails

When a prescribed owner is fixed sure, the complementary players' complete
one-round Nash correspondences are

    owner0: (1,0,1,0);
    owner1: (0,1,t,1), 0<=t<=9/20;
    owner2: (0,1,1,0);
    owner3: (0,0,1,1).                                          (27)

Here the designated owner's own action need not be a best response; that is
the condition the extension would need to repair. To prove exhaustion, use
(25). With owner0 sure, row1 is strictly negative, forcing q1=0; row3 then
is strictly negative, forcing q3=0, and row2 is positive, forcing q2=1.
With owner1 sure, row0 forces q0=0. If q3<1, row2 forces q2=0 and row3 then
forces q3=1, a contradiction. Thus q3=1, row2 is indifferent, and row3's
optimality gives t=q2<=9/20. With owner2 sure, row0 is strictly negative,
so q0=0; row3 then forces q3=0, and row1 forces q1=1. With owner3 sure,
row1 forces q1=0; row2 forces q2=1 and row0 forces q0=0. In every case the
new R terms vanish before the remaining calculations.

The designated owner's native Quit-minus-Continue gaps on (27) are

    -1,  -1-(kappa+1/10)t,  -1,  -2.                            (28)

Another owner is sure in every member of every correspondence. Consequently
these strict losses persist under ANY later punishment continuation; no
survival event remains on which a tail can improve that owner's comparison.
This is stronger than failure of stationary repetition. It excludes the
full sure-owner punishment alternative on these fibers. Relevant interfaces
are in `UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`,
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
and `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.

### 9.4. The mixed pair/solo selector and other finite screens

For the period-two architecture solo0 followed by joint23, exact active
mixing and periodicity at (20) force positive odds Y2,Y3 and0<u<1 with

    Y2^2+(5u-3)Y2+u=0,
    -2Y3^2+(2u-3)Y3+u=0,
    kappa=1/Y2+1/Y3.                                             (29)

These identities follow by propagating the two active endpoints and the
solo0 zero-own endpoint through the two-date period. All coordinates queried
by those phases and their one-owner deviations are unchanged by R. The first
discriminant is25(u-9/25)(u-1), so u<=9/25. The second identity gives
Y3=u/(3-2u+2Y3)<=3/19. Hence the required funding is strictly greater than
19/3, contradicting kappa=12/5. Interchanging anchors0 and1 gives the same
exclusion. This concerns this entire architecture, not arbitrary phase words.

The positive weighted native terminal-floor test fails because the grand
vector in (20) is strictly negative. The weighted insertion test using
owners0 and1 has recipient coefficients(-1,-1,-21/10,-21/10), so no positive
weight can give a nonnegative lower bound there. Only owners2,3 have any positive native participant entry: both do at23,
and owner2 also does at023. Owners0,1 have none, so every premium trap must
be contained in23; neither singleton is a trap. Thus23 is the sole premium
trap. At the singleton coalition{0}, the two active recipients2,3 have
inserted participant premiums Z2(02)=-1/10 and Z3(03)=-2. Thus every
positive weighting on that trap fails its required global inserted floor. A product-low-premium
condition fails directly because both participants at23 have positive native
Quit payoffs. These are the displayed necessary finite tests of
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`,
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`
and `UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`.

For matrix comparisons, Gamma has positive favorite entries3 on01,23 and
crossing entries-1. Its inverse is

    (1/15)*[2,7,3,3; 7,2,3,3; 3,3,2,7; 3,3,7,2],

and det Gamma=45. Every reciprocal product is positive, so no opposite-sign
Hamiltonian or singleton escort role exists. A negative crossing2-principal
block is not Q (offset(-1,-1) has no complementary solution) and has no
nonzero homogeneous complementary vector. Thus the full projective Q-bar
criterion fails. Every proper3-principal block has a row with both other
entries negative, excluding its positive-image and positive-inverse premise.
The relevant matrix notions are in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`; escort
construction is in `UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`.

The common favorite-participant scalar class requires identical normalized
favorite participant values. Identical singleton magnitudes force identical
row scales, while the four favorite participant values here are(-1,-1,4,1).
Every pair has at least one negative L entry, preventing classes requiring
both pair joining increments positive; the favorite23 product is-2, preventing
the paired both-funded or both-below variants. No triple has all six positive
joining entries. The old four-singleton favorite participant bound, in
original units, is at most(5+sqrt(5))/2<4, whereas owner2's original23 reward
is5. The monotone passive-cap chamber fixes opposite participant values-1
in native units and adjacent follower values2 in original units; the literal
entries(4,1) and9/10 here fail those identities. These are raw admission
comparisons; a theorem restricted to a full-zero least source is not treated
as a direct UE theorem for this table, whose equilibrium conclusion is the
output of the present proof.

### 9.5. All24 passive-pole roles and the asymptotic boundary

Section12's second exact program reconstructs (20), enumerates all24 role
permutations, and proves signs uniformly after R=3+t,t>=0 using polynomial
coefficient signs. Exactly seven roles pass the first two endpoint guards;
exactly one passes all eight:

    (old0,old1,old2,old3)=(1,3,0,2), c=9/40,
    (a2,b2,l0,l1,f0,f1)
      =(-1,-5,-89/40,-53/40,3519/16000,-(90R+409)/400).           (30)

For original own levels1 its first two required negative passive poles are
r3(01)=R+1 and r0(23)=17/5; its third nonnegative-slope coordinate is r2(13)=0.
The ray is therefore not the fixed-background ray with two negative growing
poles required by that asymptotic producer. Passing (30) is preserved
honestly; no unspecified finite threshold is invented to exclude a point.

The signed passive-coalition asymptotic criterion prescribes one growing
passive pole for EVERY recipient, with signs determined by Gamma inverse.
Here the inverse is entrywise positive, forcing its pole signs negative;
only two positive passive coordinates grow in (20). The signed one-column
jackpot criterion requires its growing coalition to contain the selected
recipient, even in its thickened version. The positive-inverse participant
jackpot criterion likewise grows participant coordinates. In (20) every
participant coordinate is fixed, and relabeling cannot change passive into
participant status. Thus these fixed-background families do not supply the
present ray. This is a family-level comparison: it does NOT establish that
every fixed finite table lies outside every theorem with an unspecified
eventual threshold and an arbitrarily chosen background box.

## 10. Exact boundary tests and the limitation of the relaxation

A second table gives a sharp funding calculation and an attempted falsifier.
Start with (20), replace both passive row2,row3 coordinates at01 by-1, and
allow Z0(23)=M,Z1(23)=N. Replace their grand coordinates by-M-61/10 and
-N-61/10 respectively; all other coordinates stay fixed. The observed rows
are independent of M,N. Every deterministic calendar satisfies

    20*u2-41*u3<=63+62*(u2-m2)-3*(u3-m3),       m3>=-1.          (31)

On the diagonal, putting s=-u3 in(0,1] yields funding at least32/11. The
difference from32/11 has numerator2(1-s)(693-656s) and denominator
11s(63-41s). The bound is attained by this convex mixture, where calendar
tuples list relative stopping dates:

    weight1/4:   (0,0,0,0), observed(-1/10,-31/10,-1,-1);
    weight9/40:  (1,0,0,1), observed(-2,-1,-1,-1);
    weight21/40: (1,1,1,0), observed(3,0,3,-1).

Its average is(11/10,-1,11/10,-1). Thus the theorem covers all M,N<=32/11
in that family, including equality. This calculation alone is a constant
improvement; the independent unbounded family (20) supplies the qualitative
raw-class distinction.

The calendar relaxation is not a complete solution of Fin4. At M=N=4 the
full eight-coordinate hull recording all four own-Never payoffs contains
u=m=(0,0,4/5,-3/4). An exact mixture is

    (0,1,1,0):1525/5168;        (0,1,1,1):4049/65280;
    (0,1,2,2):406331/3720960;   (1,0,1,0):23/15504;
    (1,0,1,1):4801/72675;       (1,1,0,0):3/64;
    (1,1,1,0):31/80;           (2,0,1,1):75091/4651200;
    (2,2,0,1):1/64.

At that continuation, q=(0,0,3/11,4/9) is a proper whole-game root Nash with
survival40/99 and prescribed output(1/99,1/99,16/9,3/11). Its Continue
endpoints equal that output; its Quit endpoints are
(-232/495,-787/990,16/9,3/11). Thus all complete one-root caps equal the
prescribed outputs while both marked coordinates become positive. This
falsifies an EVERY-root marked-invariance claim on that larger relaxed
slice. It does not assert independent-law realizability of the mixture,
failure of every root selector, or failure of UE. The strict funding margin
in the theorem is doing real work.

## 11. Source correspondence and Lean handoff

The semantic input and output declarations have the following exact scopes.
`quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff` and
`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`
apply to any finite nonempty player type and any finite reward table. They
identify independent complete laws with behavioral terminal payoffs and their
full behavioral replacement caps. This is the probability and agency mode
used in Section2.

`exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean` supplies an exact mixed
root for every continuation and reward table. No genericity, matrix
nonsingularity or source-specific equilibrium hypothesis is required.

`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
`UniformEquilibrium/Quitting/Root/CapNashRootStack.lean` gives exact debt
scaling for a root Nash at the cap annotation. The proof here uses its
diagonal case b=u. The literal full-word behavioral cap is the scalar fold
in `quittingContinuationBestResponseValue_literalRootStack_eq_capFold`, and
`quittingFiniteRootWordCap_sub_le_opponentSurvival_mul_posPart` bounds terminal
cap differences by opponent survival times their positive part, both in
`UniformEquilibrium/Quitting/Root/CommonPrefixCapStability.lean`. Sections2--3
write the required exact formulas explicitly. No factor equal to word length
is introduced in the seed seam.

Finally,
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
requires terminal approximate Nash profiles for every positive error and
concludes existence of one fixed uniform-equilibrium payoff. Section7 supplies
exactly its hypothesis, allowing profiles to depend on accuracy while the
selected target does not. Every sufficiently long finite horizon and every
unilateral behavioral replacement are covered by this existing endpoint.

For formalization, first define deterministic calendars, their observed
own-Never vectors, and the finite convex hull. Prove the common pure-prefix
map and its product-mixture identity, then the continuous inequalities (8)
and (9). The key new lemma is the strict-radius version of finite-face
induction: retain the SAME C,P,epsilon, the original signed separator, total
survival budget, and all complete caps through every recursive stall. The
actual compact carrier must retain original N, with their positivity supplied
by (19). The funding test then produces (NI), and the passive-row perturbation
closes weak signs without moving the observed polytope. No desired strategy
or UE conclusion should appear as a raw certificate field.

The main proof is independent of degree, root regularity, matrix inversion,
stationary repetition, or a bound on word length. It proves a sufficient
finite raw-table class for every n>=3 with exactly two unmarked owners.
It does not show that arbitrary games satisfy that class, and its original
reward conclusion retains the nonnegative-own-level hypothesis.

## 12. Complete exact verification

The first program uses Python's standard library and exact fractions. Save
it as `calendar_polytope_check.py` and run `python calendar_polytope_check.py`.
It checks all150 calendars and all2400 pure-prefix maps on the stronger full
four-owner counterfactual record; both funding inequalities; the exact sharp
mixture and larger-slice falsifier; all sixty displayed family entries; the
literal joining equations; all24 singleton roles, the entire weighted-block
obstruction, and all fourteen quiet-child certificates. Uniform R statements
are affine coefficient checks, not parameter samples.

```python
"""Exact finite calendar checks. Run with standard-library Python.

Calendar mixtures are correlated relaxations, not independently realizable
profiles. The M=N4 example falsifies every-root invariance only.
"""

from fractions import Fraction as F
from itertools import combinations, permutations, product


I = range(4)
G = ((0, 3, -1, -1), (3, 0, -1, -1),
     (-1, -1, 0, 3), (-1, -1, 3, 0))
L = ((0, -4, -1, F(9, 10)), (-4, 0, F(9, 10), -1),
     (F(9, 10), -1, 0, 1), (-1, F(9, 10), -2, 0))


def multiply(values):
    result = F(1)
    for value in values:
        result *= value
    return result


def reward(coalition, owner, M=F(4), N=F(4)):
    if not coalition:
        return F(0)
    others = sorted(set(coalition) - {owner})
    if not others:
        passive = F(0)
    elif len(others) == 1:
        passive = F(G[owner][others[0]])
    elif others == [2, 3] and owner in (0, 1):
        passive = M if owner == 0 else N
    else:
        passive = F(-1)
    if owner not in coalition:
        return passive
    increment = sum((L[owner][j] for j in others), F(0))
    if 2 in others and 3 in others and owner in (0, 1):
        increment -= (M if owner == 0 else N) + 1
    return passive + increment


def normalize(times, never=4):
    levels = sorted(set(times) - {never})
    return tuple(4 if t == never else levels.index(t) for t in times)


CALENDARS = sorted({normalize(t) for t in product(range(5), repeat=4)})
assert len(CALENDARS) == 150
COALITIONS = [frozenset(i for i, bit in zip(I, bits) if bit)
              for bits in product((0, 1), repeat=4)]


def payoff(times, owner):
    first = min(times)
    if first == 4:
        return F(0)
    return reward({j for j in I if times[j] == first}, owner)


def calendar_vector(times):
    prescribed = tuple(payoff(times, i) for i in I)
    never_values = []
    for i in I:
        changed = list(times)
        changed[i] = 4
        never_values.append(payoff(changed, i))
    return prescribed + tuple(never_values)


def prefix_calendar(coalition, times):
    raw = tuple(0 if i in coalition else times[i] + 1
                if times[i] != 4 else 10 for i in I)
    return normalize(raw, never=10)


def pure_map(coalition, vector):
    prescribed = tuple(reward(coalition, i) if coalition else vector[i]
                       for i in I)
    never_values = tuple(reward(coalition - {i}, i)
                         if coalition - {i} else vector[4 + i] for i in I)
    return prescribed + never_values


def mixture(weighted_times):
    assert sum((weight for weight, _ in weighted_times), F(0)) == 1
    assert all(weight >= 0 for weight, _ in weighted_times)
    return tuple(sum((weight * calendar_vector(times)[j]
                      for weight, times in weighted_times), F(0))
                 for j in range(8))


for times in CALENDARS:
    vector = calendar_vector(times)
    for coalition in COALITIONS:
        after = prefix_calendar(coalition, times)
        assert after in CALENDARS
        assert calendar_vector(after) == pure_map(coalition, vector)
    x, y, v, w = (vector[j] for j in (2, 3, 6, 7))
    assert 20 * x - 41 * y <= 63 + 62 * (x - v) - 3 * (y - w)
    assert w >= -1

# The observed rows are independent of the two passive parameters by the
# reward formula: only owner0/owner1 branches access M or N. Check all sixty
# coordinates at the chosen M=N=4 point against the original formula too.
table = {coalition: tuple(reward(coalition, i) for i in I)
         for coalition in COALITIONS if coalition}
assert len(table) == 15
assert table[frozenset((2, 3))] == (4, 4, 4, 1)
assert table[frozenset(I)] == (F(-101, 10), F(-101, 10),
                              F(-1, 10), F(-31, 10))

sharp = mixture([(F(1, 4), (0, 0, 0, 0)),
                 (F(9, 40), (1, 0, 0, 1)),
                 (F(21, 40), (1, 1, 1, 0))])
assert tuple(sharp[j] for j in (2, 3, 6, 7)) == (
    F(11, 10), F(-1), F(11, 10), F(-1))
assert 1 / sharp[2] + 2 / (-sharp[3]) == F(32, 11)
# Polynomial numerator in the reciprocal comparison, ascending powers of s.
assert (2 * 693, -2 * (693 + 656), 2 * 656) == (1386, -2698, 1312)

fence = mixture([
    (F(1525, 5168), (0, 1, 1, 0)),
    (F(4049, 65280), (0, 1, 1, 1)),
    (F(406331, 3720960), (0, 1, 2, 2)),
    (F(23, 15504), (1, 0, 1, 0)),
    (F(4801, 72675), (1, 0, 1, 1)),
    (F(3, 64), (1, 1, 0, 0)),
    (F(31, 80), (1, 1, 1, 0)),
    (F(75091, 4651200), (2, 0, 1, 1)),
    (F(1, 64), (2, 2, 0, 1)),
])
u = (F(0), F(0), F(4, 5), F(-3, 4))
assert fence == u + u
q = (F(0), F(0), F(3, 11), F(4, 9))
survival = multiply(1 - qi for qi in q)
stopping = [F(0)] * 4
quit_values = [F(0)] * 4
never_values = [F(0)] * 4
for coalition in COALITIONS:
    mass = multiply(q[i] if i in coalition else 1 - q[i] for i in I)
    for i in I:
        if coalition:
            stopping[i] += mass * reward(coalition, i)
        never_values[i] += mass * (reward(coalition - {i}, i)
                                  if coalition - {i} else u[i])
for i in I:
    others = [j for j in I if j != i]
    for bits in product((0, 1), repeat=3):
        coalition = {j for j, bit in zip(others, bits) if bit}
        mass = multiply(q[j] if j in coalition else 1 - q[j] for j in others)
        quit_values[i] += mass * reward(coalition | {i}, i)
out = tuple(survival * u[i] + stopping[i] for i in I)
assert out == (F(1, 99), F(1, 99), F(16, 9), F(3, 11))
assert quit_values == [F(-232, 495), F(-787, 990), F(16, 9), F(3, 11)]
assert tuple(never_values) == out
assert tuple(max(quit_values[i], never_values[i]) for i in I) == out
assert 0 < survival < 1 and all(qi < 1 for qi in q)

print('PASS: all150 calendars and all2400 pure-prefix maps')
print('PASS: exact supporting inequality and sharp funding32/11')
print('PASS: rational all-four diagonal mixture at M=N4')
print('PASS: proper exact Nash root exits marked cone, output', out)
print('No independent-law realization or selected-root failure is asserted.')

# A separate qualitative calibration: raise only Z2(01)=Z3(01)=R>=3,
# retain the displayed two-parameter table with M=N=12/5. Its passive upper extremum is unbounded.
def raised_reward(coalition, owner, R):
    if set(coalition) == {0, 1} and owner in (2, 3):
        return R
    return reward(coalition, owner, F(12, 5), F(12, 5))


def raised_vector(times, R):
    def evaluate(changed, owner):
        first = min(changed)
        return F(0) if first == 4 else raised_reward(
            {j for j in I if changed[j] == first}, owner, R)
    prescribed = tuple(evaluate(times, i) for i in I)
    never_values = []
    for i in I:
        changed = list(times)
        changed[i] = 4
        never_values.append(evaluate(changed, i))
    return prescribed + tuple(never_values)


for times in CALENDARS:
    one, two = raised_vector(times, F(1)), raised_vector(times, F(2))
    def functional(v):
        return 40 * v[2] - 21 * v[3] - 147 * v[7]
    assert functional(one) <= 267
    assert functional(two) - functional(one) <= 0
    # The reward entries and therefore each calendar vector are affine in R.
    assert one[7] >= -1 and two[7] - one[7] >= 0

# Exact reciprocal lower bound: numerator factors (1-s)(52866-39984s).
assert (52866, -(52866 + 39984), 39984) == (52866, -92850, 39984)
assert F(238, 99) - F(12, 5) == F(2, 495) > 0
assert F(12, 5) > 2 + F(1, 3)

# Reconstruct the exact zero-tail joining field from all32 literal opponent
# coalitions. Multiaffinity in hazards and affinity in R make these coefficient
# checks an identity for all q and every R. The third-opponent Continue factor
# in the two changed passive-pair entries must not be omitted.
for R in (F(3), F(4)):
    for i in I:
        opponents = [j for j in I if j != i]
        for bits in product((0, 1), repeat=3):
            B = frozenset(j for j, bit in zip(opponents, bits) if bit)
            hazards = tuple(F(int(j in B)) for j in I)
            actual = raised_reward(B | {i}, i, R) - raised_reward(B, i, R)
            model = sum((L[i][j] * hazards[j] for j in I), F(0))
            if i in (0, 1):
                model -= (F(12, 5) + 1) * hazards[2] * hazards[3]
            else:
                remaining = 3 if i == 2 else 2
                model -= (R + 1) * hazards[0] * hazards[1] * (1 - hazards[remaining])
            assert actual == model, (R, i, B, actual, model)
assert all(L[i][j] + L[j][i] < 0 for i, j in combinations(I, 2))
assert all(any(L[i][j] > 0 for i in I) for j in I)

# The only viable ordered boxed roles have marked owners0,1 and ordered
# pair2,3: both rows2,3 have positive participating reward at coalition23.
# A first marked owner therefore belongs to01. A second marked owner in23
# would meet its positive pair partner in the remaining two-owner set.
boxed_roles = []
for first, second, up, down in permutations(I):
    if any(raised_reward(A, first, F(3)) > 0 for A in COALITIONS if first in A):
        continue
    if any(raised_reward(frozenset(B) | {second}, second, F(3)) > 0
           for size in (1, 2) for B in combinations((up, down), size)):
        continue
    if not (L[up][down] > 0 and L[down][up] < 0):
        continue
    boxed_roles.append((first, second, up, down))
assert boxed_roles == [(0, 1, 2, 3), (1, 0, 2, 3)]

# All14 existing quiet-child singleton Farkas certificates are unchanged.
quiet_count = 0
for child in (A for A in COALITIONS if 0 < len(A) < 4):
    if child == {1, 2, 3}:
        outsider = 0
        terms = [('F', 2, 1), ('F', 3, 1), ('J', 3, 2)]
    else:
        j, outsider = next((j, o) for j in child for o in I if o not in child
                           and L[o][j] > 0 and max(L[i][j] for i in child) <= 0)
        terms = [('J', j, 1)]
    coefficients = [sum(weight * (-G[i][j] if kind == 'F' else L[i][j])
                        for kind, j, weight in terms) for i in child]
    rhs = sum(weight * (-G[outsider][j] if kind == 'F' else L[outsider][j])
              for kind, j, weight in terms)
    assert max(coefficients) <= 0 < rhs
    quiet_count += 1
assert quiet_count == 14
print('PASS: uniform raised-passive R>=1 calendar bound and funding238/99')
print('PASS: literal full-table joining fields, with both necessary Continue factors')
print('PASS: unbounded R>=3 family fails every old boxed role and14 quiet screens')
print('These checks certify only the explicitly described finite comparisons.')

# The complete block extension of the passive-extrema test is also excluded.
# Exactly two unmarked owners means |C|=2. Positive participant rewards at23
# prohibit C intersect23 for EVERY ordered block/positive weight choice.
# For C=01, its one-block version and both singleton orders have identical
# per-owner funding inequalities, failing at every R>=3.
block_choices = 0
for marked in (A for A in COALITIONS if A):
    owners = sorted(marked)
    for count in range(1, len(owners) + 1):
        for labels in product(range(count), repeat=len(owners)):
            if set(labels) != set(range(count)):
                continue
            blocks = [set(i for i, label in zip(owners, labels) if label == k)
                      for k in range(count)]
            if marked & {2, 3}:
                first = next(B for B in blocks if B & {2, 3})
                assert all(raised_reward({2, 3}, i, F(3)) > 0
                           for i in first & {2, 3})
            else:
                assert marked <= {0, 1}
                assert all(raised_reward({2, 3}, i, F(3)) > 0 for i in marked)
            block_choices += 1
assert block_choices == 149
assert F(12, 5) > 2 + F(1, 3)
print('PASS: all149 unbounded marked-block choices and full extrema block extension')

# Verify the printed full60 family literally at two R values. Each coordinate
# is affine in R, so this proves equality of the displayed family and producer.
for R in (F(3), F(4)):
    literal = {
        (0,): (0,3,-1,-1), (1,): (3,0,-1,-1),
        (2,): (-1,-1,0,3), (3,): (-1,-1,3,0),
        (0,1): (-1,-1,R,R), (0,2): (-2,-1,F(-1,10),-1),
        (0,3): (F(-1,10),-1,-1,-2),
        (1,2): (-1,F(-1,10),-2,-1),
        (1,3): (-1,-2,-1,F(-1,10)),
        (2,3): (F(12,5),F(12,5),4,1),
        (0,1,2): (-6,F(-41,10),F(-11,10),-1),
        (0,1,3): (F(-41,10),-6,-1,F(-11,10)),
        (0,2,3): (F(-11,10),-1,F(9,10),-4),
        (1,2,3): (-1,F(-11,10),-1,F(-21,10)),
        (0,1,2,3): (F(-17,2),F(-17,2),F(-1,10),F(-31,10))}
    assert len(literal) == 15
    for A, row in literal.items():
        assert tuple(raised_reward(A,i,R) for i in I) == row
print('PASS: all60 displayed reward coordinates, uniformly in R')

```

The second program requires SymPy. Save it as `calendar_poles.py` and run
`python calendar_poles.py`. It certifies all24 passive-pole roles uniformly
for R>=3 and retains the one passing endpoint role without assigning an
unknown asymptotic threshold.

```python
"""Exact uniform all-role pole census. Run with Python and SymPy.

Passing endpoint guards alone is not membership in an asymptotic ray.
"""
from itertools import permutations
import sympy as s

R = s.symbols('R', real=True)
t = s.symbols('t', nonnegative=True)
G = s.Matrix([[0, 3, -1, -1], [3, 0, -1, -1],
              [-1, -1, 0, 3], [-1, -1, 3, 0]])
L = s.Matrix([[0, -4, -1, s.Rational(9, 10)],
              [-4, 0, s.Rational(9, 10), -1],
              [s.Rational(9, 10), -1, 0, 1],
              [-1, s.Rational(9, 10), -2, 0]])
kappa = s.Rational(12, 5)


def native(i, coalition):
    coalition = set(coalition)
    if not coalition:
        return s.Integer(0)
    if coalition == {0, 1} and i in (2, 3):
        return R
    others = sorted(coalition - {i})
    if not others:
        passive = s.Integer(0)
    elif len(others) == 1:
        passive = G[i, others[0]]
    elif i in (0, 1) and others == [2, 3]:
        passive = kappa
    else:
        passive = s.Integer(-1)
    if i not in coalition:
        return passive
    return passive + sum(L[i, j] for j in others) - (
        kappa + 1 if i in (0, 1) and 2 in others and 3 in others else 0)


def joining(i, coalition):
    return s.cancel(native(i, set(coalition) | {i}) - native(i, coalition))


def polynomial_sign(expression):
    polynomial = s.Poly(expression, t)
    if polynomial.is_zero:
        return 0
    if polynomial.eval(0) > 0 and all(c >= 0 for c in polynomial.all_coeffs()):
        return 1
    if polynomial.eval(0) < 0 and all(c <= 0 for c in polynomial.all_coeffs()):
        return -1
    raise AssertionError(('Uniform sign not proved', polynomial))


def sign(expression):
    numerator, denominator = s.cancel(expression.subs(R, t + 3)).as_numer_denom()
    return polynomial_sign(numerator) * polynomial_sign(denominator)


details, passing = [], []
for i, j, k, l in permutations(range(4)):
    a, b = joining(i, [l]), joining(i, [k, l])
    if not (sign(a) == 1 and sign(b) == -1):
        continue
    c = a / (a - b)
    guards = tuple(s.cancel(g) for g in (
        joining(k, [l]), joining(k, [i, l]),
        (1 - c) * joining(j, [l]) + c * joining(j, [k, l]),
        (1 - c) * joining(j, [i, l]) + c * joining(j, [i, k, l]),
        c * (c * native(l, [k, l]) - native(l, [k])),
        (1 - c) * joining(l, [i]) + c * joining(l, [i, k])))
    signs = tuple(sign(g) for g in guards)
    details.append(((i, j, k, l), s.factor(c), signs))
    if signs == (-1, -1, -1, -1, 1, -1):
        passing.append(((i, j, k, l), s.factor(c), guards))

assert len(details) == 7
assert len(passing) == 1
roles, c, guards = passing[0]
assert roles == (1, 3, 0, 2) and c == s.Rational(9, 40)
assert guards == (-1, -5, -s.Rational(89, 40), -s.Rational(53, 40),
                  s.Rational(3519, 16000), -(90 * R + 409) / 400)
pole_values = (1 + native(3, [0, 1]), 1 + native(0, [2, 3]),
               1 + native(2, [1, 3]))
assert pole_values == (R + 1, s.Rational(17, 5), 0)
print('PASS: all24 roles uniformly for R>=3; exactly one endpoint role passes.')
print('First-two-guard roles:', details)
print('Passing role:', passing[0])
print('Its original passive coordinates:', pole_values)
print('No isolated-table exclusion from an unspecified eventual threshold is claimed.')

```
