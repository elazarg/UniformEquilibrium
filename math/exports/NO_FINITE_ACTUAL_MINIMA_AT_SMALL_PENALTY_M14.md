# Excluding the entire finite actual minimum mode in the M14 quitting benchmark

For the native four-player table below, sufficiently small selectable source
penalties exclude every finite-calendar actual minimum, with no bound on the
number of occupied dates. This is a complete exclusion of one residual source
mode. It does not solve the arbitrary four-player UE conjecture: actual
four-infinite-owner minima and nonrealized inherited semantic endpoints remain
outside this theorem. No UE payoff or fixed-target strategy producer is claimed.

## 1. Raw table, full behavioral semantics, and exact source

Players are0,1,2,3. Own singleton, live and Never rewards are0. The singleton
matrix Gamma and participant-pair matrix J, with diagonal0, are

    Gamma=[0,-1,-1,2; -1,0,1,1; 1,2,0,-1; 1,-1,1,0],
    J=[0,-5,13,-5; 13,0,-5,-5; -5,-5,0,13; -5,13,-5,0].

Every passive nonsingleton reward is0. Every participant reward in a coalition
of size at least3 is-5. Thus all60 native absorption rewards are specified.
The pivot is2 and the observer set is O={0,1,3}.

An actual profile consists of independent stopping laws on the nonnegative
integer dates together with Never. Before absorption the public history is
only a sequence of Continue outcomes. Every unrestricted private behavioral
deviation therefore induces a random first-Quit date, and conversely every
such stopping law is executable. Its payoff is an average of deterministic
deadline payoffs and the Never payoff. Thus the full unilateral cap B_i is
the supremum over all deadlines and Never, not a finite-menu cap.

For an actual profile let U be its prescribed terminal payoff, B its full
response cap, e its payoff vector when each player separately uses Never,
N_i its marginal Never probability, nu=prod_i N_i, and d_i=B_i-U_i>=0.
Let H be the compact closure of all actual tuples(U,B,e,N), and

    C={Y in H: d_i(Y)=0 for i in O},
    m=min{d2(Y):Y in C, nu(Y)=0}>0.                              (1)

The absorbing face is assumed nonempty. Importantly, C is the zero-observer-
debt part of the closure of ALL actual tuples. It is not defined as the
closure of actual profiles that already have exact observer debts.

For0<r<m write J_r=d2+r nu and mu=min_C J_r. The theorem concerns an ACTUAL
profile representing a global minimizing tuple in C with the incoming
subcritical-source properties

    0<mu<r, B2>mu, all N_i>0, e=B, d_i=0 for i in O.             (2)

The equality e=B is ALL-END: Never is a full best response for every player.
These are the existing actual branch of the partial-Nash minimum reduction.
Actual realization is an explicit branch hypothesis, not asserted here.

**Theorem.** There is r0>0 such that for every0<r<min(m,r0), no actual
minimizing profile satisfying(2) has finitely many occupied dates. The number
of dates is unrestricted. The theorem makes no claim that r=m/2 already
has this property, and makes no uniform claim over different raw games.

The proof below produces its semantic competitors from actual finite profiles.
It requires no supplied continuation strategy or finite descent witness.

## 2. Exact finite-prefix calculus

For root hazards q_i<1 write x_i=q_i/(1-q_i), H_i=prod_(j!=i)(1-q_j),
and c=prod_i(1-q_i). Let P_i be the expected root payoff when i Continues
and at least one opponent quits, and Q_i its immediate-Quit payoff. Against
a continuation tuple, the exact maps are

    U'_i=q_i Q_i+(1-q_i)P_i+c U_i,
    B'_i=max{Q_i,P_i+H_i B_i},
    e'_i=P_i+H_i e_i, N'_i=(1-q_i)N_i.                          (3)

They are continuous, including the maximum. Prefixing actual approximants
therefore proves that these maps preserve H. If the tail is ALL-END and
root Never dominates Quit, then

    d'_i=q_i H_i[v_i-C_i(x)]+c d_i,
    C_i(x)=(Q_i-P_i)/H_i, v_i=B_i.                             (4)

For this table, with L=J-Gamma,

    L=[0,-4,14,-7; 14,0,-6,-6; -6,-7,0,14; -6,14,-6,0],
    R_i(x)=5[sum_(j<k;j,k!=i)x_j x_k+prod_(j!=i)x_j],
    C_i(x)=L_i x-R_i(x),  P_i=H_i Gamma_i x.                    (5)

Hence root Never dominance is C_i(x)<=v_i; active observer contact is
equality, and root Nash conditions are these inequalities together with
x_i[C_i(x)-v_i]=0 for every i. Every reached conditional tail of an actual ALL-END profile is ALL-END:
a better conditional deadline would, after continuing through the finite head,
improve the original Never response by the positive opponent-head survival
factor. Formula(4) then has nonnegative summands; positive prefix survival
forces every conditional observer debt to vanish when the original debt is0.

Two simple consequences of global minimality and(1) will be used. First,
the first occupied root of a source profile cannot involve only pivot2.
If its quit probability were q>0, its Never cap would be the unchanged
positive tail cap B2, and

    mu=q B2+(1-q)J_r(tail)>q mu+(1-q)mu=mu.

Here the actual tail is in C, so J_r(tail)>=mu. Second, for any sequence in
C with d2->0, joint Never mass stays bounded away from0. Otherwise a compact
subsequence would reach nu=0,d2=0, contrary to(1). Neither fact says that a
conditional tail itself minimizes J_r.

## 3. The unique nonempty proper native Nash root

The positive inverse

    A=L^-1=(1/6284)[714,1057,810,609;
                   732,714,672,994;
                   994,609,758,663;
                   672,810,1132,758]                            (6)

first gives a collar around the empty root. At any nonempty ALL-END last
root the continuation is literal Never, so C(x)<=0 and x<=A R(x).
If s=max_i x_i<=1, then R_i(x)<=20s^2 and max_i(A1)_i<1; thus
s<=20s^2 and s>=1/20. If s>1 the same lower bound is immediate. Therefore
nonempty admissible last roots cannot converge to the empty root.

Any nonempty proper Nash root against literal Never has full support.
A singleton j violates the quiet comparison on its premium successor,
where C_i=14x_j>0. If the support has at least two owners, an active owner
whose predecessor is absent has C_i<0, since every other off-diagonal
coefficient in its row is strictly negative. This contradicts its equality
C_i=0. The four-cycle predecessor closure forces all four owners active.

Here is the full algebra needed to classify these Nash roots. Put z=x2,
y=x3 and

    ell=5(1+z), h=14-5z, c0=6+5z, k=6z,
    phi_z(y)=(k+c0 y)/(h-ell y),
    d=h^2-ell k, e0=20ell, a=c0^2-ell k, b=20k.

The observer1 and3 contacts give

    x0=phi_z(y), x1=phi_z(phi_z(y))=(a y+b)/(d-e0 y).

Positivity of these equations forces h>0,d>0,0<y<d/e0. The remaining
observer contact is F_z(y)=0, where

    F_z(y)=(4+5z)x1+(7+5z)y+ell x1 y-14z.

The phi maps and F_z increase strictly with y on this legal interval.
At its upper endpoint F tends to infinity. At y=0,

    F_z(0)=z A0(z)/d, A0(z)=70z^2+2980z-2264.

Let z_* be the unique positive zero of A0; exact signs give.74<z_*<.75.
There is a unique legal positive y exactly for0<z<z_*. On this branch set

    g=6x0+7x1-14y+5(x0x1+x0y+x1y+x0x1y)=-C2(x).

As z decreases to0,

    (x0,x1,y)/z ->(405,336,566)/379, g/z ->-3142/379<0.

At z=z_* one has y=0,x0>0,x1>0 and g>0. Thus g has a zero in(0,z_*).
To prove uniqueness, put F=(d-e0 y)F_z(y), G=(h-ell y)(d-e0 y)g.
Direct polynomial elimination gives

    Res_y(F,G)=-10z(5z^2+70z+84)^3 R8(z),
    R8(z)=33173125z^8+1623635000z^7+12936067000z^6
      -15895969500z^5-307529649300z^4-629973729300z^3
      -333138223960z^2+40832208960z+1080998816.

R8 has exactly two coefficient sign changes. Its signs at3/25,121/1000,1,5
are respectively+,-,-,+. Descartes' rule therefore gives exactly one zero
below1 and exactly one above1. There is exactly one nonempty proper native
Nash root x_alpha, with alpha=x_alpha,2 in(3/25,121/1000).

## 4. Its cap forbids every nonempty proper Nash prefix

Let B_alpha be the four Never caps of x_alpha. The following rational
box and lower cap bounds are useful both here and in the descent argument:

    126/1000<x_alpha,0<129/1000,
    122/1000<x_alpha,1<125/1000,
    120/1000<alpha<121/1000,
    133/1000<x_alpha,3<136/1000.                                (7)

To verify(7), phi increases in z and y on this box. In F_z(133/1000), bound
all positive terms at z=121/1000 and -14z at z=3/25. The result is
-57077215903529/6417899800000000<0. For F_z(136/1000), reverse endpoints;
the result is2219971/2087187500>0. Strict monotonicity gives the y bounds,
and applying phi twice gives the other two bounds. All displayed phi
denominators are positive on the indicated boxes.

Using B_i=H_i Gamma_i x and(7), the four lower cap bounds are

    (10000/716319, 7750000/89858239,
     13000/80159, 968000/11390481) > b0=(1,8,16,8)/100.

Moreover A1> (12/25)1 and

    A b0=(13501/314200,6287/157100,11649/314200,1958/39275)
          >(37/1000)1.

There is no x>=0 satisfying C(x)=B_alpha. With t=min_i x_i, such an x
would satisfy x=A[B_alpha+R(x)], R_i(x)>=15t^2+5t^3, and hence

    t>37/1000+(36/5)t^2.

The quadratic (36/5)t^2-t+37/1000 is strictly positive on the entire real
line: its discriminant is-41/625. This is a strict algebraic obstruction.

Finally, because B_alpha>0, every active owner in a nonempty Nash root
against B_alpha must have its predecessor active: C_i(x)=B_alpha,i>0
requires the unique positive linear term14x_pred(i). Four-cycle closure
forces full support and the excluded system C(x)=B_alpha. Thus no nonempty
proper Nash prefix exists, including prefixes with an initially proposed
proper subset of active owners.

## 5. A produced semantic tail and local one-date descent

This step uses the full source carrier C, not a restricted closure of
already observer-exact actual profiles. Put w=(4,5,1,3), so
Gamma w=11e2 and Jw=(-27,32,-6,40). For fixed t>=0 and each positive integer
N, take N identical actual roots with odds(t/N)w, followed by literal Never.
For observers, every passive offer is exactly0, every Quit offer is O(1/N),
full caps are O(1/N), and prescribed payoffs are O(1/N). No finite approximant
is claimed observer-exact. For pivot2, immediate Quit is negative for large
N, while every conditional Never value is nonnegative; its cap is Never.
The geometric sums of these finite profiles converge to the tuple Q_t with

    B(Q_t)=e(Q_t)=b(t)e2, U(Q_t)=u(t)e2,
    b(t)=(11/12)(1-exp(-12t)),
    u(t)=(11/13)(1-exp(-13t)), N_i(Q_t)=exp(-w_i t).

For example, the pivot's passive offer at one approximating root is
11(t/N)H2, while its prescribed root reward is11(t/N)+O(N^-2).
Opponent and joint survival rates tend to exp(-12t) and exp(-13t), giving
the stated sums. Thus Q_t belongs to C, is ALL-END, and

    d2(Q_t)=b(t)-u(t)=O(t^2), nu(Q_t)=exp(-13t).                  (8)

Now consider any one-date ALL-END, zero-observer-debt profile whose odds x
are sufficiently close to x_alpha. They have full support. Put z=x2,
g=-C2(x)>=0, n_i=(1+x_i)^-1, and nu_x=prod_i n_i. Its objective is
nu_x(zg+r). Let D=DC(x). The exact inequalities below show D invertible
throughout the closed box(7). The implicit function theorem therefore
produces x(t) with x(0)=x and

    C(x(t))=[b(t)-g]e2.

Prefix Q_t by this root. Observer contacts hold exactly, the pivot gap is
the unchanged nonnegative g, and(3) proves that the resulting tuple belongs
to C and is ALL-END. Every newly required object has been constructed.
Its objective is

    J_r(t)=nu_x(t)[x2(t)g+b(t)-u(t)+r exp(-13t)].                (9)

Since x'(0)=11D^-1 e2, differentiating gives

    J_r'(0)/nu_x
       =11g(e2^T-z n^T)D^-1e2-r[13+11n^T D^-1e2]<0.           (10)

This is strict for every r>0 and every g>=0 in the box. Here is a completely
specified finite certificate for its signs. Set

    P=prod_i(1+x_i), u=adj(D)e2,
    S=sum_i [prod_(j!=i)(1+x_j)]u_i.

On the closed box(7), every tensor Bernstein coefficient is positive for
all three polynomials

    detD,
    A1=13P detD+11S,
    A2=-11(Pu2-zS).

Their multidegrees, coefficient counts and minimum coefficients are

    (2,2,2,2),81: 23793606226737828229/1953125000000000;
    (3,3,3,3),256:
      468002355419767964503678041841/3051757812500000000000000;
    (2,2,4,2),135:
      8171189161025339761981431647753/500000000000000000000000000.

The matrix entries are explicitly

    D_ii=0,
    D_ij=L_ij-5[sum_(k notin{i,j})x_k+prod_(k notin{i,j})x_k].

For reproducibility, map each box coordinate to a unit variable. If the
transformed power coefficients are c_m and the multidegree is d, coefficient
k in the tensor Bernstein basis is
sum_(m<=k)c_m prod_i binom(k_i,m_i)/binom(d_i,m_i).
Positive coefficients imply positivity on the entire closed box. Dividing
A1 and -A2 by P detD proves the two signs in(10).

Therefore an actual source minimum with just one occupied date and root
sufficiently close to x_alpha is impossible. Initial empty dates do not
change this argument: these one-date caps are strictly positive near x_alpha,
and the constructed prefix caps stay positive, so every such extra Quit0
option is dominated. The competitor is a valid point of C even when Q_t
itself is not represented by an actual infinite tail.

## 6. Calendar-independent exclusion of every finite source profile

Suppose the theorem fails. Choose r_n->0 and finite actual source minima
P_n with d_n<=mu_n<r_n. Section2 gives nu_n>=eta>0 after a subsequence.
Every individual root Continue probability is then at least eta, and every
finite prefix joint survival is at least eta. All root odds are bounded
by(1-eta)/eta. By(4), every conditional pivot debt is at most d_n/eta->0.

Let the final occupied roots be q_n^last. The collar in Section3 prevents
their odds limits from being empty. Every subsequential limit is proper
and Nash against literal Never: observer contacts and quiet inequalities
pass to the limit, while the vanishing pivot debt gives its complementarity.
Section3 therefore implies q_n^last->q_alpha and their caps tend to B_alpha.
If infinitely many P_n have one occupied date, Section5 contradicts their
minimality. Pass to the remaining subsequence with at least two dates.

There are at least two dates with an observer active. The first occupied
date is observer-active by Section2; the last one also is, since a last
pivot-only root violates observer0's quiet comparison C0=14x2<=0. If there
were only one observer-active date, these would be the same occupied date.

Choose the penultimate observer-active date k_n. Between it and the final
occupied root only pivot2 can quit. Let s_n be its total Continue probability
through this block, equal to1 for an empty block. Exact conditioning gives

    v2^block=v2^last,
    v_i^block=s_n v_i^last+(1-s_n)Gamma_i2   (i!=2),
    d2^block=(1-s_n)v2^last+s_n d2^last.                        (11)

All these caps are Never values by ALL-END. The block debt tends to0,
while v2^last->B_alpha,2>0. Hence s_n->1 and v^block->B_alpha. Formula(11)
has no dependence on the number of physical dates in the block.

At k_n choose, after a subsequence, a fixed observer i active for every n.
Its contact is C_i(x_n)=v_i^block->B_alpha,i>0. Thus the uniformly bounded
root odds x_n cannot converge to0. Take a convergent subsequence. All root
inequalities and observer complementarity identities pass to its limit.
Furthermore H2>=eta^3 and the conditional debt tends to0; equation(4)
gives q2[v2^block-C2(x_n)]->0, exactly pivot complementarity in the limit.
The limit is therefore a nonempty proper Nash root against B_alpha.
Section4 forbids it, completing the contradiction.

No conditional tail was treated as a global minimum. The cap in(11) is an
actual conditional Never cap. No empty-date compression, finite-menu repair,
or fixed-date-budget compactness was used. The quantifier is one sufficiently
small source penalty range excluding ALL finite calendars simultaneously.

## 7. Exact checks, scope, source correspondence, and handoff

The accompanying single exact checker reconstructs L^-1, the inverse axis,
the native-Nash resultant and sign counts, the rational box and cap bounds,
the no-prefix discriminant, and all472 positive Bernstein coefficients.
It uses rational SymPy arithmetic and no sampling or numerical tolerance.
The formulas above specify the certificate independently of any scratch path.

Useful falsification boundaries are explicit. The native Nash root x_alpha
itself is a finite positive-Never zero-debt profile, so this theorem does not
exclude all finite partial-Nash profiles. Its exclusion as a SOURCE MINIMUM
uses the strict semantic descent in Section5. The proof also does not permit
choosing r0 uniformly over tables, identifying an inherited endpoint as an
actual root, or concluding that an infinite observer calendar has a terminal
root. An independent exact no-stationary/no-sure-root benchmark census is
not a premise of this proof; all required proper-root cases were derived here.

The existing source reduction supplies the alternatives of an actual
subcritical minimum or a nonrealized positive-Never minimum with a mixed
zero-observer-cap inherited endpoint. This result consumes the entire finite
submode of the former. It leaves its infinite submode and the latter alternative
open. The previously known finite support classifications alone did not do so.

The semantic interfaces inspected for this theorem are:

* quittingStoppingLawExpectedPayoff, the full replacement cap, and the
  behavioral/canonical payoff-cap bridges in
  UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean;
* quittingTerminalSemanticPair_rootThenContinuation in
  UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean;
* not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt
  in UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean;
* exists_positive_minimumTerminalSemanticDebt_face_of_no_uniformPayoff in
  UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean.

These declarations provide the surrounding semantics, not a Lean proof of this
new exclusion. The additional positive-Never augmented carrier, partial pivot
minimum, and actual/nonrealized source partition are ordinary mathematical
source inputs stated in(1)--(2); no new formalization seal is claimed.

A formalization should first define this complete raw table and the augmented
carrier, prove(3)--(4) for full behavioral caps and its compact prefix extension,
then verify the finite polynomial certificates. The produced finite approximants
in Section5 must be used to prove Q_t in C; an assumption of an available
observer-exact tail would weaken the theorem. The final consumer should quantify
one r0>0, all0<r<min(m,r0), and every actual minimizing profile, and conclude
its occupied-date set is infinite. It must not replace this statement by a
fixed bounded-horizon verifier or a claim of an original-game uniform payoff.
