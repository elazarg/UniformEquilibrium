# Global least-Never sources reduce to positive payoffs or AllNever

## Exact statement

Let I={0,1,2,3}. For every nonempty coalition S, let Z_i(S) be a real
terminal reward, with Z_i({i})=0. Live play and literal AllNever pay zero.
Each owner independently chooses its first Quit date in the natural numbers
or a separate Never point; a unilateral deviation may replace its entire law.
Fix M>=1 bounding all absolute rewards. For an actual profile write U_i for
its prescribed payoff, B_i for the supremum of EVERY finite-deadline and
Never response, e_i for its Never response, and N_i for its ORIGINAL Never
probability. Define

    C=closure{(U,B,e,N): actual independent profiles},
    D=sum_i(B_i-U_i), nu=product_i N_i,
    E=C intersect{D=0}, mu=min_(X in E)nu(X),
    A=inf{D(P): P actual and nu(P)=0}.

C is a compact Euclidean carrier. E is nonempty because AllNever is Nash.
Escaping finite stopping mass is never relabeled Never.

For distinct i,j set Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}), L_ij=J_ij-Gamma_ij;
put their diagonals equal to zero. Call Z joining-generic when all twelve
off-diagonal L entries and all four principal three-by-three determinants
of L are nonzero.

**Theorem.** Suppose Z is joining-generic and mu>0. Then exactly one of
the following global source alternatives holds:

1. mu=1, and every point of E is the AllNever annotation U=B=e=0,N=one.
2. 0<mu<1, and EVERY minimizer of nu on E has U=B=e strictly positive
   in all four coordinates.

More precisely, if a minimizer has exactly three zero payoff coordinates
T, its exclusion requires genericity only of L_T, not of the other entries.
The new excluded configuration is a GLOBAL UNMARKED least-Never source
with one positive payoff and three zeros. Neither a marked minimum nor an
inherited exact-payoff-fibre minimum can replace that hypothesis.

**Counterexample reduction.** Any signed Fin4 table without a uniform
equilibrium payoff produces a native joining-generic table with A>0.
For that table mu>0 and the theorem applies. Thus the previously surviving
three-zero global source branch is absent after generic perturbation and
fresh source selection. The all-positive and AllNever alternatives remain
open; the theorem does not settle Fin4. Section9 gives a further necessary
condition on the AllNever alternative: under explicit additional genericity,
the entire four-owner joining pencil is R0 of degree1.

## Conjecture-facing change and strategic inputs

The reduction removes an entire attained global source configuration, rather
than classifying a supplied local direction. The producer requires only the
finite reward table and the hypothesized positive absorbing gap. Compactness
produces the minimizing annotations; finite mixed Nash existence supplies
auxiliary roots; explicit finite words produce all comparison profiles.
No source realization, favorable eigenvector, root selector, continuation
openness, or strategy certificate is assumed. Eigenvectors occur only in
exhaustive contradiction cases of the displayed matrix pencils.

The proof uses the inverse function theorem, Banach contraction on a weighted
sequence space, and the usual homotopy and nonzero-degree existence properties
of Brouwer degree. The finite-word constructions and degree computation are
included. There is no public randomizer or correlated strategy choice.

## Definitions and source correspondence

Before absorption there is only one live public history at each date.
Conditional hazards therefore implement exactly independent first-Quit laws.
Any complete behavioral replacement averages its pure first-Quit dates and
Never, so B is the unrestricted behavioral cap. Supremum need not be attained.
All limiting arguments retain expectations, full response suprema and
original Never probabilities as separate coordinates.

The full cap formula is represented by
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`. Finite mixed Nash
existence is `exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`. The normalization input
is `nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`.
The terminal-debt endpoint is
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`.
These source results do not assert the global least-Never dichotomy proved
below. The mathematical packet makes no new Lean-certification claim.

## Proof

### 1. Compactness, complete prefix maps, and original Never

All values lie in[-M,M] and N in[0,1]^4, so C is compact. Every actual
profile satisfies

    B_i-U_i>=N_i(B_i-e_i)>=0.

This follows by averaging its prescribed finite responses, each bounded by
B_i, and its own Never response. It passes to C. Hence every zero-debt point
with nu>0 has U=B=e. Also |U_i|<=M(1-nu), including in C.

For q in[0,1]^4 let Q_i(q) be its forced-Quit offer, P_i(q) its passive
offer on nonempty opponent coalitions, H_i(q)=product_(j!=i)(1-q_j), and
h(q)=product_i(1-q_i). Prefixing q to a tail has the exact formulas

    U'_i=q_iQ_i+(1-q_i)P_i+h U_i,
    B'_i=max(Q_i,P_i+H_i B_i),
    e'_i=P_i+H_i e_i, N'_i=(1-q_i)N_i.                (1)

Every response either quits now or uses a complete old response after
continuing, proving the cap identity. These continuous maps preserve C by
prefixing actual realizing sequences. Payoff and cap coordinates are
nonexpansive in their corresponding tail coordinate, uniformly through
words of any finite length. The exact debt identity is

    D'=hD+sum_i[max(Q_i,P_i+H_iB_i)
                    -q_iQ_i-(1-q_i)(P_i+H_iB_i)].    (2)

The second term is nonnegative and uses the NEXT FULL CAP.

At a global minimizer X with nu(X)=mu>0, put w=U=B=e. Every exact Nash
root against w has zero defect in(2), hence prefixes X to another point
of E with Never h(q)mu. Minimality forces q=0. Thus the root game has
ONLY AllContinue as a Nash root; existence implies w>=0.

### 2. The elementary zero sets and the AllNever endpoint

If w has exactly one zero coordinate j, a small solo-j hazard is Nash:
j is indifferent at zero, and positive outside continuations strictly
prefer Continue for sufficiently small hazard. This contradicts(1).

If only i,j have zero payoffs and L_ij<=0, a small solo-j hazard is Nash;
similarly when L_ji<=0. Otherwise both increments are positive. Replace
those two continuations by -epsilon and choose a finite Nash root. As
epsilon->0, every cluster root must be AllContinue. Near zero all positive
outsiders stay quiet. The two remaining comparisons are exactly

    Quit_i-Continue_i=epsilon(1-q_j)+L_ij q_j>0,

and the analogous expression for j. Both owners would quit surely,
contradicting convergence to zero. Two zero coordinates are excluded.

If w=0 and mu<1, concatenate two independent copies of finite approximants
of X. Such approximants exist by censoring late finite masses to Never;
coupling bounds every prescribed or fixed-response change by2M times the
moved mass, uniformly over responses. Pad the first block with an unused
date, representing its Never offer as a finite deadline. For a finite
block P the exact two-copy formulas are

    U_i(P*P)=(1+nu(P))U_i(P),
    B_i(P*P)=max(B_i(P),e_i(P)+H_i(P)B_i(P)),
    N_i(P*P)=N_i(P)^2,

where H_i(P)=product_(j!=i)N_j(P). The approximating limits give a point
of E with Never mu^2<mu, impossible. No infinite source block is executed.
Conversely mu=1 forces nu=1 throughout E, and |U_i|<=M(1-nu) gives the
AllNever annotation. It remains to exclude exactly three zeros.

### 3. A common finite-word comparison rule

Assume w=b e_p, b>0, and let T=I minus{p}. In this part G=Gamma_T,
J=J_T and L=J-G. All constructed roots keep p quiet. If their total
activity sum_(dates,i in T)q_i is at most b/(16M), the pivot stays strictly
on Continue: its cap changes by at most2M times current activity, whereas
its Quit offer has absolute value at most M times that activity. Induction
keeps its Continue cap at least7b/8 and each Quit offer at most b/16.
Since its initial U_p=B_p=b, its debt remains exactly zero.

It is therefore enough to produce finite words with vanishing observer
debt and survival c_k in a fixed interval[c0,c1], where0<c0<=c1<1.
Prefix each word to X, extract a compact limit in C, and use (1) to retain
nu'=c mu<mu. This contradicts global minimality, whatever the endpoint
payoff signs. Virtual observer starting pairs may be used for estimates
only: if they tend to zero, nonexpansiveness transfers their endpoint
estimates to the same words applied to X. Original Never always belongs
to the actual prefixed sequence.

### 4. A homogeneous complementarity vector gives a diffuse word

A matrix G is R0 if its only v>=0 with Gv>=0 and v_i(Gv)_i=0 is zero.
Suppose it is not R0 and normalize such a nonzero v by sum_i v_i=1.
Fix0<tau<=b/(16M), use q_T=epsilon v repeatedly for
K=floor(tau/epsilon) dates, and then X. Write c=product_T(1-epsilon v_i).
The one-date offers satisfy

    |P_i-epsilon(Gv)_i|<=2M epsilon^2, |Q_i|<=M epsilon.

For an active owner, (Gv)_i=0. Its prescribed one-date reward is bounded
by3M epsilon^2; every complete reply accumulates at most K passive terms
and one Quit offer. Thus its debt is at most5MK epsilon^2+M epsilon.
For an inactive owner, its payoff is P_i sum_(s<K)c^s. Any deadline k<K
has value P_i sum_(s<k)c^s+c^kQ_i and exceeds that payoff by at most
M epsilon+2MK epsilon^2; continuing into X has the prescribed value.
All observer debts tend to zero, and c^K->exp(-tau)<1. Section3 gives
a contradiction. Hence G is R0. In particular each column of G has a
negative entry, since a nonnegative column gives a unit-vector solution.

### 5. A positive singleton inverse gives expanding macrocycles

Suppose G is invertible with G^-1>0 entrywise. The off-diagonal entries
of GG^-1 and G^-1G force one positive and one negative entry per row and
column. Relabel cyclically so G_i,next(i)=-A_i<0 and G_i,prev(i)=B_i>0.
The diagonal cofactors are positive; positivity of G^-1 implies
rho=product B_i/product A_i>1.

Starting with virtual observer payoff x e_i, a solo-next(i) macrohazard
q=x/(A_i+x) makes coordinate i zero and leaves value B_prev(i)x/(A_i+x)
at prev(i), with the moving owner's value zero. Three steps, with movers
2,1,3 from x e_1, return to that axis with amplitude

    F(x)=rho x/(1+Cx),
    C=(A_2A_3+A_2B_3+B_2B_3)/(A_1A_2A_3)>0.

Choose1<r<rho and fixed small a>0 with Ca<=rho-r. Put x_0=a and
x_(n-1)=x_n/(rho-Cx_n) for n<=0. Then x_-m<=a r^-m. Every intermediate
amplitude and macrohazard is bounded by a constant times its input.
Consequently the words from x_-m to a have uniformly O(a) total activity
and contain a fixed final macrohazard q_*>0.

Subdivide each macrohazard q into ell microhazards
eta_l=q/(ell-lq),0<=l<ell. Their survival product is1-q and their sum
is at most q/(1-q). Make every eta_l<=delta. Throughout a macrostep
with aggregate partial hazard Q, the observer payoffs are
(1-Q)x-A_iQ>=0, zero at the mover, and B_prev(i)Q>=0.
Starting virtual caps at these payoffs, their debts obey

    d'_mover=d_mover,
    d'_i=max(eta_l Z_i({i,mover})-U'_i,(1-eta_l)d_i)
          <=max(Mdelta,d_i) for every other observer.

Thus every observer debt stays at most Mdelta, independently of word
length. Choose a so the total microactivity is at most b/(16M). Apply
the same words to X: starting observer mismatch x_-m gives endpoint
debt at most Mdelta+2x_-m. Let delta->0 as m->infinity. Survival is
bounded below15/16 and above1-q_*<1, contradicting Section3. Therefore
G^-1 cannot be strictly positive.

### 6. A nonnegative column of the pencil gives a geometric word

Suppose for some j in T and0<s<1, G_ij-sJ_ij>=0 for both other observers.
Fix a small f>0 and put

    R_n=f(1-s)^n, S_n=1-f+R_n, r_n=R_n/S_n, q_n=s r_n.

At chronological date n only j acts with hazard q_n. Then
1-q_n=S_(n+1)/S_n, sum_n q_n<=f/(1-f), and
q_n+(1-q_n)r_(n+1)=r_n. Give the virtual observer suffix n payoff and
cap G_ij r_n for i!=j and zero for j. Continue has exactly that value,
whereas Quit has sJ_ij r_n; thus every root is exactly Nash in observer
rows, even if their common values are negative. For the truncated word
through n=m, its virtual terminal observer pair differs from zero by
O(r_(m+1)). Choose f/(1-f)<=b/(16M), apply the same words to X, and
let m grow. Observer debt tends to zero and survival tends1-f<1.
Section3 excludes every such nonnegative pencil column.

### 7. A positive expanding mode gives an exact root orbit

Suppose L is invertible and A0=L^-1J has a positive eigenvector v>0
with eigenvalue rho>1. Define, near observer hazard zero,

    z_i(q)=[Q_i(q)-P_i(q)]/H_i(q), s_i(q)=Q_i(q).

Their derivatives at zero are L and J. The inverse function theorem
gives F=z^-1 composed with s, with F(q)=A0q+R(q),
|R(q)|<=C|q|^2 and |R(q)-R(r)|<=C' max(|q|,|r|)|q-r|.
The identity z(F(q))=s(q) concatenates fully mixed exact observer roots.

Here is the required positive backward orbit without a simplicity or
dominance assumption on rho. Choose rho<sigma<rho^2 avoiding every
eigenvalue modulus of A0. Split into invariant spaces E_s,E_f below
and above sigma. Equivalent norms give
||A_s||<=alpha_s<sigma<alpha_f and ||A_f^-1||<=1/alpha_f.
For sequences indexed n<=0 use ||x||_sigma=sup sigma^-n||x_n||.
For forcing f_n,n<0, define

    (Gf)^s_n=sum_(k=-infinity)^(n-1)A_s^(n-1-k)f^s_k,
    (Gf)^f_n=-sum_(k=n)^(-1)A_f^(n-1-k)f^f_k.

The operator norm is bounded by
1/(sigma-alpha_s)+1/(alpha_f-sigma); omit empty blocks.
Direct cancellation gives (Gf)_(n+1)-A0(Gf)_n=f_n.
Such equivalent norms follow, for example, from the convergent norm
sum_(k>=0)c^-k||A^k x|| whenever the spectral radius is below c.

Set y_n=a rho^n v. On the ball ||x||_sigma<=Ba^2, the nonlinear map
x->G(R(y+x)) has norm at most C0a^2 and Lipschitz constant at most C1a.
These bounds use rho^(2n)<=sigma^n and sigma^n<=rho^n for n<=0.
First choose B>2C0 and then a small. Banach contraction gives

    F(q_n)=q_(n+1), q_n=a rho^n v+O(a^2 sigma^n), n<=0.

Since v>0, reducing a makes every q_n positive and proper. Total activity
is O(a), while q_0 is nonzero. Start a virtual observer diagonal at
z(q_-m) and prefix q_-m,...,q_0 in construction order. Every observer
remains exactly indifferent and ends at s(q_0). The physical finite
calendar has the reverse order; no infinite reversed word is executed.
The initial mismatch from X is O(a rho^-m). Choose a for the pivot
buffer, transfer by nonexpansiveness, and let m grow. Survival lies
between15/16 and product_i(1-q_(0,i))<1. Section3 excludes this mode.
No sign of L^-1 is needed for this unmarked global comparison.

### 8. Root inertia and the entire three-dimensional pencil

Every column of L has a positive entry, or a small solo hazard would be
Nash at b e_p. Joining-genericity now makes -L R0: a singleton support
is blocked by that column entry, a pair support would require two zero
reciprocal entries, and full support is excluded by det L!=0.

For any z in R^T, replace the zero continuations by t z, retain b at p,
and choose a finite Nash root. Uniqueness at t=0 forces q^t->0; p is
quiet eventually, and the observer Nash conditions are

    q>=0, c=t z-Lq+O(||q||^2+t||q||)>=0, q_i c_i=0.

If ||q||/t were unbounded, normalization would give a nonzero homogeneous
solution for -L. Therefore clusters of q/t solve LCP(-L,z). Thus -L is
standard Q, meaning every offset z has a complementary solution.
At offset -one it supplies x>=0 with -Lx>=one, so each row of L has
a negative entry. Together with a positive entry in every column, the
six positions force a strict signed cycle. Write
L_i,next(i)=a_i>0,L_i,prev(i)=-b_i<0. The inequalities force x>0 and
product b_i>product a_i. Its inverse is strictly negative, and
det(-L)=product b_i-product a_i>0.

For -L at offset -one, singleton supports fail its zero diagonal, pair
supports fail their opposite-sign entries, and the unique full-support
solution is (-L)^-1 one>0. Near it the minimum-complementarity map is
x->-Lx-one, with index+1. Hence the homogeneous R0 degree of -L is1.

Consider M(t)=G-tJ,0<=t<=1. Its endpoints G and -L are R0. A nonzero
homogeneous solution at0<t<1 has one of three supports. A singleton
gives a nonnegative column, excluded by Section6. A pair {i,j} forces
M_ij=M_ji=0; the third-row inequality makes at least one of its two
remaining column entries nonnegative, again giving a forbidden column.
Full support gives v>0,M(t)v=0, hence

    L^-1J v=[1/(1-t)]v,

the expanding mode excluded by Section7. Thus the whole pencil is R0.

For an R0 matrix A, f_A(x)=min(x,Ax) has only zero as a root and obeys
||f_A(x)||>=c_A||x||, by homogeneity and compactness of the unit sphere.
This lower bound is uniform along a compact R0 pencil. Brouwer homotopy
invariance therefore gives degree_R0(G)=degree_R0(-L)=1. For any offset z,
the maps min(x,Gx+u z),0<=u<=1, differ from f_G by at most||z||.
On a sufficiently large ball they have no boundary zero; nonzero degree
supplies an LCP(G,z) solution. In particular Gx>=one for some x>=0.

Every row of G consequently has a positive entry; Section4 gave a negative
entry in every column. Counting the six positions makes G a strict signed
cycle, G_i,next(i)=-A_i<0,G_i,prev(i)=B_i>0. The inequalities Gx>=one
force x>0 and product B_i>product A_i. The explicit adjugate

    adj(G)=[ A_2B_3  B_1B_3  A_1A_2
             A_2A_3  A_3B_1  B_1B_2
             B_2B_3  A_1A_3  A_1B_2 ]

is positive and det G=product B_i-product A_i>0, so G^-1>0.
Section5 excludes this. Exactly three zeros are impossible, completing
the theorem together with Section2.

### 9. A further restriction on the global AllNever alternative

The AllNever case has a stronger four-owner test. For this subsection use
the full matrices Gamma,J,L on I and write
Delta_S(t)=det(Gamma-tJ)_SS. Impose the following additional generic
conditions on the pair data:

    det L_SS!=0 for every |S|=2,3,4;
    Gamma_ij J_ji-Gamma_ji J_ij!=0 for every unordered pair;
    det J_SS!=0 for every |S|=3,4;
    Res_t(Delta_S,Delta_I)!=0 for every |S|=3.          (GEN)

The third condition fixes the resultant degrees at3 and4. These are
finitely many polynomial nonvanishings; the exact witness below proves
their simultaneous open density in the24 independent pair coordinates.

**AllNever restriction.** If mu=1 and(GEN) holds, EVERY matrix
M(t)=Gamma-tJ,0<=t<=1, is R0, has homogeneous complementarity degree1,
and is standard Q. Thus a homogeneous complementary crossing anywhere
on this closed pencil excludes the AllNever alternative. It does not
exclude the all-positive global alternative.

Indeed mu=1 forbids every nonempty zero-debt actual or compact profile.
The diffuse construction of Section4 works with all four coordinates
and literal AllNever as tail, omitting the positive-pivot buffer. Its
same estimates would contradict mu=1 if Gamma were not R0.
For0<t<=1 a nonnegative column j of M(t) gives an ACTUAL exact profile:
j has atoms f t(1-t)^n and Never1-f, for fixed0<f<1; all others Never.
Their deadline n minus Never value is

    f(1-t)^n[tJ_ij-Gamma_ij]<=0.

The mover's replies pay0. At t=1 this is one atom. Its Never product
is1-f<1, so every such column is excluded.

If0<t<1 has a homogeneous complementary vector v with support S, size2
would force both reciprocal entries of M(t) to vanish, contrary to(GEN).
For |S|=3 or4, L_SS is invertible and

    L_SS^(-1)J_SS v_S=rho v_S, rho=1/(1-t)>1.

Apply the dimension-independent backward-orbit construction of Section7
on S. Play the ACTUAL chronological roots q_0,q_-1,q_-2,... and let
outside owners choose Never. The hazards are positive and summable, so
original joint Never lies strictly between0 and1. The identity
z(q_n)=Q(q_(n-1)) makes every active finite deadline and Never equal to
Q(q_0), by telescoping with a remainder tending to zero.

For |S|=3 the remaining owner k has (M(t)v)_k>0. Equality would make
(v_S,0) a kernel vector of the full M(t), contradicting the resultant
condition. At the suffix beginning with q_n, its opponents' remaining
finite masses are

    (a rho^n/t)v_S+O(a^2 sigma^n), n<=0.

The contribution of two or more finite opponent clocks is
O(a^2 rho^(2n)). Its Never-minus-current-Quit value is therefore

    (a rho^n/t)(M(t)v)_k+O(a^2 sigma^n)>0

uniformly in n for small fixed a, since(sigma/rho)^n<=1. Canceling
common earlier outcomes proves that Never dominates every finite
deadline. The complete infinite profile is exact Nash, contradicting
mu=1. Full support has no outside row. Finally t=1 has no homogeneous
support of size at least2 by the principal nonsingularity of L. All
supports and both endpoints have been exhausted, so the pencil is R0.

To determine its degree, put g(q)=Q(q)-P(q), extending the root
polynomials to R^4, and F(q)=clip(q+g(q),0,1) coordinatewise. Its fixed
points are exactly the native zero-tail Nash roots. A nonzero one would
already contradict mu=1, so its only fixed point is0. Since F maps into
the cube, Id-tF has no zero on a large sphere for0<=t<=1. Thus Id-F has
degree1 and local degree1 at zero. Near zero the upper clip is inactive:

    Id-F(q)=min(q,-g(q))=min(q,-Lq)+O(||q||^2).

The R0 lower bound for -L gives a zero-free comparison on a small sphere,
so degree_R0(-L)=1. Homotopy along the R0 pencil transports this degree
to every M(t). The bounded-offset argument in Section8 proves the Q
property for each matrix.

The source constraint is the GLOBAL AllNever-only zero-debt condition.
Whole-pencil tests are stronger than inspecting either endpoint; they
do not assert a new general linear-clock producer or a finite-period
normal form for equilibria.


## Adapter from arbitrary signed no-UE data

The normalization declaration named above produces from a signed Fin4
counterexample a literal table R, still without a uniform payoff, whose
own singleton vector is one at a pivot p and zero elsewhere. The terminal
sum-debt endpoint gives delta=inf_(P actual)D_R(P)>0. Subtract one from
the entire pivot RECIPIENT row at every nonempty coalition, preserving
literal Never0, to obtain the native table Z.

For any table with nonnegative own singletons, a forced finite deadline
tending to infinity has payoff tending to the Never payoff plus its own
singleton times the opponents' joint Never probability, by bounded
convergence. Thus finite deadlines already have supremum at least the
Never offer and determine the full cap. Every finite response absorbs,
so its pivot payoff shifts by exactly one under this row subtraction.
At an absorbing prescribed profile its prescribed payoff also shifts by
one, leaving every debt unchanged. Consequently A_Z>=delta>0.
The relevant deadline-limit identity is
`quittingTerminalPayoff_update_finiteTime_tendsto_of_profile` in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`.

For any actual native profile choose the smallest original Never mass n
and move it to one finite date. The new profile absorbs surely. Coupling
changes four prescribed payoffs and the other three full caps by at most
2Mn each; the mover's cap is unchanged. Therefore, also by closure,

    A_Z<=D+14M nu^(1/4),

so mu>=(A_Z/(14M))^4>0. This supplies the theorem's positive global
Never hypothesis, without asserting actual attainment of a minimizing law.

If two native tables differ by at most eta in each reward, every U and
every pure response changes by at most eta; full caps do too. Their
absorbing sum-debt infima differ by at most8eta. The joining-generic
conditions are the nonvanishing of finitely many nonzero polynomials in
the independently adjustable pair-recipient rewards, hence are dense.
Perturb Z arbitrarily little, with eta<A_Z/16, retaining own singletons0.
Its positive absorbing gap persists. RESELECT the global minimum at the
new table and apply the theorem. No old minimum is transported through
the reward perturbation. The same argument permits imposing Section9's
additional generic conditions simultaneously: the twelve off-own singleton
and twelve pair-recipient rewards are independent native coordinates.
Their polynomial nonvanishings have the witness below, so the common
generic set is open dense and the positive gap survives before selection.

## Exact boundary tests

Here is one complete family testing both positive global Never and global
selection. Use core owners0,1,2 cyclically. Core rewards ignore membership
of observer3. They are0 when the core subset is empty or a singleton;
on a pair {j,j+1}, owner j gets1, owner j+1 gets-2 and the omitted core
owner gets0; on the full core each gets-1. Observer3 gets1 on nonempty
core coalitions excluding3, and0 on coalitions containing3, including{3}.
Every own singleton is0. The core has G=0 and L_i,next=1,L_i,prev=-2,
with det L=-7!=0.

For0<f<=1 give each core owner mass f/N at each date0,...,N-1 and
original Never1-f; observer3 chooses Never. Every core finite response
at t<N pays -(f/N)(1-tf/N), while every later deadline and Never pays0.
Thus B_i=e_i=0 and

    U_i=-f^2/N+f^3(N-1)/(2N^2)->0.

The observer has U_3=B_3=e_3=1-(1-f)^3. The limiting carrier point has
w=(0,0,0,1-(1-f)^3) and N=(1-f,1-f,1-f,1). At this w the observer
strictly continues; each core root gap is q_next-2q_prev. A singleton
active support gives a profitable quiet successor, a pair gives an active
owner a negative gap, and full support has negative summed gap. Hence
AllContinue is the only Nash root despite exactly three zero payoffs.

At f=1 the point has nu=mu=0, showing why the positive global minimum
hypothesis matters even with a generic joining block. At0<f<1 it has
positive original Never but is not globally minimizing, showing why root
inertia and actual carrier membership alone are insufficient. The theorem
uses global minimality to exclude its nonnegative G columns through actual
finite-prefix comparison, not through root uniqueness alone.

### Endpoint tests do not imply the whole-pencil condition

The additional generic conditions and the interior-pencil test are
nonvacuous as matrix conditions. Set

    G=[0,3,-1,-1; 3,0,-1,-1; -1,-1,0,3; -1,-1,3,0],
    A0=[0,-20,75,-10; -12,0,-20,24;
        36,-16,0,-8; -15,60,-25,0],
    Gamma=G, J=G-A0, M(t)=(1-t)G+tA0.

Here det G=45 and
15G^-1=[2,7,3,3; 7,2,3,3; 3,3,2,7; 3,3,7,2]>0.
A0 is obtained by swapping labels1,2 in G and multiplying its rows by
(5,4,4,5), columns by(3,4,5,2). Thus both endpoints have positive inverse
and determinant. Positive inverse implies R0: if x>=0, Bx=y>=0 and
x_i y_i=0, then y!=0 would force x=B^-1y>>0, a contradiction.
At offset -one every complementary solution satisfies x=B^-1(one+y)>>0,
so y=0 and the solution is unique, with local index sign det B=1.
Both endpoints therefore satisfy R0 and degree1.

All conditions(GEN) hold for these pair data, as the exact calculations
below verify. Nevertheless, on S={0,1,2},

    Delta_S(t)=33269t^3-4200t^2-275t+6

changes sign between a=21/125 and b=169/1000. At any root t* there,
the negative first adjugate column is the positive kernel vector

    v_S=((15t+1)(19t+1), (19t+1)(37t-1),
         3(1-5t)(15t+1)), v_3=0.

The outside residual is45193t^3-1881t^2-121t+9, bounded below by
45193a^3-1881b^2-121b+9>0 on that interval. Section9 thus produces a
nontrivial actual infinite Nash profile for EVERY higher-reward completion
of these fixed pair data. Its global minimum cannot be1. This is a test
of the AllNever source alternative, not a full UE theorem for those
completions or a claim that a counterexample has been constructed.

### Exact finite algebra check

The following standalone Python/SymPy check verifies the finite identities
and the generic witness. The unrestricted-clock and compact-source proofs
are the arguments above, not conclusions of this computation.

```python
from itertools import combinations
import sympy as s
t,x=s.symbols('t x')
a1,a2,a3,b1,b2,b3=s.symbols('a1 a2 a3 b1 b2 b3', positive=True)
amplitude=x
for denominator,numerator in [(a1,b3),(a3,b2),(a2,b1)]:
    amplitude=numerator*amplitude/(denominator+amplitude)
rho=b1*b2*b3/(a1*a2*a3)
constant=(a2*a3+a2*b3+b2*b3)/(a1*a2*a3)
assert s.cancel(amplitude-rho*x/(1+constant*x))==0
cycle=s.Matrix([[0,-a1,b1],[b2,0,-a2],[-a3,b3,0]])
adj=s.Matrix([[a2*b3,b1*b3,a1*a2],[a2*a3,a3*b1,b1*b2],
              [b2*b3,a1*a3,a1*b2]])
assert cycle.adjugate()==adj
assert s.expand(cycle.det()-(b1*b2*b3-a1*a2*a3))==0
f=s.symbols('f', positive=True)
n=s.symbols('n', integer=True, positive=True)
k=s.symbols('k', integer=True, nonnegative=True)
assert s.simplify(s.summation(-(f/n)**2*(1-k*f/n),(k,0,n-1))
                  -(-f*f/n+f**3*(n-1)/(2*n*n)))==0
G=s.Matrix([[0,3,-1,-1],[3,0,-1,-1],[-1,-1,0,3],[-1,-1,3,0]])
A=s.Matrix([[0,-20,75,-10],[-12,0,-20,24],[36,-16,0,-8],[-15,60,-25,0]])
J=G-A; M=G-t*J
for B in [G,A]:
    assert B.det()>0 and all(value>0 for value in B.inv())
    for size in [2,3,4]:
        assert all(B.extract(S,S).det()!=0 for S in combinations(range(4),size))
assert all(G[i,j]*J[j,i]-G[j,i]*J[i,j]!=0
           for i in range(4) for j in range(i))
assert J.det()!=0
for S in combinations(range(4),3):
    assert J.extract(S,S).det()!=0
    assert s.resultant(M.extract(S,S).det(),M.det(),t)!=0
a,b=s.Rational(21,125),s.Rational(169,1000)
delta=s.expand(M[:3,:3].det())
assert delta==33269*t**3-4200*t**2-275*t+6
assert delta.subs(t,a)<0<delta.subs(t,b)
v=s.Matrix([(15*t+1)*(19*t+1),(19*t+1)*(37*t-1),
            3*(1-5*t)*(15*t+1)])
assert s.expand(M[:3,:3]*v)==s.Matrix([-delta,0,0])
assert 37*a>1 and 5*b<1
outside=s.expand((M[3,:3]*v)[0])
assert outside==45193*t**3-1881*t**2-121*t+9
assert 45193*a**3-1881*b**2-121*b+9>0
print('PASS: global reduction algebra, boundary response, and entire-pencil witness')
```


## Lean handoff and scope

A suitable theorem takes a native reward table, its augmented closure C,
a GLOBAL minimizer of nu on full zero debt with positive nu, and genericity
of the joining block on a proposed three-zero set. Its conclusion is that
this zero set is impossible. The four finite-word constructions should
produce actual prefix sequences, uniform full-cap error bounds and a
strict survival upper bound; the desired descent must not be a supplied
structure field. The global dichotomy and no-UE reduction are consumers. The AllNever
subcase additionally consumes a positive mode on a three- or four-owner
support, with the actual fourth-row quiet comparison when needed. Its
clipped-root degree argument must retain the unique-root premise.

Reusable existing interfaces are the complete cap prefix map, finite root
Nash existence, the stated normalization and terminal-debt endpoint.
Finite algebraic checks include the macrocycle formula, signed-cycle
adjugate, the three homogeneous support cases, and the boundary response
formula. The backward-orbit lemma should retain spectral multiplicity and
nonattainment: neither a dominant eigenvalue nor an actual carrier realizer
is assumed. No fresh Lean checking is claimed here.

The result excludes a global source branch, not an additional numerical
reward family. It does not produce absorbing approximate equilibria in the
remaining all-positive or AllNever alternatives, prove marked-source
descent, or establish unrestricted Fin4 existence.
