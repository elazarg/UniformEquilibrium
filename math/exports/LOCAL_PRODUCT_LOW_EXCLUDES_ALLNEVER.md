# A local Quit-offer sign rule excludes the global AllNever source

## Exact statement

There are four owners I={0,1,2,3}. Independent Continue/Quit choices on
natural dates determine the first nonempty quitting coalition D, which
absorbs at finite rewards Z_i(D). Live play and the event that nobody ever
quits pay zero. Own singleton rewards Z_i({i}) are zero. A unilateral
deviation may replace the owner's entire behavioral strategy. Before
absorption there is one live history per date, so these are independent
first-Quit laws on N union a separate Never point.

Put Gamma_ij=Z_i({j}) and J_ij=Z_i({i,j}) for i!=j, with zero diagonals.
For an actual profile let U be its payoff, B its cap over all finite and
Never replies, e its unilateral Never payoff, and N its original marginal
Never masses. Let C be the Euclidean closure of these tuples, and put

    D=sum_i(B_i-U_i), nu=product_i N_i,
    E=C intersect{D=0}, mu=min_E nu.

The carrier is compact and E contains AllNever. Escaping finite mass is
never relabeled Never. Consider the following raw-table condition:

    There is delta>0 such that every q in[0,1]^4 with
    0<sum_i q_i<delta has an i with q_i>0 and Q_i(q)<=0.     (PL)

Here Q_i(q) is the forced-Quit offer, the expectation of Z_i(D union{i})
over independent opponent quit coins. It is a polynomial of degree at
most three and does not depend on q_i. The vector q in(PL) need not be
Nash or strategically realizable. This is a first-order real polynomial
condition and can be decided by quantifier elimination.

**Theorem.** Under(PL), mu<1, without any genericity assumption.
Equivalently, an AllNever-only source requires arbitrarily small nonzero
hazard vectors for which EVERY active owner's forced-Quit offer is positive.

One finite raw producer of(PL) is the existence of strictly positive weights
d_i satisfying

    d_i J_ij+d_j J_ji<0 for every unordered pair{i,j}.       (W)

Thus the global AllNever-only zero-full-debt source is impossible throughout
this participant-reward region. In particular this holds for every strictly
negative off-diagonal J, with no smallness condition, no assumption on Gamma,
and arbitrary finite higher rewards.

Condition(W) is strict linear feasibility in four positive weights; one
may normalize sum_i d_i=1. It does not assume a root, strategy, continuation
source or equilibrium certificate. The conclusion concerns the complete
carrier; it does not assert that an actual infinite exact Nash law attains
its point, nor prove absorption, zero absorbing gap, or UE for the original
game with positive own levels. The strictly positive global minimum remains
a separate obligation. This is ordinary mathematics.

All strategic objects used in the proof are produced from the reward table:
finite roots by finite-game Nash existence, virtual tails by a separating
linear functional, and macros by the exhaustive three-owner argument below.
No selected root, realizable continuation or comparison strategy is assumed.

## 1. A local sign rule from the raw weights

Normalize sum_i d_i=1 and choose kappa>0 with every pair sum in(W) at most
-kappa. Let M>=1 bound all rewards, and put r=sum_i q_i and
sigma2=sum_(i<j)q_i q_j. The exact identity

    sum_i d_i q_i Q_i(q)
      =sum_(empty!=D subset I) Pr_q(D) sum_(i in D)d_i Z_i(D)

expresses the weighted active Quit offers as the expected weighted reward
of the quitting coalition. Singleton terms vanish. Pair probabilities
sum to at least(1-r)sigma2, and the probability of at least three quitters
is at most r sigma2. Consequently

    sum_i d_i q_i Q_i(q)<=[-kappa(1-r)+M r]sigma2.           (1)

For all sufficiently small r this is negative if at least two owners act.
If exactly one owner acts, that owner's Quit payoff is zero. At any Nash
root, each owner with q_i>0 receives Q_i(q): a proper mixer is indifferent,
and a sure quitter receives Quit. Hence every nonzero sufficiently small
Nash root has at least one nonpositive output coordinate. This sign rule
also holds uniformly under a sufficiently small reward perturbation.

### A complete generic participant classification

Call a principal matrix J_SS an S-matrix when some x_S>0 satisfies
J_SS x_S>0. By common rescaling this is the ordinary linear feasibility
test x_i>=1 and (J_SS x)_i>=1 for every i in S. Suppose every
off-diagonal J entry is nonzero and every principal determinant of sizes
2,3,4 is nonzero. Then, for EVERY finite higher-reward completion,

    (PL) holds iff none of the eleven principal matrices
    J_SS, |S|>=2, is an S-matrix.                          (S)

If J_SS x_S>0, take q_S=t x_S and q_outside=0. Every active Q_i(q) is
positive for small t, so(PL) fails regardless of the higher rewards.

Conversely assume no principal S-matrix exists. There is epsilon>0 such
that the same holds after adding epsilon to every off-diagonal J entry.
Otherwise choose epsilon_n decreasing to zero and one fixed S with
x^n_S>0, sum x^n=1, (J_SS+epsilon_n(offdiag-one))x^n>0. Pass to a limit
x with nonempty support T. If |T|>=2, then J_TT x_T>=0. Invertibility
lets us replace x_T by x_T+eta J_TT^-1 one, still positive for small eta,
making its image strictly positive: a contradiction. If T={j}, each
J_ij for i in S minus{j} is nonnegative by the limiting inequalities,
and hence strictly positive by the off-diagonal assumption. Absence of
a positive pair forces J_ji<0. The j-row of the perturbed product is then
strictly negative for large n, again a contradiction.

For any q, the exact Quit polynomial obeys

    |Q_i(q)-(Jq)_i|<=C(sum_j q_j)(sum_(j!=i)q_j),

where C is finite and depends on the reward table. For small total hazard,
Q_i(q) is at most the i-coordinate of the positively perturbed J times q.
The latter has a nonpositive active coordinate by the absence of principal
S-matrices. Singleton support has its active Q identically zero. This
proves(PL) and the classification. Thus a generic AllNever source requires
one of eleven explicit principal positive directions. Feasibility is a
necessary source condition, not a counterexample or a UE obstruction.

This criterion is strictly broader than(W). For example take the circulant
matrix with cyclic offsets +1,+2,+3 equal to1,-10,-1/2, respectively.
Its full column sums are -19/2, so it is not an S-matrix. Every principal
triple has a row with two negative entries, and no pair is mutually positive.
Its principal triple determinants are -25/2 and its full determinant is
163191/16. Thus(S) applies for every higher completion. But(W) is impossible:
the four positive directed cycle edges would require successively
 d_(i+1)>2d_i, whose product is contradictory.

### Exact classification of the weighted sufficient region

When every off-diagonal J entry is nonzero, condition(W) itself has the
following exhaustive graph test. There must be no mutually positive pair.
Orient an edge i->j when J_ij>0; its reverse is then negative. For every
directed simple cycle, require

    product_(i->j in cycle) J_ij/(-J_ji)<1.                 (CYCLE)

Only cycles of length3 or4 can occur. Necessity follows by multiplying
d_j/d_i>J_ij/(-J_ji). Conversely take logarithms. Strictly negative total
weight on each cycle permits adding one small common positive margin to
all edge weights while every cycle total remains negative. Maximum path
weights from an auxiliary source are finite (cycles can be deleted), and
supply potentials x_j-x_i strictly above the original edge weights. Set
d_i=exp(x_i). Mutually negative pairs impose no constraint. This proves(W).
In particular acyclic positive-edge graphs are covered at arbitrary reward
magnitudes; a positive cycle with product at least one fails this weighted
criterion, though it may still pass(S) as the preceding example shows.

For direct boundary tests, all-negative J uses d=one. A positive triangle
with forward entries1 and reverse entries-2 also uses d=one, with all pairs
to the fourth owner negative. Reversing those magnitudes makes its cycle
product8 and rules out(W); equality of the magnitudes gives the excluded
strict boundary. If all grand-coalition recipient rewards are positive,
q=one has all Q_i>0, so the global product-low condition fails even though
these local criteria can hold. No claim is made that a particular higher
completion escapes every existing UE theorem.

The genericity in(S) is necessary. Take cyclic offsets1,-1/2,-1/2.
All off-diagonal entries and proper principal determinants are nonzero,
but det J=0 and J one=0. Again no principal matrix is S: pairs have no
mutually positive entries, triples have a wholly negative off-diagonal row,
and the full column sums are zero. Give every owner reward1 whenever its
quitting coalition has size at least three. At q=t one every active offer
is Q_i(q)=3t^2-2t^3>0 for0<t<1. Thus(PL) fails. If instead all those
higher participant rewards are zero, then for proper q,
Q_i(q)=product_(j!=i)(1-q_j) (J x)_i with x_j=q_j/(1-q_j).
The absence of principal S-matrices then proves(PL). On this singular
boundary the same J can therefore admit or fail(PL), depending on the
higher rewards. The unrestricted theorem under(PL) includes both generic
and nongeneric data; only the eleven-test equivalence requires genericity.

These exact boundary calculations can be reproduced with Python and SymPy;
the inequalities certifying absence of principal S-matrices are explicit
rows or column sums, so no numerical feasibility solver is needed.

```python
from itertools import combinations
import sympy as s

half = s.Rational(1, 2)
t = s.symbols('t')
def circulant(offsets):
    return s.Matrix(4, 4, lambda i, j: 0 if i == j else offsets[(j-i-1) % 4])

for middle, determinant, triple, colsum in [
    (-10, s.Rational(163191, 16), -s.Rational(25, 2), -s.Rational(19, 2)),
    (-half, 0, -s.Rational(5, 8), 0),
]:
    J = circulant([1, middle, -half])
    assert J.det() == determinant
    assert all(sum(J[:, j]) == colsum for j in range(4))
    for pair in combinations(range(4), 2):
        i, j = pair
        assert not (J[i, j] > 0 and J[j, i] > 0)
        assert J.extract(pair, pair).det() != 0
    for triple_set in combinations(range(4), 3):
        A = J.extract(triple_set, triple_set)
        assert A.det() == triple
        assert any(all(A[i, j] < 0 for j in range(3) if i != j)
                   for i in range(3))
    assert (1 / half)**4 == 16  # four-cycle obstruction to (W)
    if determinant == 0:
        assert J * s.ones(4, 1) == s.zeros(4, 1)
        offer = sum(J[0, j] for j in range(1, 4))*t*(1-t)**2
        offer += 3*t**2*(1-t) + t**3
        assert s.expand(offer) == 3*t**2 - 2*t**3
print('Exact participant boundary checks passed.')
```

## 2. AllNever supplies a signed strict drift functional

Assume for contradiction mu=1. Then every zero-debt point has nu=1 and
U=B=e=0. In particular Gamma is R0: there is no nonzero v>=0 with
Gamma v>=0 and v_i(Gamma v)_i=0.

Here is the needed proof. Otherwise normalize sum v_i=1, fix a>0, and
repeat q=epsilon v for floor(a/epsilon) dates, then use AllNever. One-date
passive offers satisfy P_i=epsilon(Gamma v)_i+O(epsilon^2), and every Quit
offer is O(epsilon). For active owners the leading passive term vanishes,
so prescribed payoffs and every complete response differ by O(epsilon)
after the whole word. For inactive owners the leading passive term is
nonnegative; quitting early loses the remaining leading passive payments
and can gain only O(epsilon)+O(number_of_dates*epsilon^2). Thus all debts
tend to zero. Original joint Never tends to exp(-a), contradicting mu=1.
These estimates are uniform over all finite deadlines and Never, and hence
over complete randomized replies.

In particular no nonnegative nonzero vector lies in ker Gamma. Thus zero
is outside the compact convex hull of the four columns of Gamma. Let z be
the closest point of that hull to zero. Then z!=0 and

    lambda=z^T/|z|^2 satisfies lambda Gamma e_j>=1 for all j. (2)

Indeed the directional derivative toward any column is nonnegative at z.
The row vector lambda may have mixed signs; its positivity is not assumed.
Also every Gamma column has a negative entry, since a nonnegative column
would itself give a homogeneous complementary vector. Fix one column v.
Then min_i v_i<0 and lambda v>0.

This yields an exact finite-word drift estimate. Allow a nearby reward
table Y with lambda Gamma_Y e_j>=c>0, and let L0=M|lambda|_1 bound every
absolute scalar reward |lambda Z_Y(D)|. For a finite prefix word of joint
survival nu_P=exp(-a), independence gives

    Pr(prefix absorbs at a nonsingleton coalition)
      <=sum_(i<j)(1-N_i(P))(1-N_j(P))<=a^2/2.

Indeed a collision requires two owners to have finite prefix clocks, and
sum_i(1-N_i(P))<=sum_i(-log N_i(P))=a. Every singleton scalar reward is
at least c. Applying the prefix to any tail payoff w therefore gives

    lambda U'-lambda w
      >=(1-exp(-a))(c-lambda w)-(c+L0)a^2/2.                (3)

For |lambda w|<=c/4 and sufficiently small a>0, uniformly,

    lambda U'-lambda w>=c a/4>0.                           (4)

For example choose a<=min(1,c/[4(c+L0)]), using 1-exp(-a)>=a/2.
No Nash condition, intermediate-state estimate or bounded calendar length
is used. The inequality also passes to bounded-activity word limits.

Throughout, the activity of a finite word P is
a(P)=-log nu_P=sum_(dates,i)-log(1-q_i). Its total hazard is the different
quantity sum_(dates,i)q_i. When every hazard is at most1/2, total hazard
is at most a(P), which is at most twice total hazard.

## 3. Virtual terminal payoffs and a global compact gap

Fix a reward table Y close to Z, using a common reward bound M>=1 throughout
this neighborhood. We will perturb only participant pair
rewards DOWNWARD, keeping Gamma and every other reward fixed.
For a vector b v, regard a finite calendar as ending at a terminal outcome
that pays b v if everybody survives it. The only terminal reply is Never;
finite replies are the dates in that calendar. This is an auxiliary finite
game, not a change of the original game's literal Never convention.

Let P_i(q) be the expected passive reward on nonempty opponent quitting
coalitions, H_i(q)=product_(j!=i)(1-q_j), and h(q)=product_i(1-q_i).
Initialize (U,B,e,N)=(b v,b v,b v,one). A root q prefixes any tuple by

    U'_i=q_i Q_i+(1-q_i)P_i+h U_i,
    B'_i=max(Q_i,P_i+H_i B_i),
    e'_i=P_i+H_i e_i, N'_i=(1-q_i)N_i,                      (5)

Let C_b^Y be the closure of outputs of
ALL finite words under(5), including the empty word. Values are bounded,
so C_b^Y is compact. It is closed under every fixed finite prefix. For
every point in it,

    B_i-U_i>=N_i(B_i-e_i)>=0.                              (6)

This is the average over the owner's finite replies and its Never reply.
If D=0 and nu>0, it gives U=B=e. For any finite word or carrier limit,

    |U|_infinity<=M(1-nu)+b|v|_infinity.                   (7)

Every prefix map is nonexpansive in its respective tail U,B,e coordinates.
Replacing b v by zero therefore changes every U and B by at most b|v|,
uniformly over word length. With zero tail, the tuple is the actual
native tuple: all later finite replies equal Never because own singletons
are zero. Changing Y back to Z changes every payoff and full cap by at
most |Y-Z|_infinity. Consequently a virtual carrier point with D=0 and
joint Never nu yields an actual Z-carrier point with the same nu and

    D_Z<=8(b|v|_infinity+|Y-Z|_infinity).                   (8)

Choose tau>0 below delta in(PL) and small enough for(4), uniformly in
the chosen reward neighborhood where lambda Gamma_Y e_j>=c>0. Also choose
M tau |lambda|_1<=c/4. After b is made small, (7) then gives
|lambda U|<=c/4 whenever nu>exp(-tau/2). No root-size estimate is needed.

Since mu=1, compactness of the ORIGINAL carrier gives

    gamma=min{D_Z(X): X in C, nu(X)<=exp(-tau/2)}>0.         (9)

Choose Y and b>0 so small that the right side of(8) is below gamma.
Then EVERY zero-debt point of C_b^Y satisfies

    nu>exp(-tau/2).                                       (10)

This applies globally, with no calendar-length or activity restriction on
C_b^Y. It is the margin that prevents a prefix from leaving the small
region. We perturb only the twelve participant pair rewards DOWNWARD, inside an
arbitrarily small open rectangle J_ij-epsilon<J_Y,ij<J_ij, so that
L=J_Y-Gamma has all off-diagonal entries and all principal triple
determinants nonzero. These finitely many nonvanishing polynomial conditions
are dense in those twelve independent entries. Each Q_i^Y is pointwise at
most Q_i^Z: only exact-one-opponent coalition rewards decreased. Thus even
the weak property(PL), with its SAME delta, is preserved. Gamma, lambda,
and the fixed seed v are unchanged. No old selected source is transported.

## 4. A maximal virtual source

Let F={X in C_b^Y: D(X)=0, min_i U_i<=0}. It is nonempty: the empty word
has payoff b v with a negative coordinate. It is compact. Maximize
Phi(X)=lambda U on F. The maximum is positive, since lambda b v>0.
Write its payoff as w. Equations(6),(10) give U=B=e=w and w!=0.

Take ANY finite-game Nash root against continuation w. Such a root exists.
Prefixing it preserves zero debt by(5). By(10), the NEW joint Never still
exceeds exp(-tau/2); hence this root is proper and its total activity is
less than tau/2. If it is nonzero, the sign rule(PL) makes its output have
a nonpositive coordinate, so the prefixed point belongs to F. Equation(4)
strictly increases Phi, a contradiction. Thus AllContinue is the only
Nash root against w. In particular w>=0. Since w!=0 and min w<=0, it has
one, two or three zero coordinates.

One zero j permits a small solo-j Nash root: j is indifferent and every
other owner's positive continuation strictly favors Continue. If precisely
i,j are zero and L_ij<=0 or L_ji<=0, a small solo root also works. If both
are positive, lower both zero continuations to -epsilon and choose Nash
roots. Uniqueness at w forces these roots to tend to zero. Positive
outsiders are quiet. But the two active gaps are

    Quit_i-Continue_i=epsilon(1-q_j)+L_ij q_j>0,

and its reverse, forcing both owners to quit surely, a contradiction.
Thus only three zero coordinates need further treatment.

## 5. Local escape from three zero coordinates

Write w=b0 e_p, b0>0, and T=I minus{p}. AllContinue is the unique Nash root
at w, and the downward perturbation gives joining-genericity and(PL).
Throughout this section G=(Gamma_Y)_T, J=(J_Y)_T and L=J-G.
There is a sequence of finite words on T, with total
activity as small as prescribed but bounded positively away from zero,
whose endpoints from the diagonal w have debt tending to zero and a limit
with a nonpositive payoff coordinate. The pivot stays exactly on Continue.
This statement is local; no original source-minimum premise is used.

Choose a total hazard ceiling s>0 so small that it is below tau/8 and the
root payoff changes in the pivot are below b0/8. Its Continue cap then
stays positive and exceeds every pivot Quit offer, whose absolute size is
at most M times one-date activity. The following four mechanisms all fit
this ceiling, after choosing their amplitudes sufficiently small.

(a) If G is not R0, repeat epsilon v for a nonnegative complementary vector
v as in Section2, for floor(s0/epsilon) dates with fixed small s0>0.
Observer debts tend to zero. At least one active observer has limiting
payoff zero, so the endpoint has a zero coordinate. Survival tends to
exp(-s0), strictly below one.

(b) If G^-1 is strictly positive, row/column mixing makes G a strict signed
three-cycle. Write G_i,next(i)=-A_i<0 and G_i,prev(i)=B_i>0. Its explicit
cofactors are positive, and rho=product B_i/product A_i>1. From x e_i,
a solo-next(i) macrohazard x/(A_i+x) kills coordinate i and transfers
positive value to the remaining observer. Three such transfers return
to the same axis by F(x)=rho x/(1+C x), C>0. Indeed composing three maps a_s x/(1+b_s x), with a_s,b_s>0,
gives C=b_1+b_2 a_1+b_3 a_1 a_2>0. Choose a small a>0 with
F(x)>=r0 x for 0<x<=a and 1<r0<rho. Its inverse iterates x_-m tend
geometrically to zero; the words from x_-m to a have bounded small total
activity and a fixed positive final hazard.

Split each macrohazard q into tiny microhazards
eta_l=q/(ell-lq), 0<=l<ell, whose survival product is1-q. Throughout a
macrostep the observer Continue payoffs are nonnegative and the mover's
payoff is zero. Writing d_i=B_i-U_i, a quiet observer has
d_i'<=max(J_ij eta-U_i',(1-eta)d_i)<=max(M delta,d_i); the mover's
debt is unchanged. Thus all observer
debts are at most M delta when all microhazards are <=delta, independently
of word length. Apply the same words to zero observer tails; their initial
mismatch x_-m tends to zero, and prefix nonexpansiveness preserves that
bound. Let delta tend to zero with m. The limiting endpoint is the axis
a e_i and has two zero observer coordinates.

(c) If for some 0<t<1 a column j of G-tJ is nonnegative, take f>0 small
and chronological solo-j hazards q_n=t R_n/S_n, where
R_n=f(1-t)^n and S_n=1-f+R_n. The virtual suffix payoff of observer i!=j
is G_ij R_n/S_n and that of j is zero. Continue equals this value and
Quit is tJ_ij R_n/S_n, so every observer comparison is exact. Truncations
have tail mismatch tending to zero. Total activity is small for small f,
survival tends to1-f<1, and the mover's payoff remains zero.

(d) If L^-1 J has v>0 with eigenvalue rho>1, let
z_i(q)=(Q_i(q)-P_i(q))/H_i(q) on T and s_i(q)=Q_i(q). These have derivatives
L and J. The local analytic map F=z^-1 composed with s has derivative
L^-1 J. The signed backward-orbit lemma below gives positive proper q_n,
n<=0, with F(q_n)=q_(n+1) and q_n=a rho^n v+O(a^2 sigma^n),
rho<sigma<rho^2. Their total activity is arbitrarily small and their last
root q_0 is nonzero. Prefix q_-m,...,q_0 in construction order from virtual
observer tail z(q_-m), and then transfer the same finite word to zero.
The mismatch tends to zero. Every observer is exactly indifferent in the
virtual calculation, and the endpoint is s(q_0). By(PL), at least one of
its active observer coordinates is nonpositive when a is small. No action is
placed after an infinite prefix.

Here is why at least one mechanism occurs. Every column of L has a positive
entry, or a small solo root would contradict the assumed root uniqueness
at w. Joining-genericity makes K=-L R0: singleton supports are blocked by
those column signs, pair supports by nonzero reciprocal entries, and full
support by det L!=0.

Replace the three zero continuations by epsilon z, for arbitrary z, and
choose Nash roots. They tend to zero by root uniqueness at w, and the pivot
is quiet. Their observer comparisons are

    q>=0, c=epsilon z-Lq+O(|q|^2+epsilon|q|)>=0,
    q_i c_i=0.

An unbounded q/epsilon would give a nonzero homogeneous solution for K.
Thus a cluster of q/epsilon solves LCP(K,z), for every z: K is standard Q.
At z=-one, Kx>=one. Each row of L therefore has a negative entry; each
column already has a positive entry. The six positions force a strict
signed cycle L_i,next=a_i>0, L_i,prev=-b_i<0. Positivity of Kx implies
x>0 and product b_i>product a_i. Hence K^-1 is strictly positive and its
R0 degree is1: at offset-minus-ones the sole complementary root is its
positive full-support root, of positive determinant index.

If(a) or(b) holds, we are done. Otherwise consider G-tJ, 0<=t<=1.
A homogeneous complementary crossing at 0<t<1 has a singleton, pair or
full support. A singleton gives(c). A pair forces both reciprocal entries
to vanish; its third-row inequality makes one column nonnegative, again(c).
A full support gives v>0 with (G-tJ)v=0, hence L^-1J v=v/(1-t), giving(d).
If no such crossing occurs, the whole pencil is R0, because its endpoints
G and K are R0. The homogeneous map min(x,(G-tJ)x) has a positive lower
bound on the unit sphere, uniformly on this compact pencil. Homotopy
preserves degree1. Adding bounded offsets on a sufficiently large sphere
then makes G standard Q. At offset-minus-ones this forces every row of G
to have a positive entry. R0 forces every column to have a negative entry.
Again the six positions form a strict signed cycle, now with positive
cycle product larger than the negative cycle product. Its inverse is
strictly positive, contradicting the exclusion of(b). The cases exhaust
the three-zero obstruction.

## 6. The signed backward-orbit lemma used above

Let F be C^2 near zero, F(0)=0, A=DF(0), and A v=rho v with rho>1 and v!=0.
Write F(x)=Ax+R(x). Choose rho<sigma<rho^2 away from all eigenvalue moduli
and split real invariant spaces below/above sigma. Equivalent norms give
|A_s|<=alpha_s<sigma<alpha_f and |A_f^-1|<=1/alpha_f. On sequences n<=0
use norm sup sigma^-n|x_n|. For forcing f_k, k<0, define

    (Gf)^s_n=sum_(k=-infinity)^(n-1) A_s^(n-1-k)f^s_k,
    (Gf)^f_n=-sum_(k=n)^(-1) A_f^(n-1-k)f^f_k.

Its norm is at most 1/(sigma-alpha_s)+1/(alpha_f-sigma), and
(Gf)_(n+1)-A(Gf)_n=f_n. Put y_n=a rho^n v. On a sufficiently large ball
|x|_sigma<=C a^2, x->G(R(y+x)) maps the ball into itself and contracts
for small a: use rho^(2n)<=sigma^n<=rho^n and the C^2 remainder estimates.
The fixed point gives q_n=y_n+x_n and the claimed recurrence. For v>0,
small a makes all q_n positive. This argument permits signed derivatives,
repeated eigenvalues and faster eigendirections.

## 7. Finish the compact maximum contradiction

Apply Section5's words to the maximizing point X in C_b^Y. Prefixing a
fixed word preserves C_b^Y. The local calculations use only its diagonal
w, so their debts tend to zero; total activity is bounded away from zero
and can be kept below tau/4. Apply the WHOLE-WORD estimate(4) once to
each macro, starting at w. It gives a fixed strictly positive increase
of Phi, with no intermediate-state estimate. Pass to
a compact subsequential endpoint. It belongs to C_b^Y, has zero debt and
a nonpositive coordinate, so it belongs to F, contradicting maximality.

For clarity, arbitrarily long macros cause no hidden composition issue.
For each macro first approximate X by a finite word sufficiently accurately.
Uniform prefix nonexpansiveness preserves that error independently of the
macro length. Diagonal choice then gives actual finite words in the same
virtual carrier with exactly the limiting payoff, cap and original-Never
annotations used above. No incompatible realization is reused.

This contradiction disproves mu=1 at the ORIGINAL table Z. The joining
genericity was imposed only on the arbitrarily close auxiliary table Y;
the compact original gap(9), transfer estimate(8), signed drift and(PL)
persist. Thus no genericity, nonsingularity or inverse sign assumption
remains in the theorem.

## Actual-source consumer and formalization boundary

A signed Fin4 counterexample supplies a table R, still without UE, whose
own singleton vector is one at a pivot p and zero elsewhere, through
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`.
The declaration `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
in `UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean` supplies
Delta=inf D_R>0 over all actual profiles. Define the native table by
Z_i(D)=R_i(D)-1_(i=p) on NONEMPTY coalitions; literal Never remains zero.

At nonnegative own singleton, finite deadlines tending to infinity have
payoff tending to Never plus own singleton times opponents' joint Never,
by `quittingTerminalPayoff_update_finiteTime_tendsto_of_profile` in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`.
Hence finite replies determine the full cap, both before and after the
subtraction. Every finite pivot reply loses exactly one. On an absorbing
prescribed profile its payoff also loses one, preserving every debt. Thus

    A=inf{D_Z(P): P actual, nu(P)=0}>=Delta>0.

Move the smallest original Never mass n to one finite date. The resulting
profile absorbs. Coupling changes four prescribed payoffs and three
other-owner caps by at most2M n each; the mover's own cap is unchanged.
Since n<=nu^(1/4), also on the closed native carrier,

    A<=D_Z+14M nu^(1/4), hence mu>=(A/(14M))^4>0.

The present theorem adds mu<1 whenever(PL), in particular(W) or the
generic criterion(S), holds. It excludes the AllNever-only source for
these native tables, without asserting an absorbing equilibrium or
repairing the remaining positive global source.

The weighted Quit identity is already represented by
`quittingQuitProbability_mul_quitPremium_eq_sum_terminalPremium` in
`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremium.lean`.
The new use is local: higher contained-coalition rewards are unrestricted
under the strict pair criterion, unlike a global product-low guard.
In particular `IsSupportwiseBalancedQuittingPremiumTable` in that file,
consumed by `exists_uniformEquilibriumPayoff_of_supportwiseBalance` in
`UniformEquilibrium/Quitting/Classification/Existence/SupportwisePremiumUniformPayoff.lean`,
requires weighted participant inequalities on every contained coalition for
each support. Positive grand-coalition participant rewards prevent its full-support
certificate, while the present local criterion may still hold. The new
mathematics is the compact original-gap argument that forces all zero-debt
virtual prefixes into the small region where the local rule applies.
The exact cap-prefix recursion used here is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`; finite root
existence is `exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`.
The missing formalization is the virtual compact carrier, the global-gap
transfer and signed drift maximum, plus the local zero-face macro lemma.
No selected root, source realization or favorable clock is an input field.
