# Reflection and multi-affine exclusions for universal quitting potentials

Date: 2026-09-09.

Status: ordinary mathematical proofs developed in this response. Not independently
reviewed or Lean-checked. No repository source, branch, commit, or PR was changed.
The companion Python file checks finite identities and boundary cases only.

## 1. Output and scope

Let there be n >= 2 players. Assume every terminal reward satisfies
|r_i(S)| <= 1 and every own singleton s_i = r_i({i}) is nonnegative.
All live and Never rewards remain zero. Define the annotation box

    K = [-3,3]^n.

For a product root q in [0,1]^n, let pi_q(S) be its independent coalition
probability, A(q) = 1 - pi_q(empty) its absorption, and

    F(v,q) = pi_q(empty) v + sum_{S nonempty} pi_q(S) r(S).

A root is exact Nash against v when no player improves its one-stage expected
payoff by changing its own root action, with continuation v on all Continue.
These are the root inequalities of the full robust relation; they are not
claimed to bound full behavioral deviations by themselves.

Consider the universal exact-root inequality

    P(v) - P(F(v,q)) >= A(q)                         (E)

for every v in K and EVERY exact Nash root q against v.

**Theorem A (quadratics).** No real polynomial P of total degree at most two
satisfies (E). This includes indefinite and degenerate quadratics.

**Theorem B (multi-affine functions).** No real polynomial affine separately
in each coordinate satisfies (E). In four players this excludes every
linear combination of the sixteen square-free monomials, including arbitrary
triple and four-coordinate interaction terms.

Neither theorem assumes standard Q, R0, punishment normality, the existence
of a behavioral continuation realizing v, or any restriction on nonsingleton
rewards other than the stated bound.

**Theorem C (radial reversal).** Suppose P is continuous on K, differentiable
on a neighborhood of the part of K above s, and satisfies (E). For EVERY
global minimum a of P on K, there is x >= s in K such that x_i=s_i for
some i, 2x-a is in K, and

    gradient P(x) dot (x-a) <= -delta/2 < 0,
    delta = min_i (a_i-s_i) > 0.                     (RR)

The entire segment from a through x to 2x-a stays in K. Thus P must rise
and then fall along a ray starting at each of its global minima. Quasiconvexity
is not used in this conclusion.

If P is C3 on a neighborhood of K, put d=x-a and f(t)=P(a+td). Then

    max_{0<=t<=2} D^3 P(a+td)[d,d,d] >= 3 delta.      (T3)

This derivative is directional, not necessarily a mixed coordinate derivative.
Its location may be outside the region above s, but is always in K.

Theorems A and B also exclude every C1 monotone scalar transform of a
quadratic or multi-affine polynomial. An exact proof is in Section 7.

### Conjecture-facing meaning

The existing polynomial characterization has box radius rewardBound+2.
For tables bounded by one, this is exactly K. Every robust potential also
satisfies (E), since exact roots and their exact successors have zero root
regret and zero Bellman residual. Therefore these results apply to the
ACTUAL full certificate language, not a selected orbit or face-only surrogate.

In the normal, positive-singleton class of that characterization, adding
“total degree at least three and not multi-affine” to its existential
certificate clause preserves its equivalence. Every such certificate also
satisfies (RR) and (T3).

A decision representative with nonnegative own singletons can be commonly
scaled so all rewards lie in [-1,1]. This common positive scaling preserves
Never=0 and scales all gains and punishment values. The positive own singleton
need not remain numerically one. The argument does NOT use a terminal-only
translation as strategic equivalence. It also does not say that scaling a
particular certificate automatically preserves its fixed-box domain.

This excludes certificate classes. It produces no new class of games with
uniform equilibria, no arbitrary-table strategy selector, and no positive-gap
counterexample. In particular, cubic and higher-degree polynomials with
repeated-coordinate terms remain unexcluded in general.

## 2. Dependencies, credited separately

The uploaded `QUITTING_POTENTIAL_SHAPE_EXCLUSIONS(2).md` supplies the exact
full-root setting, collision-adjusted singleton probes, and the fact that
global box minima of a full potential lie strictly above the singleton vector.
Those two elementary facts are reconstructed in Section 3, not claimed as
new here. Its quasiconvex exclusion does not by itself exclude an indefinite
quadratic or a coupled, nonquasiconvex multi-affine polynomial.

The exact declaration read through the GitHub connector was

    quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential
    UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean

It quantifies over Fin 4, a bound on all terminal rewards, punishment normality
for every player, and a positive own singleton. The potential is a rational
polynomial on the full robust relation with a positive rational tolerance
at most 1/4 and box radius rewardBound+2. Its forward implication constructs
that polynomial; the present arguments assume no additional polynomial producer.

The repository main head inspected in this turn was
`5aac30ad2553dadd5895dc79fbc4f1f5680d7570`. This is source inspection, not
compilation or a theorem-level axiom audit. A bounded code search did not
establish any worldwide novelty claim.

The new steps are the minimum-dependent rectangle, its radial reversal and
reflection argument, the multi-affine corner comparison, and their consequences.
Only ordinary finite-game Nash existence is needed to obtain a root at a
minimizing annotation. No topological degree or LCP existence theorem is needed.

## 3. The two existing geometric facts, with complete proofs

Write r^i=r({i}).

### 3.1 Collision-adjusted face drift

For every x in K with x>=s and x_i=s_i,

    gradient P(x) dot (x-r^i) >= 1.                    (F)

To prove it, let only owner i quit with probability h>0. Put d_i=0. For j!=i
with x_j<3 put

    Delta_j = r_j({i,j})-r_j({i}),
    d_j=max(Delta_j,0),

and set d_j=0 when x_j=3. Define

    v^h = x + h d/(1-h),
    u^h = (1-h)v^h+h r^i.

For all sufficiently small positive h, v^h is in K. Each coordinate below
three has a fixed positive margin to the upper boundary. Coordinates at
three were deliberately frozen. The successor u^h is also in K by convexity.

The owner is indifferent because its two pure endpoints are s_i and v_i^h=s_i.
For a nonowner below the upper boundary, Continue minus Quit is

    (1-h)(v_j^h-s_j)-h Delta_j
      = (1-h)(x_j-s_j)+h(max(Delta_j,0)-Delta_j) >= 0.

At an upper coordinate it is (1-h)(3-s_j)-h Delta_j, positive for small h
because 3-s_j>=2. Thus this is an EXACT Nash root, including the collision
reward and all intersecting lower or upper faces. Its charge is h.

Now v^h=x+hd+O(h^2), while u^h=x+h(d+r^i-x) exactly. Dividing (E) by h
and taking the limit proves (F). The common displacement d cancels. An
unadjusted solo root at x would generally fail the nonowners' joining tests.

### 3.2 Every global minimum lies strictly above s

Let a minimize P on K. Select any exact Nash root q against a. Its successor
is in K. Therefore

    0 <= A(q) <= P(a)-P(F(a,q)) <= 0.

Consequently q is all Continue. Its Nash inequalities give a_i>=s_i.
If a_i=s_i, apply (F) at a. The feasible segment from a to r^i is in K,
so minimality gives gradient P(a) dot (r^i-a)>=0, contradicting (F).
Hence

    a_i>s_i for EVERY i.                               (M)

The same argument applies to every global minimum, not just a selected one.
It does NOT prove that a lies in the interior of K: some coordinates may
still equal three. That distinction is essential in the next proof.

## 4. The minimum-dependent rectangle and radial reversal

Fix a global minimum a and set

    b_j=max(a_j,1),
    D_a=product_j [s_j,b_j],
    B_a={x in D_a : x_i=s_i for some i}.

Every interval has positive length by (M). The point a lies in D_a and
strictly above every lower face. Every singleton reward obeys

    r_j^i<=1<=b_j.

Choose x minimizing P on the compact set B_a and write J={j:x_j=s_j}.

If J={i}, variations in any coordinate j!=i stay on the same lower face.
Thus g_j=partial_j P(x) is zero at an interior coordinate and nonpositive
at an upper coordinate. The own term in g dot (x-r^i) is zero. All remaining
upper-coordinate factors b_j-r_j^i are nonnegative. It follows that

    g dot (x-r^i)<=0,

contradicting (F). Therefore |J|>=2.

Because at least two lower coordinates bind, every permitted one-coordinate
variation remains in B_a. One-sided minimality now yields

    g_j>=0  if x_j=s_j,
    g_j=0   if s_j<x_j<b_j,
    g_j<=0  if x_j=b_j.                                (S)

For any i in J, the upper contributions to g dot (x-r^i) are nonpositive,
and the interior contributions vanish. The lower coefficients satisfy
s_j-r_j^i<=2. Combining (F) with (S) gives

    1 <= g dot (x-r^i) <= 2 sum_{j in J} g_j,
    sum_{j in J} g_j >= 1/2.                            (L)

Let delta=min_j(a_j-s_j)>0. At lower coordinates a_j-x_j>=delta. At upper
coordinates a_j-x_j=a_j-b_j<=0, which multiplies a nonpositive derivative.
All interior derivatives vanish. Consequently

    g dot (a-x) >= delta sum_{j in J} g_j >= delta/2.     (R)

This establishes the strict radial reversal, apart from its box assertion.

### The reflected point really is in the source box

Put y=2x-a. For each j,

    y_j >= 2s_j-a_j >= -a_j >= -3,

where nonnegative s_j is used. In the other direction,

    y_j <= 2b_j-a_j
         = max(a_j,2-a_j) <= 3,

since 0<a_j<=3. Thus y is in K. Convexity puts the entire segment a+td,
0<=t<=2, d=x-a, in K.

Using the original upper bound three for D_a would be wrong: 2*3-a_j
can exceed three. The adaptive choice b_j=max(a_j,1) simultaneously keeps
the gradient signs, dominates the reward columns, contains a, and makes
the reflection admissible. It handles boundary minima a_j=3 without
assuming their gradients vanish.

Since a is a global minimum, the univariate function f(t)=P(a+t(x-a))
satisfies f(t)>=f(0) on [0,2]. Yet f'(1)<=-delta/2. In particular its
maximum on [0,1] is attained at an interior point: for small positive e,
f(1-e)>f(1)>=f(0). This is an actual rise-and-fall property along a ray
from each global minimum. It completes Theorem C's C1 part.

## 5. Quadratic exclusion and the third-derivative account

For every quadratic polynomial, regardless of the signature or rank of its
Hessian,

    P(2x-a)-P(a) = 2 gradient P(x) dot (x-a).             (Q)

The left side is nonnegative by global minimality and the reflected-box
proof. The right side is at most -delta by (R). This contradiction proves
Theorem A. No inference from a local minimum to global convexity is made.

For C3 P, apply the exact midpoint derivative identity to f(t)=P(a+td):

    [f(2)-f(0)]/2-f'(1)
      = (1/4) integral_0^2 (1-|t-1|)^2 f'''(t) dt.      (I)

It follows by integrating by parts on [0,1] and [1,2], or by the symmetric
Taylor formula with integral remainder. The left side is at least delta/2.
The nonnegative kernel on the right has total mass 1/6. Thus

    max_{0<=t<=2} f'''(t)>=3delta,

which is (T3). The quadratic contradiction is the zero-third-derivative case.

The quantity delta depends on the potential's chosen minimizing point. This
is not a table-uniform coefficient bound, and no lower bound for delta
independent of P is claimed. It is also not a claim about the sign of an
individual mixed coordinate derivative.

## 6. The independent multi-affine exclusion

Suppose P is affine separately in each coordinate. Successively minimizing
in each coordinate shows that P attains its minimum on K at a vertex.
By (M), no minimizing vertex can have a coordinate -3. Therefore the top
vertex t=(3,...,3) is a minimizing vertex, and every other vertex has a
strictly greater value.

For A subset of the players let t^A flip precisely the coordinates in A
from three to minus three, and put

    c_A=P(t^A)-P(t).

Then c_empty=0 and c_A>0 for every nonempty A. Choose i minimizing the
singleton corner cost c_{i}. Let x_i=s_i and x_j=3 for j!=i, and put

    theta=(3-s_i)/6,       0<theta<=1/2.

Multi-affinity gives

    P(x)-P(t)=theta c_{i}.

If x^{-j} additionally flips coordinate j!=i to minus three, then

    P(x^{-j})-P(t)=(1-theta)c_{j}+theta c_{i,j}.

The exact affine secant formula in coordinate j therefore gives

    partial_j P(x)
      = [theta c_{i}-(1-theta)c_{j}-theta c_{i,j}]/6 < 0.

Indeed c_i<=c_j, theta<=1/2, and c_{i,j}>0. In the face drift for owner i,
the own coefficient is zero and every other coefficient is
3-r_j^i>=2. Thus

    gradient P(x) dot (x-r^i)<0,

contradicting (F). This proves Theorem B. It does not depend on Theorem A
or on any Hessian-sign assertion.

Both Theorems A and B are unchanged when the right side of (E) is k A(q)
for any fixed k>0, by rescaling P. Zero charge coefficient would not suffice.

## 7. Monotone scalar transforms and rational rejection

Let Q be quadratic or multi-affine and suppose P=Phi(Q), where Phi is C1 and
monotone on the compact interval Q(K). If Phi is nondecreasing, let
H=max_{Q(K)} |Phi'|. If H=0, P is constant and cannot satisfy (F).
For a positive-charge exact edge, (E) and monotonicity give Q(v)>Q(F(v,q));
the mean value bound then gives

    Q(v)-Q(F(v,q)) >= A(q)/H.

The same inequality is automatic at zero-charge identity edges. This makes
H Q a forbidden unit-charge potential. If Phi is nonincreasing, apply the
argument to -Q. Hence such compositions are excluded too. This covers
high-degree examples such as the cube of an indefinite quadratic; it does
not cover arbitrary nonmonotone outer maps.

For rational reward data and a rational polynomial in either excluded class,
there is a rational rejecting edge for every supplied rational tolerance
0<tau<=1/4 in the FULL ROBUST relation. To see this, failure of (E) gives a
real v and exact q with positive absorption and strict inequality

    P(v)-P(F(v,q))<A(q).

Approximate v within K and q within its strategy cube by rational points.
Root defects are continuous and initially zero, while tau A(q)>0. The strict
potential violation persists, and the nearby root defects are below tau
times its positive absorption. Set u=F(v,q) for the approximating rational
data, so the successor is rational, boxed, and has zero Bellman residual.

Consequently, enumeration of rational v and q, evaluating this exact u,
eventually rejects every proposed rational quadratic or multi-affine
certificate. All acceptance/rejection tests are rational polynomial
calculations and finite endpoint maxima. This is a candidate-rejection
procedure, not a bounded-denominator result or an equilibrium construction.
The rational root produced by approximation is robust-approximate Nash;
it is NOT asserted to remain exact Nash.

## 8. Why face-only checks do not prove the quadratic result

Use the normalized paired singleton gaps

    Gamma=(1/4) [0 3 -1 -1; 3 0 -1 -1;
                  -1 -1 0 3; -1 -1 3 0],
    s=(1/4,1/4,1/4,1/4),       y=v-s.

The singleton rewards lie in [0,1]. Define the indefinite quadratic

    Q(y)=-4 sum_i y_i
         +64(y_0 y_1+y_2 y_3)
         +16(y_0+y_1)(y_2+y_3).

On face y_i=0, write t for the partner's coordinate and u,v for the two
opposite-pair coordinates. Direct expansion gives

    gradient Q(y) dot (y-Gamma_i)
      =1+4t+32t(u+v)+128uv >=1

throughout the nonnegative orthant. Its Hessian eigenvalues are
96, 32, -64, -64. Thus every singleton face test can hold for an indefinite
quadratic, even for this paired matrix.

Nevertheless Q is not a full potential. At the top annotation (3,3,3,3)
its value is 1408; at (3,-3,3,-3) it is -1136. Since Q is multi-affine, a
minimum is at a vertex; the top vertex is not minimizing, so some minimizing
vertex violates the singleton floors. This contradicts the full-root
minimum lemma. The nonsingleton completion is irrelevant to this diagnosis.
The example confirms that retaining all exact roots at all annotations is
substantive, not a redundant formulation of the face tests.

## 9. Verification, boundary checks, and formalization boundary

`VERIFY_REFLECTION_AND_MULTIAFFINE_EXCLUSIONS.py` ran successfully and reports:

- 160 exact quadratic reflection identities;
- 201 exact reflected-box cases, including the attained lower endpoint -3;
- 36 exact multi-affine derivative identities with strict negative signs;
- 120 collision-adjusted exact Nash probes on arbitrary signed nonsingleton data;
- 11 exact third-derivative kernel checks on monomials;
- the four paired face identities and the indefinite Hessian spectrum.

All arithmetic is rational or symbolic SymPy arithmetic. These are finite
regressions. The proofs of the universal conclusions are Sections 3-7,
not an inference from these checks. No Lean compiler was present in the
local runtime, no Lean build was run, and no source was published.

A faithful formalization can separate: the two credited full-root lemmas;
the minimum-dependent rectangle and its derivative signs; the reflected-box
lemma; the quadratic identity; the multi-affine vertex and secant identities;
and restriction of the robust relation to exact roots. The reflected point
and the minimum property must refer to the SAME global minimum and SAME box.
The potential produced by the existing characterization is used unchanged.
No structure field should assume its impossible shape or the radial reversal.

The nonnegative own-singleton hypothesis is explicitly used in both the
reflection bound and theta<=1/2. No arbitrary signed-table extension at the
same fixed box is asserted. The chosen bound one and radius three are a
convenient normalized setting, not a claim that the radius is optimal.

The remaining open task is exclusion or construction of a genuinely coupled,
non-multi-affine polynomial of degree at least three satisfying the original
full robust relation. These results alone do not settle that task or Fin4 UE.
