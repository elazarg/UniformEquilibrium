# Adversarial review of physical core uniformity across three joins

Reviewer: CODEX_COLLAR_ADVERSARY.

**Mathematical verdict: PASS.** No unresolved objection remains in the complete
internal note. This review independently attempted to falsify the corner
switchback constructions, weighted c=1 contraction and unbounded-depth
right-band argument. No other review was read. This is ordinary mathematics, not an export-gate decision
or Lean verification. No Lean command ran.

Reviewed artifact:
[CODEX_UNIFORM_JOINS__PHYSICAL_CORE_UNIFORMITY.md](../notes/CODEX_UNIFORM_JOINS__PHYSICAL_CORE_UNIFORMITY.md).
Exact SHA256:

    1805d0fe098483278f20241fc9d525d1ab7896224a83566e79ac1dcfcd6c3b83

## Exact accepted scope

For the stated native singleton matrix, seven passive entries, nine homogeneous
core premiums and row0 upper bounds, the note proves three common-threshold
UE statements: a closed neighborhood of (3,1); a two-sided a=3 band for each
compact c-interval in (0,1); and a two-sided c=1 band for each compact
a-interval in (0,3). Ratios may vary with beta inside these regions.
The right-side a=3 radius and threshold are independent of its unbounded
sheet count.

The proof fixes a target for each game before accuracy. It covers complete
unilateral behavioral replacements, including Never, with private independent
randomization. Own levels and all unlisted rewards are arbitrary finite data;
thresholds do not depend on their magnitudes. No joint parameter continuity
across the left/right a=3 constructions is inferred. Uniformity as c tends
zero, on all positive ratio rectangles, or on the whole premium cube remains
unproved; Fin4 remains open.

## Corner: clipped roots and unrestricted switchbacks

I reproduced the exact pair identity, residual contact identity and the entire
corner derivative table. In particular R0_z=-2 and J_z=4/3, while R0_u=R0_v=0.
The candidate term changes R_h's z slope by at most delta*(11/2+O(theta));
thus the stated uniform decreasing slope is valid using finite increments.

At z=0, nonnegative h only decreases the residual. Its positive part is
bounded by C*epsilon*(u+v), since the remaining quadratic term is negative.
This gives a unique clipped root z_h=O(epsilon*(u+v)). Future arguments
remain in the common triangular domain. Coordinate Lipschitz bounds on that
domain give the required global L1 increment estimate, by connecting two
points through their coordinatewise minimum if necessary.

The pair height is J plus the quiet-player slack divided by its survival.
Its player2 output is exactly T(beta*K), whereas the triple output is beta*W.
These coincide at a switch. The formula with the positive part therefore
implements arbitrary successive pair/triple switches; it never assumes a
pair-legal region is forward invariant.

The operator preserves h>=0 exactly. On a pair it equals h(beta*K)/P.
On a triple, positivity of the initial residual implies Psi<J(x,0), and J
increases with z. Finite-increment comparison gives the two stated bounds
on z_h. In the Lipschitz estimate the leading coefficient is 2/3, with the
positive-part term contributing only O(beta). Choosing delta first and then
epsilon, radius and beta closes the invariant class and the strict contraction.

The weighted metric sup|h1-h2|/(u+v) is complete on that closed class.
Clipped-root comparison also works when one root is zero: its residual
inequality supplies the missing equality. The resulting contraction bound
is uniform across arbitrary switching sets. Parameter continuity is only
asserted for beta>0; no extension of h(beta*K)/beta through beta=0 is used.
At (3,1), every candidate uses the pair branch and U0=0, proving T=Psi.
Exact continuation, common hazard contraction and the passive recurrence
then give the claimed continuous axis and full Nash guards.

## Right band: estimates independent of sheet depth

The full analytic linearization is valid. In the quadratic holomorphic norm,
L_beta^-1 composition by F_beta costs O(beta), so the stated operator
contracts uniformly; its division by beta is removable. The change and its
inverse preserve the exact a=3 solo3 axis. Analytic factorization gives
transverse errors O(|x|*J_epsilon(x)) and the corresponding product-rule
derivative bounds. It does not give that stronger estimate for the u error,
and the proof correctly retains only O(|x| squared) there.

I independently verified the reverse matrix R_beta=N^-1+beta*Id. Its cone
inequalities check uniformly. For the z lower bound use
alpha*u<=delta*v/Lambda and z<=k*delta*v; for its upper bound use
u>=-M*v and z>=-h*delta*v. The positive v expansion and the lower u facet
follow by the specified small choices. In the upper-u facet calculation,
the rescaled U=alpha*u/v stays in a bounded interval even when u/v diverges.
The displayed limiting expression has minimum at least delta; perturbations
preserve this strict margin. Thus no division by a-3 is hidden here.

The ratio estimate gives a uniform decrease proportional to 1+max(tau,0)
until tau passes a fixed negative value. For nonnegative tau with negative
next u, the small/large tau split supplies the same strict decrease; it
extends to a common small negative interval. The upper bound on v'/v and
positive z' give uniform positive z/v after one step. Consequently the
needed plane slopes satisfy the stronger estimate (U8), not just boundedness.
Only finitely many sheets are used at each a>3; the bounds do not depend on
how many are needed as a decreases to3.

The exact contact curve has both point and tangent errors O(epsilon*s squared)
and O(epsilon*s) after reparametrizing its linearizing u coordinate as s.
Every transverse facet margin of its tangent ray is proportional to epsilon.
Thus point and tangent vectors are cone-sandwiched by (1+O(s)) times that
same ray. Cone positivity preserves the sandwich at every depth without
accumulating an n-dependent loss. The positive functionals v and ell give
relative control and a strictly increasing radial parameter on every curve.
The inverse-norm bound guarantees all curves cover a common radius.

Passing through K^-1 preserves relative v and radial derivative estimates.
The crucial derivative comparison uses the SAME reference ray for point and
tangent, yielding |t|*J_epsilon(x)<=C*|x|*v(t). This avoids a 1/epsilon loss.
The uniform multiplicative gap between linear angles therefore survives
all nonlinear errors. Exact contact curves stay ordered, and the final one
lies strictly beyond u=0. The last unused preimage plane need not be a graph.

## All-depth graphs, physicality and descent

The normalized sheet remainder is bounded by
C*(C3*beta)^n*|x|*J_epsilon(x). This follows from two forward contraction
factors and the lower bound (beta/C)^n on the linear normal. Its second
derivative has the analogous unweighted bound. Together with the uniform
projection angle it gives one implicit-function radius for every needed sheet.

The original-coordinate estimate is valid only on active sectors, as stated.
There epsilon*u<=C*v and |A_n|u<=C*v. Thus the larger longitudinal coordinate
error contributes at most C*rho*(v+|z|), rather than an uncontrolled term
of size rho*u. The graph equation first gives

    |z|<=C*v+C*rho*|z|.

Absorb the last term before claiming the stronger error O(rho*v). The slope
bound controls endpoint-angle errors as well, preserving the later sheets'
positive height proportional to v. The exact hazard differs from linear cap
height by O((beta+rho)*J_epsilon), so those hazards remain positive uniformly.
This closes the potentially serious weighted-coordinate gap.

The first sheet uses an exact boundary factor instead. I reproduced its
limiting positive unit (1-c)/(1+3c). Its hazard vanishes on the exact contact
curve, so factorization proves physicality up to that shrinking boundary.
Adjacent-sheet intersections reduce, after forward iteration, to the uniformly
transverse pair/first-preimage intersection. There are no extra crossings.
Ordered boundaries and the sheet equations give descent to the preceding
sector; the legal pair sector is uniformly invariant. This proves actual
finite triple prefixes without assuming an a-independent prefix length.

## Left extension and the c=1 crossing

The negative invariant plane pulls back under the same analytic linearization.
Its exact solo3 axis at a=3 supplies the factor
T(u,0)-A*u=O((3-a)*u squared). The displayed critical-height subtraction is
exact. Its two u brackets and the v derivative margins are uniformly positive
on the fixed compact c-interval. Common C2 bounds then give
T-Psi and T-tcrit at least kappa*((3-a)*u+v). This proves the entire left
strip, including the boundary axis, with one radius and beta threshold.

Taking the smaller left/right constants proves the two-sided claim. The
consumer uses input continuity for each individual game and uniform bounds;
it needs no continuity of the chosen graph across a=3. Summable hazards give
uniform passive guards and axis error on both sides, independent of depth.

For c>=1 and a in a compact subset of (0,3), the new class is monotone in u,
with h(0,v)=0, u slope at most B(a), and v Lipschitz constant D. This class
is closed and complete in sup|h1-h2|/u. Its boundary condition is exact only
on the upper side; the proof correctly uses a separate lower construction.
The monotone first coordinate helps the residual decrease in z, so only the
small v bound D reduces the scalar monotonicity margin. I reproduced

    R_h,u>=B(a)/3-O(theta),
    K1(x,z_h)<=[3a/(3+2a)+O(D+theta)]u.

These bounds make the /u contraction valid even when v/u is arbitrarily
large. Residual monotonicity permits at most one switch along a fixed-v
u interval. Pair monotonicity and the positive triple-root increment then
preserve h_u>=0, including that switch. The upper u-slope margin is exactly
(3-a)/[3(1+a)(3+2a)]>0. The v-Lipschitz coefficient is 3/(3+2a)<1;
choosing D first absorbs its quadratic error uniformly. Finally,

    18a/(3+2a)^2<=3/4

gives a common strict contraction. All coefficients were checked exactly.
The small positive-part term also respects the /u metric because K1=O(u).
No eventual pair-tail invariance is assumed.

The lower side has the exact c=1 solo1 axis and the analytic remainder
O((1-c)*v squared). Together with the uniformly positive u margin this
proves physicality in u+(1-c)v. The pair guard is nonpositive there after
a common radius choice, so T>=tcrit>=Psi. At c=1 the analytic correction
belongs to the upper class: with a=k(1+2k), its u-slope is strictly between
0 and B(a), and its v slope is O(u). The difference from the upper bound
has positive numerator (1-k)(6k+1). Fixed-point uniqueness identifies the
two graphs. Weighted-metric parameter continuity is not asserted; ordinary
C0 continuity follows from jointly continuous finite Picard iterates and
a uniform geometric sup-norm error. This distinction is handled correctly.

## Shared return and complete behavioral consumer

The cited frozen return geometry applies with those exact inputs. The corner
and c=1 band have c>=3/4 and D-2V/3<0. On the a=3 band use
D-U+eta*U/3<0 after shrinking eta. The common graph upper bound permits one
finite pair slack before beta is chosen. Uniform axis error preserves the
other two rectangle faces. Hence the same two-dimensional intermediate-value
argument produces an actual return for every game, even for beta-dependent
ratio paths. No return selection across games is assumed.

The finite-word consumer charges flow Quit error once and seam error over
at most 1/x expected visits; opponent absorption removes every remainder.
Its uniform finite-horizon estimate and absorption justify the fixed target
and arbitrary signed own-level translation. The query census keeps all free
reward magnitudes out of beta0. The cited terminal, finite-flow and infinite-
path declarations were inspected statically and have the stated supplied-data
scopes. The new note supplies their required cores and checks the shared
return hypotheses; it does not assume an executable infinite wash.
