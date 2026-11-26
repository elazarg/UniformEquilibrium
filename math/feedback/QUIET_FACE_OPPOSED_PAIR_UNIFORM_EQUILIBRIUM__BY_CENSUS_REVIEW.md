# Independent review of the quiet-face coverage census

Reviewer: NEVER_DOMAIN_REVIEW.

**Verdict: PASS for the 80 stationary support patterns, the 65
sure-first necessary-condition patterns, and the general symbolic repair
identities.** The scope is the literal original
table r_i(A)=1+Z_i(A), with all four own offsets exactly 1. The stationary
claim concerns exact stationary equilibria. The sure-first exclusion allows
arbitrary continuation punishments after the prescribed first date.

Reviewed source:
`math/experiments/CODEX_COORDINATOR__QUIET_FACE_COVERAGE_CHECK.py`,
267 lines, SHA-256

    0bfda0fb7355c124e40a30484efb733ce37a59a0af7af252383b174a63298c59

The final checker retains the prior 196-line checker as an exact byte prefix,
including the sixty-entry table and the entire previously reviewed census
calculation. I compared those portions directly and independently reran these
final bytes successfully: stationary 80
patterns/1495 nodes; sure-first 65 patterns/186 nodes;
L=(-10000,-3,-10,-1000). The final constant and unequal-increment symbolic
identity checks also pass.
Reproduction needs only the retained source and SymPy:

    python math/experiments/CODEX_COORDINATOR__QUIET_FACE_COVERAGE_CHECK.py

## Completeness and necessary inequalities

Each coordinate has exactly three statuses: zero, strictly between zero and
one, and one. The 3^4-1=80 nonzero stationary patterns cover every absorbing
stationary profile. The omitted all-Continue original profile has payoff zero
and a unilateral immediate-Quit gain of 1, so it is not an equilibrium.
Exactly 3^4-2^4=65 patterns contain a sure owner, covering every sure-first
product root. Boundary coordinates are assigned their own patterns.

For stationary q!=0, put h=product(1-q_i), H_i=product_(j!=i)(1-q_j),
and U_i=E_i/(1-h). The one-stage gap is

    Q_i-P_i-H_i U_i = [(1-H_i)Q_i-P_i]/(1-h).

The denominator is positive. Thus F_i=(1-H_i)Q_i-P_i must be nonpositive
at q_i=0, zero at a mixed owner, and nonnegative at q_i=1. The source
uses exactly those weak signs. The own shifts cancel in this necessary
one-step comparison because the stationary prescribed continuation absorbs.

For sure-first profiles, L_i=min(-1,min_(A not containing i) Z_i(A)) is a
valid lower bound for any normalized literal-Never continuation payoff:
original nonabsorption pays zero, which becomes -1 after subtracting the
own shift. This includes arbitrary punishment laws. Every nonsure owner
faces another sure owner, hence H_i=0; its comparisons are exactly Q_i-P_i.
For a sole sure owner, continuing now and subsequently choosing Never yields
at least P_i+H_i L_i. Therefore G_i=Q_i-P_i-H_i L_i with the code's signs
is necessary. The lower bound is not asserted for arbitrary larger own
offsets without recomputing it.

## Exact finite-cover verifier

All coefficients, substitutions, inverse matrices, and transformations use
exact rational or integer arithmetic. The tensor Bernstein formula correctly
elevates each variable to degree two. Each displayed subdivision is the
degree-two midpoint de Casteljau transform multiplied by the positive factor
four. The stride indexing implements that transform on the chosen tensor
axis. The resulting two closed boxes cover their parent, including the seam.

The rejection test uses strict coefficient signs only: an inequality is
rejected when its entire box violates the required weak sign, and an equality
only when zero lies strictly outside its coefficient range. Thus it does
not discard equality cases or dyadic boundary zeros. Additional combinations
of mixed-owner equations are legitimate necessary equalities; the matrices
used for them are invertible over the rationals.

The stationary origin exclusion is justified separately. With no sure owner
and at least two mixed owners, the active equations have the form
-Gamma_SS x+R(x)=0. The code verifies that R contains only degree-at-least-two
terms and computes D with ||Gamma_SS^(-1)R(x)||_infinity<=D||x||_infinity^2
on the unit cube. Its integer E satisfies 2^E>D. Thus the cube
||x||_infinity<=2^(-E) contains no nonzero active solution. The all-zero
point is outside the open support pattern. The integer dyadic-box test
only discards boxes entirely contained in this justified origin cube.

The two analytic shortcuts are also sound. For q0=0 with mixed player2 and
q1+q3>0, P2=-2q1(1-q3)-q3<0 and Q2>=0 force F2>0. For a sole mixed
owner j, every quiet comparison is exactly q_j Z_i({i,j})<=Z_i({j});
the code intersects the resulting rational lower and upper bounds with
0<q_j<1. Its endpoint exclusions respect those strict support bounds.

Unresolved boxes cause failure rather than certification. Successful stack
exhaustion, together with the analytic cases, therefore proves the stated
infeasibility results. The reported exact pattern and node counts reproduce.

## General symbolic repair identities

The added identities are exact rational-function identities, independently
checked algebraically as well as by rerunning the checker. With
y=(v2+e alpha)/(c+v2) and b=(d alpha-v1)/(ss-v1), the first two root-gap
expressions vanish after multiplication by their displayed denominators.
Writing the third gap over (c+v2)(ss-v1), its quadratic coefficient is
d e(-12+101+7-v3)=d e(96-v3). The subtracted f alpha term contributes
no quadratic term.

At tau=ss/d, b=1, and the unscaled core3 expression is 108y-101.
Consequently the cleared numerator at tau is exactly

    (ss-v1)[(7-f tau)v2+108e tau-(101+f tau)c],

as asserted. The numerical endpoint expressions equal -243 and -266.
Rational-function evaluation requires its displayed denominators to be
nonzero; these identities alone do not assert that a proposed path remains
in the unit cube, has valid signs, or supplies a Nash selector. Those
strategic and domain implications belong to the separate mathematical
review of the producer.

The unequal-increment appendix was independently audited as well. The two
rational gap identities, both hazard derivative numerators, and the cubic
second-derivative identity are exact. In particular, after replacing v3
by a clipped value, the half second derivative is the affine corner
expression plus (60-v3)*e1*d1. The corner expression has total degree at
most one in alpha,v1,v2. Its constant-increment specialization is 36de.
The endpoint factorization includes the essential f*tau^2*Delta_e term,
and the identity comparing two v3 values has the correct sign.

The perturbation tests use copied immutable rows and leave the original
sixty-entry census table unchanged. Exact arithmetic verifies all eight
corners, the endpoint values, and strict quiet bounds for the single-entry
change Z1(012)=601/100, at both f=1 and f=1/2. I reran the entire final
checker successfully through its last assertion. The interpolation,
denominator positivity, and strategic use of these identities are checked
in the separate whole-proof review; symbolic cancellation alone would
not establish those implications.

## Limits of this review

This is ordinary mathematical and executable-checker review, not Lean
certification. The appended return-role, reset, marked-control, withdrawal,
weighted, inverse, and reference-selector assertions also ran successfully,
but their interpretation as exclusions of named producer theorems is outside
this review's scope. Neither census proves a gap against arbitrary behavioral
profiles or a counterexample to UE.
