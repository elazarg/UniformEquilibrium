Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Printed paired polynomial/Hessian and scalar boundary fixtures: 45–47

Frozen static UNCOMPILED/UNAPPLIED drafts. Both complete source exports were
reread before this work; existing 01–43 owners and later compiler repairs were
inspected. All their frozen bytes remain unchanged. No Lean/Lake, Git, shared
edits, children, cache/worktree duplication, options, or inventory/doc edits.

## Exact dependencies and root-owned check order

45 adds MathUE.Analysis.RationalPolynomialCoordinateDerivatives. It requires
the applied/checked CoordinateResetFTC owner and existing PolynomialLipschitz.
It does not depend on future 05, 12, 31–35, or integral44.

46 adds MathUE.Analysis.Examples.PairedFacePotential and depends on 45 plus
canonical Mathlib matrix/eigenspace interfaces. It does not redefine a Hessian
operator or duplicate a spectral/Rayleigh/compact-minimum proof.

47 adds MathUE.Analysis.Examples.ReflectionBoundaryArithmetic, independently
of all project analytic modules, using real arithmetic and norm_num only.

Root should apply/check 45 then 46; 47 can be checked independently. After
separate informational AXIOM_HARNESS.lean, root alone wires the appropriate
umbrellas, regenerates the exhaustive axiom audit, performs trust/import/
duplicate/telescope/docs checks, and the needed final integration gate.
No repository audit, axiom output, or compiler check was run here.

## Source mapping and literal claims

46 formalizes the reflection export's exact boundary test 5:

- one actual rational expression Q with every printed coefficient;
- the literal P(v)=Q(v−1/4), with its actual rational translated expression;
- receiver-row/quitter-column Γ=(1/4) times the printed paired matrix;
- actual Fréchet derivative and coordinate partials, not a supplied gradient;
- all FOUR exact face formulas, and their consequence drift≥1 at EVERY
  nonnegative lower-face point, including arbitrarily large upper coordinates;
- literal translated P face drift for every point above s=(1/4,1/4,1/4,1/4);
- singleton vectors s+Γ_i bounded by one;
- actual second coordinate partials of BOTH Q and P equal the printed constant
  symmetric Hessian matrix, in literal recipient-row/owner-column order;
- four nonzero eigenvectors, linear independence, and explicit spanning
  expansion, with eigenvalues 96,32,−64,−64; exact HasEigenvalue iff the value
  is 96,32,or−64, so this is a complete Hessian spectrum, not a mere negative
  direction or unrelated matrix spectrum;
- P(3,3,3,3)=1408 and P(3,−3,3,−3)=−1136;
- the literal top vertex is not a minimum on [−3,3]^4, witnessed internally
  by the printed countervertex. No minimizing point is supplied or assumed.

The matrix is tied to actual second partials before its spectral facts. This
is the Cartesian coordinate Hessian, whose eigenvalues are the Euclidean
Hessian eigenvalues; no Pi supremum norm is used or substituted. Existing
LeastHessianEigenvalue/CoordinateHessianExtrema retain ownership of the Riesz
operator, sorted least eigenvalue, and compact spectral minima. These fixture
proofs do not recreate those foundations.

45 is only the standard bridge from the existing actual rational polynomial
derivative to coordinatePartial, then coordinateMixedPartial. It reuses
RationalPolynomial.hasFDerivAt_evalReal and differential_apply, with a single
finite sum evaluated at Pi.single. Formal polynomial differentiation, actual
Fréchet differentiation, or smoothness are not reproved.

47 formalizes exact boundary tests 2–3: permitted reflection equals −3;
fixed nonadaptive cap gives 11/2>3; negative singleton gives −5<−3;
unsigned theta=2/3 gives the printed positive partial 2/45. These are failures
of the tempting changed hypotheses, not counterexamples to the proved theorem.

No game table, no-UE, actual standard Q, full-root certificate, or minimizing
vertex is assumed/constructed by the fixture. The full-root quadratic and
multi-affine exclusions already have canonical future owners 04/09; they are
not reproved here. In particular this diagnostic positive face polynomial is
not asserted to survive their full relation or to be a game counterexample.

## Residual obligations and honest verification

The separate first-export coupled cubic quasiconvex/nonconvex/nonadditive
fixture and actual two-player collision/Nash fixtures remain to be formalized
as literal fixtures. Existing canonical collision probe and matrix-free
exclusion proofs already establish their general mechanisms; none is copied
in these patches. This handoff does not claim every source fixture is done.

Pinned actual polynomial differential, coordinate partial/mixed definitions,
finite linear-independence criterion, matrix-to-linear-map application,
eigenspace/eigenvector/eigenvalue interfaces were inspected. Static line-length
scan passes non-import Lean≤100 characters. Ordinary compiler risks remain:
reduction of the translated rational expression, finite vector notation and
sum evaluation, polynomial normalization, and eigenvector tuple elaboration.
No nonminor source mathematics gap was identified. Independent static review
and root-owned compiler checks are still required.

## Frozen SHA256

```text
45 05851dcb10bf33ac7466c67fd793dee590674ae627c1c25e1ed28ec3b7ba6e49
46 e6280f4f42d8fe4e0fa84a69f1080d2f40c7fd225818efafee4580e3d1d2d171
47 533b3065ed32ac769c22074d6947a87a719220fcd76c5dacdbffa875ef17d1ca
```
