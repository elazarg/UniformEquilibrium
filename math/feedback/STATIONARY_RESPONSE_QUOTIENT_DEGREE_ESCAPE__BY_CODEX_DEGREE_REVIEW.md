# Stationary-response quotient degree escape: independent degree review

## Verdict and scope

PASS. No mathematical correction is needed in the stationary-response
quotient, the ambient degree argument, the inverse consequence, or the
33-free-nonsingleton completion class before requesting a full export review.
The argument includes singular R0 matrices, nonregular or nonisolated
nonzero roots, and both lower and upper strategy-boundary roots.

The reviewed claim is ordinary mathematics, not a Lean-checked result.
This review is not export authorization. Its main scope is the algebraic
producer and strict strengthening over the full-matrix degree-one
restriction. The complete behavioral and punishment conclusions have a
separate review; the precise tracked normality and homogeneous-consumer
interfaces used by the quotient consequence were also checked here.

The strongest valid output is:

- For any nonempty finite player set and any partition satisfying RI,
  R0 of the quotient A and integer LCP degree kappa(A) != 1 produce an
  absorbing stationary Nash--Bellman root of the original game, with
  independently randomized block-constant hazards.
- In Fin4, the same-table no-UE normality and homogeneous-normal consumer
  make every such quotient necessarily R0 of degree +1 under no UE.
  In particular the stated inverse-nonnegative, negative-determinant
  quotient condition gives UE, without input normality.
- The displayed paired class has 33 independently assignable nonsingleton
  coordinates and four independently assignable own-singleton levels,
  while its full matrix has degree +1 and its three-dimensional quotient
  has degree -1. It is a genuine additional raw-table sufficient class.

## 1. The quotient is an individual-response quotient

For each original player, put a = 1-(1-q_i)alpha_i and
R_i = q_i Q_i + (1-q_i)H_i. Direct cancellation gives

    a(Q_i-H_i) - alpha_i R_i = (1-alpha_i)Q_i-H_i.

Thus, when a > 0 and v_i = R_i/a, the original player's Quit-minus-
Continue endpoint difference has the same sign as Delta_i. No endpoint
is an endpoint for a jointly acting block. RI equates the individual
Delta_i values on the hazard subspace and therefore supplies every
individual sign or equality required by a fixed point of the quotient
map. Equal hazards do not mean a shared coin.

Each coefficient of Delta_i is linear in the reward entries. Equality
on the cube is a polynomial identity because its interior is nonempty.
Differentiating at zero gives

    D Delta(0) = -Gamma,
    sum_(j in O_b) Gamma_ij = A_ab  for every i in O_a,
    Gamma E = E A.

The use of sums, not averages, is correct. There is no zero-diagonal
assumption on A, and no step treats A as a smaller quitting game's
singleton matrix. The intertwining identity is also exactly sufficient
to lift a homogeneous complementary vector of A to one of Gamma.

For the paired class, the centered row condition gives Q_1 = Q_0+c and
H_1 = H_0+(1-alpha)c at q_0=q_1, even when s_0 != s_1. These shifts
cancel in Delta. The argument does not translate the game or its Never
reward. Recipient 2 and recipient 3 do not enter either paired residual,
so their nonsingleton rows are genuinely unrestricted.

## 2. Both degree computations retain the ambient boundaries

The map T = clip(x+Dbar(x)) is continuous on the whole real quotient
space and takes values in the strategy cube. On Omega = (-1,2)^k,
the homotopy from T to the cube center has no displacement zero on the
boundary. Therefore deg(Id-T,Omega,0) = +1.

For an R0 matrix, f_0(x) = min(x,Ax) has no nonzero zero on the whole
ambient space: a zero of this minimum already implies x >= 0, Ax >= 0,
and complementarity. Compactness of the full infinity-norm unit sphere
and positive homogeneity give a strictly positive lower bound c_A.
Neither nonsingularity of A nor smoothness of f_0 is needed.

The origin expansion is valid at signed ambient arguments. Near zero,
upper clipping is inactive but lower clipping remains, giving

    Id-T = min(x,-Dbar(x)) = min(x,Ax+O(||x||^2)).

Coordinatewise minimum is nonexpansive in its second argument. Choosing
rho with K rho < c_A proves that zero is isolated and that the straight
comparison homotopy has no boundary zero. Its local degree is kappa(A).
The compact nonzero fixed-point set is consequently contained in the
annular open domain used in (18), whose degree is 1-kappa(A).

This computation does not decompose nonregular zeros into unproved local
indices. It only uses the degree of their whole compact set. In the paired
example, +2 is total degree in the three-dimensional quotient hazard
domain. It is not a count of exactly two roots, a claim that the roots are
isolated, or the degree of those roots in the full four-dimensional domain.

The classical conventions agree with [Gowda, Applications of Degree Theory
to Linear Complementarity Problems](https://userpages.umbc.edu/~gowda/papers/trGOW93-01.pdf),
Section 2, printed pages 869--871: the ambient minimum map, R0 degree,
right-hand-side independence, and the regular-support index formula have
the orientation used here. The present proof does not need a regular
right-hand side for its actual stationary root set.

## 3. Independent boundary tests

### Singular quotient and a continuum of boundary roots

Consider four players partitioned as {0,1},{2,3}, and let

    Gamma = [ 0   -1  -1/2 -1/2
             -1    0  -1/2 -1/2
             -1/2 -1/2  0   -1
             -1/2 -1/2 -1    0 ],
    r_i(S) = sum_(j in S) Gamma_ij.

All own singletons are zero. RI holds, and the quotient is the singular
matrix A = [-1,-1;-1,-1]. It is R0: any nonzero x >= 0 makes both
coordinates of Ax negative. Its degree is zero, since LCP(A,-1) has no
solution and degree is independent of the right-hand side.

Writing the two block hazards as x,y, the quotient residuals are

    Dbar_1 = (1-x)(1-y)^2(x+y),
    Dbar_2 = (1-x)^2(1-y)(x+y).

Every point of either upper edge x=1 or y=1 is a fixed point. In
particular the proper-support corner (1,0) is retained, and the nonzero
root set is not discrete. These exact identities were checked separately
from the author's fixture. The proof's annular degree remains +1 and
requires neither an invertible quotient nor isolated absorbing roots.

### A nonnegative inverse does not supply R0

The matrix A = [0,1;1,0] has determinant -1 and nonnegative inverse.
LCP(A,-1) has the unique positive solution (1,1), but the homogeneous
problem has the nonzero solution x=(1,0), with slack (0,1).

This falsifies the tempting omitted-R0 inference, not the manuscript.
Section 6 first derives R0 under no Fin4 UE by lifting a homogeneous
quotient vector and invoking the supported-normal consumer. Only then
does it compute degree at right-hand side -1. Every row of A^{-1} is
nonzero, so A^{-1}1 > 0 follows even with zero inverse entries. The
regular full-support index calculation at that independently chosen
right-hand side is legitimate.

## 4. The paired class strictly passes beyond full degree +1

The displayed full and quotient matrices satisfy Gamma E = E A, with

    det Gamma = 45,       Gamma^{-1} > 0,
    det A = -15,          A^{-1} > 0.

The full matrix has eigenvalues 1,5,-3,-3; the quotient has eigenvalues
1,5,-3. Both strict inverse-positivity assertions imply R0. For either
matrix, LCP at right-hand side -1 has the unique full-support solution
1, whose index is its determinant sign. Thus kappa(Gamma)=+1 and
kappa(A)=-1. These matrices cannot be confused by a mod-2 index.

There are eleven nonsingleton coalitions. Assigning recipient 0's eleven
entries arbitrarily defines, by the centered swap equation, precisely
recipient 1's eleven entries. The defining permutation is bijective, so
no consistency equation is imposed back on recipient 0. Recipients 2
and 3 supply another twenty-two arbitrary entries. The singleton
instances are already satisfied by the fixed Gamma, for any four signed
own-singleton levels. The claimed 33+4 freedoms therefore hold exactly.

This is an affine completion class, not all completions of Gamma and not
an open subset of the full sixty-dimensional reward space. The separate
implicit-function argument for the explicit fixture does prove an open
sixty-dimensional solved neighborhood. It relies on that fixture's
nonsingular active Jacobian and strict inactive inequality, not on claiming
that RI survives arbitrary symmetry-breaking perturbations.

The improvement over the full-matrix degree criterion is strict: the
class is nonempty and has full degree +1 throughout. The ambient
zero-discount min-map/local-degree argument itself is already present in
`notes/CODEX_LERAY_CARDINAL__STATIONARY_REPAIR_AND_INDEX_ESCAPE.md`.
The response-invariant partition, its quotient obstruction, and the
resulting class inside degree +1 are the additional mathematical content.

## 5. Exact fixture and separation checks

The entire accompanying Python checker was inspected before execution;
it performs finite exact calculations and writes no files. Its assertions
all pass. In particular they verify:

- the complete fifteen-coalition reward table, centered symmetry, matrices,
  their inverses, and the three-variable residual identity;
- the original individual endpoint identity, origin linearization,
  displayed stationary residuals, and payoff formulas;
- the rational signs selecting the two algebraic hazards, strict negative
  residual for player 3, and the full three-active-coordinate Jacobian;
- every listed pure-profile toggle and the four exact F/J deletion-LP
  contradictions, including the relaxed systems without Never rows;
- the canonical single-pivot table, unchanged residuals and comparison
  rows, and the unit-cube scaling bound.

The full active Jacobian, not merely a block-restricted derivative, is
used for the implicit function theorem. The rational rectangle gives
A_0 > 0, B_0 > 0, C_0 < 0, hence nonzero determinant -2 A_0 B_0 C_0.
The inactive residual has the stated upper bound -8269/15625 < -1/2.
Thus the claimed full-dimensional persistence is justified without a
numerically selected root or a numerical neighborhood radius.

The exact F/J rows were compared with their definitions in
`exports/CAPPED_CLOCK_DEVIATION_DOMINATION_AND_QUIET_EXTENSION.md`.
Their nonnegative combinations have componentwise nonpositive child
coefficients and strictly positive outside bounds, so they really are
infeasibility certificates for nonnegative domination weights. These
comparisons separate named raw hypotheses; they do not claim failure of
an existing verifier supplied with the newly produced stationary root.

## 6. Source inventory and remaining boundary

The full manuscript and full supplied checker were read. Additional
mathematical dependencies inspected were:

- `FinFourQuantitativeFullSupportHardResidual`, its
  `all_punishmentNormal` field, and
  `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
  in `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
  These concern the original table and require only its finite reward
  bound and no original UE.
- `exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal`
  in `UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProductionNormalDispatch.lean`.
  Its input is a normalized full homogeneous vector, with normality on
  its positive owners; no quotient-game realization is requested.
- `IsQuittingStationaryBoundaryAdmissible`,
  `quittingStationaryEndpointBounds_of_fixedPoint_rootNash`,
  `quittingStationaryFullRateUnilateralCap_le_of_fixedPoint_endpointNash`,
  and `isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary`
  in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.
  The separate saturated-coordinate Never inequality is genuine and
  remains explicit in the manuscript.
- The full-matrix R0 degree account in
  `exports/INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md`,
  the raw compiler inequalities cited above, and the earlier ambient
  stationary-map degree account identified in Section 4 of this review.
- Gowda's primary paper, Section 2, for the stated classical integer-degree
  conventions. No source theorem identifying a quotient with a smaller
  quitting game is invoked or needed.

There is no unresolved mathematical objection in this review's scope.
For a later export request, remaining work is packaging and the complete
gate, not a missing strategic input to the quotient producer. In particular
the packet should replace attachment-dependent comparisons with exact
tracked sources or inline proofs, remove preparation/provenance language,
and describe the increment accurately. None of these changes may weaken
RI, remove R0 from Theorem A, turn total degree into a root count, or turn
the signed Fin4 UE conclusion into an unconditional exact stationary
equilibrium claim.

No claim is made that every table admits a useful nondiscrete partition,
that the 33-coordinate cylinder covers arbitrary completions of Gamma,
or that the resulting criterion resolves the remaining full degree-one
class or the finite-player conjecture.
