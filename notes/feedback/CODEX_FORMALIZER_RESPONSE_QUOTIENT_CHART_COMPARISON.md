# Response-quotient degree: next source obligation

## Checked input and output

`quittingSingletonMatrix_mulVec_blockLift_eq_quotient`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`) proves
the literal row-sum identity Γ E = E A from raw response invariance (RI) on the
closed block-constant strategy cube. Here A uses sums over blocks, including
diagonal blocks. The same module defines the actual ambient polynomial quotient
clipped map `quittingQuotientStationaryClippedMap`; its continuity, cube-valued
image, and coordinatewise fixed-point sign equivalence are checked. No root is
asserted or supplied by these results.

`BoxComplementarityProblem.exists_solution_not_mem_closure_of_localDegree_ne_one`
(`MathUE/Topology/BoxComplementarityDegreeEscape.lean`) is the downstream
degree-excision producer: an actual box problem with an isolating region whose
local integer degree differs from one has a solution outside its closure. It
does not identify the quotient problem's local degree.

## First missing source theorem

The next theorem must construct the *actual* quotient displacement problem
from a reward table, block map, representatives, RI, and R0 for the row-sum
matrix A. Let T be `quittingQuotientStationaryClippedMap`, Z(x) = x - T(x),
and f_A(x) = min(x, A x) coordinatewise. Its source-specific conclusion is:

> There is a positive, sufficiently small central neighborhood of zero in a
> displayed box chart for which the pulled-back Z problem is isolating and its
> integer local degree is `Math.LinearProgramming.r0Degree A hR0`.

Neither an isolating neighborhood nor the local-degree equality may be an
input to the raw-table producer. A concrete Lean statement could use the
fixed global chart `[-2,2]^k` for Z and return an open central region in its
unit-cube coordinates, contained in the inverse image of a small ambient
zero-neighborhood. The corresponding degree must be compared to the canonical
R0 degree of `lcpMinBoxProblem A 0 0 2 ...`. Equivalently, a small zero-centered
chart may be used, but then an explicit chart-transfer theorem is required
before applying global degree/excision in the large chart. Existing R0 degree
theorems compare *scalar charts of the same homogeneous LCP map*; they do not
yet transport a local degree between the actual quotient map's small and
global charts.

The packet's Section 4.3 supplies the proof route. The actual derivative at
zero, combined with Γ E = E A, gives Dbar(x) = -A x + o(‖x‖). Near zero the
upper clip is inactive, so Z(x) = min(x, -Dbar(x)). The R0 condition gives a
positive sphere margin for f_A; shrink the radius until the Z-to-f_A error is
strictly below that margin on the sphere. On a coordinate-interior frontier,
`BoxComplementarityProblem.localDegree_eq_of_norm_sub_lt_norm`
(`MathUE/Topology/BoxComplementarityFrontierPerturbation.lean`) can then
identify degrees through the actual straight-line gain homotopy. The
homogeneous reference degree is `localDegree_lcpMinBoxProblem_zero_eq_r0Degree`
(`MathUE/LinearProgramming/R0Degree.lean`). The missing implementation is the
quantified remainder/margin adapter **and** a common displayed-chart/region
comparison for those two existing degree interfaces. The packet proves this
mathematical comparison; it is not yet a checked Lean theorem here.

## Subsequent consumer boundary

Once the source local-degree theorem exists, degree escape with κ(A) ≠ 1
produces a nonzero quotient fixed point: the global quotient self-map has
degree one, while the central zero has degree κ(A). A separate game-semantic
adapter must then lift its coordinate signs through RI to *all original
players*, prove positive joint absorption, set v to the actual stationary
terminal payoff, and establish v = F_r(v,q) plus each original player's exact
one-stage Nash–Bellman condition. The sign equivalence currently proves only
the quotient-coordinate assertion. This Bellman adapter and the local-degree
comparison are both still open; Theorem A is not claimed in Lean.
