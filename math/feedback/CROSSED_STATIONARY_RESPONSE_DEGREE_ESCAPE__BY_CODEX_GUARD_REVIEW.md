# Independent review of the half-ceiling crossed-response theorem

## Verdict and reviewed scope

PASS. The original manuscript proves its strict, weak, and general guarded
degree theorems. I found no unresolved mathematical objection. This is an
ordinary mathematical review, not a Lean check. The full behavioral class,
signed Never boundary, and fixed-target uniform-payoff quantifiers are
preserved.

Reviewed manuscript: `gpt/CROSSED_STATIONARY_RESPONSE_DEGREE_ESCAPE.md`,
SHA-256 `12707bd1130253d4c04f853b0996184393f2be1b4beb7706652d76d5acd7166a`.
The entire manuscript and entire 257-line exact checker were read.
The checker `gpt/VERIFY_CROSSED_RESPONSE.py`, SHA-256
`474d85a3de06b92506f1314b55ad9230fec3e7a7b23a599ec567c216405e4eee`,
uses only standard-library exact fractions, internal finite loops, and
printing. Running `python -B gpt/VERIFY_CROSSED_RESPONSE.py` passed every
assertion. Its finite computations supplement, rather than prove, the
topological and behavioral arguments below.

The question checked is whether four-player signed raw rewards satisfying
the stated lower rankings, degree-two tensor Bernstein upper tests, and
positive-determinant nonnegative-inverse singleton-matrix condition produce
one uniform-equilibrium payoff, without a supplied strategic root. In the
strict case the stronger conclusion is an actual stationary equilibrium
with both selected hazards strictly between zero and one half and at least
one positive outsider hazard.

## Residuals, crossed faces, and degree

The polynomial expansion is correct: the first-order coefficient in the
recipient i residual is s_i minus the singleton reward from each opponent,
hence Δ(q) = −Γq + O(‖q‖²). Neither its sign nor the row/column convention is
changed when forming A = PΓ. The auxiliary swap changes residual ownership
only in the fixed-point map; it is not a relabeled game or a simultaneous
deviation.

Weak lower ranking makes every external singleton comparison nonpositive.
If the selected reciprocal comparison were also nonpositive, the entire
selected row of Γ would be nonpositive. Multiplying that row by the
nonnegative corresponding inverse column contradicts the diagonal identity
one. Reciprocal positivity is therefore produced by the raw assumptions.

Strict lower ranking gives the required lower face sign by factoring the
positive outsider absorption probability. At the half ceiling, the nine
Bernstein basis functions are nonnegative and sum to one; strictly negative
coefficients give a genuinely uniform negative sign. The interpolation
formula for the middle coefficient is correct, and its tensor product
applies because each outsider hazard has degree at most two. These are
sufficient coefficient tests, not an equivalence with polynomial negativity.

At a crossed fixed point with some outsider hazard positive, the lower and
upper face signs force both selected coordinates into the interior of their
half intervals. Each swapped residual is then zero, so both ORIGINAL
individual residuals are zero. The remaining two coordinates retain their
original endpoint signs. There is no false inference from capped optimality
to an unrestricted best reply.

When outsiders are absent, Δ_i(t)/t is affine. Its value at zero is negative
by reciprocal positivity, and its value at one half is negative by the
upper guard. Hence every positive selected coordinate contradicts its
crossed fixed-point condition. The origin is the only outsider-zero root.
This accounts for every artificial face, including cases with exactly one
selected hazard positive.

The global degree on the expanded ambient box is +1: throughout the
homotopy to a constant interior image, every image lies in the clipping
rectangle, strictly inside that ambient box. Near zero, upper clips are
inactive even for signed ambient coordinates, and the exact displacement is
min(q, −PΔ(q)). The homogeneous R₀ map min(q,Aq) has a positive linear
norm lower bound on the ambient unit sphere; the quadratic residual error
is strictly smaller on a sufficiently small boundary. This proves both
isolation of zero and local degree equality. Excision then gives the whole
nonzero root set degree 1 − κ(A). No isolation, nondegeneracy, root count,
or particular absorbing branch is assumed.

For A⁻¹ > 0, homogeneous complementarity forces zero. At right-hand side
−1 the unique complementary solution is A⁻¹1 > 0, where the local Jacobian
is A. Its degree is sign(det A) = −1. The manuscript supplies the needed
boundedness argument for right-hand-side homotopy by normalizing any
unbounded solution sequence to a forbidden nonzero R₀ witness. Thus the
local index computation really gives κ(A), not merely the index of a root
of a different problem.

The classical integer degree input is consistent with Gowda, “Applications
of Degree Theory to Linear Complementarity Problems,” Section 2, in the
[author-hosted original](https://userpages.umbc.edu/~gowda/papers/trGOW93-01.pdf).
The game-specific producer is proved in the manuscript; that paper is not
being used as a quitting-game existence theorem.

## Full behavioral and uniform consumers

Every produced strict root has at least three positive hazards. In
particular every deleted opponent clock contracts. A player's pure date-t
reply is the displayed geometric interpolation between Q_i and
H_i/(1−α_i), and Never is the limiting second endpoint. Private behavioral
responses are mixtures of those laws. This proves the exact full cap
formula, including negative values of the actual Never response.

The endpoint conditions bound both cap endpoints by the prescribed value;
prescribed play attains that value. Joint absorption identifies the actual
stationary payoff by its Bellman recursion. These observations justify full
terminal Nash rather than only stationary Nash.

Under every complete unilateral response, absorption occurs no later than
the first opponent quit. Its expected date plus one is 1/(1−α_i), giving
the stated uniform timing bound and regret at most
2M/[H(1−α_i)]. The same strict profile and same terminal target work for all
sufficiently long horizons. No nonnegative-singleton assumption enters.

The finite censoring estimate is also valid for an unrestricted deviator:
couple the original and censored opponent clocks, holding the deviator's
entire law fixed. A changed first outcome requires all opponents to survive
the censored prefix, with probability α_iᴷ. Reward change is bounded by
2M times that event. The prescribed payoff is exactly (1−Cᴷ)v, yielding
full regret at most 3Mρᴷ. Replies in all calendar gaps, beyond support, and
Never remain included in this argument.

Rational-hazard enumeration uses continuity only in a neighborhood where
all deleted denominators stay positive. It therefore supplies accuracy-only
finite producers, not an algorithm for an arbitrary named limiting target.

## Weak-table perturbation and quantifiers

The inverse strictification is sound. If both B_ij and (BKB)_ij vanish,
the nonempty supports of row i and column j must be the same singleton k.
Invertibility in dimension at least three supplies an entry B_uv > 0 with
u,v different from k, producing a positive second-order path. This proves
strict positivity of the convergent inverse series entry by entry.

The literal payoff perturbation has disjoint effects on the relevant raw
coordinates. At partner hazard one half, Q decreases by 3e/2. H decreases
by e/2: external-only absorption and partner-only absorption have total
weight one half. Hence

    δΔ_i = −e + (3e/4)(1−q₂)(1−q₃).

Its Bernstein coefficients are all at most −e/4, because the coefficients
of the displayed product lie in [0,1]. The lower gap increases by e. Own
singletons and Never are unchanged. This genuinely strictifies both the
matrix and raw guards while moving rewards by at most 3e; it is not a
terminal-only strategic translation.

For the original game, using each produced perturbed equilibrium unchanged
has full regret at most 6e by the common outcome-law reward-distance bound.
Taking a subsequence of ORIGINAL payoff vectors yields one fixed target.
For each requested final error, first choose one profile with sufficiently
small regret and target error, and then choose its horizon using its own
positive deleted-clock contraction margins. The proof never takes a
strategy limit or assumes cap continuity at nonabsorbing limits. The final
claim about weak polynomial guards also follows: at the lower face the
same perturbation adds e times outsider absorption, while the half-ceiling
change is strictly negative everywhere.

## Exact example, separation, and neighborhood

The displayed Γ has determinant 45 and the stated strictly positive
inverse. The two lower margins equal one. The exact checker reconstructs
the Bernstein coefficients from raw rewards and verifies the given arrays,
including minimum negative margin 1/12.

At q = (2/9,1/4,1/3,0), the actual residuals are
(0,0,0,−271/1944), all complete caps equal the stated payoff
(3/2,5/13,53/21,15/22), and the four opponent survival probabilities are
exactly those displayed. The horizon constant is
2(199/7)/(1−7/12) = 4776/35. The censoring constant is 3(199/7) = 597/7.
These checks use exact fractions and independent definitions of Q, H, and
the coalition product probabilities.

The proper-child obstruction rows have the correct N/F/J meanings and the
right inequality orientation. Every supplied nonnegative row combination
has nonpositive left coefficients and strictly positive right side. For
children omitting the pivot, all child singletons vanish, so the otherwise
available positive-singleton relaxation cannot discard their necessary
Never row. For children containing the pivot, the witnesses use only F/J
and remain obstructions after discarding N. This excludes the named raw
certificates, not every extension of a particular child profile.

All fourteen nondiscrete partitions are rejected by either necessary
linearized row-sum identities or the displayed block-constant residual
witnesses. The discrete matrix has degree +1, while the crossed one has
degree −1. Every pure nonempty coalition has the stated strictly improving
toggle preserving a nonempty coalition; all Never is beaten by the positive
pivot singleton. The strict coordinatewise payoff surplus refutes all the
named payoff-exclusion entrances. Same-sign reciprocal Γ entries preclude
the required escort edges. None of these comparisons claims worldwide
priority or exclusion of every known sufficient class.

The full reward neighborhood proof is quantitatively sound. Row-sum matrix
error is at most 6δ, the inverse perturbation bound at δ < 1/100 is below
the smallest original inverse entry 2/15, and nonsingularity along the
segment preserves determinant sign. The nine Bernstein raw-coordinate
coefficient norms are exactly the stated array, all at most two. Their
negative margin and both lower rankings survive. Signed recipient-row
translations preserve residuals and raw tests algebraically, but the proof
correctly reapplies the theorem instead of claiming invariance of arbitrary
Never-containing profile payoffs.

## Source boundary and one useful distinction

The previously inspected tracked declarations
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` are
consumers of actual roots with the contraction hypotheses established here.
They do not produce the crossed root. There is no claim that this new degree
proof is already a tracked Lean declaration.

The full-ceiling comparison can be strengthened without changing any
half-ceiling proof. For signed Fin4, weak lower ranking for just one sure
owner a and weak full-ceiling leaving inequalities for just one quiet
partner b already imply qualitative UE with no matrix assumption: fix a
sure and b Never, then take finite Nash among the remaining players. If any
outsider is active, all deleted clocks contract and the weak face signs
give exact behavioral stationary equilibrium. If all are quiet, their Nash
conditions and the partner leaving guard give all no-join inequalities at
the singleton a. Under original no-UE, the exact tracked declaration
`finFour_punishment_le_singleton_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourAuxiliaryDiscountedLocalization.lean`
supplies the owner's punishment individual rationality, and
`isUniformEquilibriumPayoff_soloReward_of_instantPunishment` in
`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean` consumes it
with no-join. Both statements were read directly and their tracking checked.

Thus sixteen weak raw tests suffice for that full-ceiling qualitative
conclusion: twelve lower comparisons for a and four leaving comparisons
for b. The negative sole-owner branch uses off-path punishment, not exact
stationary Nash. This does not yield the manuscript's interior half-ceiling
root, and the displayed half-ceiling fixture has positive pure-partner
joining gains, so the distinction remains substantive.

The strongest surviving claim is the manuscript's stated produced strict
root and weak stationary-approximation theorem. No further repair or
strategic input is requested before assembling that mathematics.
