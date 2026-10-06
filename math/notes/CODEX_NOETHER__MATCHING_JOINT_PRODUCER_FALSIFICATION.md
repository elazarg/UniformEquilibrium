# Matching joint producer: independent falsification

Identity: CODEX_NOETHER. Ordinary mathematics, not checked in Lean here.

Status: the general inverse-positive producer and strict signed matching
extension are accepted by my independent matrix, fixed-point, payoff,
full-deviation and raw-coverage review, at manuscript SHA256
`c1fab38c7e5c15dc00e7784f8ca0c929cdbd0cc6b489e54c8925f6c7ba242ad0`,
from “An inverse-positive producer with two unequal joint rows” through EOF.
A different standalone handoff requires its own review. This notebook retains
the independent boundary calculations and a proved extension of the raw
existence class. The substantive review is in
`feedback/CODEX_BROUWER__MATCHING_JOINT_PRODUCER__BY_CODEX_NOETHER.md`.
No other conference feedback was read.

## Question and finite data

There are four players, private independent Continue/Quit randomizations,
public past actions, one live state with zero stage reward, and fifteen finite
terminal reward vectors r(S). Never pays zero. Unilateral replacements are
arbitrary full behavioral strategies. Write s_i=r_i({i}) and
Γ_ij=r_i({j})−s_i. Let f=(01)(23), a=(02)(13), o=f∘a. The schedule
alternates A=02 and B=13. Its participant increments and passive increments are

    Π_i=r_i({i,a(i)})−s_i,
    K_i=r_i({f(i),o(i)})−s_i.

The strict candidate requires Γ_i,f(i)>0, Γ_i,a(i)=−b_i<0,
Γ_i,o(i)<0, Π_i>−b_i, K_i≤0, and all twelve outsider joins bounded
by s_i. It claims a fixed uniform-equilibrium target for every such raw table,
with an internally produced exact proper period-two terminal Nash profile in
the standard-Q branch. The alternative branch uses the existing original-game
no-UE-to-standard-Q theorem. No strategic witness is a hypothesis.

## Bounded exact-source inspection

The source route was selected through `docs/FRONTIER.md` and
`docs/TOOLKIT.md`, followed by narrow declaration searches. I inspected:

- `isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff`
  (`UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`),
  with no own-singleton sign, reward normalization or strategy premise;
- `quittingProjectiveLCPMatrix`
  (`UniformEquilibrium/Quitting/Projective/SingletonLCP.lean`) and
  `quittingSingletonMatrix`
  (`UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`),
  both receiver first, singleton owner second;
- `IsStandardQ`, `IsStandardLCPSolution`, and `lcpResidual_def`
  (`MathUE/LinearProgramming/CopositiveQ.lean`), using q+Γz≥0;
- `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
  `isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
  (`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`), requiring
  exact policy recursion, exact local root Nash, and every deleted-player
  cycle contraction;
- the literal pure Quit/Continue definitions and
  `quittingRootExpectedPayoff_update_eq_endpointMix`
  (`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`);
- `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
  (`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`),
  with arbitrary signed rewards and no supplied limiting target;
- raw comparison definitions in the supportwise/product-low, signed
  four-cycle, passive-row inverse, conditional face-gap, affine potential,
  signed influence, and nonnegative-weight chamber files cited in the review.

These were read-only source inspections. No Lean command, build, new Lean
file, Git stage, commit or push was performed. This is not a new certification
of any library declaration. No literature result is imported into the new
matrix/fixed-point argument.

## A proved weak-boundary existence extension

Assume instead the weak raw inequalities

    Γ_i,f(i)≥0,       Γ_i,a(i)≤0,       Γ_i,o(i)≤0,
    Π_i≥Γ_i,a(i),    K_i≤0,

with the same twelve caps. Thus the participant comparison means exactly

    r_i({i,a(i)})≥r_i({a(i)}).

Using the accepted strict theorem, every table in this weak class has a fixed
uniform-equilibrium payoff. This assertion is a mathematical consequence,
not a further supplied-strategy interface. Its standalone packaging remains
to be byte-reviewed.

For δ>0 form r^δ by changing only the twelve off-diagonal singleton
coordinates: increase r_i({f(i)}) by δ, and decrease each of
r_i({a(i)}), r_i({o(i)}) by δ. Preserve own singletons and all
nonsingleton coordinates. Its singleton sign inequalities are strict. If
b_i=−Γ_i,a(i)≥0, then b_i^δ=b_i+δ>0 and

    Π_i≥−b_i>−(b_i+δ)=−b_i^δ.

All passive increments and all twelve caps are unchanged. The strict
theorem therefore gives UE for r^δ, and every coordinate change has absolute
value at most δ. The inspected reward-closure theorem supplies one fixed UE
target for r. The approximating targets may vary; no target convergence is
silently assumed. This removes degenerate raw boundaries from the existence
problem, while making no exact proper-profile claim at those boundaries.

## Exact simultaneous boundary test

Take favorite Γ entries 13/4, both harmful entries −1, and any real
singleton vector s, for example (−4,−1,0,7). Put Π_i=−1/2,
K_i=0 and all twelve caps at equality. Set X_i=1, hence q_i=1/2.
Then

    U_i=s_i−1/4,       W_i=s_i+1/2.

The original ΓX entry is 5/4. The moved negative part changes the
scheduled-mate coefficient to −3/4, giving (BX)_i=3/2, while
N⁺_i=(1/2)(1+1+1)=3/2. Active Quit and Continue equal U_i;
passive Continue equals W_i and passive Quit equals s_i. Thus negative
own singletons, negative participant increments, K=0 and cap equalities
can occur simultaneously. Signed centering has not translated Never.

## Exact failure at the excluded participant boundary

Take Γ's favorite entry H>2 and both harmful entries −1, but set
Π_i=−1 and K_i=0 for every i. Γ has strictly positive inverse, yet
the original odds equations have no positive solution. Indeed

    ∑_i(ΓX)_i=(H−2)∑_i X_i>0,
    ∑_iN_i(X)=−∑_i X_i²/(1+X_i)<0.

This is the minimal failed extension: the exact proper two-phase producer
cannot simply replace Π_i>−b_i by Π_i≥−b_i. It is not a UE
counterexample. If all outsider caps hold, either scheduled pair is an
exact pure terminal Nash coalition: its participants are indifferent to
withdrawal and its outsiders receive s_i and cannot gain by joining.
Reward closure proves the more general weak existence extension above.

## Exact noncoverage calculations for the asymmetric table

For the author's fifteen-row fixture, independent rational substitution gives

    det Γ=7171377/4096,
    ΓX=(37/32,33/40,157/240,211/120),
    U=(549/272,183/104,61/36,61/24),
    W=(183/68,427/208,61/30,305/96).

Every active endpoint equality and every passive Continue equality holds.
The four passive Continue−Quit margins, ordered (A,1),(A,3),(B,0),(B,2), are

    181/104,       275/96,       5419/2380,       34/21.

The premium traps are exactly 02, 13 and I. Pair traps rule out a proper
greatest core and the all-traps-size-at-least-three charge criterion. All
four players have a negative participant premium somewhere, so there is no
protected leaver. Weighted floors fail at the grand coalition, where every
coordinate is below its own singleton. For the full trap and T=02, the
mixed-charge aggregate joining sum is 1>0, so mixed pair/charge coexistence
does not rescue this fixture. Product-low fails at the sure02 law; both
active Quit premiums are strictly positive.

The nonnegative-weight terminal chamber also fails. If λ≥0 satisfies
the weighted singleton upper bound at both scheduled pairs, adding those
two inequalities gives

    ∑_i(Π_i−1)λ_i≤0.

All four Π_i exceed one, so λ=0, contradicting the required positive
weight coordinates.

For each induced triple, its inverse has negative diagonal entries and
negative outside inverse weights. Up to simultaneous row/column order,
the triple inverse is

    [[−53/16,−1/2,−1/2],
     [−1/2,−4/53,4/53],
     [−1/2,4/53,−4/53]],

and its outside weights are (−2681/128,−53/16,−53/16).
The full inverse exit requires negative determinant, which fails here.
The sole-positive singleton graph consists of two 2-cycles; it cannot be
relabeled to a favorable predecessor 4-cycle or a favorable 3-cycle.

Every proper child fails the accepted finite quiet-lift F/J criterion.
If an outsider k has a(k) in the child, take the child singleton
A={a(k)}. Its own join gain is r_k({k,a(k)})−r_k({a(k)})>0,
whereas each child member's joining gain at A is nonpositive: the owner
has gain zero; its favorable partner has gain −69/8; its other partner
has gain −1. No nonnegative weights can satisfy J. If no outsider has
its active mate in the child, the nonempty proper child must be 02 or13.
At its full coalition, both child deficits s_i−r_i(A) are negative,
while every outsider deficit s_k−r_k(A)=1. No nonnegative weights
can satisfy F.

All fifteen pure quitting coalitions have an explicit profitable join or
withdrawal. The scheduled pairs have outsider joining gain 1/2; all other
pairs have a participant withdrawal; every triple has a withdrawal gain
10; the grand coalition has withdrawal gains (11,12,13,14). All Never
fails because every own singleton is one. These exclude pure-exit raw
producers, not arbitrary stationary mixed profiles.

Concrete next question: independently test the residual mixed passive signs
with each scheduled pair exposing a negative K and at least one positive K.
The current nonnegative cone proof does not apply there.
