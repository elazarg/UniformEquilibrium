# Independent adversarial review of unequal-premium contraction equilibria

Reviewer: CODEX_ACTUAL_MINIMUM_AUDIT.

Reviewed artifact: the complete self-contained candidate intended for
[UNEQUAL_PREMIUM_CONTRACTION_UNIFORM_EQUILIBRIUM](../exports/UNEQUAL_PREMIUM_CONTRACTION_UNIFORM_EQUILIBRIUM.md).
The reviewed bytes have SHA256

    740bed96fd5791f39d4c1cc65314ecffbfe8b4bfb5beb4e759a6251282379b54

The candidate has 1090 lines. This review covers its full statement and
Sections 1--9, including both existence regions, compact-parameter uniformity,
the unrestricted behavioral consumer, and the calibration comparisons.

**Mathematical verdict: PASS. Export-gate verdict: PASS.** No unresolved
mathematical objection was found at these exact bytes. This is independent
ordinary mathematical review, not a Lean check or a solution of Fin4.

## Independence and claim checked

I contributed neither the cone/graph/Bellman construction nor the calibration
proof. I read the two initial mathematical drafts and then the entire final
candidate, without reading another review of them. My earlier research in this
session concerned the separate global-minimum source and did not supply an
assumption or proof step in this packet.

The claim is an actual raw-reward existence theorem for

    a>0, 0<c<5/9, 8a<15(1-c),

or

    1<c<2, 3c/2<=a<3.

At each fixed ratio pair, sufficiently small positive beta gives an original
uniform-equilibrium payoff. A common threshold works on each compact subset
of a stated region, including compact subsets meeting 2a=3c. The result does
not assert one threshold on the entire noncompact union. It allows the stated
independent row0 upper-bounded rewards and arbitrary finite unqueried grand
rewards, without treating those coordinates as additional small parameters.

All strategic objects required by the conclusion are produced. There is no
supplied invariant graph, physical root chain, switching index, payoff return,
or favorable continuation. The statement is therefore an existence-class
producer, rather than a supplied-certificate implication.

## Adversarial checks of the closed wedge

The load-bearing potential failure was the neutral line 2a=3c. A strict
linear projective contraction would fail there. The packet instead proves
strict quadratic inwardness from an exact boundary equation, and this repair
is valid.

I checked the characteristic polynomial and its negative-root separation.
The positive spectral plane is used as a real two-dimensional invariant
space. No diagonalization or simplicity of either positive eigenvalue is
needed. The normal multiplier remains negative and of order beta. The graph
transform acts on functions vanishing to second order, so its composition
term gains a second factor of beta before division by that multiplier.
The stated weighted C2 metric and the common Lipschitz bound on second
derivatives control evaluation at different graph-dependent arguments.
These bounds give a complete preserved class and a contraction after choosing
the derivative bounds and then shrinking radius and beta. They also justify
the C2 regularity needed in the concavity argument.

As an exact degeneracy test, at

    (a,c)=(51/26,17/13),

the characteristic polynomial is

    (2X+3)(26X-17)^2/169.

Thus the positive eigenvalue is double. Here r=3/2, A=65/168 and B=13/14.
The limiting boundary is

    y=27w/[8(14w+3)],

whose second derivative at zero is -21/2. The concavity mechanism remains
strict at this double-eigenvalue point on the neutral line. This is an
explicit check against the most plausible spectral exception.

The exact transverse factorization gives the boundary equation (W11), not
merely its first-order approximation. The pair map is exactly diagonal in
the stated cap odds. Strict concavity therefore gives inwardness even when
the two diagonal factors coincide. The proof of invariance of the entire
physical region also checks the interior: the projective derivative stays
positive, while differentiation of the moving boundary contributes only
O(beta*xi). Boundary inwardness is not incorrectly used as a standalone
interior-invariance theorem.

The global maximum form of the Bellman operator (W14) is well-defined and
contracting in the weighted supremum norm. Its signs are consistent with
player2's passive reward -2y-w: the backward equation has a plus b in its
numerator. Equation (W15) gives precisely the pair spectator's required
Continue guard. Picard iteration equals the triple graph on the whole
physical region, increases from that graph outside it, and selects the pair
branch strictly outside. The two operations agree exactly at their common
boundary. Thus no favorable switch-count selection is assumed, including
when pair prefixes have unbounded length or never enter the triple region.

The small-scale limit (W16) follows with uniform errors from the graph's C2
bound and the Bellman fixed point's weighted bound. Its maximum correctly
accounts for both sides of the physical boundary. This uniform limit is
sufficient for the macro shooting argument; differentiability of the hybrid
graph is neither asserted nor needed.

## Cone, macro return, and exact algebra

For the cone region, I checked G inverse, the matrix N, the leading hazard
formulas, and both boundary slack identities. Under (C1), the lower slack
is strictly positive on both bounding planes. Moving the lower plane inward
also makes the upper slack strict. The normalized cone section is compact,
so the exact analytic map and its hazards preserve these margins for small
beta and radius. The macroscopic pair output lies strictly inside this cone.

For the wedge, the single slack parameter joins macro pair and triple roots
continuously. The projection used to evaluate the passive limit off the
shooting set is auxiliary; it becomes the actual output exactly at a shooting
zero. Opposite shooting signs and opposite transverse return signs therefore
give an actual return by Poincare--Miranda. The argument does not assume a
continuous choice of scalar shooting roots through a phase transition.

Independent exact symbolic checks reproduced:

- the two macro seam formulas (W18) and (W19);
- the rational return identity multiplying the displayed polynomial P;
- the endpoint values -238/25 and 82413/8192;
- both extrema of the Bernstein coefficients of P_w;
- both extrema of the Bernstein coefficients of P_z;
- the unequal-premium sure-face numerator (E3), the decomposition N0+h1*A+
  h3*B+h1*h3*C, and the child123 joining gain (E6);
- every displayed principal minor and all thirteen quotient determinants;
- the identity as the only permutation admitting the signed-chamber pattern.

These checks used exact rational/symbolic arithmetic as an audit of the
displayed calculations. No numerical orbit or unretained program is used as
a premise of the proof. The symbolic checks independently agree with the
complete formulas and sign arguments included in the packet.

The macro estimates give uniformly positive u,v,a0,r and 1-r. In particular
v remains positive at the upper z edge, where its margin is small. The owner0
guard uses only upper bounds on its queried participant rewards. All strict
margins can be chosen uniformly on a compact parameter subset. The second
solo2 wash is exact, including alpha_plus=0, and supplies a positive designated
opponent hazard even when its later roots are idle.

## Complete behavioral and original-game semantics

The chronological word reverses finite portions of the two backward washes.
Its annotation mismatch occurs at exactly the two displayed seams. Bellman
telescoping charges each seam by its own survival weight; it does not charge
the length of a wash. Under any complete replacement by one player, that
player's opponents retain a fixed positive absorption probability per word.
This bounds each seam's total weight by 1/delta_abs and removes the final
continuation term. Both prescribed payoff delivery and the full deviation
upper bound follow, giving regret at most 2E/delta_abs.

This prices every finite deadline, Never, and arbitrary independent private
behavioral replacement. No bounded-controller restriction, public lottery,
execution after an infinite block, or unrealized continuation is used in an
actual strategy. The infinite constructions only determine annotations that
finite periodic strategies approximate.

Opponent absorption under every replacement also justifies adding arbitrary
signed own levels to terminal rewards. Live and literal Never remain zero.
The fixed target ell+V is selected before accuracy. After choosing finite
wash lengths, the opponents' absorption time has a finite expectation uniformly
over the deviator, giving the common sufficiently-large-horizon bound. In that
bound, absorption time counts stages before the first absorbed-reward stage;
with a zero-indexed quitting-date convention the same estimate uses that date
plus one. This harmless indexing convention does not affect the conclusion.

Only player0's grand reward can be queried by the profiles or by the relevant
owner's unilateral replacement. The other grand entries do not enter the
scale threshold. Freely lowering row0 rewards only strengthens its guards,
and its solo2 rule uses alpha_plus in [0,1]. These facts establish the claimed
independence of beta0 from the unrestricted finite reward magnitudes.

## Nonredundancy and complete selection checks

The two calibration rays are actual sixty-entry tables. Their admissible
positive beta values are chosen below the produced existence threshold;
the packet does not invent a numerical bound for that threshold. Both rays
fail the earlier quantitative relative-premium test, the signed-chamber
small-premium test, the complementary pair test, and the equal-premium test.
The permutation and row-scaling analysis prevents evasion by another role
assignment or normalization.

I checked the complete sure-owner case split, including the player2 lower
continuation bound and multiple-sure faces. This excludes all admissible
punishment-vector choices, rather than inferring punishment failure from
stationary failure. The proper stationary support reduction and its final
contradictory bounds exhaust every remaining stationary support.

The protected-set argument uses the maximal protected set and a disjoint
premium trap, so it rejects every permitted protected-player selection.
The two ledger calculations force every nonnegative weight to vanish.
The fourteen proper-child controls have exact or vanishing full child debt
and a fixed quiet-outsider gap; they therefore reject every finite universal
child-debt weighting, including all five withdrawal kinds. They do not claim
to reject a different method selecting a specially favorable child profile.

I also checked the support-at-most-two periodic obstruction, the complete
principal-triple inverse comparison, R0 degree calculation, perfect-matching
comparisons, and all nondiscrete quotient partitions. The distinction between
an exact finite periodic architecture and approximate periodic profiles is
preserved. These are exhaustive checks of the indicated selectors, not a
claim to classify every abstract equilibrium certificate in the repository.

The added result is the two-dimensional unequal-ratio coverage, including
the closed wedge's neutral boundary, with a complete producer and full
consumer. It is more than the previously retained isolated unequal ray or a
stronger profile description on an already covered symmetric class.

## Source and export-gate audit

I inspected the named definitions and relevant statements in:

- `UniformEquilibrium/Quitting/Conjecture/Basic.lean`;
- `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterCharacterization.lean`;
- `UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`;
- `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`;
- `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`;
- `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.

The source references are tracked files. In particular the selected-child
inverse criterion requires the exterior inverse row to be nonnegative, and
the withdrawal consumer bounds outsiders against every child profile. The
packet's negative tests address those actual quantifiers. The terminal Nash
endpoint has the complete-behavior and fixed-payoff scope used here. No Lean
command was run and no new checked declaration is claimed.

The exact statement specifies the finite data and quantifier order. The
producer and auxiliary proofs are present without a conference-file
dependency. Strategic inputs remaining unproduced: none. The probability,
agency, absorbing-reward centering, and finite-horizon translations are
explicit. The exact calibrations and neutral-boundary checks give substantive
positive and attempted-negative tests. The handoff states the intended raw
predicate and conclusion without placing the desired strategy in its input.

Accordingly this packet passes the mandatory mathematical and export gates
within its stated restricted classes. Fin4 and arbitrary unequal-premium
coverage remain open. A change to the reviewed bytes requires checking the
change and recording its new hash; this approval does not automatically
transfer to a modified artifact.
