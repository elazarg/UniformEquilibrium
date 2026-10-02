# Independent review of absorption-weighted forward-packet repair

Reviewer: CODEX_HILBERT. **PASS of the first response**, through its source
reference and before the separator/cap-tight discussion. This is an
ordinary-mathematics review, not a Lean check or export decision.

Reviewed file: `gpt/APPROX.md`, complete-file SHA-256

    3a7e5b844186f587a454b9a7437aef72dd1a365acea3ccda36f92c0fa6b0258d

The reviewed first-response bytes, including the blank line before the
separator, have SHA-256

    68518c21ba6e20199f2e4ebf4c9ef83270da3f9493850f6aa5929bae6c9960d3

The second response is outside this review. The first response uses the
definitions in `questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`:
four independent Boolean root marginals q_i, Never payoff zero, M>0,
|r_i(S)|≤M, F(q,v)=g(q)+c(q)v, a(q)=1−c(q), and unweighted support
optimality against v. Values include both endpoints of each finite packet.
With that setting explicit, no mathematical correction is required.

## 1. Reward-box reduction

The distance inequality is correct coordinatewise: g_i(q)∈[−Ma,Ma],
so distance of F_i(q,v) from [−M,M] is at most c times the old distance.
Products of c are at most exp(−Σa), including a sure-absorption row.
The construction direction is essential and correct: v_(t+1)=F(q_t,v_t),
not an inverse Bellman operation.

If B>M, the first accumulated-charge crossing of L exists in the supplied
packet of charge at least Q+L+1. Its overshoot is at most one, leaving
charge at least Q. Projection at this cut changes its value by at most
η=δ/2. Subsequent differences equal the common product of survival factors
times this initial difference; all new values remain in the reward box.
The root Quit payoff is unchanged by a continuation change, while Continue
changes by c_−i times that change. Thus each supported action's gap changes
by at most η, giving support error δ and punishment floor P−δ.

This checks B=M, L=0, Q=0, empty retained suffix, and c=0. B is fixed before
both requested accuracy and charge. The reduction does not require any
common packet or common profile across accuracies.

## 2. Simultaneous pruning and exact recomputation

Let β=Bρ>0 and let the ordinary row regret be at most Bρ²a. Since ordinary
regret is the weighted mean of the two nonnegative action gaps, any action
whose gap exceeds β has mass less than ρa. At most one action per player
is removed. Moving its mass to the other action gives

    |q̂_i−q_i|≤ρa,       Σ_i|q̂_i−q_i|≤4ρa.

Here the norm is the sum of differences of the four Quit probabilities,
not the doubled ℓ¹ distance between Boolean PMFs. Product coupling and the
Lipschitz bound for 1−∏(1−q_i) yield

    â≥(1−4ρ)a≥a/2.

Every action in the new support was either previously retained or was the
best old action receiving transferred mass. Therefore it had old gap at
most β. All deletions are tested against the ORIGINAL row and annotation;
the subsequent comparison accounts for all simultaneous changes.

Set v̂_0=y_0 and recompute in the forward direction. The reward and value
box gives root-payoff perturbation at most 2BΣ|q̂_i−q_i|≤8Bρa. Thus

    e_(t+1)≤(1−â_t)e_t+B(ρ²+8ρ)a_t.

Putting K=B(ρ²+8ρ)/(1−4ρ), the inequality becomes
e_(t+1)≤(1−â_t)e_t+Kâ_t. Induction from e_0=0 gives e_t≤K for every t.
For ρ≤1/8,

    K/(Bρ)=(8+ρ)/(1−4ρ)≤65/4<17.

No positive lower bound on any individual a_t is used. When a_t=0, the
weighted assumptions force zero Bellman error and zero ordinary regret;
the root remains all-Continue and introduces no error. Sure absorption,
zero-probability inferior actions, and action ties also cause no exception.

For a fixed player, each pure root payoff changes by at most
2BΣ_(j≠i)|q̂_j−q_j| under the opponents' changes. Hence Q_i−C_i changes by
at most 12Bρa, and the continuation change adds at most e_t. Positive-part
action gaps are 1-Lipschitz in this difference, even when the best action
switches. Every new supported gap is therefore at most

    Bρ+12Bρa+17Bρ≤30Bρ≤32Bρ.

The punishment floor loses at most Bρ²+17Bρ≤32Bρ. Summing the rowwise
absorption comparison proves the stated charge retention. The bounds are
independent of H; there is no hidden summation of an unweighted row error.

## 3. Producer-level equivalence and quantifiers

Weighted input implies the original packet assertion by fixing the one
input box, choosing 0<ρ≤min(1/8,δ/(32B)), requesting weighted tolerance
ε=Bρ², and requesting charge 2Q. This is one finite repair at each requested
accuracy/charge, not an infinite compatible sequence.

Conversely, take an original support-δ packet with
0<δ≤min(1,ε/3) and put y_t=v_t+2δ·1. Affinity gives the exact residual
2δa_t·1. Write α=c_−i. Translation raises Continue by 2δα and leaves Quit
unchanged. If Continue becomes best, a used Quit action loses at most
3δ and its regret contribution is at most 3δq_i≤3δa. If Quit is best and
Continue is used, the old support inequality gives the new gap at most
δ−2δα; a strictly positive gap forces α<1/2, hence a>1/2. Its ordinary
regret is consequently at most δ≤2δa. The other pure-support cases have
zero ordinary regret. Thus the required weighted ordinary bound holds.

The new box [−B−2,B+2] is fixed independently of ε and Q, and the punishment
floor improves. This proves equivalence of the two EXISTENTIAL fixed-box,
ALL-accuracy, ALL-charge producer assertions. It is not a same-tolerance,
same-box pointwise equivalence and does not make one finite packet a producer.
The positive global debt and punishment-normal hypotheses are unnecessary
for these conversions; producing unbounded charge under those hypotheses
is still the unanswered question.

## 4. Narrow source overlap and actual contribution

The following declarations were inspected under their imports:

- `QuittingFiniteForwardPacket`,
  `exists_singleSeamProjectiveLasso_of_finiteForwardPackets`, and
  `quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets` in
  `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`
  provide the exact target, its forward orientation, and its unrestricted
  uniform-payoff consumer. The live question agrees with this target.
- `IsQuittingRootSupportApproxNash` in
  `UniformEquilibrium/Quitting/Boundary/Repair/SupportEnlargementAlternative.lean`
  is precisely the unweighted supported-endpoint predicate used here.
- `supportPurifiedRoot_coordinate_close_of_badAction_small` and
  `isQuittingRootSupportApproxNash_supportPurifiedRoot` in
  `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/SurvivalCrossingRepair.lean`
  already supply simultaneous bad-action purification and endpoint stability.
- `abs_quittingRootSuccessorPayoff_sub_of_quitProbability_close` and
  `abs_quittingRootSequenceBackwardPayoff_sub_tailVector_le` in its
  `FinitePrefixCompatibility.lean` companion supply product-law bounds and
  finite compatible recomputation, but the displayed general error bound
  grows with prefix length.
- `isQuittingRootSupportApproxNash_of_tail_close` and
  `abs_quittingCyclicValue_sub_terminalValue_le_of_chargedResidual` in
  `UniformEquilibrium/Quitting/Projective/Lasso.lean` already give additive
  support transfer and period-independent correction of absorption-weighted
  policy residuals for a supplied absorbing cycle.

The bounded search did not find the exact combined finite-packet pruning,
absorption-weighted recomputation, upward-translation converse, and reward-box
reduction as one existing theorem. Its ingredients are established; the
useful addition is the precise length-independent replacement of the live
packet producer's requirements by weighted ordinary regret and weighted
Bellman error. This is a source-specification reduction, not new evidence
that arbitrary game data supplies the required charge.

The response's brief literature limitation is accurate: the original
[2026 APS article](https://link.springer.com/article/10.1007/s00182-026-00982-6)
explicitly characterizes a subset of equilibrium payoffs and allows that
subset to be empty. No general producer is obtained from that citation.
No full review of the paper is needed for the elementary conversions above.

Conclusion: valid and pertinent to the current forward-packet question,
with an explicit weaker-looking but producer-equivalent input. The remaining
unbounded-charge existence claim is correctly left open. No Lean source,
question, frozen export, or shared index was changed.
