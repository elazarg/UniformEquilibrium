# Independent audit: absorption-weighted finite-packet repair

Reviewer: CODEX_FRECHET_CYCLE. Status: PASS, ordinary mathematics; no Lean
build or formalization performed. No other review was read before this verdict.

## 1. Frozen surfaces and precise scope

I read the complete FIRST response of `../gpt/APPROX.md` before giving a
verdict. The full input SHA-256 is
`3a7e5b844186f587a454b9a7437aef72dd1a365acea3ccda36f92c0fa6b0258d`;
the first response, excluding the separating rule, has SHA-256
`68518c21ba6e20199f2e4ebf4c9ef83270da3f9493850f6aa5929bae6c9960d3`.

After fixing my independent mathematical verdict, I read all 258 lines of
`../notes/CODEX_HILBERT__ABSORPTION_WEIGHTED_FORWARD_PACKET_REPAIR.md`,
SHA-256 `97c68ad84f3dd9796c5c45c62798ffb686c3dacd7aad974ad12f956e4c52fd2a`.
That complete reconstruction also PASSES and faithfully assembles the original
claims, including the existing downstream packet consumer. I did not read the
HILBERT feedback referenced by its introduction.

Fix four players, independent product roots q, rewards |r_i(S)|≤M, M>0,
and punishment floor P. Write c(q)=∏ᵢ(1−q_i), a(q)=1−c(q),
F(q,v)=Σ_(S≠∅)p_q(S)r(S)+c(q)v. With pure Quit and Continue payoffs Q_i
and C_i, set A_i=max(Q_i,C_i) and ordinary regret R_i=A_i−F_i.

The exact-packet assertion is: one fixed finite box, chosen before both
δ>0 and charge target Q≥0, contains finite forward packets satisfying exact
Bellman matching, support-δ Nash, floor P−δ, and total absorption charge≥Q.
The weighted assertion instead allows Bellman defect and ordinary regret
at most εa(q_t), with floor P−ε, at every positive ε and every charge target,
again in one fixed box. No endpoint, prescribed anchor, actual-continuation
realizability, or common infinite source is imposed on these annotations.

The proved conclusions are exactly:

- these two all-accuracy assertions are equivalent;
- the exact assertion is unchanged by requiring the reward box [−M,M]⁴;
- a supplied weighted packet has an explicit repair with error independent
  of its length and retaining at least half its charge at the stated scale.

This does not construct packets with unbounded charge from arbitrary raw
tables, positive SUM debt, positive MAX debt, or a contrary-case assumption.
It does not preserve extra source/endpoint constraints that the packet
interface does not request. The text makes the missing producer explicit.

## 2. Independent checks of the repair constants

Take B≥M and 0<ρ≤1/8. Suppose local Bellman error and R_i are at most
Bρ²a_t. Delete each action with original pure-action regret>Bρ and transfer
its mass to the other action. At most one action per player is bad; its
mass is at most ρa_t. The receiver is an original best action, even if
originally unused. Hence every newly supported action passed the original
Bρ gap test, and

    |q̂_i−q_i|≤ρa_t,   Σᵢ|q̂_i−q_i|≤4ρa_t,
    â_t≥(1−4ρ)a_t≥a_t/2.

The norm is the sum of differences of Quit probabilities, not PMF ℓ¹.
Product coupling gives a successor-payoff change≤2BΣᵢ|q̂_i−q_i|.
Recompute v̂_0=y_0 and v̂_(t+1)=F(q̂_t,v̂_t). The B box is invariant.
For e_t=‖v̂_t−y_t‖∞, direct subtraction gives

    e_(t+1)≤(1−â_t)e_t+B(ρ²+8ρ)a_t
            ≤(1−â_t)e_t+Kâ_t,
    K=B(ρ²+8ρ)/(1−4ρ)≤17Bρ.

The last inequality follows from (ρ+8)/(1−4ρ)≤17 on [0,1/8]; no
asymptotic or numerical approximation is needed. Induction starts at zero
and yields e_t≤K for every packet length.

For one player's action gap, coupling its THREE opponents changes Q_i−C_i
by at most 4BΣ_(j≠i)|q̂_j−q_j|≤12Bρa_t. This uses the individual bad-mass
estimate, not just its coarser four-player sum. Continuation replacement
adds at most e_t. Thus every supported action has regret≤30Bρ≤32Bρ.
The floor loses at most Bρ²+17Bρ≤32Bρ. Charge retains the stated factor.

At a_t=0 both input errors vanish and no positive bad mass is deleted;
the recurrence still holds without division by a_t. Sure absorption also
causes no exception. The reconstruction explicitly assumes M>0, which
avoids dividing by B=0. If one wishes to allow zero reward bounds, the
all-zero B=0 case is trivial and can be stated separately.

## 3. Falsification of the reverse implication attempted

The nontrivial reverse direction is valid; ordinary support error alone
would not be absorption-weighted, but the common upward translation fixes
the rare-action problem. Given an exact support-δ packet, put y_t=v_t+2δ·1.
Then the policy residual is exactly 2δa_t·1.

Write α=∏_(j≠i)(1−q_j). Continue's payoff rises by 2δα, while Quit's is
unchanged. If Continue is best afterwards, every used Quit has gap≤3δ,
and its weighted contribution is≤3δq_i≤3δa_t. If Quit is strictly best
and Continue is used, its new gap is≤δ−2δα, so α<1/2 and a_t>1/2.
Its ordinary regret is then≤δ≤2δa_t. Zero gaps and unused inferior
actions have zero contribution. These cases cover pure roots, ties,
arbitrarily small absorption, and all-Continue.

Choose 0<δ≤min(1,ε/3). The enlarged box [−B−2,B+2]⁴ is fixed before
ε and Q, and the floor improves. Conversely, choose
0<ρ≤min(1/8,δ/(32B)), request weighted tolerance Bρ² and charge 2Q,
and apply the repair. This proves the genuine quantified equivalence,
not a same-error or same-box equivalence for one fixed packet.

## 4. Reward-box reduction checked

The affine terminal contribution gives

    dist∞(F(q,v),[−M,M]⁴)≤c(q)dist∞(v,[−M,M]⁴).

Thus exact forward evolution contracts excess distance by the product of
c(q), bounded by exp(−Σa). For η=δ/2 and
L=max(0,log((B−M)/η)), request error δ/2 and charge Q+L+1.
Discard through the first cumulative-charge crossing of L. Its charge is
at most L+1, so the retained suffix still has charge≥Q. Project its first
annotation to the reward box and recompute using unchanged roots.
The error is≤η at every retained value, not multiplied by length.

Each pure-action regret is the positive part of Q_i−C_i or its negative;
it changes by at most η, including when the identity of the best action
switches. The floor and support bounds therefore become δ. The B=M,
L=0, Q=0, sure-absorption, and empty-suffix cases are harmless. No common
horizon or quantitative horizon bound is asserted.

## 5. Narrow production comparison and consumer correspondence

I used the Simon survival/prefix and projective-lasso entries of
`../docs/TOOLKIT.md`, then inspected the following named source surfaces
under their imports. This was a static audit, not a Lean build.

In `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/SurvivalCrossingRepair.lean`:
`quittingSupportPurifiedRoot`,
`supportPurifiedRoot_coordinate_close_of_badAction_small`,
`supportPurifiedRoot_coordinate_close_of_mul_bound`,
`isQuittingRootSupportApproxNash_supportPurifiedRoot`, and
`isQuittingRootEndpointStableWithin_of_uniformBound` already implement
the local bad-support deletion and product-law stability ingredients.

In `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/FinitePrefixCompatibility.lean`:
`abs_quittingRootSuccessorPayoff_sub_of_quitProbability_close`,
`abs_quittingRootSequenceBackwardPayoff_sub_tailVector_le`, and
`reached_supportPurifiedPrefix_compatible` already perform exact finite
recomputation. Their displayed finite-window error is proportional to
remaining length, and they consume an actual reached source window.

In `UniformEquilibrium/Quitting/Projective/Lasso.lean`,
`abs_quittingCyclicValue_sub_terminalValue_le_of_chargedResidual` already
uses absorption-weighted policy errors and Bellman contraction on a
supplied absorbing cycle. That is not the general finite forward repair
with simultaneous ordinary-to-support purification proved here.

Finally, `QuittingFiniteForwardPacket` and
`quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets`
in `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`
have precisely the exact packet data and all-accuracy/common-compact-carrier
quantifiers above. They impose no anchor or actual-source provenance.
The reconstruction's use of this existing consumer is therefore legitimate:
WP, if produced, also implies one fixed uniform-equilibrium payoff. No
new checked declaration or unconditional producer is claimed.

The useful combined contribution is the length-independent weighted finite
repair, its two-way producer equivalence, and reward-box normalization.
Its local ingredients and downstream consumer are already available.
I did not verify the original's final external literature aside; it is
not a dependency of any theorem audited here.

## 6. Handoff

PASS for the original first response and the exact frozen reconstruction
identified above. No mathematical correction is required. The next
substantive mathematical question remains production of unbounded total
absorption charge at every positive weighted tolerance; this review does
not begin that investigation.
