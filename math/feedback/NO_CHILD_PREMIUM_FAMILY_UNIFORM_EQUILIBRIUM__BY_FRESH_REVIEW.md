# Independent fresh whole-proof review of the cyclic premium family

**Verdict: PASS, including export admission.** No unresolved mathematical
objection remains. This is an independent review of the complete final
manuscript, not approval inferred from its component reviews. I did not author
the producer, cone certificate, completion lemma, or consumer.

Reviewed manuscript:
`math/exports/NO_CHILD_PREMIUM_FAMILY_UNIFORM_EQUILIBRIUM.md`, 562 lines, SHA256
`dcd61aa1226bb788b9e4149cf8168428420fda388f53794b810df01e9fe67705`.
The complete inline checker is byte-identical to
`math/experiments/NO_CHILD_PREMIUM_FAMILY_CHECK.py`, SHA256
`eb31d4d6b1d733fa8ddafa06ab942df2fc2559e2de00ddc0dd9833edbd091446`.
I extracted that inline program from the final manuscript and independently
executed it successfully. Both polynomial boxes passed, with 1008 and 1428
exact tensor Bernstein coefficients respectively.

## Exact scope

For every finite real M>=11 and every raw completion specified in Section1,
the manuscript constructs actual finite private independent-hazard profiles
whose native full debts and all four marginal Never probabilities tend to
zero. A fixed subsequence target is b_*e2 with b_* in[3/16,B]. This supplies
an absorbing zero-debt point in the augmented native semantic carrier; it
does not assert realization by one absorbing exact equilibrium profile.

Arbitrary signed recipient offsets and positive recipient scales give the
stated original-game uniform payoff, against all behavioral deviations.
Separately, the canonical original table4+Z^M is covered for every real M.
The lower-M argument does not claim arbitrary signed offsets or the broader
completion class there. Singleton geometry and twelve observer nonsingleton
coordinates remain restricted. Arbitrary Fin4 is not solved.

## Complete construction audit

1. **Raw rewards and proxy semantics.** The table rules specify every reward
coordinate. The 32 varying nonsingleton coordinates are genuinely raw
conditions: twenty arbitrary coordinates and twelve one-sided or coupled
coordinates. The eighteen invisible entries are never an observer's own
payoff at an outcome reachable by that observer's unilateral deviation from
the displayed support grammar. Pivot deviations are separately priced using
every relevant participant coordinate. The general-M joining bounds are the
stricter baseline bounds in the final manuscript, not the stronger M14-only
quiet estimate from an earlier completion idea.

2. **Finite proxy closure.** I checked both root recursions and the different
continuation coefficients: joint survival for payoff and opponent survival
for a player's full cap. Exact root Nash sends a diagonal annotation to a
diagonal annotation. Fixed finite words are separately nonexpansive in payoff
and cap, and the cap map is monotone. The finite-dimensional closure is
bounded and preserved by any fixed prefix. Consequently its successive phase
limits have actual finite-word approximants retaining U, full B, and every
N_i. No strategy is executed after an infinite phase and no finite switch is
assumed to hit a zero cap exactly.

3. **Explicit prefix.** I checked all three singleton phases, including the
adaptive speed K for arbitrary Z0(02),Z1(12). The ratio v1/v0>=1/2 makes
both positive quiet joining increments affordable. The condition Z3(23)<=1
prices its initially zero cap. The phase endpoints and survivals depend on
the singleton rewards and remain exactly those displayed. In the owner1
segment, x>=p/4 is essential because observer0 has a negative annotation.
One first atom, seven minimum atoms, and one tied atom give exactly nine
atoms. Their endpoint is lambda(-25,0,3M+62,5M-5). The joint bound5/8 and
all four marginal bounds in(4) are correct for every b>=1/10. The last
marginal bound may approach one as M grows, but is strictly below one for
each fixed finite table, which is all the consumer needs.

4. **Switched observer producer.** The face01 condition is exactly the quiet
observer3 comparison. When it fails, the scalar equation has an increasing
left side with opposite signs at its two endpoints, producing one positive
013 root. Thus no failed full-support equation is ignored. The coarse odds
bounds follow from V<10/3 and make all sign arguments valid. Both full and
face roots preserve the observer orthant(-,+,+); the quiet observer's output
is its Continue value, which need not equal its immediate-Quit offer.

5. **Descent and size.** The vector(-3,5,4) multiplies the observer singleton
matrix to(-1,-1,-1). The exact diagonal recurrence therefore gives the
claimed strict Lyapunov descent. Its sign argument uses the newly proved
output signs and includes face roots. This proves summability of all odds.
The size estimates use C3<=w, not equality on faces. I checked the displayed
coefficient209/42 and the inequality6M^2+599M-275>0. They give Mt<5/6 and
Ma<1 before the upper cone is invoked, so there is no circular bootstrap.

6. **Observer limit.** Active comparisons force S,v to zero as the odds tend
to zero. Summable odds give convergence of w. A positive limiting w would
force every sufficiently late root onto face01, where S'=5S/(4+S)>S near
zero. This contradicts S>0 and S->0. Thus all three observer values tend to
zero without assuming that the support eventually becomes full.

7. **Exact upper cone.** I derived the scalar boundary comparison at d_U and
checked its reduction to E>0. K is positive even if the hypothetical Q3 is
negative; R has the stated positive numerator. The actual next quiet cap is
at least Q3, and increasing it decreases the scalar function at the boundary,
so the same estimate covers a preceding face root. If the boundary lies
below the admissible scalar interval the cone conclusion is immediate;
otherwise strict monotonicity applies inside that interval. The two compact
parameter substitutions cover every finite M>=11, including M=14 in both
boxes. The tensor conversion formula is correct. Nonnegative coefficients
and the asserted strictly positive index sets prove strict positivity at
all allowed endpoints because t>0 and finite M excludes the h=0 limit.
No floating-point arithmetic or numerical orbit is used in acceptance.

8. **Pivot and actual return.** The entry root satisfies the upper cone.
For full roots, C2<=w/2 follows from that cone; face roots have C2<=0.
The invariant beta>=w/2 is checked using the actual quiet observer value on
faces. Nonnegative passive pivot rewards increase beta and decrease its
joining gains, while the specified participant upper bounds keep the
baseline C2 estimate valid. The convex-average bounds retain
beta in[3/16,B], and summability proves its convergence. This supplies a
returned b' for every input in the fixed bounded interval, without assuming
continuity of the return selector or a return fixed point.

9. **Actualization and signed offsets.** Reversely concatenated approximate
returns accumulate at most K eta error and multiply each marginal survival.
Replacing the terminal native proxy b0e2 by actual Never lowers its cap,
while the payoff loses exactly nu*b0e2. The debt bound(15) follows. One orbit
and one convergent subsequence fix b_* before accuracy. Under a unilateral
deviation, joint Never can change only on the event that every opponent
chooses Never, whose probability is the product of their marginal Never
masses. This proves(16) for either sign of kappa_i. Joint survival alone
would not suffice for this signed-offset step; the proof supplies the needed
per-player contraction explicitly.

10. **All finite horizons and lower M.** The direct horizon estimate correctly
allows delayed negative solo rewards, at an additional cost at most
abs(kappa_i)h_i. Choosing the profile first and the threshold afterward
gives the same profile at every larger horizon. For canonical M<=11, I
checked the inserted-reward sums and the predecessor-closure argument for
proper active supports. They produce the exact boxed selected-singleton
sublevel-return predicate, rather than assume it. The chosen bound
quittingRewardBound+1 satisfies both bounds of the named checked compiler.

## Source and implementation audit

I inspected the exact statements of the diagonal proxy and literal-splicing
theorems in `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, the
full max recursion in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`,
and the stopping-law payoff and cap correspondences in
`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`.
The fixed-target theorem
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
retains actual members of the supplied profile family and has no sign
restriction on own singleton rewards.

For Section8 I also inspected `exists_isZeroQuittingRootNash`,
`quittingWeightedQuitPremium_eq_fullCoalitionAverage`,
`HasBoxedSelectedSingletonSublevelReturn`, and
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_on_subbox`
in the named tracked files and
`UniformEquilibrium/Quitting/Projective/SelectedSingletonSublevelReturnSmoothDrift.lean`.
All hypotheses of the lower-M consumer are actually supplied. These existing
interfaces do not constitute a Lean proof of the new raw family theorem;
no Lean compilation or formalization seal is claimed here.

## Falsification attempts and admission

I checked the negative intermediate cap, improper finite switching,
face/full boundary equality, potentially negative baseline Q3, unbounded
passive pivot rewards, the loss of uniform marginal contraction as M tends
to infinity, arbitrary signed offsets, and the target/horizon quantifier
order. None creates a gap for a fixed finite table. I also checked that the
lower-M corollary has a complete tracked consumer rather than a dependency
on another conference packet.

For concrete nonredundancy beyond the exact M14 theorem, I independently ran
the existing complete benchmark checker at M=15. It excludes all80 nonzero
stationary patterns in648 exact nodes and all65 sure-root patterns. The raw
upper tests sum to4 sum(w)>0, the joining-ledger tests sum to
4w0+3w1+2w2+3w3>0, anchor predecessor closure would require14^4<=5^4,
and every proposed pair has a negative participant endpoint. The singleton
geometry, no-child obstruction, protected-row obstruction and scalar-circuit
denominator obstruction remain the same as in the maintained benchmark
audit. These are complete selection-set failures of the identified criteria,
not failure of one guessed witness. The stationary exclusion is not used to
reject a nonstationary punishment-tail consumer.

The exact M14 packet does not cover this M=15 table or the entire unbounded
premium range. The new theorem gives a complete producer on that range and
its explicit raw completions. No continuation, return, rate, correction
strategy, or other strategic witness remains an assumed input. Thus the
conditional-export exception is unnecessary. The self-contained manuscript
and its exact certificate satisfy the mathematical admission gate. The
result is a substantive new family closure, with arbitrary Fin4 still open.
