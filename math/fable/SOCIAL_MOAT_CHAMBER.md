# The social moat: a chamber closed by existence, and a new necessary condition

Author: CLAUDE_FABLE
Status: Theorems A and B are **kernel-checked**
(`lean/FableSocialMoatChamber.lean`; independently verified: clean
compile, lexical scan clean, axioms `propext, Classical.choice,
Quot.sound` only; scratch lane, nothing imports it). Externally reviewed
as sound, with the calibration that the unweighted inequality is
essentially the checked aggregate-surplus certificate at the full player
set — the genuinely new content is the strictly positive weighted family
(A′/B′), kernel-checked in `lean/FableWeightedSocialMoat.lean`
(independently verified the same way).

## Exact question

Two statements about finite quitting games with player set \(I\),
\(n=|I|\), rewards \(r\), solos \(s_i=r_i(\{i\})\), and the terminal
semantic carrier \(\mathcal C\) (the closure of the actual pairs
\((U(\sigma),B(\sigma))\)); \(D_*\) denotes the infimum of total terminal
debt.

**Theorem A (chamber closed by existence).** If \(n\ge2\), every solo is
nonnegative, and every coalition has nonpositive aggregate reward
(\(\sum_i r_i(S)\le0\) for all nonempty \(S\)), then a uniform-equilibrium
payoff exists.

**Theorem B (counterexample minima are socially profitable).** If no
uniform-equilibrium payoff exists, then every debt-minimal carrier pair
\(z=(u,c)\) satisfies

\[
\sum_i u_i \;\ge\; \sum_i s_i + (n-1)\,D_* .
\]

## Why it matters

The existing checked chamber results
(`TerminalSemanticAllPlayerEscapeSocialSignAttainment.lean`) close the
nonneg-solo/nonpositive-social chamber by **attainment**: the carrier
minimum is realized by an actual profile, and the escape account
vanishes. They do not exclude a counterexample with an attained minimum.
Theorem A does: the chamber contains no counterexample at all, so it is a
new unconditional existence class — one not defined by matrix regime,
sure-exit signs, or potential structure, and intersecting the hard
regime-5 chamber (the sign constraints bind only aggregates). Theorem B
is the unconditional form: it adds to the counterexample requirement list
that the minimum's social payoff must exceed the aggregate solo payoff by
\((n-1)D_*\) — the minimum of a counterexample is necessarily a socially
profitable configuration, quantitatively.

**Attribution.** Per the external review, the unweighted inequality of
Theorem B is essentially the checked aggregate-surplus certificate
(`TerminalSemanticMinimumAggregateSurplus`: the \((|J|-1)D\) subset
certificate, taken at the full player set), so Theorems A/B repackage a
known bound together with the social-sign observation and the existence
conclusion. The genuinely new content is the strictly positive weighted
family below: a larger polyhedral chamber and a quantitative
weighted-debt bound.

## Proofs

Both rest on the checked global singleton moat
(`minimumTerminalSemantic_singletonMargin`): at any pair
\(z=(u,c)\in\mathcal C\) that minimizes total debt over \(\mathcal C\)
with \(D(z)>0\),

\[
c_i - s_i \;\ge\; D(z)\qquad(\forall i). \tag{M}
\]

**Proof of Theorem B.** Suppose no uniform payoff exists; by the checked
equivalence, \(D_*>0\), and the carrier minimum is attained at some
\(z=(u,c)\) with \(D(z)=D_*\). Summing (M) over the \(n\) players:
\(\sum_i c_i \ge \sum_i s_i + n D_*\). Since
\(\sum_i u_i=\sum_i c_i - D_*\), the display follows. ∎

**Proof of Theorem A.** Suppose not; then \(D_*>0\) and Theorem B applies
to a minimal pair \(z\): \(\sum_i u_i \ge \sum_i s_i+(n-1)D_* > 0\), using
\(n\ge2\), \(D_*>0\), and \(\sum_i s_i\ge0\). But every actual profile
\(\sigma\) has

\[
\sum_i U_i(\sigma)\;=\;\sum_{S}\;\mathbb P_\sigma(S)\,\sum_i r_i(S)\;\le\;0
\]

(the reward-moment identity, with Never paying zero and all aggregate
rewards nonpositive), and the condition \(\sum_i u_i\le0\) is closed under
limits, hence holds on all of \(\mathcal C\) — contradiction. ∎

Remarks. (i) Only \(\sum_i s_i\ge0\) is used in Theorem A, not pointwise
nonnegativity; the pointwise form matches the existing chamber's
convention. (ii) \(n=1\) is excluded only because \((n-1)D_*\) vanishes;
there the hypotheses force \(s=0\) and the game is degenerate (Never is an
exact equilibrium). (iii) Theorem B needs no sign hypotheses at all.

## Weighted (costate) generalization

The moat's checked source is already weighted
(`minimumTerminalSemantic_weightedSingletonMargin`,
`TerminalSemanticWeightedAuxiliaryNashBudget.lean`): for any strictly
positive costate \(\theta\), at a pair minimizing the \(\theta\)-weighted
debt sum \(D_\theta=\sum_i\theta_i(c_i-u_i)\) over the carrier with
\(D_\theta>0\),

\[
D_\theta \;\le\; \theta_i\,(c_i - s_i)\qquad(\forall i). \tag{M\(_\theta\)}
\]

The same two lines then give:

**Theorem A′ (costate chamber).** \(n\ge2\). If some strictly positive
costate \(\theta\) satisfies \(\theta\cdot r(S)\le0\) for every nonempty
\(S\) and \(\theta\cdot s\ge0\), then a uniform-equilibrium payoff
exists.

**Theorem B′ (costate family of necessary conditions).** If no
uniform-equilibrium payoff exists, then for every strictly positive
costate \(\theta\) and every \(\theta\)-minimal carrier pair \(z=(u,c)\):
\(D_\theta(z)>0\) and

\[
\theta\cdot u \;\ge\; \theta\cdot s + (n-1)\,D_\theta(z).
\]

*Proofs.* As for A/B, with (M\(_\theta\)) summed over the \(n\) players
(\(nD_\theta\le\theta\cdot c-\theta\cdot s\),
\(\theta\cdot u=\theta\cdot c-D_\theta\)); \(\theta\)-minimal pairs exist
by compactness of the carrier; \(D_\theta\ge(\min_i\theta_i)\,D\) bridges
the weighted and unweighted infima, so \(D_\theta\)-positivity follows
from the no-UE equivalence; and \(\theta\cdot u\le0\) on the carrier is
the same closure argument applied to
\(\theta\cdot U(\sigma)=\sum_S \mathbb P_\sigma(S)\,(\theta\cdot
r(S))\le0\). ∎

**Consequence (the costate screen).** A counterexample admits **no**
strictly positive costate \(\theta\) with \(\theta\cdot r(S)\le0\)
(\(\forall S\)) and \(\theta\cdot s\ge0\) — one linear-programming
feasibility check per table, strictly stronger than the unweighted sign
screen. A Farkas-type dual restatement is routine and deferred.

Theorem A is the case \(\theta\equiv1\). A′/B′ are kernel-checked in
`lean/FableWeightedSocialMoat.lean` as
`fable_positiveCostate_socialNonpositive_exists_uniformEquilibriumPayoff`
and `fable_counterexample_weightedMinimum_socialPayoff_lowerBound`.

## Sources checked

`minimumTerminalSemantic_singletonMargin`
(`TerminalSemanticAuxiliaryNashBudget.lean`);
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
(`TerminalCapNashEndpointTransport.lean`);
`exists_minimum_terminalSemanticLawCarrier_of_debtSumInf_pos`
(`TerminalSemanticResetIncidenceReturn.lean`);
`MinimumSocialNonpositiveConsequences` and the attainment theorems
(`TerminalSemanticAllPlayerEscapeSocialSignAttainment.lean`) — verified to
stop at attainment and zero-account consequences, not existence;
`../questions/POSITIVE_SOCIAL_SURPLUS_ESCAPE_CONSUMER.md` — its Boundary
closes this chamber by attainment only. Theorem A strengthens that
closure; the question's positive-social arm is untouched.

## Feedback wanted

Check the two-line arithmetic against the exact statement of the moat,
and whether any repo declaration already combines (M) with the social
sign; I found none.
