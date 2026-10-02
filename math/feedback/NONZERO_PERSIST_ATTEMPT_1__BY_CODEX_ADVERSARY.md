# Adversarial review of the finite hazard-capacity reduction

Reviewer: Codex Adversary

Reviewed material:

- gpt/NONZERO_PERSIST_ATTEMPT_1.md, especially Sections 1--2 and its claimed consumers;
- Sections 5--6 of notes/CODEX_STRENGTHEN__FIN4_NONZERO_PERSISTENT_SPINE_SELECTION.md.

## Verdict

I found no counterexample to the mathematical result. The compact-cover
extraction, the constant \(5\), the chronological seam orientation, the
fixed-label conclusion, and both persistence consumers are sound.

The strongest accurate verdict is:

> **PASS as an ordinary-mathematics reduction after the mandatory
> clarifications below; FAIL the export gate in its present split/sketched
> form.**

The export failure is not a false theorem. The two files presently omit the
exact seam/debt ledger needed by the two-label consumer, omit the quantitative
error ledger needed by the unique-label consumer, and leave the state space of
the capacity potential underspecified. Those points must be repaired in a
self-contained packet. No existing checked declaration packages the new
approximate-spine adapter.

## 1. The compact-cover extraction survives falsification

Let

\[
 C_t=\sum_{s<t}h(x_s),\qquad 0\leq h(x_s)\leq4.
\]

For a cover of \(K\) by \(N\) sets of diameter less than \(\delta\), choose a
block with \(C_n>5N\). The first crossing \(t_j\) of level \(5j\) exists for
each \(0\leq j\leq N\). If \(t_j>0\), minimality and the one-row bound give

\[
 C_{t_j}=C_{t_j-1}+h(x_{t_j-1})<5j+4.
\]

The formula also holds at \(j=0\), where \(t_0=0\). If two marked payoffs with
indices \(a<b\) lie in one cover cell, their intervening chronological
subblock has

\[
 C_{t_b}-C_{t_a}>5(b-a)-4\geq1.
\]

Thus the displayed weaker bound by \(1\) is valid. The gap \(5=4+1\) is the
correct safe constant.

For \(\delta_k\downarrow0\), compactness first gives a subsequence
\(a_k\to z\); because \(\lVert a_k-b_k\rVert_\infty\to0\), also \(b_k\to z\).
A further fast subsequence can ensure

\[
 \sum_k\lVert b_k-a_{k+1}\rVert_\infty<\eta/3.
\]

At the last root of block \(k\), the old exact successor is \(b_k\), while
the actual next flattened annotation is \(a_{k+1}\). Therefore the seam is in
the direction used in the proposal. Tail Lipschitz continuity gives Bellman
error at most \(d_k=\lVert b_k-a_{k+1}\rVert_\infty\); applying the same
estimate once to the deviated root and once to the prescribed root gives
root-Nash error at most \(2d_k\). Hence the total residual is less than
\(\eta\).

Every extracted word carries hazard at least \(1\), so the flattened word has
divergent total marginal hazard. Since there are four fixed labels,

\[
 \sum_t\sum_{i\in\operatorname{Fin}4}q_i(y_t)=\infty
\]

implies that at least one single label \(p\) has
\(\sum_tq_p(y_t)=\infty\). This \(p\) is fixed over that entire flattened
sequence. It may depend on the selected subsequence and on \(\eta\); no common
label across all accuracies has been proved or is needed, because one finite-
total-error spine already suffices.

Trace provenance is not used in this compact argument after one has obtained
same-table exact blocks. It remains essential when claiming that a proposed
Fin4 producer actually supplies those blocks.

## 2. The two-persistent semantic-seam adapter is valid

Write

\[
 P_t=F_{y_t}(w_{t+1}),\qquad
 S_t=(w_{t+1},w_{t+1}),\qquad
 C_t=\operatorname{Prefix}_{y_t}(S_t).
\]

For player \(i\), let

\[
 D_{t,i}=C_t^{\mathrm{cap}}(i)-C_t^{\mathrm{prescribed}}(i).
\]

Because \(S_t\) is diagonal, the cap coordinate of \(C_t\) is the maximum of
the pure-Quit and pure-Continue endpoint values, while \(P_t(i)\) is their
mixture under \(y_t(i)\). Thus \(D_{t,i}\geq0\). Hypothesis (33), which ranges
over every mixed marginal replacement and hence over both pure endpoints,
gives

\[
 0\leq D_{t,i}\leq\nu_t. \tag{A}
\]

After shifting to time \(T\), define the seam-chain fields at calendar
\(n\) by

\[
 \text{root}(n)=y_{T+n},\quad
 \text{candidate}(n)=C_{T+n},\quad
 \text{successor}(n)=S_{T+n}.
\]

The exact-step field has the correct orientation by definition. Its seam is
between \(S_{T+n}\) and \(C_{T+n+1}\), not between \(C_{T+n}\) and
\(S_{T+n}\). For every player,

\[
\begin{aligned}
 \operatorname{prescribedSeam}(n)
   &\leq \beta_{T+n+1},\\
 \operatorname{capSeam}(n)
   &\leq \beta_{T+n+1}+\nu_{T+n+1},\\
 \operatorname{totalSeam}(n)
   &\leq 2\beta_{T+n+1}+\nu_{T+n+1},\\
 \operatorname{debt}(\text{candidate}(0),i)
   &\leq\nu_T. \tag{B}
\end{aligned}
\]

The first inequality is (32). The second is the triangle inequality together
with (A); the third is the sum of the first two. Uniform boundedness of \(w\)
and finiteness of the reward table give the prescribed- and debt-bounded
fields of QuittingBoundedSeamChain.

Since \(\beta,\nu\) are nonnegative and summable, choose \(T\) so that the
tails of \(2\beta+\nu\), the tail of \(\beta\), and \(\nu_T\) are below the
requested accuracy. This produces a QuittingSummableSeamSource at every
positive accuracy.

If two distinct fixed marginal labels are nonsummable, deleting any player
leaves at least one of them. The checked
HasTwoPersistentQuittingMarginals.survival supplies joint and every
player-deleted survival for these same shifted roots. Therefore
quittingGame_exists_uniformEquilibriumPayoff_of_summableSeams_all_errors
applies. Its route through chronological terminal semantic debt controls a
replacement of the player's complete behavioral strategy, not merely a
stationary deviation.

No semantic-seam counterexample remains. The inequalities (A)--(B) are,
however, mandatory in an export proof; the current prose only asserts them.

## 3. The unique-persistent adapter is also valid

Suppose \(p\) is the unique nonsummable marginal label. Then every other
marginal is summable, and
summable_quittingOpponentClockCharge_iff gives summability of \(p\)'s
opponent clock.

Let \(U_t\) be the literal terminal payoff vector of the root suffix starting
at \(t\). The nonsummable \(p\)-clock forces joint survival to zero on every
suffix. Consequently \(U\) is bounded and satisfies the exact recursion

\[
 U_t=F_{y_t}(U_{t+1}).
\]

Let \(B_t=\sum_{s\geq t}\beta_s\). Iterating the one-step contraction

\[
 \lVert w_t-U_t\rVert_\infty
 \leq\beta_t+c_t\lVert w_{t+1}-U_{t+1}\rVert_\infty,
 \qquad c_t=\Pr_{y_t}(\text{all Continue}),
\]

and using boundedness plus vanishing joint survival gives

\[
 \lVert w_t-U_t\rVert_\infty\leq B_t. \tag{C}
\]

The checked abs_value_sub_soloReward_le_of_bounded_bellman, applied to
\(U\), does not require root Nash and gives, coordinatewise,

\[
 |U_t(i)-R(i)|
 \leq2M\,\operatorname{OpponentClockTail}(p,t),
 \qquad R=\operatorname{SoloReward}(p). \tag{D}
\]

Thus (C)--(D) give an explicit nonnegative target-error sequence tending to
zero.

Choose dates \(t_n\to\infty\) with \(q_p(y_{t_n})>0\). At such a date, for
each outsider \(i\ne p\), approximate root Nash and Bellman give

\[
\begin{aligned}
 \operatorname{FixedOpponentsQuitValue}(y_{t_n},i)
 &=\operatorname{RootQuitPayoff}(w_{t_n+1},y_{t_n},i)\\
 &\leq F_{y_{t_n}}(w_{t_n+1})_i+\nu_{t_n}\\
 &\leq w_{t_n,i}+\beta_{t_n}+\nu_{t_n}. \tag{E}
\end{aligned}
\]

The proposal's error \(\beta_t+\nu_t\) in (E) is correct. One must **not** add
a solo-reprojection term to (E):
isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits performs that
deletion internally and charges it separately through its hazardError. Use:

- hazardError(n) equal to \(p\)'s opponent-clock charge at \(t_n\);
- targetError(n) equal to
  \(B_{t_n}+2M\operatorname{OpponentClockTail}(p,t_n)\);
- quitError(n) equal to \(\beta_{t_n}+\nu_{t_n}\).

All three vanish. Punishment normality is needed only for the owner \(p\),
although the maintained Fin4 hard residual supplies it for every player. The
checked deleted-Quit consumer ends in a punishment-completed solo profile and
covers unrestricted behavioral deviations and the uniform-horizon
quantifiers.

## 4. Fin4 consequence and the capacity potential

The repository update at commit a0842d1 provides the checked exact-spine
endpoints:

- IsCanonicalExactQuittingNashBellmanSpine.isUniformEquilibriumPayoff_soloReward_of_uniquePersistent;
- FinFourQuantitativeFullSupportHardResidual.all_marginalQuitHazards_summable;
- all_marginalQuitHazards_summable_of_no_uniformPayoff.

The latter two concern supplied **exact** spines. They do not by themselves
consume the approximate spine selected by the capacity argument. Sections
5--6 add precisely the still-unchecked ordinary adapter analysed above.

Combining that adapter with the checked fact that the no-uniform Fin4 hard
residual is punishment-normal makes the advertised capstone mathematically
valid:

> In the punishment-normal Fin4 residual, unbounded finite hazard capacity
> for same-table exact Nash--Bellman blocks in one compact value set implies
> existence of a uniform-equilibrium payoff.

Equivalently, a hypothetical no-uniform-payoff Fin4 game must have bounded
capacity in every such actual-source family.

There is one genuine qualification to Section 2. The state \(s\) in

\[
 \Phi(s)=\sup\{H(B):B\text{ begins at }s\}
\]

must be a node of a prepend-closed directed source graph, including whatever
history/provenance makes continuation legal. If \(s\) is only a payoff vector
while legality depends on its incoming trace, a block legal after one trace
need not be prependable to another edge ending at the same payoff, and

\[
 \Phi(s)\geq h(x)+\Phi(s')
\]

can fail. Allow length-zero blocks and define legal blocks as directed paths
from the trace node; then the inequality, its telescoping, and the
all-summable conclusion are correct. This correction is mandatory.

Section 2 must also say explicitly that its “every nonempty persistent set is
consumed” premise includes the summable-residual adapter, or specialize to the
punishment-normal Fin4 hard residual. An exact-spine consumer alone does not
justify the inference because the extracted spine is approximate at the
seams.

## 5. Boundary tests

- A positive-charge exact block with equal endpoints repeats periodically
  with zero seam and gives a fixed persistent marginal by finiteness. This
  confirms the orientation in the degenerate case.
- The proposal's length-\(N\) player-\(0\) example has unbounded finite
  capacity but a pointwise all-Continue limit. The near-return extraction
  retains the charge, and the game already has a uniform payoff; it is
  consistent with the theorem.
- The one-player negative-singleton example does not refute the unique branch
  because its persistent owner is not punishment-normal. This verifies that
  normality cannot be deleted.
- “One positive marginal somewhere in every block” is insufficient; the
  proof correctly uses a uniform positive **total charge** per extracted word
  and only then invokes finiteness to obtain one fixed infinite-stream label.

## 6. Mandatory edits before export

1. State the capacity theorem and its consumer in one self-contained place,
   with the fixed reward table, compact set, finite-player specialization,
   product-root convention, norms, and all quantifiers.
2. Insert the exact semantic-debt and seam bounds (A)--(B), including
   nonnegativity and boundedness of the artificial chain.
3. Insert the unique-branch bounds (C)--(E) and the three explicit error
   sequences passed to the deleted-Quit consumer.
4. Say that persistent labels are fixed along a selected infinite root
   sequence but may depend on that selection/accuracy.
5. Define the capacity potential on prepend-closed trace nodes, not on bare
   payoff vectors unless payoff-state Markov closure is separately assumed.
6. Distinguish the checked exact-spine declarations from the new ordinary
   approximate-spine adapter. Do not attach a Lean seal to the capstone.
7. Name the conjecture-facing finite-capacity obligation that this reduction
   strictly narrows; otherwise it remains a conditional supplied-block
   theorem and does not meet the export queue's relevance gate.

After these edits I would pass the result as a rigorous ordinary-mathematics
reduction, not as a proof of the Fin4 conjecture and not as Lean-checked.

## Source declarations inspected

- IsεQuittingRootNash in
  UniformEquilibrium/Quitting/Root/FirstBranch.lean;
- isεQuittingRootEndpointNash_iff_isεQuittingRootNash and
  quittingRootQuitPayoff_le_successor_add_of_isεNash in
  UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean;
- quittingRootCoordinateNashDefect and
  isεQuittingRootNash_iff_coordinateNashDefect_le in
  UniformEquilibrium/Quitting/Root/NashDefect.lean;
- quittingTerminalSemanticPrefix and quittingTerminalSemanticDebt in
  UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean;
- QuittingBoundedSeamChain,
  QuittingBoundedSeamChain.nonempty_chronologicalDebtShadowingCertificate_of_twoPersistent,
  QuittingSummableSeamSource, and
  quittingGame_exists_uniformEquilibriumPayoff_of_summableSeams_all_errors in
  UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalSeamReduction.lean;
- summable_quittingOpponentClockCharge_iff and
  HasTwoPersistentQuittingMarginals.survival in
  UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean;
- quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff in
  UniformEquilibrium/Quitting/Boundary/Exceptional/InfiniteLTG.lean;
- abs_value_sub_soloReward_le_of_bounded_bellman and
  IsCanonicalExactQuittingNashBellmanSpine.isUniformEquilibriumPayoff_soloReward_of_uniquePersistent
  in
  UniformEquilibrium/Quitting/Classification/Existence/NormalUniquePersistentNashBellmanSpine.lean;
- isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits in
  UniformEquilibrium/Quitting/Cycles/ConditionedDeletedClockSoloCompletion.lean;
- nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff in
  UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean;
- FinFourQuantitativeFullSupportHardResidual.all_marginalQuitHazards_summable
  and all_marginalQuitHazards_summable_of_no_uniformPayoff in
  UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardNashBellmanSpine.lean;
- quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
  in
  UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean.
