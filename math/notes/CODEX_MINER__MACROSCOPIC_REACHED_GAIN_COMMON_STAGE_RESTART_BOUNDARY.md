# Macroscopic reached gain: exact common-stage restart and its cycle boundary

**Owner:** `CODEX_MINER`  
**Status:** `REVIEWED REVISE -> REPAIRED / INTERNAL / NO ACCEPTED CONSUMER`  
**Independent review:**
[`CODEX_EULER`](../feedback/CODEX_MINER__MACROSCOPIC_REACHED_GAIN_COMMON_STAGE_RESTART_BOUNDARY__BY_CODEX_EULER.md).
The review verified the finite-depth constants and literal restart, and
required the singleton-exit arm and the fixed-tail restriction in Section 5;
both repairs are incorporated below.  This note is not proposed for export.

## 1. Question and answer

Start with the reviewed fixed-scale gain arm of
[`MACROSCOPIC_COLLISION_LAW_CAUSAL_DISPATCH`](CODEX_MINER__MACROSCOPIC_COLLISION_LAW_CAUSAL_DISPATCH.md).
Can its legal one-stage endpoint repair be restarted chronologically, rather
than compactifying independently selected source and target profiles?

There is a genuine positive answer at finite depth:

* the endpoint target is literally the next actual source;
* every repair occurs at the same reached date and resumes the same suffix;
* the source/successor semantic anchors are exact; and
* the routed unconditional coalition mass only squares at each repair.

For a fixed number of repairs this gives a quantitative four-way alternative:
a fixed common-tail debt excursion, a fixed actual endpoint debt excursion, a
reached singleton atom, or a literal source-target restart chain of profitable
pure-endpoint repairs.  Since only finitely many stage-root states can occur,
a sufficiently long fourth arm contains an exact common-stage
better-response cycle.

The cycle is **not yet** a chronological consumer.  Every one of its selected
source phases has, at the fixed common suffix continuation `T.1`, a supported
action whose endpoint loss is bounded below by the same positive constant.
Thus the constructed word is not itself an exact Nash--Bellman return with
that fixed continuation.  This does **not** exclude a signed projective lasso
on the same roots with separately chosen rotated phase values; such a lasso
tests support against those phase values rather than `T.1`.

The newly checked AGKRS signed-lasso bridge is also not a compatible target
for this positive-minimum packet: its source premise already implies a
uniform-equilibrium payoff and hence excludes positive terminal-semantic debt
infimum.  Section 7 records this exact hypothesis separation.

Thus the fixed reached-gain arm has no remaining **profile provenance** seam.
Its exact remaining seam is strategic: simultaneous Nashification of the
finite endpoint-improvement component while preserving a positive absorbing
root and the Bellman successor values.

## 2. Fixed data and notation

Let `I` be a nonempty finite player set of cardinality `N`.  Let `r` be a
quitting reward table.  Fix

* a terminal-semantic carrier minimum `X` with
  `D(X)=D_*>0`;
* an actual behavioral profile `sigma_0`;
* a reached date `t`;
* a nonempty terminal coalition `S_0` with `|S_0|>1`; and
* numbers `alpha,eta>0` such that

\[
 D(\operatorname{Sem}(\sigma_0))\le D_*+\eta,
 \qquad
 a_t^{S_0}(\sigma_0)\ge\alpha.
 \tag{2.1}
\]

Here `a_t^S(sigma)` is the unconditional probability of first absorption at
date `t` by exactly `S`.  Necessarily `0<alpha<=1`.  Put

\[
 \beta_k=\alpha^{2^k}\qquad(k\ge0).
 \tag{2.2}
\]

For an actual source `sigma_k`, apply
`causalCollision_tailEscape_or_quantitativeNearMinimumTransfer` at date `t`
and coalition `S_k`, with lower bound `beta_k` and near-minimum error `eta`.
In its gain arm write

\[
 i_k=\text{mover},\quad e_k\in\{C,Q\}=\text{best endpoint},
 \quad
 \sigma_{k+1}=\sigma_k[i_k\leftarrow e_k\text{ at }t],
 \tag{2.3}
\]

and let

\[
S_{k+1}=\operatorname{route}(S_k,i_k,e_k).
 \tag{2.4}
\]

The update in `(2.3)` is the checked complete behavioral strategy
`quittingStagePureEndpointBehaviorDeviation`: it follows `sigma_k` before
`t`, uses the pure endpoint at `t`, and resumes the same live marginals after
`t`.  This is not a normal-form surrogate.

The next invocation is made only while `|S_k|>1`.  The routed coalition is
always nonempty, but a Continue erasure from a two-player coalition can make
`S_{k+1}` a singleton.  That event is an explicit stopping arm below, not a
new collision input.

## 3. Exact one-step restart lemma

### Lemma 3.1 (literal successor and common suffix)

Assume the gain arm is selected at step `k`.  Then:

1. `sigma_{k+1}` is an actual behavioral profile and is literally the target
   profile returned by the theorem.  It may therefore be used as the next
   source without any compact reselection.
2. The live roots before `t` and after `t` agree with those of `sigma_k`; only
   coordinate `i_k` at date `t` is replaced.  In particular

   \[
   \operatorname{Spine}(\sigma_{k+1},t+1)
   =\operatorname{Spine}(\sigma_k,t+1)
   \tag{3.1}
   \]

   at the level of the canonical live root word and terminal-semantic pair.
   Hence every step in the chain has one common suffix pair `T`.
3. Live mass at date `t` is unchanged.
4. The routed coalition satisfies

   \[
   a_t^{S_{k+1}}(\sigma_{k+1})\ge\beta_k^2=\beta_{k+1}.
   \tag{3.2}
   \]
5. If `g_k=U_{i_k}(sigma_{k+1})-U_{i_k}(sigma_k)`, then

   \[
   g_k>0,qquad
   g_k\ge {\beta_{k+1}D_*\over 2N},
   \tag{3.3}
   \]

   and the mover debt has the exact source/successor identity

   \[
   d_{i_k}(\operatorname{Sem}(\sigma_{k+1}))
   =d_{i_k}(\operatorname{Sem}(\sigma_k))-g_k.
   \tag{3.4}
   \]

**Proof.** Items 1 and 5 are literal fields of
`causalCollision_tailEscape_or_quantitativeNearMinimumTransfer`.  The
definition of `quittingStagePureEndpointBehaviorDeviation` and
`quittingBehaviorLiveHazard_stagePureEndpointBehaviorDeviation` show that the
new live word is the old word with only the displayed date-coordinate
changed.  This proves item 2.  Item 3 is checked as
`quittingLiveMass_stagePureEndpoint_eq`.

The old stage coalition mass is at most the old live mass, so the latter is
at least `beta_k`.  The gain theorem gives routed **root** coalition mass at
least `beta_k`.  Multiplying these two bounds and using unchanged live mass
gives `(3.2)`.  Finally the checked quantitative gain inequality is

\[
 {\beta_k^2D_*\over2}\le N g_k,
\]

which is `(3.3)`. `QED`

### Remark 3.2 (availability accounting)

There is no hidden chronological availability loss in this restart.  The
loss is explicit and multiplicative: after `k` repairs the same actual date
is reached with a routed atom of mass at least `beta_k`.  For any fixed depth
this remains a fixed positive number.  It is not uniform in unbounded depth.

## 4. Finite-depth restart theorem

### Theorem 4.1 (excursion, singleton atom, or literal restart chain)

Fix `K>=1` and set

\[
 c_K={\beta_KD_*\over2N},
 \qquad e_K={\beta_KD_*\over2}.
 \tag{4.1}
\]

From the data in Section 2, at least one of the following holds:

1. **Common-tail excursion:** the common suffix `T` satisfies

   \[
   D(T)-D_*\ge e_K.
   \tag{4.2}
   \]

2. **Actual endpoint excursion:** before `K` repairs, an actual target
   `sigma_{k+1}` satisfies

   \[
   D(\operatorname{Sem}(\sigma_{k+1}))>D_*+\eta.
   \tag{4.3}
   \]

3. **Reached singleton atom:** before `K` repairs, a literal target
   `sigma_{k+1}` carries at date `t` a singleton routed coalition
   `S_{k+1}` with

   \[
        a_t^{S_{k+1}}(\sigma_{k+1})\ge\beta_{k+1}>0.
   \tag{4.4}
   \]

4. **Literal source-target restart chain:** there are actual profiles
   `sigma_0,...,sigma_K`, fixed-date coalitions `S_0,...,S_K`, and labels
   `(i_k,e_k)` for `k<K` such that every successor is literally the next
   source, every `S_k` is still a collision, `(3.1)--(3.4)` hold, and in
   particular every edge has

   \[
   U_{i_k}(\sigma_{k+1})-U_{i_k}(\sigma_k)\ge c_K>0.
   \tag{4.5}
   \]

**Proof.** Induct for `k=0,...,K-1`.  At step `k`, `beta_k>=beta_K`.
The tail-escape arm gives

\[
 D(T)-D_*\ge\beta_kD_*/2\ge e_K.
\]

In the gain arm, Lemma 3.1 constructs the next actual source.  If its routed
coalition is a singleton, stop in arm 3.  Otherwise it remains a collision.
If its debt is above `D_*+eta`, stop in arm 2; otherwise it satisfies the
near-minimum hypothesis for the next application.  After `K` collision-
preserving gain arms, `(3.3)` and `beta_{k+1}>=beta_K` give `(4.5)`. `QED`

The theorem is honest about the off-minimum branch.  Existing paid-cap
trichotomies can be applied to its actual reached source, but still permit an
inert stall; positive excess debt is not itself a charged return or a
well-founded descent.

## 5. Finite state recurrence and the fixed-tail support boundary

At the marked date, each coordinate of every iterated root is one of

\[
 q_i^0,\quad \delta_C,\quad\delta_Q,
\]

where `q^0` is the initial live root.  All other dates have the common live
word.  Thus at most `3^N` marked root states occur.

### Corollary 5.1 (excursion, singleton atom, or literal endpoint-improvement cycle)

Take `K=3^N`.  If neither excursion arm nor the singleton-atom arm of Theorem
4.1 occurs, two sources in the literal source-target restart chain have the
same complete live word and hence the same terminal-semantic pair.  The
intervening nonempty segment is a literal closed word of stage-pure endpoint
repairs.  Every edge has actual mover gain at least

\[
 c={\alpha^{2^{3^N}}D_*\over2N}>0.
 \tag{5.1}
\]

This is stronger than a finite-label subsequence: all successor/source
equalities are literal and the closing semantic state is exact.

### Proposition 5.2 (uniform support-Nash failure)

No selected source phase of that word satisfies

`IsQuittingRootSupportApproxNash r T.1 delta root`

for any `delta<c`.

**Proof.** At a selected source, exact reached-gain factorization gives

\[
 g=L_t\,\operatorname{defect}_{i}(T^U,q).
\]

Since `L_t<=1`, the coordinate defect is at least `g>=c`.  Positive defect
forces positive probability on the action opposite the selected best
endpoint by
`quittingRoot_oppositeBestEndpointProbability_pos_of_defect_pos`.  The
endpoint payoff gap has absolute value at least the coordinate defect (the
latter is the gap multiplied by the probability of the losing action).
Therefore this positively supported losing action is more than `delta` below
the other endpoint.  This contradicts the defining support-local inequality
of `IsQuittingRootSupportApproxNash`. `QED`

Consequently these roots, when tested against the **fixed common suffix value
`T.1`**, cannot supply the support field of a
`QuittingFiniteSignedProjectiveLasso` at errors tending to zero.  This local
statement does not rule out freely chosen rotated phase values that move the
endpoint comparisons enough to restore support approximate Nash.  The
present construction supplies neither such values nor the Bellman estimates
that would relate them to `T.1`.  An occupation measure of the cycle can be a
correlated distribution over pure roots, but it is not a product root and
does not by itself restore the fixed-tail inequalities.

This boundary is already foreshadowed by the checked theorem
`finite_stageFullBestEndpoint_cycle_strictBestResponseWord` in
`TerminalSemanticPositiveMinimumUnitResetOrientation.lean` and by the exact
root-game cycle in Section 13 of
[`CODEX_CEDAR__PAID_ROW_REENTRY`](CODEX_CEDAR__PAID_ROW_REENTRY.md).  The new
content here is the literal common-stage restart and quantitative routed-atom
lower bound inherited from the macroscopic collision producer.  The old
cycle obstruction remains the surviving strategic output.

## 6. Why the usual finite-label and Nash arguments do not finish

1. **Finite labels.** Pigeonholing fixes movers, actions, recipients, or
   coalitions, but Proposition 5.2 persists at `T.1` on every selected phase.
   The missing phase-value/Bellman field is not a label.
2. **Mixed Nash of the one-stage game.** A finite binary game at continuation
   `T.1` has a mixed Nash root, but it may be the all-Continue root.  The
   reached collision root and its profitable endpoint do not make a
   positive-absorption Nash component invariant.  The exact two-player cycle
   in `CODEX_CEDAR__PAID_ROW_REENTRY` exhibits this best-response-carrier
   failure.
3. **Occupation.** Averaging phases loses the independent product-law form;
   taking coordinatewise average marginals creates cross terms in coalition
   rewards and does not preserve either payoff or endpoint inequalities.
4. **Debt rank.** On the minimum fiber, `(3.4)` lowers the mover debt, but
   other debts increase by at least the compensating amount.  A closed word
   returns the whole debt vector exactly.  Total debt, support cardinality,
   and every unweighted coordinate sum therefore fail to orient the word.
5. **Exact Nash--Bellman path.** The common suffix and literal successor
   equalities solve a source-target provenance component of that interface.
   Proposition 5.2 fails its strategic half at the common suffix value by a
   fixed amount.  It leaves open a different path carrying rotated phase
   values and a small signed Bellman seam.

## 7. Exact separation from the AGKRS signed-lasso bridge

The new checked structure
`QuittingCofinalPrioritizedPreemptionSeedSequence` in
`PrioritizedPreemptionSeedBoundary.lean` retains a fixed source owner and
preemptor at tolerances tending to zero.  Its proposed consumer input
`QuittingCofinalPrioritizedSignedLassoBridge` requires, at every scale,

* phase-indexed product roots and values;
* a rotation-uniform signed Bellman residual;
* phasewise support approximate Nash;
* punishment rationality; and
* one positively absorbing phase.

The macroscopic collision input and the **actual AGKRS-produced** seed
sequence cannot be placed on the same contradiction hypothesis.  This is a
claim about the invocation of the producer under the AGKRS table premise, not
about arbitrary inhabitants of the bare seed structure considered in
isolation.

Indeed, the collision transfer assumes `D_*>0`.  By
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`, this
is equivalent to nonexistence of a uniform-equilibrium payoff.  In contrast,
the source sequence in the AGKRS decomposition is extracted under
`QuittingApproximateEquilibriumExistence`; the checked theorem
`quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence`
(equivalently
`quittingApproximateEquilibriumExistence_iff_exists_diagonal_mem_terminalSemanticCarrier`)
already supplies such a payoff.  Thus there is no common reward-table source
on which to combine the positive-minimum collision chronology with the
cofinal prioritized seed.

Even ignoring this mutually exclusive premise, the seed stores static solo
rewards and source provenance, not roots, phase values, Bellman successors,
or support inequalities.  The collision cycle supplies roots and literal
source-target restarts but fails small-error support at the fixed common
suffix value.  It neither constructs the rotated phase values needed by the
signed-lasso bridge nor proves that no such values exist.

This also explains why
`QuittingCofinalPrioritizedSignedLassoBridge.wellSupportedExistence` and
`not_nonempty_cofinalPrioritizedSignedLassoBridge` are not contradictory
tools for the present route: deriving the bridge would eliminate an AGKRS
classification residual, while the positive-minimum route assumes failure of
uniform payoff existence from the outset.

## 8. Duplicate and source audit

Declarations inspected narrowly:

* `causalCollision_tailEscape_or_quantitativeNearMinimumTransfer`
  (`TerminalSemanticCausalCollisionMinimumTransfer.lean`);
* `quittingStagePureEndpointBehaviorDeviation`,
  `quittingBehaviorLiveHazard_stagePureEndpointBehaviorDeviation`,
  `quittingTerminalPayoff_stagePureEndpointDeviation_sub_eq_liveMass_mul`,
  and
  `quittingRoot_oppositeBestEndpointProbability_pos_of_defect_pos`
  (`TerminalSemanticPlateauLocalizedOtherDefect.lean`);
* `quittingProfileLiveRoot_stagePureEndpoint_self` and
  `quittingLiveMass_stagePureEndpoint_eq`
  (`TerminalSemanticCausalCollisionAtomicOrientation.lean`);
* `quittingRootCoalitionMass_eq_actionProbability_mul_routed`
  (`TerminalSemanticPlateauDefectStratification.lean`);
* `IsQuittingRootSupportApproxNash`
  (`Quitting/Boundary/Repair/SupportEnlargementAlternative.lean`);
* `finite_stageFullBestEndpoint_cycle_strictBestResponseWord`
  (`TerminalSemanticPositiveMinimumUnitResetOrientation.lean`);
* `QuittingFiniteSignedProjectiveLasso` and its compiler
  (`Quitting/Projective/SignedProjectiveLasso.lean`);
* `QuittingCofinalPrioritizedPreemptionSeedSequence`,
  `QuittingCofinalPrioritizedSignedLassoBridge`, and their consumer/no-bridge
  declarations (`PrioritizedPreemptionSeedBoundary.lean`); and
* the uniform-payoff/positive-debt equivalences in
  `StationarilyGeneratedBranch.lean`,
  `UniformPayoffTerminalSemanticCarrier.lean`, and
  `TerminalCapNashEndpointTransport.lean`.

A phrase and declaration search found no existing theorem which iterates the
causal routed coalition on its literal endpoint targets with the explicit
`beta_{k+1}=beta_k^2` stage-mass account.  The qualitative strict
best-response-cycle boundary is not new, and no novelty is claimed for it.

## 9. Scope and next exact question

This note does **not** produce a cumulative admissible payoff near-return, a
support-rational lasso, a finite debt rank, a uniform equilibrium, or a
positive-minimum counterexample table.  Producing an explicit table with
`D_*>0` would itself refute the finite-quitting conjecture; local two-player
root cycles with `D_*=0` are not substituted for that demand.

The exact surviving question is:

> Given the finite common-stage endpoint-improvement component in Corollary
> 5.1, can one produce a forward-invariant **positive-absorption product-root
> Nash carrier** whose successor payoffs remain in the same component, or
> prove from `PunishmentNormalResidualHardClass`/the Fin4 residual that one of
> the two fixed excursion arms must enter an existing paid consumer?

The current hard-residual fields do not answer this.  In particular the Quit
orientation's atomic-blocker output is explicitly a strategic handoff, not a
consumer, and `PunishmentNormalResidualHardClass` is a principal-matrix
nonprojectivity condition rather than a sign eliminating that orientation.
