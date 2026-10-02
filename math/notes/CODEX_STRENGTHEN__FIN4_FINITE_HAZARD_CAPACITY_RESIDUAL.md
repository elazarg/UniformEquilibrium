# Fin4 finite hazard capacity: the conditional discrete rank and the exact reset obstruction

Author: `CODEX_STRENGTHEN`

Status: **PRECISE REDUCTION / SHARP NO-GO; INTERNAL, NOT FOR EXPORT.**

## Outcome

Finite exact Nash--Bellman hazard capacity does supply a canonical discrete
rank once a source transition is already a composable exact charged path with
a fixed positive charge floor.  The rank is

\[
   \rho(s)=\left\lceil \Phi(s)/\kappa\right\rceil,
\]

where `Phi` is the charged-relation budget-to-go and `kappa` is the uniform
charge floor.  No capacity attainment or upper semicontinuity is needed.

For a cap--Nash block which prefixes a carrier tail of total debt `D_H` to a
returned profile of debt `D_L`, the checked exact scaling identity gives the
useful quantitative floor

\[
 D_H\ge D_*+\delta,\qquad D_L\le D_*+\delta/2,\qquad D_H\le D_{\max}
 \quad\Longrightarrow\quad
 H(B)\ge \kappa:=\frac{\delta}{2D_{\max}}.                 \tag{1}
\]

Here `H(B)` is the sum of all marginal Quit probabilities in the block.  Thus
the proposed capacity mechanism is mathematically correct.

It does **not** currently attach to the renewable Fin4 minimum-source lane.
There are two independent missing fields:

1. none of the three renewable terminal exits supplies a cap--Nash tail with
   one fixed excess `delta` and a cap--Nash return to `D_*+delta/2`; and
2. the horizontal full-replacement/source-regeneration seam is not an exact
   Nash--Bellman path.  It therefore resets `Phi` instead of decreasing it.

The global strict-minimum moat is uniform over all regenerated minimum-fibre
sources, but it does not repair either field.  Its root-freezing statement is
about Nash roots against the **prescribed payoff** `tail.1`; cap--Nash
causalization selects roots against the **behavioral cap** `tail.2`.  Moreover,
an arbitrary strict off-minimum endpoint may remain inside the payoff tube and
may have debt excess tending to zero.

Consequently the strongest surviving result is a conditional capacity-rank
compiler plus a precise reduction of the actual Fin4 residual.  I found no
terminal consumer and no unconditional new renewable rank for the
finite-capacity branch.

All proofs below are ordinary mathematics unless a checked declaration is
explicitly cited.

## 1. Self-contained capacity lemma

Let `R` be a charged relation.  Its finite paths have nonnegative charge, and
assume every finite path has charge at most `C`.  Let

\[
  \Phi(s)=\sup\{\operatorname{charge}(P):P\text{ starts at }s\}.
\]

Then

\[
  0\le \Phi(s)\le C,
  \qquad
  \Phi(t)+\operatorname{charge}(P)\le \Phi(s)              \tag{2}
\]

for every path `P : s -> t`.  This is the standard prepend-a-path argument;
it does not require a maximizing path.

### Proposition 1 (uniform charged transitions give a natural rank)

Fix `kappa>0`.  For every allowed recursive transition `s -> t`, suppose an
actual `R`-path from `s` to `t` is supplied and its charge is at least
`kappa`.  Define

\[
  \rho(s)=\left\lceil\frac{\Phi(s)}{\kappa}\right\rceil.
\]

Then `rho(t)<rho(s)`.  Hence every recursive trace has length at most
`ceil(C/kappa)`.

**Proof.**  Equation (2) gives

\[
  \frac{\Phi(t)}{\kappa}
       \le \frac{\Phi(s)}{\kappa}-1.
\]

Taking ceilings and using `ceil(x-1)=ceil(x)-1` gives

\[
  \rho(t)\le \rho(s)-1.
\]

Nonnegativity of `Phi` makes `rho` natural-valued.  This also proves the trace
bound.  Notice that `Phi` remains real-valued; only its fixed-size decrement is
discretized.  There is no assertion that `Phi` is attained or semicontinuous.

This proposition is already supported abstractly by the checked declarations

- `ChargedRelation.value_tgt_add_charge_le_value_src`,
- `ChargedRelation.value_isBoundedPotential`, and
- `ChargedRelation.IsPotential.chargeSum_le`

in `MathUE/ChargedPathBudget.lean`.  The missing formal wrapper is only the
ceiling-rank corollary.

## 2. Exact quantitative charge of a cap--Nash escape return

Consider a finite cap--Nash root word `x_0,...,x_{n-1}` over one actual tail.
Let

\[
 c=\prod_{t<n}\prod_i(1-x_{t,i})
\]

be its joint Continue product.  Let `D_H` be the tail's total terminal debt and
`D_L` the debt after prefixing the whole word.  Exact cap--Nash scaling gives

\[
   D_L=cD_H.                                                \tag{3}
\]

This is checked as `quittingTerminalDebtSum_capNashRootStack_eq` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`; the
one-row semantic version is
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
`TerminalCapNashEndpointTransport.lean`.

Assume

\[
  0<D_* ,\qquad
  D_H\ge D_*+\delta,qquad
  D_L\le D_*+\varepsilon,qquad
  0\le\varepsilon\le\delta/2,qquad
  D_H\le D_{\max}.
\]

Then (3) gives

\[
  1-c=\frac{D_H-D_L}{D_H}
      \ge \frac{\delta-\varepsilon}{D_{\max}}
      \ge \frac{\delta}{2D_{\max}}.                       \tag{4}
\]

For the one-row absorption masses `a_t`,

\[
  1-c\le\sum_{t<n}a_t
       \le\sum_{t<n}\sum_i x_{t,i}=H(B).                  \tag{5}
\]

The first inequality is checked as
`one_sub_capNashStackContinueProduct_le_absorptionSum`; the second follows
rowwise from `quittingRootAbsorptionMass_le_sum_quitProbability`.
Equations (4)--(5) prove (1).

There is also an exact Nash--Bellman interpretation.  At every cap--Nash row,
the current behavioral envelope equals the Bellman successor of the tail
envelope by
`quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`.
Thus the cap vectors along the literal word form a finite exact Nash--Bellman
block.  Actual behavioral envelopes lie in the reward box and dominate the
punishment floor, so after the routine list adapter the word is a path in the
full punishment-floor admissible relation.

Finite *marginal* hazard capacity therefore bounds the absorption relation as
well.  In fact, under a terminal-exploitability witness the checked
`QuittingTerminalExploitabilityWitness.prefixCharge_le` already supplies a
finite absorption-charge bound.  Hence the absence of Proposition 1's Fin4
conclusion is not caused by lack of a real potential: the missing datum is the
source-compatible positive path.

## 3. Why the uniform minimum-fibre moat does not supply `delta`

Under hypothetical Fin4 nonexistence,
`exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff` in
`TerminalSemanticFinFourMinimumFiberIsolation.lean` produces one open payoff
tube and one number `epsilon>0` for the entire compact global-minimum carrier
fibre.  All regenerated minimum-fibre sources use the same game and the same
global minimum, so this tube and moat are genuinely uniform through the
existing support descent.

The exact consequence is:

> if a carrier tail has debt below `D_*+epsilon`, then its prescribed payoff
> lies in the tube; every exact Nash root against that prescribed payoff is
> all Continue.

Equivalently,
`minimumFiber_debt_add_epsilon_le_of_carrierTail_exactRoot_absorption_pos`
says that a positive exact root against `tail.1` forces tail debt at least
`D_*+epsilon`.

This does not apply to the roots used in cap--Nash causalization or cap-lifted
returns.  Those roots are Nash against `tail.2`.  Positive debt means precisely
that `tail.1` and `tail.2` need not agree.  Substituting the cap for the payoff
in the moat theorem would erase this distinction and is invalid.

Nor does `D(endpoint)>D_*` imply the uniform gap `epsilon`.  The moat says

\[
  D(endpoint)<D_*+\epsilon\Longrightarrow endpoint.1\in tube,
\]

not that every off-minimum endpoint lies outside the tube.  The strict
positive-slope and paid-endpoint excesses can approach zero across freshly
selected sources.  The flat support-entry minimum endpoint has excess exactly
zero.  Thus no current terminal tag supplies a common `delta` for (1).

If a future theorem supplies a tail whose **payoff is outside the uniform
tube**, then the moat does give `D_H>=D_*+epsilon`, and (1) applies with that
fixed epsilon once a cap--Nash near-return is also supplied.  This is a valid
conditional use, not a present producer.

## 4. Why source regeneration resets the potential

The renewable support theorem has a genuine natural rank already:

- `FinFourRenewableMinimumSourceNode.terminalExit_or_nonempty_supportDescent`,
- `FinFourRenewableTrace.descentCount_le_three`,
- `canonicalPairRenewableTransition_rank_lt`, and
- `canonicalPairRenewableTransitionRel_wellFounded`

in `CanonicalPairRenewableSourceRank.lean`.

Every recursive no-entry minimum-fibre full replacement is reconstructed as a
complete same-residual child source.  But the reconstruction is horizontal:
it compactifies the actual full-replacement profiles, chooses/retains a law
point, causalizes a realizing family, and starts a fresh tangent family there.
No exact Nash--Bellman path has the parent capacity state as one endpoint and
the child capacity state as the other.

Potential inequality (2) applies only to a literal path with matching
endpoints.  Equality of hard residuals, equality of minimum debt, convergence
to a common semantic cluster, and equality of support labels do not give that
path.  They also cannot be passed through `Phi` by compactness: `Phi` is a
supremum over finite continuations and no upper-semicontinuity theorem is
available or true for a general compact closed-edge relation.

The checked theorem
`FullReplacementCluster.not_hasVanishingHorizontalDeviationLeak_of_minimumFiber`
is aligned with this obstruction.  On every recursive minimum-fibre
replacement, some nonmover absorbs a fixed positive share of the killed
mover's debt; hence no one vanishing error compares all of that nonmover's
behavioral deviation gains across the seam.  This theorem does not by itself
prove that no more specialized capacity adapter can exist, but it rules out
the natural uniform all-deviation seam estimate.

### Minimal abstract reset regression

The logical failure is already visible in a four-state charged system.  Let
the genuine exact relation have only

\[
  H_A\longrightarrow L_A,qquad H_B\longrightarrow L_B,
\]

each of charge `kappa`, and no other nontrivial paths.  Its capacity is
`kappa`.  Add two *external source resets*

\[
  L_A\dashrightarrow H_B,qquad L_B\dashrightarrow H_A.
\]

The alternating regeneration process is infinite, although the genuine
charged relation has finite capacity.  If the dashed arrows are silently
declared zero-charge exact edges, the augmented graph has a positive cycle
and unbounded capacity.  Therefore that declaration is exactly the missing
mathematics, not harmless bookkeeping.

The actual Fin4 lane currently has the same type pattern: a cap--Nash return
can be a genuine charged arrow, but the next source's horizontal
full-replacement/reselection is a dashed arrow.  A history capacity cannot be
carried across it without an exact endpoint-matching theorem.

## 5. Support and face ranks: exact algebraic boundary

The existing positive-debt support rank completely consumes the flat
**no-entry** minimum-fibre branch.  It deliberately stops at support entry.
There is no monotone continuation through entry based only on the support or
zero face.

The smallest tangent/debt calculation is already cyclic.  Put

\[
 b^A=(1,0,0,0),\qquad t^A=(-1,1,0,0),\qquad b^B=(0,1,0,0),
\]

and at `b^B` use

\[
 t^B=(1,-1,0,0).
\]

Both tangent rows are flat, kill their active mover exactly, enter a
previously zero coordinate, preserve total debt one, and satisfy the endpoint
coordinate inequalities with equality.  They form the support-label cycle

\[
  \{1\}\longrightarrow\{2\}\longrightarrow\{1\}.
\]

For every `0<theta<1`, the proper chord between `b^A` and `b^B` has support
`{1,2}`.  Thus the same example appears as alternating support expansion and
support drop.  Neither support cardinality, the positive support ordered by
inclusion, nor the complementary zero face can strictly decrease through all
these steps.

This is an exact countermodel to any rank conclusion using only the displayed
flat tangent and minimum-fibre debt ledgers.  It is not claimed to be a full
positive-gap quitting-game counterexample.  Turning recurrence of the finite
support label into a consumer would again require exactifying the horizontal
seams; a repeated label alone is not a chronological cycle.

## 6. Audit of the three renewable terminal exits under finite capacity

### 6.1 Positive total slope

`nonempty_positiveTotalSlopeEndpointAtomPassport` gives a fixed positive
static atom/deviation charge and arbitrarily long exact prefix access.  It
does not give an exact return from the off-minimum full-replacement endpoint.

There is a sharper hazard boundary.  With two active debt owners,
`QuittingStoppingLawAtomExactPrefixStackAccess.absorptionSum_tendsto_zero_of_twoActive`
already proves that the whole long stack's sum of one-row absorption masses
tends to zero.  Since for a finite player set

\[
  \sum_i x_{t,i}\le |I|\,a_t
\]

at each row (`quittingQuitProbability_le_absorptionMass` coordinatewise), the
**total marginal-hazard charge of the stack also tends to zero**.  Thus these
arbitrarily long blocks not only fail to create unbounded absorption charge;
they are asymptotically zero-charge for the capacity used in the export.

With one active owner `p`, `opponentSurvival_tendsto_one` similarly implies
that the aggregate marginal charge of all outsiders tends to zero.  Only
`p`'s own clock can retain charge.  The Continue-through atom deviation
removes that clock, so the positive atom payoff does not lower-bound it.
Finite capacity merely bounds this remaining owner charge; it does not create
a renewable packet.

### 6.2 Flat support entry

A minimum-fibre endpoint is a source-faithful support expansion, not a charged
exact edge.  It lies in the common minimum-fibre payoff tube, where exact roots
against its prescribed payoff are all Continue.  The two-state calculation in
Section 5 shows why an expansion cannot simply be appended to the existing
support-decrease rank.  An off-minimum entry endpoint is routed to the paid
exit, with the same gap/return issues as below.

### 6.3 Off-minimum paid first disagreement

`PaidCapPortExactTrichotomy.lean` gives charged near-return, quantitative debt
descent, or inert stall.  The charged near-return is already consumed.  The
quantitative descent is real-valued, its size can vanish, and it carries no
regenerated source/history endpoint.  The inert arm has all-Continue selected
roots and zero charge.  Finite capacity neither excludes it nor turns the
strict descent into a well-founded rank.

The generic escape-return calculation in Section 2 would consume a strengthened
paid output that supplied all of: a fixed tail gap, a near-minimum cap return,
and exact attachment to the next source history.  The present `PaidCapPort`
does not contain that package.

## 7. Strongest surviving Fin4 theorem

Combining the checked renewable support rank with the finite-capacity analysis
gives the following exact reduction.

> Starting from the canonical minimum-endpoint handoff, after at most three
> same-residual minimum-fibre support descents one reaches positive slope,
> support entry, or an off-minimum paid row.  Finite exact-block marginal
> capacity supplies a bounded charged-relation potential, but none of these
> exits currently gives a uniform positive, endpoint-matched path on which
> that potential decreases.  Hence finite capacity adds no unconditional
> terminal consumer to `exists_renewalTerminalExit_sameResidual`.

The corresponding conditional completion is rigorous:

> If every unconsumed terminal exit produces either a uniform-equilibrium
> payoff or a regenerated same-residual source together with an
> extension-compatible exact path of charge at least one game-wide
> `kappa>0`, then the regenerated lane terminates after at most
> `ceil(C/kappa)` such exits.  Composing this with the existing three-step
> support traces gives a finite terminal consumer.

This is the strongest theorem I can justify.  Calling the actual Fin4 branch
solved would require supplying the emphasized producer, not only defining its
rank.

## 8. Declaration-level handoff

The following small generic/quantitative lemmas are justified now:

1. `ChargedRelation.ceilValueRank_lt_of_path_charge_ge`:
   Proposition 1 for a supplied finite-budget charged relation and fixed
   positive threshold.
2. `capNashRootStack_marginalHazardCharge_ge_of_escapeReturn`:
   equations (3)--(5), with the explicit floor
   `(delta - epsilon) / Dmax`, specialized to `delta/(2*Dmax)` when
   `epsilon<=delta/2`.
3. `IsQuittingCapNashRootStack.toPunishmentFloorAdmissiblePath`:
   the list adapter obtained from the exact envelope Bellman identity and the
   behavioral-cap punishment floor.
4. `QuittingStoppingLawAtomExactPrefixStackAccess.marginalHazardSum_tendsto_zero_of_twoActive`:
   the checked absorption-sum theorem plus the finite-player factor.
5. A singleton-active companion saying the total outsider marginal charge
   tends to zero.

The actual Fin4 declaration must remain conditional, for example a structure
`FinFourCapacityRenewalPacket` containing:

- a parent history endpoint in one fixed charged relation;
- a literal exact path of charge at least `kappa`;
- literal equality of its terminal endpoint with the child history endpoint;
- a complete same-residual child source attached to that endpoint; and
- the same game-wide positive `kappa` at every recursive call.

Neither canonical full-replacement regeneration nor the three terminal-exit
interfaces currently construct this structure.

## 9. One next obligation

Prove or refute the following single producer statement for one actual
terminal-exit family:

> There are game-wide `delta>0` and a source-history construction such that
> every unconsumed exit either closes, or supplies a literal cap--Nash block
> from a tail of debt at least `D_*+delta` to a returned profile of debt at
> most `D_*+delta/2`, and the returned block endpoint is literally the next
> regenerated source-history endpoint.

The boundary case where the strict excess tends to zero must be included in
the disjunction and consumed; compactness alone cannot upgrade strict
positivity to a uniform `delta`.  This one statement would discharge both the
charge-floor and nonreset requirements and would make Proposition 1 an actual
Fin4 well-founded rank.

## 10. Narrow source audit

Files/declarations inspected for this note:

- `math/SOURCES.md`, `math/GOAL.md`, and the renewable/capacity rows of
  `docs/FRONTIER.md` and `docs/TOOLKIT.md`;
- `math/exports/UNBOUNDED_FINITE_HAZARD_CAPACITY_COMPILER.md`;
- `Research/Quitting/FinFourProducerAtlas/CanonicalPairRenewableSourceRank.lean`;
- `Research/Quitting/FinFourProducerAtlas/CanonicalPairMinimumEndpointRenewal.lean`;
- `Research/Quitting/FinFourProducerAtlas/CanonicalPairFullReplacementSourceRegeneration.lean`;
- `Research/Quitting/MinimumFiberDebtTransfer.lean`;
- `Research/Quitting/SourceFaithfulMinimumLawCausalization.lean`;
- `Research/Quitting/FinFourProducerAtlas/PaidExitCapPortRefinement.lean`;
- `Research/Quitting/FinFourProducerAtlas/StrictRayPositiveRootReturn.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticStrictTailEscapeReturn.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Atom/ExactPrefixStackAccess.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Atom/ExactPrefixStackCharge.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PositiveTotalSlopeAtomAccess.lean`;
- `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`;
- `MathUE/ChargedPathBudget.lean`.

No Lean theorem, export, shared index, or author-owned note was edited.
