# Independent audit of finite cap-threshold descent

Reviewer: CODEX_FRECHET_CYCLE. Reviewed source:
[`CAP_THRESHOLD_DEBT_DESCENT.md`](../gpt/CAP_THRESHOLD_DEBT_DESCENT.md),
SHA256 `6ed5921bfbd6af18ab087322a5012bc285f11315306d22558c94ecd862aa5bc4`.

Verdict: the finite first-threshold theorem, its full-debt ledger, the
quadratic minimum collar, and the rational finite selector are valid ordinary
mathematics with the stated hypotheses. I found no unresolved mathematical
objection. The qualitative weak-exclusion UE class and qualitative minimum
separation are already covered by existing arguments; they must not be
advertised as new classes or as closure of arbitrary Fin4. No Lean check ran.

The independently rewritten proposed packet is
[`CODEX_FRECHET_CYCLE__FINITE_CAP_THRESHOLD_DESCENT_PACKET_DRAFT.md`](../notes/CODEX_FRECHET_CYCLE__FINITE_CAP_THRESHOLD_DESCENT_PACKET_DRAFT.md).
It remains an internal proposal requiring review of its own final text.

## Claim checked and agency

There are finitely many players, independent Continue/Quit actions at each
live date, bounded terminal rewards, and zero Never reward. An actual source
may have arbitrary unbounded stopping laws. Its pair `(U,B)` retains both
prescribed terminal payoff and the supremum over every complete unilateral
behavioral deviation. For a selected owner with a strict singleton preemptor,
the claim constructs a finite literal prefix with total debt at most

    C - 3 C^2/(32 M + 6 C),       C=max(D,B_i-s_i).

It does not replace the source by another realization of the same payoff.
The finite stopping index in the proof is a deterministic index of the
construction, computed from semantic cap values. It is not a stopping rule
using an observation unavailable to a player. The produced profile uses
ordinary independent row hazards. A player deviating from it can replace its
entire stopping law, including Never and arbitrarily late finite dates.

## Exact finite ledger and crossing

I checked the owner-cap issue explicitly. A general source need not satisfy
`B_i>=s_i`: immediate opponent quitting can make that false. The proof uses
owner-cap constancy only in its branch where **every** initial margin exceeds
`z=4M theta>0`. Thus `max(s_i,B_i)=B_i` there. An initially low cap, including
the owner's own cap, goes directly to the auxiliary step. There is no missing
singleton-cap hypothesis.

At a solo-owner row and an outsider `j`, the Quit endpoint is
`Q_j=(1-theta)s_j+theta r_j({i,j}) <= s_j+2M theta`. If the old margin is
above `4M theta`, the Continue endpoint satisfies

    (1-theta)B_j+theta r_j({i})
       >= B_j-2M theta > s_j+2M theta >= Q_j.

At the first threshold-crossing row it is the **old** cap that must satisfy
this test, and it does. This proves branch selection through that row,
including when several outsiders cross together. It also proves the useful
crossing interval `2M theta < B_j(new)-s_j <= 4M theta`.

Subtracting the exact U and B recurrences gives

    d_i(m)=L_i-rho^m(U_i-s_i),
    d_j(m)=rho^m d_j(0)                 (j!=i),
    D_m=rho^m D+(1-rho^m)L_i.

No individual-debt monotonicity is used. The owner's debt can increase, and
the sum remains controlled by `max(D,L_i)`.

For a fixed preemptor with `r_j({i})=s_j-ell`, hypothetical failure to hit by
date m gives `B_j(m)-s_j<=-ell+2M rho^m`. Taking
`m=ceil(theta^(-1) log(4M/ell))` makes this at most `-ell/2`, contradicting
the no-hit condition. Since `0<ell<=2M`, this bound is finite and positive.
The extra one in the stated row count pays for the auxiliary row.

## Final root and constants

The already available auxiliary-root ledger yields
`D'<=D_m-a(D_m-C/2)`. A threshold cap makes an auxiliary coordinate at most
its singleton minus `3C/8`, so every exact auxiliary root has
`a>=3C/(16M+3C)`. Since `D_m>C/2`, its use preserves the direction of the
inequality. The resulting upper bound is increasing in `D_m` and hence at
most `C-3C^2/(32M+6C)`.

If the current debt is at most `C/2`, the empty-word or early-stop branch
suffices because the advertised subtraction is smaller than `C/2`.

For the rational version, the tolerance `k(C)/(4n)` is below the required
`(3C/8)/4`. The absorption lower bound halves; the sum of root regrets costs
at most `k(C)/4`. Therefore the retained decrease is `k(C)/4`, exactly the
denominator `128M+24C` in the note. These estimates include all coordinates.
Finite-game Nash existence and the stated Lipschitz estimate justify a
finite rational grid search. This is computability for **finite rational
sources**. The arbitrary-source theorem does not claim an algorithm for
computing a cap supremum from a black-box infinite behavioral strategy.

## Carrier passage and quadratic collar

The inspected semantic carrier is the closure of actual **pairs**, not only
payoffs. Each fixed prefix is a continuous map preserving that carrier. The
same finite branch argument therefore applies to a carrier point without
claiming that the point is actual.

At a positive global minimum, the existing singleton-margin theorem gives
`L_i>=D_*` for every i. Take hazards tending to zero, stop each finite block
at its first threshold, and pass to a subsequence with a fixed crossing
outsider j. Compactness gives a carrier point Y with

    B_j(Y)=s_j,       D_*<=D(Y)<=L_i.

The upper bound is the full-debt affine identity, not a payoff-only
continuity assertion. Prefixing Y by an exact root at `B(Y)-D_*/2` gives
absorption at least `D_*/(4M+D_*)`. Global minimality then forces

    D(Y)>=D_*+D_*^2/(8M),

which proves the claimed owner margin. Subtracting `d_i<=D_*` proves the
prescribed-payoff collar. The limiting Y need not be actual and is not used
as the renewed source of the finite algorithm.

The no-preemptor argument is sign-sensitive exactly as stated. If the
owner's singleton is nonnegative, its stationary solo profile has zero
owner debt. If that singleton is negative, Never could improve the owner;
the direct equilibrium alternative cannot be silently reused. The exact
declaration `exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform`
does provide all strict preemptors for arbitrary signed four-player tables.
Thus the signed Fin4 corollary has its required existing adapter.

The optional joining-loss refinement is also correct: endpoint subtraction
uses only `r_j(T)-r_j(T union {j})`. If that loss is zero for all outsiders,
the forcing coordinate makes any exact root have absorption one, giving the
claimed contradiction at a positive minimum. No constant optimization was
needed for acceptance.

## Finite selector and actual renewability

For all nonnegative singleton rewards, all-Never has debt `D_0=sum_i s_i`.
At each actual finite source satisfying weak exclusion, choose
`U_i<=s_i`. Then `L_i<=d_i<=D`, so the next full-prefix block has

    D_next<=D-D^2/C_0,       C_0=(128M+24D_0)/3.

Every new source is a literal finite profile, so weak exclusion applies
again. This is the exact renewal argument. It uses the universal finite-word
payoff condition at every iterate; the local theorem alone does not ensure
renewal for arbitrary tables. Reciprocal iteration and the row estimate give
the stated quadratic inverse-error date count. For a rational source, caps
are finite maxima over displayed dates, one post-cutoff date, and Never.

One small implementation clarification is useful: the unblocked alternative's
displayed estimate bounds maximum coordinate regret. To meet the theorem's
**total** debt tolerance epsilon, use that estimate at epsilon/n. The draft
below makes this scaling explicit. This is a straightforward choice of its
free parameters, not a counterexample to the theorem.

The canonical finite-menu and late-pivot inequalities hold for the same
selected four-law profile because each is bounded by its unrestricted
coordinate regret, which is at most total debt. No claim about preserving
other caps under a separately optimized pivot response is needed.

The final cluster-point argument fixes one payoff before accuracy, and the
fixed finite profile has a uniform finite-horizon comparison over all
deviations. It therefore matches the actual semantic endpoint.

## Falsification attempts and exact tests

1. **Owner debt can rise.** Modify the source's four-player regression by
   changing its singleton vector to `(-1,0,0,0)`, retaining the default rule
   “own singleton when included, -1 otherwise” and its two overrides
   `r({1,2})=(1,1,1,1)`, `r({0,1,2})=(2,-1,-1,-1)`. The pure `{1,2}` source
   has `U=(1,1,1,1)`, `B=(2,1,1,1)`, `D=1`, and owner-0 margin `L_0=3`.
   An owner-0 solo block has `D_m=3-2rho^m>1` for every m>0 before crossing.
   Thus replacing `C` by `D` without `L_i<=D` would be false. The reviewed
   theorem retains C and passes this test.
2. **Continuing past the threshold loses the affine cap formula.** In that
   same signed table, use theta=1/16 for the standalone crossing lemma, with
   `M=2` and threshold 1/2. The first crossing is m=5: old outsider cap is
   `17857/32768>1/2`, new cap is `235087/524288`, which lies above 1/4.
   Unstopped affine continuation predicts a negative outsider cap at m=11,
   while the actual cap resets to the Quit endpoint zero. Stopping before
   cap reset is mathematically essential.
3. **An arbitrary source can have a cap below its singleton.** In a two-player
   game with player 0 singleton reward 1 and both player-0 rewards at coalitions
   containing player 1 equal -1, a source where player 1 quits immediately
   gives `B_0=-1<s_0`. This rules out an unconditional owner-cap-constancy
   lemma. The low-cap branch in the reviewed proof handles this situation.
4. The supplied archive checker was run with its writing main disabled. Its
   explicit 59-row regression, 300 exact rational auxiliary-ledger checks,
   30 additional signed first-hit blocks, and 16 collar-algebra instances all
   passed. These are exact finite tests, not proof of the universal claim or
   existence of a positive-minimum game.

## Source audit and frontier delta

The audit used the root and conference AGENTS files, SOURCES, GOAL, the two
research-method files, the export gate, and bounded FRONTIER/TOOLKIT lookup.
Exact declarations inspected include:

- `quittingTerminalSemanticPair_rootThenContinuation`,
  `quittingTerminalSemanticCarrier_isCompact`,
  `exists_terminalProfile_sequence_tendsto_semanticPair`, and
  `quittingTerminalSemanticPrefix_mem_carrier`
  (`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`): complete-cap
  semantics, actual prefixing, compactness, and carrier closure.
- `quittingTerminalSemanticDebt_prefix_le_auxiliaryNash`
  (`UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`): the existing
  coordinate auxiliary budget.
- `minimumTerminalSemantic_singletonMargin` and
  `not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticPlateau`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`):
  the old margin and no-UE/global-minimum interpretation.
- `exists_offMinimum_collar_on_completeCap_singletonSlab`
  (`UniformEquilibrium/Diagnostics/Quitting/CompleteCapSingletonSlabCollar.lean`)
  and `exists_eventual_offMinimum_collar_of_completeCap_tendsto_singleton`
  (`UniformEquilibrium/Diagnostics/Quitting/CompleteCapSingletonLimitCollar.lean`):
  qualitative off-minimum collars already exist.
- `QuittingSingletonTightMinimumFace`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSingletonTightMinimumFaceIteration.lean`):
  the old fixed-row argument has a singleton-tight, unique-debtor source.
- `quittingTerminalSemanticDebt_prefix_eq_of_capContinue` and
  `abs_quittingTerminalSemanticCapContinueGap_sub_singletonMargin_le`
  (`Research/Quitting/TerminalSemanticWeightedDebtAxisInsertion.lean`): existing
  local cap-Continue algebra, outside the integrated production surface.
- `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`)
  and the named strict-minimum declarations in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`:
  qualitative strict minimum-fiber separation is existing mathematics.
- `exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform`
  (`UniformEquilibrium/Quitting/Classification/LCP/FourPlayerSingletonColumnBlockers.lean`):
  the all-sign Fin4 blocker adapter has precisely the claimed hypotheses.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`):
  the fixed-uniform-payoff consumer.

The auxiliary absorption and approximate-root input is credited to
[`AUXILIARY_CAP_DESCENT_AND_EXACT_LIMITS.md`](../gpt/AUXILIARY_CAP_DESCENT_AND_EXACT_LIMITS.md);
the portions used here were rederived above. Its separate exact-limit claim
is not an input to this audit. Literature README and a narrow transcription
phrase search were inspected; no original-paper theorem is invoked and no
literature-wide priority is claimed.

The strict new boundary is a finite source construction with an exact total
budget at arbitrary actual sources, followed by an explicit finite selector
under weak payoff exclusion and an explicit quadratic collar. This does not
answer all tables in
[`FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md`](../questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md).
It neither supplies weak exclusion for every canonical table nor returns a
useful owner from every strict-interior source. That residual remains open.

## Narrow recheck after external integration

At external head `c2789f0`, I inspected the newly integrated
`eventually_capResponseSegment_debtSum_ge_min_add`
(`UniformEquilibrium/Diagnostics/Quitting/CapResponseSegmentCollar.lean`) and
`eventually_capResponseSegment_exactRoot_debtDrop_and_absorption`
(`UniformEquilibrium/Diagnostics/Quitting/CapResponseSegmentExactRootExpenditure.lean`).
The former transports the already audited qualitative singleton-slab collar
over supplied unilateral response mixtures. The latter assumes an actual
sequence with attained responses, a positive named owner-debt floor, and
that owner's cap converging to its singleton; it gives eventual exact-root
debt and absorption bounds. Neither supplies arbitrary-source finite
threshold selection or the WE iteration. In particular the threshold
crossing outsider in the present theorem need not have a positive coordinate
debt floor. The new integration therefore does not subsume the packet's
actual-source construction or explicit all-debt quadratic collar.
