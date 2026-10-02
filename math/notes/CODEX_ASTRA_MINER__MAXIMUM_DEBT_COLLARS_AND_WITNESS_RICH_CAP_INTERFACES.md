# Maximum-debt collars and witness-rich cap interfaces

Identity: CODEX_ASTRA_MINER.

Status: bounded static source audit and routine-composition proposals. No new
Lean theorem, compilation of the proposed results, export, or conjecture
advance is claimed. The coordinator reported that the completed product-low
packet passed the full integration gate; this note deliberately looks beyond
its theorem coverage. The separate prepared `ScreenedMembershipDebt` source
passed a strict local check, but it is not evidence for the proposals below.

## Question and bounded source selection

Which literal conclusions can be recovered from already implemented
constructions without producing a new unrestricted equilibrium argument?
The selection started from the minimum-fiber, stopping-law reset, and
finite-calendar entries in `docs/TOOLKIT.md`. Following the LARCH
[selection guidance](CODEX_LARCH__CROSS_EPISODE_PATTERN_MINING.md), this pass
compares exact hypotheses, preserved witnesses, and distant consumers rather
than repeated tactic text. No claim of exhaustive novelty is made.

Three candidates survive:

1. A uniform low-coordinate-debt collar around the positive **maximum**-debt
   minimum, with the same actual half-reset and chronological retention.
2. The full semantic graph on each fixed finite calendar, including all
   unrestricted caps, as a compact semialgebraic set.
3. A quantitative common approximate-response witness retained from the
   convexity proof for a single stopping-law mixture.

The first is the best near-term source adapter. The second is bounded
classification infrastructure. The third is a small generic extraction,
not a new common-witness theory. All are known compactness, finite-polynomial,
or supremum arguments. None requires solving an open mathematical proposal.

Throughout, players are finite and nonempty, the reward table is fixed unless
explicitly parameterized, Never pays zero, and caps range over complete
unilateral behavioral strategies. Write `C` for the terminal semantic carrier,
`d_i(z)` for its coordinate debts, and `E(z)=max_i d_i(z)`.

## 1. A low-debt-coordinate collar for the maximum-debt minimum

### Proposed literal theorem

Assume every reward entry has absolute value at most one, `z0` belongs to `C`,
`m=E(z0)>0`, and `m <= E(z)` for every `z` in `C`. For every `a<m`, there is
one `delta>0` such that

    z in C and (exists i, d_i(z) <= a)  implies  m + delta <= E(z).

The same `delta` works for every player and every carrier point, not merely a
selected sequence. A proposed descriptive name is
`exists_maximumDebt_collar_of_coordinateDebt_le`.

This strengthens strict separation to a uniform collar. It does not select
an actual realization of `z0` or imply that all carrier minima are actual.

### Exact dependencies and routine proof

`minimumTerminalSemantic_maximumDebt_allPlayersTie`
(`UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`)
says that **every** coordinate of **every** positive maximum-debt minimizer
equals `m`. It has the displayed unit reward bound and no punishment-normality
or singleton-sign hypothesis.

`quittingTerminalSemanticCarrier_isCompact`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`) and
`continuous_quittingTerminalSemanticDebt`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticDebt.lean`) make

    F = C intersect union_i {z : d_i(z) <= a}

compact. If `F` is nonempty, minimize `E` on `F`. Its minimum is strictly
larger than `m`, since equality would contradict all-player ties and `a<m`.
Half that positive difference is a collar. If `F` is empty, any positive
collar works.

The same compact-slab proof is already implemented for a different observable
and a different objective by `exists_offMinimum_collar_on_completeCap_singletonSlab`
(`UniformEquilibrium/Diagnostics/Quitting/CompleteCapSingletonSlabCollar.lean`).
That theorem concerns **total** debt and cap-to-singleton distance; it is a
proof template, not an applicable theorem with its objective silently changed.
Likewise the older carrier-source charge gate has a total-debt minimum.

### Actual constructor-to-consumer match

Suppose an actual profile `p` attains this positive global maximum-debt minimum.
For any selected player, use
`exists_stoppingLawMixture_debtContraction_and_windowRetention`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMixture.lean`)
with mixture weight `1/2` and response error `m/2`. Its same actual mixed
profile `q` satisfies

    d_i(q) <= 3m/4,
    E(q) >= m + delta,
    stageMass(q,t,S) >= stageMass(p,t,S)/2  for every t,S.

Here use the collar with `a=3m/4`. The stagewise conclusion holds
simultaneously for every chronological atom by
`one_sub_mul_stageCoalitionMass_le_stoppingLawMixture` in the same file;
the constructor's displayed single-window conclusion need not force a fresh
response choice for each window. Preserve the selected response explicitly,
then apply that universal lemma. No stopping cutoff enters `delta` or the gain.

`quittingTerminalSemanticDebt_stoppingLawMixture_le`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`)
also retains the actual approximate-response endpoint `b`. Since all source debts are
`m`, a coordinate maximizing the mixed profile's debt has

    d_j(b) >= m + 2delta,  with j different from i.

The mover has debt at most `3m/4` at the mixture, so it cannot be that `j`.
This is an actual same-witness off-minimum response endpoint, not a positive
UE consumer or a return to the minimum fiber.

A simpler useful corollary: an exact cap-attaining unilateral response cannot
land anywhere on the positive maximum-minimum fiber. Its mover debt is zero.
The old `QuittingPureTimeMaxDebtExactResponseStep.target_mover_debt_eq_zero`
(`UniformEquilibrium/Diagnostics/Quitting/PureTimeSelectedExactResponseOrbit.lean`)
supplies that conclusion for the already selected inherited-clock response.
Thus such a step from a maximum-minimizing pure-clock profile exits the fiber
in **one** step. This is distinct from `pureTimeMinimum_exists_offMinimum`
(`UniformEquilibrium/Diagnostics/Quitting/PureTimeMinimumDescent.lean`), whose
objective is total debt and whose proof uses finite replacement ancestry.

### Scope and priority

High priority, short compactness lemma plus actual-reset adapter. The collar
is existential, table-dependent, and not an explicit numerical modulus. It
gives no uniform positive separation over all reward tables. Exact-response
attainment is not needed for the half-reset consequence. Do not infer that an
off-minimum response produces a profitable coordinated descent.

The unit bound can separately be generalized to an arbitrary positive absolute
reward bound by the same supplied solo-prefix proof with scaled constants.
That generality is already ordinary mathematics in
[the all-player-ties note](CODEX_HILBERT__GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES.md);
it is a routine formalization gap, not a newly discovered theorem.

## 2. Fixed-calendar full semantic graphs, not global cap compression

### Proposed literal theorem

For fixed player count `n>0` and fixed deadline `H`, let `x` range over the
literal product of simplices on `Option (Fin H)`. The graph

    {(x,U,B) : U = actual terminal payoff of x,
                 B = unrestricted behavioral response-cap vector of x}

is compact and semialgebraic for every fixed real reward table. With reward
entries added as variables, the joint graph is semialgebraic; it is compact
only after restricting rewards to a compact set. Therefore the image in
`(U,B)`, the graph of full exploitability, and fixed-target full-error
feasibility on this calendar are semialgebraic. The minimum full
exploitability over this fixed calendar is attained.

### Exact old and new interfaces

`quittingContinuationBestResponseValue_finiteDeadlineTimingProfile_eq_max`
(`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineFullReplyCap.lean`)
identifies the complete cap with the maximum of the displayed finite reply
cap and **one additional late-Quit row**:

    B_i = max(menuCap_i, NeverPayoff_i + opponentNeverProduct_i * singleton_i).

The same file's
`quittingFiniteDeadlineTimingProfile_pureTime_eq_never_add_of_le` proves
literal equality for every finite response date at least `H`. Deadline zero
is included. `quittingFiniteDeadlineReplyCap`
(`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineReplyCap.lean`) is a
finite maximum over the early dates and Never, not a supplied cap bound.

`eval_quittingFiniteCalendarJointPayoffPolynomial_simplex`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarJointPolynomial.lean`)
already provides actual joint reward/calendar payoff evaluation. Substituting
a pure action into one player's simplex row gives the displayed reply
polynomials. Substituting Never gives `NeverPayoff_i`; multiplying the other
players' Never coordinates and the same original singleton reward gives the
last row. The polynomial graph of a finite maximum is a finite conjunction
of upper bounds plus a finite disjunction of equality to one candidate.
Continuity of these finite maxima on the compact simplex gives compactness.

The only representation adapter is between the raw simplex realization and
the existing finite timing PMFs. Reuse `finiteCalendarSimplexPMF_toReal`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPayoff.lean`) and
`quittingFiniteDeadlineTimingPayoffMap_stdSimplexEquiv`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffClosure.lean`). No new
stopping-law representation is warranted.

### Concrete consumer and nonclaims

For rational reward, target, tolerance, and a specified finite `H`, encode

    exists x in simplex, all target-error bounds hold and all B_i-U_i <= error.

Use `decideClosedFormula_eq_true_iff`
(`MathUE/RealQuantifierElimination/QuantifierElimination.lean`) to obtain an
executable decision with actual full-cap semantics. This requires a rational
syntax frontend and a computable coordinate enumeration; the existing real
`MvPolynomial` graph alone is not an executable recognizer.

Medium priority: the mathematical proof is routine; the literal row
substitution/PMF adapter is the substantive implementation work. Preserve
Never and the late row separately for signed singleton rewards.

Most importantly, the fixed calendar used by
`quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff`
(`UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffClosure.lean`) preserves
payoffs only. It cannot be used to replace arbitrary full semantic pairs by
this fixed-calendar graph. Allowing unbounded `H` does not make the union
semialgebraic and does not turn the family of finite decisions into a decision
of UE existence. This is not the already-mined finite-menu approximation or
single-pivot inner LP identity; it is the missing literal full-cap graph on
each separately supplied finite calendar.

## 3. Retain one approximate response from cap convexity

### Small generic extraction and actual specialization

For bounded real payoff families `f0,f1` on the same nonempty deviation type,
let `B0,B1` be their suprema and let `Bt` be the supremum of
`(1-t)f0+t*f1`, with `0<t<1`. Put

    J = (1-t)B0 + t*B1 - Bt >= 0.

If a displayed deviation `d` is `eta`-optimal at the mixture, its two endpoint
regrets obey the exact identity and bounds

    (1-t)(B0-f0(d)) + t(B1-f1(d))
      = J + Bt - ((1-t)f0(d)+t*f1(d)) <= J+eta,
    B0-f0(d) <= (J+eta)/(1-t),
    B1-f1(d) <= (J+eta)/t.

Thus `J=0` iff for every positive tolerance there is **one** deviation
simultaneously approximately optimal at both endpoints. This does not require
attainment. Nor does exact equality imply an exact common maximizing
deviation when the suprema are not attained.

This is ordinary weighted nonnegative-regret algebra. In the quitting
specialization, hold all but one prescribed stopping law fixed and use
`quittingTerminalPayoff_stoppingLawMixture_eq` and
`quittingContinuationBestResponseValue_stoppingLawMixture_le`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`).
Apply the affine identity after installing the observer's **same** deviation
at both endpoints, exactly as that proof already does. A mixture
approximately optimal response is provided by
`exists_quittingContinuation_deviation_ge_sub`
(`UniformEquilibrium/Quitting/Root/FirstBranch.lean`).

### Why keep this, and why not call it new theory?

The current convexity conclusion forgets its useful response witness. The
generic `OrientedSupremumWitnessSwitch` and
`finiteCube_commonPassport_or_edgeWitnessSwitch`
(`MathUE/Optimization/SupremumTwoResetWitnessSwitch.lean`) address four corners
or a reset cube, with different curvature hypotheses. They do not directly
state this two-endpoint mixture-gap estimate. A narrow generic lemma followed
by the actual single-law adapter would make future cap-affinity claims
auditable without silently selecting different responses at the endpoints.

Lower priority, small implementation. No source in this pass supplies small
`J`; it is an observable defect to retain, not a discharged premise. The
constants deteriorate as the mixture approaches an endpoint. This does not
repair simultaneous multi-player witness switching, arbitrary continuation
splicing, or the existing common-witness noncompositionality examples. The
broader [LARCH witness-interchange rejection](CODEX_LARCH_ROUND3_JOINT__WITNESS_INTERCHANGE_MINING_CHECKPOINT.md)
therefore remains valid.

## Rejected matches and next bounded task

- Zero Never and zero singleton law plus strict singleton margin already
  produces a two-sure unpadded product root preserving the complete semantic
  pair and law:
  `exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`
  (`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`).
  The connection to positive minima is already explicit in the formalized
  zero-singleton product-base packet. Another bundled existential is not a
  new discovery. Weak-margin padded realization cannot replace it.
- The linear all-Continue basin, its successor-path bootstrap, and the
  carrier-source debt/error gate are already explicitly composed in
  `FinFourCarrierSourceChargeDebtErrorGate.debt_or_error`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourCarrierSourceChargeDebtErrorGate.lean`).
  Their minimum objective is total debt. No automatic conversion to the
  maximum-debt source or reversal of path orientation is available.
- Weighted coalition partition and solo-floor/cap connections were excluded
  by the initial LARCH screen, not nominated again.

Recommended next task: independently review and formalize item 1, first the
generic low-coordinate collar, then one same-response half-reset theorem
retaining all chronological atoms and the strict endpoint debt increase.
Items 2 and 3 can be implemented independently after separate approval.
No open return, descent, cap-attainment, or same-source realization claim has
been added to the mathematical frontier by this audit.
