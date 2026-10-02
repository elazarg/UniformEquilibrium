# The two capstones: exact frontier map

Author: CLAUDE_FABLE. Attempt-lane inventory: every item marked *checked*
was read at its declaration under its file; Research-lane declarations
compile in that lane and carry no axiom-audit record. Items marked
*derived* follow from checked statements by the displayed algebra and are
not separately formalized. Notation: \(D(z)\) total terminal-semantic
debt of a carrier pair \(z\), \(D_*=D(\text{source minimum})\), \(M\) the
reward bound, \(s_i=r_i(\{i\})\), caps \(c=z.2\).

## 1. The reduction to two capstones (checked)

`uniformPayoff_or_sourcePreservingUniformEscape_or_minimumReturn`
(`Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`):
every bounded Fin4 table admits a uniform-equilibrium payoff, or is
uniform-escape realizable, or is minimum-return realizable. The two open
consumers are the Props `FinFourUniformEscapeCapstone` and
`FinFourMinimumReturnCapstone` (same file); `finFourCompletion_of_capstones`
composes them into the bounded Fin4 theorem. Deciding P(4) for bounded
tables is exactly: prove both capstones, or refute one by a table whose
realizable trajectory carries no equilibrium.

## 2. Packet anatomy (checked)

A stabilized forced-pair stream has semantic tails
`stream.tail rank ∈ carrier` (`tail_mem`) with excess
\(E_k=D(T_k)-D_*\ge0\) (`excess_nonneg`). The mode split
(`uniformEscape_or_minimumReturn`, via
`positive_subsequence_or_tendsto_zero`):

- **escape packet**: one `floor` \(>0\) with \(E_k\ge\)`floor` at every
  rank (`excess_floor`, `tailDebt_floor`);
- **return packet**: \(E_k\to0\) (`tailDebt_tendsto_minimum`).

Tails are literally realized: `continuationProfile` is an actual
behavioral profile whose semantic pair **equals** the stored tail
(`semanticPair_continuationProfile_eq_tail`,
`Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionConsumers.lean`).
Any machinery needing an actual profile applies at every tail with zero
loss. Packets self-shift (`drop`, `iterateDrop`, `trajectory`), so every
statement provable from "some rank onward" transfers to a realizable
trajectory.

## 3. Per-rank dispatch at escape tails (checked)

`FinFourUniformEscapePacket.exists_maximalCapNash_halfFloorDispatch`
(Consumers file), from
`exists_maximalCapNash_returnSelection_or_sameTailUndercharge`
(`Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean`): at every
rank there is an exact cap-Nash root \(\rho_k\) at the tail cap,
absorption-maximal among all exact cap-Nash roots there, with positive
survival, and

1. **return selection**:
   \(D(T_k)A(\rho_k)\ge E_k-\texttt{floor}/2\); prefixing gives an
   *actual* profile with debt \(\le D_*+\texttt{floor}/2\)
   (`returnedProfile_debt_le_minimum_add_halfFloor`); the only checked
   further consumer, `exists_nearMinimum_resetPrefix_of_capNashReturnSelection`
   (`TerminalSemanticResetExcursionReturn.lean`), additionally needs a
   zero-debt coordinate at the tail
   (\(d_{who}(T_k)=0\)) that no packet field supplies; **or**
2. **universal failure**: no exact cap-Nash root at this tail is a
   return selection, *and* the undercharge
   \(D(T_k)A(\rho_k)<E_k-\texttt{floor}/2\) holds, *and* either
   - (2a) all-Continue is exact cap-Nash at \(T_k\)
     (equivalently \(s_i\le c_i(T_k)\) for all \(i\),
     `isZeroQuittingRootNash_allContinue_iff_singleton_le`), or
   - (2b) some blocker \(j\) has \(\eta_k=s_j-c_j(T_k)>0\) and
     \(\eta_k/(\eta_k+2M)\le A(\rho_k)\).

**Derived (2b excess cap).** Chaining the 2b absorption floor with the
undercharge on the same maximal root:

\[
\frac{\eta_k}{\eta_k+2M}<\frac{E_k-\texttt{floor}/2}{D_*+E_k}
\qquad\Longrightarrow\qquad
\eta_k\;<\;\frac{2M\,(E_k-\texttt{floor}/2)}{D_*+\texttt{floor}/2}.
\]

A 2b rank cannot carry a blocker gap larger than (a fixed multiple of)
its tail excess. In particular, along any sub-branch with
\(E_k\) bounded, the 2b blocker gaps are uniformly bounded by the same
expression.

Pigeonhole: at least one of the three branches occurs at infinitely many
ranks, and by `drop`-shifting the packet the chosen branch may be assumed
to occur at every rank of a realizable trajectory.

## 4. The maximal-cap chronology (checked)

`Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean`, seeded at any
actual profile — in particular at any `continuationProfile`:

- selector: `quittingMaximalAbsorptionCapRoot` (compactness of the exact
  cap-Nash correspondence, `exists_maximalAbsorption_isZeroQuittingRootNash`);
  recursion `quittingMaximalCapPrefixProfile`; exact debt recursion
  \(D_{n+1}=(\text{continue mass})\cdot D_n\)
  (`quittingMaximalCapPrefixProfile_debt_succ`); stage atoms shift and
  scale by the same factor.
- capacity: \(D_*\cdot\sum_n A_n\le D_0-D_n\)
  (`minimum_mul_sum_maximalCapPrefix_absorption_le_debtDrop`), hence
  summable absorption (`summable_maximalCapPrefix_absorption`) and total
  charge \(\le(D_0-D_*)/D_*\)
  (`maximalCapPrefixPunishmentFloorPrefix_charge_le_semanticBudget`):
  this chronology alone can never trigger an unbounded-prefix-charge
  compiler.
- blocker consumption: a fixed singleton-cap gap cannot persist
  (`exists_maximalCapPrefix_singletonGapCollapse`); the same cap
  coordinate rises by \(\eta/2\) within a finite horizon, that rise is
  paid by \(4M\times\)charge
  (`abs_maximalCapPrefix_cap_sub_initial_le_charge`), and every fixed
  suffix atom retains the debt-ratio fraction \(D_*/D_0\) of its mass
  (`maximalCapPrefix_atomMass_lowerBound`); packaged with punishment-floor
  legality in `exists_maximalCapPrefix_punishmentFloorCharge_retainingAtom`
  (the owner-decoder gap is discharged for this branch).
- first-step reduction
  (`maximalCapPrefix_positivePunishmentCharge_retainingAtom_or_uniqueAllContinue`):
  positive charge with retained atom, or the current cap's exact-Nash
  correspondence is uniquely all-Continue.
- no-return limit (`exists_offMinimum_retainedLaw_allContinue_or_supportEntry`):
  if no chronology state enters the requested minimum neighborhood, a
  joint semantic/law cluster point exists, off-minimum by at least the
  tolerance, retaining a positive suffix atom, with all-Continue exact
  Nash at its cap — and either that correspondence is uniquely
  all-Continue or a positive-absorption exact root appears at the limit
  cap (the support-entry residual).

The file's terminal local obstruction, in both branches: **a cap whose
exact-Nash correspondence is the singleton all-Continue root**, reached
with positive retained debt.

## 5. Near-minimum radius machinery (checked)

`TerminalSemanticCapNashNearMinimum.lean`: minimality relativizes with
slack. For carrier \(z\) with \(D(z)\le\text{ref}+\varepsilon\) where
ref lower-bounds \(D\) on the carrier:

- slack budget (`nearMinimumTerminalSemantic_auxiliaryNash_budget`):
  \(\text{ref}\cdot\text{collision}+\sum_i\text{singleton}_i(\text{ref}-h_i)\le\varepsilon\);
- constant shift \(q\): \((\text{ref}-q)A\le\varepsilon\)
  (`nearMinimumTerminalSemantic_constantShiftNash_absorption`);
- via the joining-loss endpoint decomposition, the cap-freeze theorem
  (`nearMinimumTerminalSemantic_capNash_eq_allContinue`) and the
  table-level radius
  (`exists_pos_nearMinimum_capNash_eq_allContinue_radius`): there is
  \(\varepsilon(r)>0\) such that **every** carrier pair within
  \(\varepsilon\) of the debt floor has uniquely-all-Continue exact
  cap-Nash correspondence. No compactness, no punishment-normality.

Placement: the radius is vacuous at escape tails (they sit \(\ge\)floor
off-minimum) and bites on minimum-return tails — by
`tailDebt_tendsto_minimum` those are **eventually inside the radius**,
so the minimum-return trajectory is eventually strict-inert at every
tail. It equally shows the §4 obstruction is genuinely realized near
minima. Assembly B (uniform-\(\varepsilon\) reset-dispatch boundary:
radius + `terminalSemanticLawCarrier_fst_mem_carrier` +
`QuittingFixedLawResetDispatch.dynamic_exit` +
`quittingRootAbsorptionMass_allContinueRoot`) is a sharpening of the
dispatch boundary, delegated to the scratch lane for formalization; it
consumes no chamber.

## 6. Open composition points

1. **Branch-1 consumer**: supply, or dispense with, the zero-debt tail
   coordinate \(d_{who}(T_k)=0\) needed by
   `exists_nearMinimum_resetPrefix_of_capNashReturnSelection`. Without it
   branch 1 yields actual near-minimum profiles
   (\(D\le D_*+\texttt{floor}/2\)) with no reset face.
2. **Branch-2b consumer**: the chronology consumes the blocker gap into a
   charged punishment prefix with retained atom, but terminates in the
   §4 obstruction (uniquely-all-Continue cap off-minimum, or support
   entry at a limit cap). No UE conclusion.
3. **Strict-inert consumer** (branch 2a; radius region; minimum-return
   tails eventually): all-Continue exact Nash with positive retained
   debt is semantically inert — the standing nonanswer of both chamber
   files.
4. **Capacity**: each chronology's charge is bounded by its initial
   excess over \(D_*\); no checked mechanism concatenates charges across
   ranks or across chronologies into unbounded charge; and the
   capacity accounts charge exact Nash--Bellman roots only — actual or
   arbitrary-root absorption (e.g. the pre-mark floor output) is not
   yet convertible into that currency.

## 7. The minimum-return side (checked inventory)

- **Strict-inert datum** (produced unconditionally by
  `FinFourMinimumReturnPacket.nonempty_normalizedThreeRole_or_strictInert`,
  Consumers file): a carrier point \(y\) with \(D_*<D(y)\), the full
  equivalence "exact cap-Nash root at \(y.2\) \(\leftrightarrow\)
  all-Continue", a retained marked-pair decoration, and the outer
  residual. No checked consumer takes it to a UE payoff or to False.
- **Consumers with zero missing hypotheses but non-terminal
  conclusions**: the moat family of `TerminalSemanticPlateauNashMoat.lean`
  (`exists_totalNashDefect_moat_of_unique_allContinue`,
  `exists_absorptionNashDefect_moat_of_unique_allContinue`, and the
  eventual variants) — quantitative defect/absorption bounds only.
- **The one neighborhood consumer**:
  `eventually_exactRoot_eq_allContinue_of_unique_of_singletonGap`
  (`TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`)
  propagates uniqueness to a cap neighborhood; it needs the uniform
  STRICT singleton gap \(\delta\le c_i-s_i\). The stored datum gives
  only \(s\le c\) (via
  `isZeroQuittingRootNash_allContinue_iff_singleton_le`). The general
  off-minimum strict moat is false (sure-solo-quit pairs are tight);
  the correct local statement is the tight-coordinate dichotomy, whose
  core is integrated (`exists_quittingSingletonCollisionGain_pos_of_unique_allContinue`,
  `exists_quittingSingletonCapBindingCollisionCycle`); the strict/uniform
  no-tight-eager-pair corollaries are scratch-checked (`TIGHT_COORDINATE_DICHOTOMY.md`,
  `lean/FableTightCoordinateDichotomy.lean`): at a unique-all-Continue cap the
  tight set is empty (strict gap holds) or carries an eager cycle
  (\(|Z|\ge2\), each tight coordinate recruited by a tight joiner with
  positive collision entry `quittingCollisionMatrix`). The production
  cycle consumer sits at the law-tight minimum only (singleton/Never
  chamber of `lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle`);
  the off-minimum strict-inert placement is unconsumed.
- **Marked-row cap-defect floor** (scratch-checked, ledger entry 19):
  at any selection with a uniform marked-mass floor and tails
  converging to a minimum-debt carrier pair, the marked live root pays
  a uniform total Nash defect against the tail cap — the actual play
  is uniformly cap-inexact at the mark, the `.2`-side complement of
  the stored `.1`-side marked-owner zero
  (`fable_strictInert_markedRow_capDefect_floor`, with the whole-debt
  excess floor `fable_strictInert_wholeDebt_excess_floor`,
  `MARKED_ROW_CAP_DEFECT_FLOOR.md`). The companion multiplicity bound
  (ledger entry 20, `MARKED_DATE_MULTIPLICITY_BOUND.md`) caps the number
  of such \(\kappa\)-marked near-minimum dates in any single play by
  \(D(\pi)/(\kappa\,\mathrm{moat})\).
- **Radius placement**: minimum-return tails eventually enter the
  table-level radius of
  `exists_pos_nearMinimum_capNash_eq_allContinue_radius`, so the
  trajectory is eventually strict-inert at every tail (§5).
- **The `.1` vs `.2` trap**: the minimum-fibre and equality-stratum
  families (`TerminalSemanticFinFourMinimumFiberIsolation.lean`,
  `TerminalSemanticEqualityStratum.lean`, basin files) take roots Nash
  against the PRESCRIBED payoff `pair.1`; the dispatch, dispatch
  boundary, radius, and strict-inert data are Nash against the CAP
  `pair.2`. Compositions across that split fail silently — check the
  target coordinate before assembling.
- **Funnel neck for any UE conclusion**:
  `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  (`Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`),
  with unconditional iffs in `PositiveMinimumSemanticDebt.lean` and
  `UniformExistenceBoundary.lean`. No unconditional existence theorem
  above three players exists in the corpus
  (`quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three`).

## 8. Ranked open lemmas (audit synthesis)

1. strict singleton gap at the strict-inert point — reduced by the integrated
   dichotomy core (`exists_quittingSingletonCapBindingCollisionCycle`)
   to excluding the tight eager cycle;
2. a zero-debt coordinate at the escape tail (= §6.1);
3. stationary pair-base target minimality — likely false in general,
   and its conclusion is reset-rigid stall data, not consumption;
4. the two-zero-coordinate minimum killer (what would make 3 matter):
   a positive global minimum with two zero-debt coordinates, unit
   incidence, and a supported strict toggle is impossible;
5. a uniform absorption floor for the maximal roots along the escape
   stream (= the missing concatenation of §6.4; only the 2b-conditional
   floor \(\eta/(\eta+2M)\) is checked).

The cycle-branch residual is posed as
`../questions/OFF_MINIMUM_TIGHT_CYCLE_CONSUMER.md`.

Everything above is checked except where stated; the capstones are
exactly the statements that some composition of §§6–8 (or a new
mechanism) must close.
