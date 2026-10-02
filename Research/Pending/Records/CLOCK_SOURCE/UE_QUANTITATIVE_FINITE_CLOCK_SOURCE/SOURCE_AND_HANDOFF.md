Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Actual quantitative finite-clock source

## Scope and status

Frozen known-proof implementation, not checked here. No Lean/Lake, Git, cache,
worktree, child agent, shared edit, or math-note operation was performed. Root
remains the sole shared editor and compiler. This is the finite-profile
approximation dependency of the single-pivot packet, not a strict-pressure or
whole-packet seal. Independent review has been requested from Astra.

Complete source read: `math/exports/SINGLE_PIVOT_SECANT_COLLAR_AND_STRICT_PRESSURE.md`,
SHA256 `d91cf597df1f45d4287b53244d4f91463ed7f9313d75748a3f0fbcb87dbdfe0c`.
The literal claim is Section6.1's reward-uniform approximation and Section11's
printed actual profile with support8j+1 and exploitability at most eta+24/j.
Complete dependency report read:
`/tmp/UE_SINGLE_PIVOT_PACKET_COMPLETION_DEPENDENCIES_20261002.md`,
SHA256 `4376763deede29be9ab5047c3f07995f6ecf1a1aad8322c8d1aae4019490cfa9`.
Its old generic smoothing/envelope absence is superseded by the checked current
`MathUE/Analysis/FiniteLogSumExp.lean` and
`MathUE/Analysis/CompactMinimumEnvelope.lean`; neither is reimplemented here.

## Exact source-producing declarations

All declarations below are frozen drafts, not reported as checked.

- `exists_finiteClockStoppingLaws_exploitability_le`
  (`UniformEquilibrium/Quitting/Paths/QuantitativeFiniteClockSource.lean`):
  arbitrary finite nonempty players; only unit terminal-reward bound and positive
  level. Internally selects independent complete marginal laws, finite support at
  the canonical common-quantile clock count, eta <= actual full exploitability <=
  eta + twice the semantic radius, and terminal approximate Nash against EVERY
  full behavioral replacement at that same bound.

- `exists_fin4_finiteClockStoppingLaws_exploitability_le`:
  SAME literal profile and laws, support8j+1, error24/j, full behavioral Nash.
  No zero-infimum, no-UE, nonnegative reward or singleton assumption.

- `exists_fin4_uniformCalendarStoppingLaws_exploitability_le`:
  ONE law tuple precedes ALL clock bounds at least8j+1; all payoff/cap/Nash
  conclusions concern its unchanged actual independent profile.

- `fin4FiniteClockApproximationError`,
  `tendsto_fin4FiniteClockApproximationError`, and
  `exists_fin4_calendarUniformStoppingLaws_exploitability_le`:
  literal j=(clock-1)/8 and rho(clock)=24/j. For every clock>=9 internally
  select ONE laws tuple before ALL larger calendars. The bound is independent
  of reward and tends to zero. This supplies the uniform-in-reward estimate
  used on the source parameter interval, without taking that interval or a
  supplied favorable compression/minimum/profile as an input.

Full caps are the canonical `quittingTerminalExploitability` caps.
`IsεAsymptoticNash` is only terminal approximate Nash here; it is not silently
a finite-horizon equilibrium, one fixed UE target or a uniform-equilibrium payoff.
Never is a separate allowed law atom. Quantile compression retains each marginal's
Never probability exactly, proved by the promoted
`quittingQuantileClockCompressedLaws_none`.
Finite support means dates strictly below the clock bound plus literal Never;
date zero is allowed. This is not the later silence-shifted source on dates1,...,N.

## Canonical reuse and promotion

00 extracts the EXISTING game-independent mutual-supremum proof into
`MathUE/Order/MutualSupremumApproximation.lean`, with declaration
`Math.Order.abs_sSup_range_sub_sSup_range_le_of_mutual_approx`.
Only pinned real conditional completeness and linarith are imported.
02 preserves the existing `GameTheory` name/signature by thin delegation.
No new competing generic proof remains.

01 moves `Research/Quitting/FiniteClockTerminalSemantics.lean` byte-for-byte to
`UniformEquilibrium/Quitting/Paths/FiniteClockTerminalSemantics.lean`.
02 moves the active quotient/coupling proof to
`UniformEquilibrium/Quitting/Paths/CommonQuantileClockTransport.lean`;
apart from owner imports and that generic delegation its proof body is unchanged.
03 moves the existing compact-center hierarchy proof to
`UniformEquilibrium/Quitting/Paths/CommonQuantileClockApproximation.lean`;
only the owner import/documented paths change.
The three OLD Research files become thin compatibility imports. Thus no long
Research copy or production import of Research remains. Existing Research
consumers keep their original import paths and public declaration names.
All three original bodies and the precise changed declarations were inspected.

Existing reconstruction/expectation wrappers already delegate:
`quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile`,
`quittingTerminalPayoff_update_pureTime_eq_compactStoppingLawsOfProfile`,
`quittingTerminalPayoff_compactStoppingLawProfile_eq_expect`, and
`quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_eq_expect`.
The production `quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff`
in `Paths/StoppingLawOperationalDistance.lean` instead has a first-outcome reward
integrand and a Nonempty player premise. The preserved wrapper has a
pure-profile payoff integrand and permits empty player types. Neither its
foundational expectation proof nor a second independent-law semantics is copied.

Current nonquantitative
`exists_finiteDeadlineTimingProfile_approximation`
(`Terminal/FiniteMenuFullProfileApproximation.lean`) has a source/error-dependent
deadline and does not supply the prescribed8j+1 or24/j. It cannot replace this
literal source claim. Current raw-calendar decoded-law and finite full-reply-cap
owners remain the next actual common-pool adapter dependencies, not duplicated
by this unit.

04 delegates compact internal attainment to
`exists_finiteClockSemanticPair_exploitability_eq_upper`, error control to
`escapeAwareQuantileClock_quantitative_bracket`, actual eta lower bound to
`quittingTerminalExploitabilityInf_le`, and all-behavior Nash to
`isεAsymptoticNash_of_quittingTerminalExploitability_le`.
It supplies canonical normalized compression internally. No attained behavioral
global minimum is inferred. Monotone support embedding reuses
`isFiniteClockStoppingLaw_mono`; the floor level and vanishing error reuse
`Nat.tendsto_div_const_atTop`, `Filter.tendsto_sub_atTop_nat`, and
`tendsto_const_div_atTop_nhds_zero_nat`.

## Application and verification order

Exact base/result and artifact hashes: `ORDERED_APPLICATION_MANIFEST.json`.
Apply00,01,02,03,04, then05. The first two units are independent;02 needs both;
03 needs02;04 needs03. No future chart, secant, screened fiber or payoff
normalization patch is a prerequisite.

05 adds one MathUE and four production umbrella imports against the recorded
CURRENT umbrellas. Queued independent umbrella additions may change their
whole-file hashes; its two unique import contexts are the intended local merge
boundary, never an instruction to replace an entire newer umbrella.
Research.lean needs no change: its old imports now reach the canonical modules.
Root must regenerate exhaustive AxiomAudit after the inventory change.

Root-owned named checks, one at a time:
`MathUE.Order.MutualSupremumApproximation`;
`UniformEquilibrium.Quitting.Paths.FiniteClockTerminalSemantics`;
`UniformEquilibrium.Quitting.Paths.CommonQuantileClockTransport`;
`UniformEquilibrium.Quitting.Paths.CommonQuantileClockApproximation`;
`UniformEquilibrium.Quitting.Paths.QuantitativeFiniteClockSource`.
Then check the supplied source-scope harness, compatibility module
`Research.Quitting.EscapeAwareQuantileClockHierarchy`, all import/duplicate/trust
checks and the inventory-wide axiom audit/full gate as root chooses.
`AXIOM_HARNESS.lean` prints15 relevant core/producer declarations; only standard
propext, Quot.sound and Classical.choice are permitted. Neither harness has run.

Static result-body scan: no non-import lines exceed100 characters, no forbidden
project trust constructs or deprecated if/dif aliases were introduced, production
payloads have no Research imports, and the original canonical proof source hashes
remain unchanged in the shared checkout. This is not a substitute for compilation.

## Remaining actual source obligations

This unit does NOT select the tilted outer parameter, its scalar-envelope inner
minimizers or tester weights. It does NOT establish same-weight pressure,
every-competitor derivative residuals, MAX-minimum cap moats, silence/normalizer
transport, fixed-table limiting selection, finite pivot response, private max-clock
delay or outsider-debt control. Source C1's actual independent full-cap
approximation is the supplied dependency; the full packet remains incomplete.
No source mathematical defect was found in this unit.
