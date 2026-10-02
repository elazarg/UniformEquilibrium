# REDUCTION: source correspondence and the positive-finite-reach corollary

Reviewer: CODEX_RENY. Bounded source comparison, not a new full export gate.

Read the complete `gpt/REDUCTION.md`, SHA-256
`1a59b513cc8d1f127c773b72b4d1ee0d8bf3b0e23203f16e6d2f9b4cd70a35db`.
Then followed the exact hardness entry in `docs/TOOLKIT.md` to
`UniformEquilibrium/Quitting/Classification/Existence/ReverseSequentiallyPerfectAbsorbingHardness.lean`
and the associated
`formalized/AKRS_REVERSE_S3_NULL_TAIL_AND_HARDNESS.md`.

## Conclusion

The main universal equivalence, one-player cardinal shift, and quantitative
positive-gap transport are **already covered by checked declarations**.
The new packet uses a genuinely different but mathematically analogous
padding convention. Its positive-reach source is a valid elementary
strengthening not explicitly packaged in the named hardness file; the
same strengthening works on the **existing** padding, without changing
any terminal reward. There is no new reduction of the remaining universal
equilibrium problem.

## 1. Exact correspondence and the genuine table difference

For an arbitrary nonempty finite old player set I, let H_i and L_i include
every old terminal reward and the old Never value z_i, and set
W=max_i(H_i−L_i). Both constructions add one dummy d with Never payoff
zero and choose penalty K>0.

The checked construction gives priority to old quitters. If a terminal
coalition has a nonempty old part S, it pays the old reward r(S) and gives
the dummy zero, whether or not the dummy joins. Only the dummy-only
coalition pays (H,−K). The new packet instead gives (H,−K) whenever the
dummy belongs to the terminal coalition, including simultaneous joining.

These are not definitionally the same table. For example, with one old
player, r({i})=−1 and z_i=0, the joint coalition pays (−1,0) under the
checked convention and (0,−K) under the new convention. The exact source
declarations expressing the checked convention are
`QuittingPayoffTable.oneDummyPadding_terminal_inl_of_oldPart_nonempty`,
`QuittingPayoffTable.oneDummyPadding_terminal_inr_of_oldPart_nonempty`, and
the two `oneDummyPadding_terminal_dummyOnly_*` declarations.

Nonetheless, the retraction proof is the same one-sided coupling mechanism.
Its intervention event is T_d<T_old in the checked construction, and
T_d≤T_old with T_d finite in the new construction. Outside that event old
payoffs agree; on it the enlarged payoff is H_i and the counterfactual old
payoff belongs to [L_i,H_i]. The dummy's exact debt is K times that
event's probability. For an old player's arbitrary deviation, enlarged
payoff is still at least the old payoff; no bound on the intervention
probability **after** deviation is used. Thus both give the same factor
1+W/K and its inverse K/(K+W).

The checked pointwise counterparts are
`QuittingPayoffTable.oneDummyPadding_project_exploitability_le` and
`QuittingPayoffTable.oneDummyPadding_retractionFactor_mul_exploitability_le`.
The quiet-lift and two-sided global-infimum comparisons are already in
`UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingExploitabilityRetraction.lean`
as `quittingTerminalExploitability_passivePaddingQuietProfile_le`,
`retractionFactor_mul_quittingTerminalExploitabilityInf_le_padding`, and
`quittingTerminalExploitabilityInf_padding_le`. In particular the new
packet's factor-three normalized consequence is not a new gap bound.

The exact universal declarations are
`universalReverseSequentiallyPerfectAbsorbing_iff_universalApproximateEquilibriumExistence`
and `universalStationaryExactEveryRestartSource_iff_approximateExistence`.
`stationaryExactEveryRestartSource_sum_punit_implies_approximateEquilibriumExistence`
retains the actual one-player shift. Nothing here identifies the five-player
reverse problem with a same-cardinality four-player reverse implication.

## 2. Minimal corollary on the existing old-quitter-priority table

**Ordinary-mathematics corollary.** In the existing padded table, for every
α∈(0,1], prescribe all old players to Continue and the dummy to Quit
independently with probability α at every date. This is one stationary
exactly row-perfect sequence terminating after every restart. If α<1,
its survival through every finite number of rows is strictly positive.

**Proof.** After any restart, the dummy eventually quits alone with
probability one, because (1−α)^n→0. Hence its actual restarted value is
−K and every old player's restarted value is H_i. An old player i's
pure Quit endpoint is r_i({i}) under **both** root outcomes: if the dummy
Continues then i quits alone, and if the dummy Quits then old-quitter
priority still gives the old singleton payoff. Its pure Continue endpoint
is αH_i+(1−α)H_i=H_i. Its prescribed value is H_i, and
r_i({i})≤H_i. All upper and used-action lower clauses of exact row
perfection hold. For the dummy, Quit and Continue both have value −K,
as does its prescribed mixture. Thus the same exact source works for
every requested positive error. For m≤N its survival is

```text
a_{m,N}=(1−α)^(N−m).
```

This is positive for every finite N when α<1 and tends to zero as
N→∞. Taking arbitrarily small fixed α>0 also makes all stationary Quit
probabilities arbitrarily small. No new payoff construction or retraction
estimate is required. ∎

The inspected Lean file constructs `oneDummySureQuitRoot`, hence α=1,
and proves `oneDummySureQuitRoots_rowZeroPerfect` and
`QuittingPayoffTable.oneDummyPadding_has_exactEveryRestartSource` for
that source. Its predicate
`QuittingPayoffTable.HasStationaryExactEveryRestartRowPerfectSource`
does not require positive finite-date survival. I found no arbitrary-α
source declaration in that file or explicit statement in the associated
formalized packet and original two review reports. Therefore this corollary
should not be advertised as already Lean-checked. It is a direct small
strengthening of the **existing** source, not a new hardness mechanism.

## 3. User-facing scope

The source can be made stationary, exact, every-restart terminating, and
positively reachable at every finite date, yet reverse S.3 over all finite
player sets remains equivalent to general approximate-equilibrium existence.
The new packet correctly illustrates that local row perfection does not
price the dummy's complete Never deviation. That lesson and the main
hardness theorem are already present; the extra positive-reach assertion
is the minimal additional ordinary mathematical content worth preserving.

No frozen formalized packet, Lean source, or export was changed. This
correspondence check does not supply the missing reverse implication.
