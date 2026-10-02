Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Full-table rational positive-eta initial source: unit 74

Frozen static draft, not compiled or integrated. No Lean/Lake, Git, shared
edit, cache, worktree, children or math-note write was used. Root remains the
sole editor/compiler/build-queue owner. Earlier frozen drafts and selections
are unchanged.

## Exact source claim and nonclaims

Source: `math/exports/GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md`,
Section 5.1's paragraph beginning “The initial table can additionally be made
rational in ALL its coordinates”. Complete export previously read; Section
5.1 was revisited. Source SHA256:
`c3004d986acc316a20b7c29a7cdc9c764235f843e4b006a7fc99e0cbe0e0f5d7`.

The source concerns a rational INITIAL table, not rationality of the singleton
vector maximizing eta over a fixed rational free-coordinate fiber. 74 does
not alter 67's ONE rational b, real singleton maximizer or rational gamma.
It does not produce polynomial nonvanishing, a screened gap, singleton collar,
calendar, finite-clock law or equilibrium. Those are separate owners/units.

## Frozen implementation

`74_FULL_RATIONAL_POSITIVE_ETA_SOURCE.patch`
SHA256 `23a9cb9fcf3474b1a7bb8e067b6f3d43331c4f0bfd1a0c241d14ab6040a5b420`.

It adds only
`UniformEquilibrium/Quitting/Terminal/RationalPositiveExploitabilityApproximation.lean`.
It does not write umbrellas, inventories, documentation or other shared files.

Actual declaration/quantifier map:

- `exists_rationalQuittingReward_close_of_strictUnit_positive_inf` takes an
  actual strict-unit Fin4 real table and positive actual eta. It produces ONE
  `RationalQuittingReward 4`, before ALL terminal/player coordinate bounds,
  strictly inside the unit cube and within eta(original)/4 in every coordinate.
  Its actual eta is at least eta(original)/2 and positive.
- `exists_strictUnit_rationalQuittingReward_of_positive_inf` takes only a raw
  actual Fin4 real table and positive actual eta. It internally chooses the
  common positive scale from canonical 66, then the entire rational table.
  It retains the same scale, all strict cube bounds, coordinatewise closeness
  to the scaled original and the quantitative half-scaled-eta lower bound.
- `exists_strictUnit_rationalQuittingReward_of_no_uniformEquilibriumPayoff`
  takes the raw actual table and literal no-uniform-equilibrium-payoff source
  hypothesis. Canonical no-UE-to-positive-eta supplies the preceding theorem's
  input. Its ONE strict-unit rational table has positive actual eta and the
  canonical converse gives actual no-UE for that SAME table.

The type `RationalQuittingReward 4` is the canonical complete table over all
fifteen nonempty coalitions and all four recipients: all sixty entries,
including the four own singleton entries, are rational. No rational input
table, supplied strategy, response cap, favorable minimizer or certificate is
assumed. Eta and all caps retain ALL full behavioral profiles/replies and
Never; the literal game still pays zero on live/Never histories.

## Discovery and proof reuse

Searches found rational-table encodings and rational strategies/certificates,
but no existing positive-eta/full rational reward approximation declaration.
Do not confuse the numerous rational individual-rationality response weights
or finite-clock realization producers with rationalizing the actual table.

Reused without reproof:

- `RationalQuittingReward` and `rationalQuittingRewardToReal` in
  `UniformEquilibrium/Quitting/Root/RationalReward.lean`, source SHA
  `fbdb58551c589331641329a09857ccac4d501901c83eb1a1e23691c8887a4e02`;
- Mathlib `exists_rat_btwn`, with the interval intersected with (-1,1);
- `abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close` and positive
  scale homogeneity in `TerminalExploitabilityRewardRobustness`, source SHA
  `6ec9f2a4ccc5c6fa94d52ae86e477025cfaec3102603427d51c09a473b939bd0`;
- `exists_strictUnit_scaleQuittingReward` from frozen 66;
- the canonical actual positive-eta/no-UE implications in
  `TerminalDebtPrefixDescent`.

For each coordinate, rational density in
`(max(-1,r−eta/4), min(1,r+eta/4))` gives the strict cube and closeness bounds
simultaneously. Canonical robustness changes eta by at most twice the common
coordinate error, hence at most eta/2. This is the printed source's openness
argument with explicit constants, not a new genericity proof.

## Exact dependency/check order

74 needs only 66's `StrictUnitRewardScale` module plus existing canonical
owners. The complete 66 patch also contains the separate screened-fiber
entrance module; applying it in full retains its original 62 closure, but 74
does not import that screened module and does not itself need polynomial
density, witness algebra, extrema, 67 or 68–73.

Frozen 66:
`/tmp/ue-screened-rational-selection-sInZmW/66_POSITIVE_RATIONAL_SCREENED_FIBER_ENTRANCE.patch`
SHA `6e8b02b20bf1f95d45c47230ffc9b9704f09fb34fe4951c17ce554053fee13da`.
Frozen 67 remains unchanged at SHA
`796e94ee41afe255e168ed01e21fa055d8eb93b98015d3e2a030b50dc8b8d623`.

Apply 74 after the actual strict-scale module exists, then root's one-target
named check is
`UniformEquilibrium.Quitting.Terminal.RationalPositiveExploitabilityApproximation`.
`AXIOM_HARNESS.lean` separately prints all three new theorem axiom sets and
delegates two literal quantified consumers (raw no-UE and raw positive eta).
It has NOT been run; permitted axioms remain propext, Quot.sound and
Classical.choice only. No mathematical source gap was encountered.

Static checks: all non-import code lines ≤100, new names absent from current
canonical owners, no prohibited proof constructs, no deprecated conditional
aliases or project options. No compiler/axiom/trust/import/build seal is claimed.
Root alone owns integration inventory, generated audit and full verification.
