Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Literal singleton-fiber extrema and screened strict gap

Status: frozen static drafts, not compiled/applied/axiom-checked/integrated here.
Root is the sole shared editor/compiler. No Lean/Lake, shared writes, Git,
cache/worktree, children or math-note edits were used. Density61/62 and all
original chart/algebra drafts remain immutable.

## Source and scope

The complete 1109-line GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR
export and complete 534-line dependency specs were read for this source chain.
Their bytes were reverified during this unit:

- math/exports/GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md
  c3004d986acc316a20b7c29a7cdc9c764235f843e4b006a7fc99e0cbe0e0f5d7
- /tmp/three-source-packets-dependency-audit.xEpZYgxQ/DEPENDENCY_AND_THEOREM_SPECS.txt
  0f4412a92546f7036c1d850e96141275526cf18e9aa000bc48c1c079d8509a59

63 realizes audit D2's singleton-fiber compact maximum (and D1's exact unit
bound split). 64 realizes D3's screened full-debt compact minimum and singleton
invariance. 65 realizes P6: section5's strict theta(b)>Omega_b argument.
The optional global reward-cube maximum from D2 and pure-coalition Gamma extrema
from D3 are NOT implemented or claimed by this narrower requested unit.

## Exact new files and frozen hashes

63_OWN_SINGLETON_FIBER_MAXIMUM.patch
  f1816c277e0db1d6ea696a0d6739479498f2fa52ab203c5bc9fb11fce5abb19c
  Adds two modules:
  UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityContinuity
  UniformEquilibrium.Quitting.OwnSingletonRewardFiberMaximum

64_SCREENED_ROOT_COMPACT_MINIMUM.patch
  6cc75d542579b934155f309d6f13a096769371115034e39a9fe0a22ee6a38009
  Adds UniformEquilibrium.Diagnostics.Quitting.ScreenedRootCompactMinimum

65_SCREENED_SINGLETON_FIBER_STRICT_GAP.patch
  fa436850afb00636522974ceec6671cfc2f30a8288e664bf358f0f7d621521dd
  Adds UniformEquilibrium.Diagnostics.Quitting.ScreenedSingletonFiberStrictGap

AXIOM_HARNESS.lean
  c9b522f2a9f6dd53343db076f1205d2f858cb5f20a5a7f79c893d59575fd5c66
  Prints all fifteen new theorems plus the closed-face-set definition.
  Expected policy: only propext, Quot.sound, Classical.choice; not checked here.

## Canonical reuse and nonduplication

Current abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close is the
entire reward perturbation theorem. The new continuity owner ONLY supplies
canonical nested-Pi distance bounds to that theorem and invokes
LipschitzWith.continuous. No payoff/cap/supremum/behavioral semantics is reproved.
The same actual infimum over ALL profiles is continuous; no actual minimizing
strategy is asserted or assumed.

The direct chart's existing continuous_quittingOwnSingletonReward_singletons
is composed with that continuity owner. isCompact_Icc.exists_isMaxOn produces
the singleton vector. This does not create another coordinate chart or extremum
principle. The exact unit-bound split uses the literal chart's singleton/free
entry simp identities.

The root owner continuous_quittingRootCoordinateNashDefect_simplex supplies
each coordinate's continuity. Continuous.finset_sup'_apply supplies the MAX
over all four recipients; quittingRootTotalNashDefect is intentionally NOT
used, since that canonical quantity is a SUM. Existing complete-debt screening
identifies this MAX with actual unrestricted terminal exploitability on the
six faces. Existing sure-opponent reward invariance identifies the same score
for every own-singleton vector; no new cap or corner proof is given.

The canonical product simplex is already compact via MathUE.Simplex and the
Mathlib compact standard-simplex owner. A finite union of closed equality faces
is closed; IsClosed.isCompact and IsCompact.exists_isMinOn produce the root.
There is no separate polynomial minimum proof or homeomorphism-to-a-square proof.
The face definition literally leaves two Boolean simplices unrestricted, which
is the source's two closed optional intervals.

For the strict gap, quittingTerminalExploitabilityInf_le compares eta against
each actual profile. If the internally selected screened minimum equals the
internally selected eta maximum, it is an ACTUAL positive global minimum.
quittingTerminalDeviationDebt_eq_exploitability_of_attained_positive_minimum
then ties ALL actual complete debts. The previously frozen
not_positive_equal_screened_debts_of_polynomial_ne_zero contradicts those ties.
No copy of the semantic moat/all-player-ties proof is introduced.

## Exact APIs and quantifier order

63:

- lipschitzWith_quittingTerminalExploitabilityInf: arbitrary finite nonempty
  players, actual table map two-Lipschitz in nested finite-Pi sup distance.
- continuous_quittingTerminalExploitabilityInf: same actual full-profile eta.
- abs_quittingOwnSingletonReward_le_one_iff: literal reward table unit bound iff
  BOTH independent singleton and free-coordinate blocks are unit-bounded.
- continuous_quittingTerminalExploitabilityInf_ownSingletonReward: fixed b,
  continuity in the independent s coordinates only.
- exists_maximum_quittingTerminalExploitabilityInf_ownSingletonReward: for
  EVERY literal b, internally produces s in the WHOLE closed [-1,1]^I cube,
  then eta(b,t)<=eta(b,s) for EVERY other allowed t. Arbitrary finite nonempty I;
  no unit bound on b, positive eta or favorable optimizer is needed. The
  source value Omega_b is exactly eta at this produced s.

64:

- exists_sureOpponent_of_isScreenedQuittingRoot: derives the required different
  sure opponent for every observer; not a favorable input certificate.
- quittingTerminalExploitability_oneDateThenNever_eq_max_rootNashDefect_of_screened
- quittingTerminalExploitability_ownSingletonReward_eq_of_screened
- screenedQuittingRootSimplexSet: explicit union over the SIX sorted pairs of
  their literal Quit-probability-one equality faces; optional endpoints are kept.
- mem_screenedQuittingRootSimplexSet_iff: EXACTLY IsScreenedQuittingRoot after
  canonical simplex-to-PMF conversion. Three/four sure players are retained;
  duplicate boundary representations do not remove them.
- isClosed_screenedQuittingRootSimplexSet
- isCompact_screenedQuittingRootSimplexSet
- screenedQuittingRootSimplexSet_nonempty: actual all-Quit root witness.
- continuous_screenedRootNashMaximum: continuous MAX score, not total Nash debt.
- exists_minimum_screenedQuittingRootExploitability: EVERY literal b produces
  ONE actual screened PMF root BEFORE forall real singleton vectors and forall
  other screened PMF roots. It is minimizing for ALL those singleton vectors,
  without bounds/signs/Nash/interiority/supplied-cap hypotheses. Its actual
  full-debt value is source theta(b), independent of s. Every behavioral
  replacement remains included through the existing screening owner.

65:

exists_strict_screenedSingletonFiber_gap takes ONLY bounded literal b,
Pi(b)!=0, and existential positive actual eta at SOME allowed singleton vector.
That last hypothesis expresses Omega_b>0 WITHOUT a supplied maximizer. It returns
ONE closed-cube maximizing s, ONE screened minimizing root and ONE positive gap,
retaining their extremum facts, eta(b,s)>0, exact gap=theta(b)-eta(b,s), THEN

  forall t in CLOSED [-1,1]^4, forall screened root q,
    eta(b,s)+gap <= E_(direct(b,t))(root-then-Never(q)).

The produced minimizing root works even for unbounded t; the final facade
prints the requested source closed fiber. Lower/upper singleton-face maximizers
are allowed. Optional Quit/Continue endpoints and every screened root are
allowed. No source minimum, gap, favorable strategy or optimizer is supplied.
The positive-minimum tie consumer's unit-reward premise is derived from the
actual independent-coordinate bound split, not added as a witness field.
The SAME b, SAME constructed polynomial, SAME selected s/root/gap are retained.

## Dependencies and application/check order

63 needs only the frozen direct-chart patch and current checked reward robustness.
It does NOT depend on the secant patch reviewed separately this turn, on density
61/62 or on any screened polynomial/degree/witness module.

64 needs the old direct chart; actual debt branches/label module;
four-corner baseline plus its explicit repair (to provide SureOpponentRewardFiber);
and ScreenedRootSurePairOrder from SCREENED_ROOT_POLYNOMIAL.patch. It does not
use degree, witness or density declarations. That old polynomial patch's cofactor
prerequisites/repairs must of course be retained when applying its complete patch.

65 needs 63+64, ScreenedRootPolynomial's actual exclusion, and the current
PositiveMaximumDebtMinimum owner. It does not require the nonzero-polynomial
witness or density APIs because its fixed-fiber premise is Pi(b)!=0. A later
source-selection join will PRODUCE that premise via immutable61/62; it is not
implied by existential positive eta.

The old exact ten-patch chain paths/hashes/order remain listed in immutable
/tmp/ue-screened-polynomial-density-Z9NPbs/HANDOFF.md
  e470d528865baf2ebc20cfc19fa61a5d62e157a07f7a63791abad71a54126cbb
No old patch has been edited or replaced here.

Root's minimal new check order, one target at a time:

1. UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityContinuity
2. UniformEquilibrium.Quitting.OwnSingletonRewardFiberMaximum
3. UniformEquilibrium.Diagnostics.Quitting.ScreenedRootCompactMinimum
4. UniformEquilibrium.Diagnostics.Quitting.ScreenedSingletonFiberStrictGap
5. Local AXIOM_HARNESS.lean, then root-owned umbrellas/AxiomAudit regeneration
   and trust/import-graph/full-gate checks as appropriate.

No imports or module inventories are changed by this worker in the shared tree.
Warnings/coercions/tactics remain uncompiled; static line lengths and forbidden
token checks were clean. Relevant current owner hashes:

TerminalExploitabilityRewardRobustness.lean
  6ec9f2a4ccc5c6fa94d52ae86e477025cfaec3102603427d51c09a473b939bd0
Root/NashDefectContinuity.lean
  803794f8505fbce12c470adeb845980b1de0c3ea131679ad35de26f9e0585f23
Root/Simplex.lean
  0a3247ed40355b607ebe01e53f33153419c1cee0a814ce2832fc818d9ab0a3d9
Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean
  35e435f28596f84f97b88cbb281c3dc27f52a74e3dce89028f27aab185111b2c
Boundary/FinitePlayerMax.lean
  5dfaa23c9bf2e563ce1339f1ea4dfcb78ee672c03f57e57e0f194a3f6c76ef07

## Remaining source joins and nonclaims

This closes the requested singleton-fiber/screened extrema and strict fixed-fiber
gap AS STATIC DRAFTS. Complete counterexample-preserving rational selection P8
still must use actual positive scaling and robustness, immutable density61/62,
then THESE extrema/gap afresh at the newly selected b. Its maximizing s need not
be rational. A rational gamma can be chosen smaller than the produced positive
gap by canonical rational density; that final source join is not printed here.
The final table cannot be inferred no-UE from nonvanishing or positive theta alone.

Zero-singleton/Never exclusion, joint-carrier graph, uniform near-minimum collar,
common-calendar tester source, harmonic bound and regressions remain separate.
No collar, actual minimum strategy for eta, low-regret producer or Fin4 UE
resolution is claimed. No mathematical defect was found in this known-proof unit.
