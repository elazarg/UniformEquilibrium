# Final mathematical review of three-player cycle row inheritance

Reviewer: CODEX_SCHUR_CLOCK.
Reviewed [frozen packet](../notes/CODEX_CAUCHY__THREE_PLAYER_CYCLE_PASSIVE_ROW_PACKET.md).
Approved final packet SHA-256:

```text
63d7596ad29ae962332c4aa3df578bf06e99bed5e6ba4c520fcb3c8cd657c78a
```

The complete mathematical text was reviewed at SHA-256:

```text
e2216f527781d51d32e620ff36ebae5d0f9c330fbf961af4de6c6df0f911f29a
```

The final packet adds two review links and adjusts three source links to
use the `../notes/` prefix. Reversing only those header and link changes
reproduces the fully reviewed hash exactly. The mathematical content is
unchanged, and this affirmative verdict applies to the final hash above.

The complete frozen text passes this independent mathematical and admission
review. There is no unresolved mathematical objection. The result qualifies
as a raw-table special-case existence theorem filling a missing implemented
ambient row-adapter capability. Publication novelty is not an admission
requirement. This verdict is ordinary mathematical review; no Lean build,
axiom audit, or new formalization seal is asserted.

## Exact claim and strategic source

For arbitrary finite player sets, signed quitting rewards and a selected
three-player principal T, the conditions T invertible, T⁻¹ ≥ 0 and
Γ_kS T⁻¹ ≥ 0 for every outsider produce a fixed uniform-equilibrium payoff.
All outsiders use Never. The strict-inverse case produces explicit finite
private clock laws and a target from singleton data; the weak-inverse case
uses literal nearby tables and selection of payoff vectors.

These are independent reward-table conditions. No selected child equilibrium,
continuation, punishment, recurrence, or hidden strategy-class completeness
hypothesis is left unproduced. The supplied-child row-inheritance lemma is
correctly distinguished from the raw theorem: the raw theorem constructs
its child certificate and then fills every ambient field. The result's
complete behavioral deviation coverage concerns the conclusion, not an
assertion that every game admits this strategy form.

## Proof checks and falsification attempts

The strict inverse characterization is correct. Off-diagonal equations in
TB and BT force one positive and one negative nonzero entry per row and
column, yielding the cyclic sign pattern. The displayed cofactor formula
then forces a positive determinant. The rate identities and three vectors
z⁰,z¹,z² satisfy every coordinate of the exact arc equation. Nonnegative
outside row factors preserve the actual singleton Bellman equations and
floors; an existing child opponent phase supplies outside divergence.

I checked the subtle strategic steps against possible complete deviations:

- Subdivision preserves each phase survival exactly and keeps intermediate
  values between its two coarse endpoints. Owner indifference is therefore
  retained at every microdate, not merely at coarse boundaries.
- The queried player's Continue equation is an equality even on dates when
  that player is the prescribed active owner. Thus a pure quitting-date
  response incurs one collision error at its own quit date. No error is
  summed over all preceding dates.
- Opponent divergence makes the opponent-only survival product vanish and
  justifies the claimed Never value, including signed payoffs. A full
  behavioral strategy is an independent first-quit law along the unique
  live history; integrating pure-date bounds therefore covers every such
  strategy without best-response attainment.
- Under finite censoring, differences against any fixed deviator require
  all opponents to survive to the censor date. Their probability is the
  stated ρ_i^K, independently of the deviator's clock. This validates the
  cap comparison, not only an on-path approximation.
- For a late negative singleton, the finite-horizon proof compares against
  Never rather than against the late negative terminal payoff. This is the
  correct signed repair and makes the horizon bound uniform over all
  replacement dates. The target is fixed before accuracy selection.

The weak-inverse perturbation also survives an independent check. If B_ij
and (BK₀B)_ij both vanish, the supports of row i and column j are the same
singleton {k}. Invertibility supplies a positive B_uv with u,v different
from k, giving a strictly positive second-order Neumann coefficient.
Keeping the outside factors w_k fixed and replacing their rows by w_kT_e
preserves every admission condition on a literal nearby reward table.
Payoff changes are at most the table sup-distance, and full regrets change
by at most twice that distance. Compact selection is applied to actual
payoffs in the original table. No limiting strategy or uniform calendar
bound at the weak boundary is needed.

The displayed negative outside row gives a true positive outside gain; the
coarse joining example shows why the floor needs refinement; and the
permutation boundary shows why direct substitution of a unit hazard would
be invalid. These tests support the stated boundaries rather than claiming
nonexistence of equilibrium outside the class.

## Exact algebra and implementation comparison

An independent standard-library rational elimination recomputed all eleven
support candidates of the four-player example. Every determinant, candidate,
and outside slack agrees with the packet. The only admissible inhomogeneous
support is {0,1,2}, with determinant 7, weights (1,1,1), and outside slack 2.
Nonzero principal determinants and a negative entry in every column exclude
all nonzero homogeneous complementary vectors. The unique regular root has
positive index, establishing the stated R₀ degree +1 under the explicitly
defined minimum-map convention. The strict witnesses also justify openness.
Independent exact rate checks at a_i=2,b_i=1 and at
a=(3,5,7), b=(1,2,3) reproduce the survival identity and cancellation
identities; the latter hazards are (3/5,9/14,3/5).

The important increment is the general ambient nonnegative-row composition
and its weak-inverse raw criterion. It extends the implemented special
integral-tournament lift: the example's two negative reciprocal entries on
{0,3} preclude that tournament input. Its negative-entry graph has no
Hamiltonian cycle, so the stated negative-successor four-cycle criterion
does not cover it. Its {0,3} principal also fails the exact projective-Q-bar
test given in the packet. None of these comparisons is inflated into
exclusion from every existing game theorem.

## Named declarations inspected

The bounded static source check includes:

- `RightSingletonCycle`, `rightAlpha`, `rightBeta`, `rightGamma`,
  `rightCoarse`, `right_coarse_active`, `right_coarse_arc`,
  `right_coarse_floor`, and `rightSingletonCycle_isUniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/CyclicCompiler.lean`).
  Their receiver/owner convention agrees with the stated b/a identification.
- `BalancedSingletonCycleCertificate` and
  `BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`):
  these already supply the general finite-ambient semantic consumer, with
  explicit owner ties, floors, arcs, and opponent divergence.
- `FinFourIntegralTournamentBalancedSingleton.certificate` and
  `target_isUniformEquilibriumPayoff_of_singletonRows`
  (`UniformEquilibrium/Quitting/Classification/LCP/FinFourIntegralTournamentBalancedSingleton.lean`):
  their literal tournament hypothesis does not state the general row-factor
  adapter assembled in this packet.
- `StandardLCPSolution`, `IsStandardQMatrix`,
  `isProjectiveQMatrix_iff_standard_or_homogeneous`, and
  `IsProjectiveQBarMatrix`
  (`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`).
- `SignedFourCycleSingletonData`
  (`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`),
  whose negative successor requirement matches the graph comparison.
- `quittingGame_isUniformεEquilibrium_of_terminalNash`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean`)
  and `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).

The packet contains complete direct strategic proofs in addition to naming
these reusable consumers. It credits the existing active cycle and compiler
instead of presenting them as newly implemented capabilities. Its exact
scope, raw-data producer, full behavioral consumer, boundary tests, and
formalization handoff meet the mathematical admission requirements of the
updated export gate. The frozen packet itself was not edited in this review.
