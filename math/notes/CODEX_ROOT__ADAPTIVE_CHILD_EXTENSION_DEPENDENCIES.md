# Adaptive unchanged-child extension: formalization dependencies

Author: CODEX_ROOT. Source read in full on 2026-09-07.
Packet: `ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO.md`.
Frozen SHA-256:
`358787dd7cac784c8104244bc2431844d414c7bda28e10851a04d8bd7c00da1a`.
This is an implementation plan, not a checked theorem record.

## Implementation boundary

`UniformEquilibrium/Quitting/Examples/AdaptiveChildCenter.lean` is integrated
and full-build checked and pushed in commit `11809f7`. It contains the literal
center reward table, unchanged survivor-law reconstruction, the actual
one-date profile, exact terminal Nash, and its fixed uniform payoff.
Its uniqueness theorem currently assumes all three active roots are
completely mixed.

`MathUE/Probability/StoppingLawQuantile.lean` supplies the complete-law first
quantile bounds, including date zero and Never mass, and a crossing-product
estimate. Its integration passed silent full build 86273 and complete
repository gate 49706, and was pushed in commit `a815024`. It does not
supply the game's crossing-event inequality.

The independent scalar proof including boundary mixed actions is frozen in
`ephemeral/formalization/AdaptiveChildFiniteGameUniqueness.lean`, SHA-256
`125960cb1102835781f461fce5a506b0e99ae6f7642507613941a4dee81e3f50`.
Its direct check was silent. It remains to be incorporated as a private
scalar lemma and an actual root-Nash uniqueness theorem in the center
module. The current scalar hypothesis labels for Quit and Continue gains
must be interchanged.

The paused anchor calculation is frozen in
`ephemeral/formalization/AdaptiveChildAnchorCrossing.lean`, SHA-256
`f69541c3f085601e61f558f39ba674013d88b48770151186f2092de38424c265`.
The agent checked its prefix through the pointwise crossing implication.
The appended independence factorization is unverified: direct checks
stopped on transient missing imported build artifacts, before checking
the source. Do not give the whole snapshot a Lean seal. Remove the unused
`MixedPotential` import in a separate revision, check the factorization,
then derive crossing mass and anchor Never mass bounds from actual
exploitability and combine them with the quantile theorem.

Conditioning estimates, finite-coordinate concentration, the unchanged-child
deviation gains, the positive common parent/child floor, reward robustness,
and nearby one-date equilibria all remain. No new mathematical gap has
been identified. The implementation team is working on the shared real
quantifier-elimination dependency before resuming these steps.

## Required construction order

1. Define the literal signed Fin4 table and unchanged three-player
   restriction of independent stopping laws through an explicit Fin3
   equivalence. Reconstruct behavioral profiles from those laws: histories
   have different types in the parent and child, so an untyped restriction
   of behavioral functions is not the required interface.
2. Prove the anchor cap, actual first-quantile bounds, and the two
   counterfactual payoff estimates. Include zero error, a date-zero
   quantile, arbitrary Never mass, and unbounded clocks. Conditioning
   changes only the actual independent laws, not a terminal outcome law.
3. Prove uniqueness of the finite active matching game's Nash vector.
   Compactify only its four real coordinates, including the anchor atom.
   This yields the packet's actual-law concentration and conditional
   participation limits. No limiting stopping profile is evaluated.
4. For the three restrictions retaining the anchor, derive the explicit
   limiting deviation gains. For the restriction deleting the anchor,
   prove the exact adjacent-date payoff difference and move only the
   existing date-K atom. Preserve every other atom and Never. Affinity
   then supplies the positive child gain independently of hidden tails.
5. Use the finite choice of deleted player to obtain one positive
   existential lower bound on parent-plus-child exploitability. The
   main theorem constructs that bound; it must not accept it as data.
6. Promote or narrowly extract the reusable reward-robustness estimates
   before importing them into production. Apply the whole-strategy
   estimate separately to parent and child to obtain the open-neighborhood
   obstruction.
7. Independently construct the nearby one-date-then-Never equilibrium by
   the three-coordinate face-sign theorem. Check the anchor's later-date
   and Never responses explicitly, then prove the same profile's uniform
   payoff claim. Repeating the active hazards indefinitely is a different
   profile and does not discharge this clause.

## Reuse and boundaries

The source identifies the one-law payoff-affinity theorem in
`UniformEquilibrium/Quitting/Paths/FiniteStoppingLawMixture.lean` and the
generic face-sign tools. Existing quiet-deletion lifts do not preserve
child semantics after arbitrary nonquiet outsider insertion.

`Research/Quitting/TerminalExploitabilityRewardRobustness.lean` contains
the required whole-strategy reward perturbation bound and positive common
scaling tools. It was statically inspected for this plan, not rebuilt as
part of this packet. Production may not import Research.

The existing single-anchor existence theorem in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingleAnchorArbitraryCompletionEscape.lean`
uses a stationary active profile. It provides a relevant qualitative
existence result, not the packet's one-date laws or explicit later-date
cap identities.

The obstruction concerns every adaptive choice of an unchanged child.
It does not concern extensions that change surviving laws, and does not
rule out a construction using extra positive-global-gap ancestry. The
parent games have equilibria; this is not a counterexample to Fin4 UE.
The finite-calendar payoff realization and paired-cycle producers do not
use the prohibited unchanged-child inference.
