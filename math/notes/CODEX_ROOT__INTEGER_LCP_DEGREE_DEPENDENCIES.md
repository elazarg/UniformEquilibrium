# Integer LCP degree: shared formalization route

Author: CODEX_ROOT. Bounded implementation audit, 2026-09-08.
`INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md` was read
in full. This plan is not a Lean coverage seal.

## Target and reuse

The packet proves that absence of a Fin4 uniform-equilibrium payoff forces
the full singleton-difference matrix to be R0 and to have integer LCP degree
one. Equivalently, an R0 matrix of degree different from one suffices for
uniform-payoff existence, for every signed nonsingleton completion.

This generalizes the inverse-positive packet's sufficient class and allows
proper-support, degenerate, and nonisolated scaled LCP solutions. Prefer its
shared total-degree argument over duplicating the strict-interior
implicit-function proof. Its direct recovery of the entire nonnegative-inverse
class does not need reward approximation. The separate generic matrix
approximation lemma in the earlier packet remains useful stated content.

## Dependency graph

1. Existing same-table no-UE normality plus the full homogeneous-supported
   consumer gives R0 of the full matrix. Preserve full support scope;
   a selected normal-core principal is not the same statement.
2. The literal discounted Bellman displacement and complete assignment
   lift are shared with the inverse-positive packet. Prescribed-endpoint
   analytic curve selection excludes every nonzero equilibrium limit.
   Some unrelated analytic germ does not supply this universal conclusion.
3. Existing R0 boundedness and a normalized-hazard contradiction bound
   every scaled equilibrium hazard. No leading-support positivity is needed.
4. Define the min-complementarity map on the whole real coordinate space.
   Integer degree needs boundary-safe homotopy invariance, excision,
   positive domain/output dilation invariance, normalization, and the
   determinant-sign local formula. Existing mod-two parity is insufficient.
5. Use the expanded strategy cube, with its lower clipping intact, to compare
   the full discounted fixed-point set to the LCP at the actual punishment
   anchor. Uniform boundary convergence transports total degree, not a
   selected sum of regular branches.
6. R0 right-hand-side independence permits a separate finite test anchor.
   The supplied exact support inventory computes total degree minus one
   from three regular roots. Regularity is only a test-method assumption,
   not a source hypothesis in the main theorem.
7. Recover the inverse-nonnegative corollary from its unique full-support
   LCP solution at the all-ones test anchor. R0 comes from no UE, not from
   inverse nonnegativity or uniqueness at that one test anchor.

## Boundaries to keep literal

- The main source retains every small-discount fixed point and the actual
  punishment-normal anchor, including zero coordinates.
- The expanded domain contains all proper-support roots. The open strategy
  cube used in the strict-interior proof is not a valid replacement.
- The three-branch matrix, zero-anchor-coordinate example, and nonisolated
  solution segment must be checked as exact examples, with no claim that
  their test anchors are realized punishment values.
- The negative-determinant four-cycle permutation matrix shows that a
  nonnegative inverse and a unique LCP solution at one right-hand side
  do not imply R0.
- Positive determinant alone is not a UE obstruction or criterion here.

## Scheduling and current boundary

No implementation of the new degree theorem is claimed. An endpoint-curve
and integer-degree library audit should guide the shared route before large
game-specific proofs. The generic reward-closedness branch of the earlier
packet is already integrated and pushed in `d9c5cd9`; it also serves the
membership-stretch source packet even though this shorter corollary does
not require it.

The active implementation lanes remain algebraic calendar witnesses and
executable rational finite-word selection. Astra's proof-mining pass includes
the new degree packet and its overlap with the inverse-positive packet.
