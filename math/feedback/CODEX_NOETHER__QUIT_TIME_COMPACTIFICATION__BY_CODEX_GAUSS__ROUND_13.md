# Review of Proposition 41: selection-independent deficit extinction

**Reviewer:** `CODEX_GAUSS`  
**Author:** `CODEX_NOETHER`  
**Claim reviewed:** Section 44, Proposition 41 of
`notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`  
**Verdict:** **VALID ordinary mathematics.** I found no counterexample or
quantifier defect. This is not a Lean check of Proposition 41 itself.

## Claim restated

Assume `witness : QuittingTerminalExploitabilityWitness reward`. For
`eta > 0`, let

```text
M = quittingRewardBound reward,
c_eta = eta / (eta + 2*M),
B = quittingPunishmentFloorPrefixChargeBound reward.
```

For any finite path in the full exact punishment-floor-admissible charged
relation, let `J` be the set of nonfinal path indices whose source state has
some coordinate at least `eta` below its own singleton reward. Proposition 41
claims

```text
c_eta * card(J) <= path.chargeSum <= B.
```

It then concludes that every coherent infinite exact admissible path visits
each such deficit set only finitely often, uniformly in the path, and that
every fixed player's one-sided singleton deficit tends to zero.

## Checks

1. **The local charge orientation is correct.** In
   `quittingPunishmentFloorAdmissibleChargedRelation`, an edge has `src = tail`,
   `tgt = current`, and stores
   `IsQuittingNashBellmanEdge reward current tail`. Thus an index counted in
   `J` supplies a gap at the edge's `tail`, exactly the payoff against which
   the edge root is endpoint Nash. There is no current/tail reversal.

2. **The local constant is correct, including boundary cases.** For a
   witnessing player `i`, membership in `D_eta` says

   ```text
   tail_i <= r({i})_i - eta.
   ```

   Applying
   `gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash`
   (`UniformEquilibrium/Quitting/Boundary/Repair/FixedTailUniformAbsorption.lean`)
   with the canonical absolute reward bound gives precisely
   `c_eta <= edge charge`. The declaration handles the zero-Continue case by
   sure absorption. Since `M >= 0` and `eta > 0`, its denominator is positive
   and `c_eta > 0` even when `M = 0`.

3. **Re-entry does not weaken the count.** Every visit time in `J` identifies
   a different outgoing path edge, and every other edge charge is nonnegative.
   Hence summing the local inequalities over an arbitrary subset of indices
   gives `c_eta * card(J) <= path.chargeSum`. No consecutiveness, fixed owner,
   or invariant deficit carrier is used.

4. **The upper bound applies to the full relation, not only an anchored or
   reachable component.** The constructor
   `QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix`
   (`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`)
   decodes a path from any floor-admissible source. Its initial value need only
   dominate the punishment floor. The checked identity
   `pathToFinitePrefix_charge` preserves the whole path charge, and
   `QuittingTerminalExploitabilityWitness.prefixCharge_le`
   (`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityWitness.lean`)
   bounds every such finite prefix by `B`. Thus the right inequality has the
   claimed universal path quantifier.

5. **Infinite visits are excluded uniformly.** Applying the finite estimate
   to every prefix gives
   `c_eta * visits(N) <= B`. Since `c_eta > 0` and `B` is finite, the
   natural-valued visit counts are uniformly bounded. They are monotone in
   `N`, hence stabilize. This proves eventual avoidance even if the path
   leaves and re-enters `D_eta` before that point.

6. **The convergence quantifiers are correct.** Fix a player `i`. Its deficit
   sequence

   ```text
   d_t = max(0, r({i})_i - payoff(s_t)_i)
   ```

   is nonnegative. If `d_t` did not tend to zero, some `eta > 0` would satisfy
   `d_t >= eta` at arbitrarily large indices. Every such state belongs to the
   union `D_eta` (with this fixed player as a witness), contradicting finite
   visitation. Applying this argument separately to each positive `eta` and
   each player proves exactly the stated coordinatewise one-sided convergence;
   it does not assert convergence of states or roots.

## Scope and overlap

`highAbsorptionStageCount_mul_threshold_le_prefixChargeBound` and the infinite
orbit summability theorems in
`UniformEquilibrium/Diagnostics/Quitting/Capacity/InfiniteOrbitConsequences.lean`
already package the common charge budget and show root absorption tends to
zero. Proposition 41 adds a legitimate semantic adapter: a fixed singleton
payoff deficit forces a fixed local absorption threshold, so the charge budget
also bounds **deficit-state visits**. I did not find that state-deficit
conclusion already named in the inspected source.

The result remains a counterexample-side restriction, not a producer of the
finite paths required by Proposition 40. In particular, independently selected
floor-clipped reset states need not lie on one coherent path, so the proposition
does not silently supply source matching.

## Requested disposition

Mark Proposition 41 independently reviewed as ordinary mathematics. Preserve
the existing distinction between this universal orbit restriction and the
still-open producer that must place enough fixed-gap reset tails on compatible
paths.
