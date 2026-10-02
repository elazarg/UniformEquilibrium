# Review of terminal-gap deterministic semantic-pair return

Reviewer: `CODEX_RAMSEY`

## Verdict

**Mathematically valid, but subsumed; keep internal and do not export.**

The cap classification and pigeonhole proof in
[`CODEX_MINER__TERMINAL_GAP_DETERMINISTIC_SEMANTIC_PAIR_RETURN.md`](../notes/CODEX_MINER__TERMINAL_GAP_DETERMINISTIC_SEMANTIC_PAIR_RETURN.md)
are correct.  However, the claimed closure follows more strongly from two
already checked declarations:

- `QuittingTerminalExploitabilityWitness.exists_strictToggleClosedOrbit_from`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StrictOrbit.lean`;
- `quittingContinuationBestResponseValue_pureSetRoot_eq` in
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.

Apply the strict-toggle orbit to the stationary pure-set roots.  At an edge
`S -> toggle S i`, the two entries in the displayed pure-set cap formula are
exactly the old and new membership payoffs.  The checked strict gain says the
new entry exceeds the old one by at least `Gamma`; hence the new updater debt
is exactly zero, not merely at most `min(eta,Gamma/4)`.  Recurrence of the
coalition gives recurrence of the whole profile and therefore of its complete
semantic pair.  Finite pigeonhole on the `2^n` coalitions also gives a bound
at least as strong as the note's `2^(n*(n+1))` bound.

## Quick falsification checks

The note's independent cap calculation survives the boundary cases:

- with all opponents Never, the only pure-time values are `0` and the solo
  reward;
- when the first opponent coalition quits at date zero, solo preemption is
  unavailable, so only the tie and post-tie values occur;
- at a positive first date, solo preemption, the full tied-coalition value,
  and the post-tie value all occur.  A behavioral deviation is a mixture over
  pure stopping times, consistently with
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime`.

Thus there is no counterexample in the one-player case, the date-zero case,
or a two-opponent tied example.  The finite-value count and the update
constants are also sound.  These facts do not restore novelty because the
pure-set orbit already supplies exact best responses and exact profile
return.

## Scope

Neither proof supplies a Nash--Bellman edge, a punishment-floor path, or an
absorption charge.  The absence of a Bellman consumer is not the reason for
the negative export recommendation; exact subsumption by the checked
strict-toggle/pure-set-cap route is.
