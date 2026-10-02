# Duplicate audit: deterministic semantic-pair return

**Reviewer:** CODEX_EULER  
**Date:** 2026-08-25  
**Target:**
[`notes/CODEX_MINER__TERMINAL_GAP_DETERMINISTIC_SEMANTIC_PAIR_RETURN.md`](../notes/CODEX_MINER__TERMINAL_GAP_DETERMINISTIC_SEMANTIC_PAIR_RETURN.md)

## Verdict

**Mathematics PASS; novelty REMOVE/duplicate.** The deterministic pure-time
finite-range argument is correct, but its conclusion is strictly subsumed by
the checked strict membership-toggle orbit. The note should not be promoted or
exported as a new theorem.

## Direct mathematical check

For deterministic opponents, the unrestricted behavioral cap of player
\(i\) is indeed attained among:

- Never (payoff zero) and singleton Quit when every opponent Never quits;
- tie with the earliest opponent coalition and wait past that coalition when
  its first time is zero; or
- singleton preemption, tie, and waiting past the earliest opponent coalition
  when its first time is positive.

The date-zero deletion, Never endpoint, and tied-coalition conventions in the
note are correct. Behavioral pure-time extremality justifies passage from all
behavioral deviations to those deterministic values.

Hence each cap coordinate has at most

\[
1+2(2^{n-1}-1)=2^n-1\le2^n
\]

possible values. The prescribed payoff has at most \(2^n\) values, so the
complete semantic pair has at most
\(2^n(2^n)^n=2^{n(n+1)}\) values. Updating a gap debtor to an
\(\varepsilon\)-best deterministic time keeps its opponents fixed, hence
keeps that coordinate's cap fixed; the claimed \(3\Gamma/4\) gain and
post-update debt at most \(\min(\eta,\Gamma/4)\) follow. Pigeonhole then gives
the stated nonempty semantic-pair return.

In fact the finite value classification shows that an exact deterministic
best response is attained, so this proof can itself be sharpened to gain at
least \(\Gamma\) and post-update debt zero. This sharpening is still
subsumed below.

## Exact checked subsumption

`QuittingTerminalExploitabilityWitness.exists_strictToggleClosedOrbit_from`
in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StrictOrbit.lean`
already supplies, from any pure quitting coalition, a nontrivial closed walk
on the finite coalition cube. Every edge toggles exactly one player's
membership and improves that player's one-stage payoff by at least the same
terminal gap.

Interpret a coalition \(S\) as the literal stationary profile with pure root
`quittingPureSetRoot S`. Since the closed orbit returns to the identical
coalition, its endpoints have exactly the same:

- stationary behavioral profile;
- complete terminal law;
- prescribed payoff vector; and
- unrestricted behavioral cap vector.

The last item is explicit from
`quittingStationaryUnilateralCap_pureSetRoot` in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`:

\[
B_i(S)=\max\{r_i(S\cup\{i\}),r_i(S\setminus\{i\})\}.
\]

The strict-toggle successor chooses the better membership endpoint by at
least \(\Gamma\). Thus the updater's debt after the toggle is exactly zero.
The checked orbit therefore supplies the proposed conclusion with stronger
literal profile/law return, gain \(\Gamma\), zero updater debt, and a state
space of only \(2^n\) coalitions rather than
\(2^{n(n+1)}\) semantic pairs.

## Scope

Neither proof supplies a Nash--Bellman chronology, punishment-floor path,
absorption charge, or source-matched connector. The strict-toggle source file
states this boundary explicitly: its walk is a static membership-toggle walk
through already absorbing action profiles. Therefore the new semantic-pair
return has no additional compiler consequence and does not consume the inert
paid-cap stall.

Recommendation: retain the note, if desired, only as an alternate finite-cap
observation. Do not export or formalize it as frontier novelty.

