# Whole-packet gate for `OPPONENT_TIGHT_TERMINAL_SEMANTIC_REALIZATION`

Reviewer: `CODEX_MINER`  
Date: 2026-08-26  
Repository head inspected: `29a172f34a919f925bd1109a55c75c9a55d4078c`

Packet reviewed:
[`OPPONENT_TIGHT_TERMINAL_SEMANTIC_REALIZATION.md`](../exports/OPPONENT_TIGHT_TERMINAL_SEMANTIC_REALIZATION.md)

Prior reviews checked independently:

- [`POS_DEBT_REAL__BY_CODEX_RAMSEY.md`](POS_DEBT_REAL__BY_CODEX_RAMSEY.md);
- [`CHATGPT_EXTERNAL__OPPONENT_TIGHT_POSITIVE_MINIMUM_REALIZATION__BY_CODEX_EULER.md`](CHATGPT_EXTERNAL__OPPONENT_TIGHT_POSITIVE_MINIMUM_REALIZATION__BY_CODEX_EULER.md).

## Verdict

**REVISE, then ACCEPT without another mathematical review.**  Theorems A--C,
their constants and quantifiers, the unrestricted-deviation upgrade, and all
three current boundary tests pass.  I found no new mathematical overclaim in
the assembled packet.  The packet nevertheless misses three exact packaging
items required by `exports/README.md`: one checked adapter is attributed with
the wrong quantifier, the two live obligations are described but not named,
and the source audit omits the closest prior ordinary-mathematics overlap that
Euler identified.  These are narrow documentary repairs; none changes a
theorem or proof.

## Mathematical and quantifier audit

The statement now correctly fixes a finite player type with `2 <= |I|`, and
all conclusions involving the exceptional player and `kappa` are local to one
selected compactified law-limit subsequence.

For Theorem A, fixed finite cylinders pass to the weak limit.  The discarded
prescribed-payoff contribution is bounded by

\[
 R\Pr(\min_iT_i^n>H)\le R\Pr(M_{-i_0}^n>H).
\]

For the cap, two pure times later than `H` differ only on
`{M_{-i}^n>H}`, giving the stated `2R` oscillation bound.  Comparison with
`H+1`, convergence on the finite early menu, and (OT) give uniform convergence
of the complete finite-plus-Never pure-time menu.  The checked declaration
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` then upgrades this to
the cap over arbitrary behavioral deviations.  No stationarity or bounded
controller restriction enters.

For Theorem B, two distinct proper limit laws give every player a proper
opponent.  In the nonattained case, choosing the unique proper player when it
exists, and any player when none exists, makes every selected opponent
nonproper.  Hence

\[
 q_{-i}=\prod_{j\ne i}\mu_j(\{\infty\})>0,
\]

and fixed-cutoff clopen-tail convergence plus product independence proves the
common late-or-Never lower bound with `kappa = q_{-i}`.  The packet does not
misstate this as convergence of the approximants' Never atoms.

For Theorem C, the unique proper clock makes total absorption tight and is a
proper opponent for every other cap coordinate.  Thus only player `k`'s cap
can jump.  Actual carrier membership and global minimality give
`widehat b_k >= b_k`; nonattainment makes this strict.  Every finite pure-time
value is at most `b_k`, so pure-time extremality puts the excess at Never.
Dominated convergence gives exactly

\[
 \lim_{t\to\infty}v_k(t)
 =v_k(\infty)+q_{-k}r_k(\{k\}),
\]

and therefore

\[
 r_k(\{k\})<0,
 \qquad
 0<\widehat b_k-b_k\le -q_{-k}r_k(\{k\}).
\]

The positivity assumption `D_* > 0` is not used in this final algebraic step,
but retaining it is honest because it is the frontier to which the corollary
is being applied.

## CompactStoppingLaw and topology audit

The packet uses the correct repository type:

```text
CompactStoppingTime = WithTop Nat
CompactStoppingLaw  = ProbabilityMeasure CompactStoppingTime
```

from `MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`.  This is the
one-point compact topology, not the discrete topology on `Option Nat`.
Finite singletons and every fixed cutoff tail `(H,infinity]` are clopen;
`{infinity}` is closed but not open.  Accordingly, the proof passes finite
atoms and fixed tails but never asserts convergence of singleton Never mass.
`CompactStoppingLaw.toPMF` and `CompactStoppingLaw.ofPMF` provide the exact
bridge to the hazard reconstruction.  Finite-player product compactness gives
the simultaneous subsequence used in the packet.

The checked source names used by the proof are current:

- `quittingStoppingLawBehaviorStrategy` and
  `quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
  `StrategicallyPrecompactWatchdogProperBoundary.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `BehaviorPureTimeExtremality.lean`; and
- `exists_terminalProfile_sequence_tendsto_semanticPair` and
  `exists_profile_sequence_tendsto_minimumTerminalSemanticDebt` in the two
  named terminal-semantic root files.

## Boundary tests

All three current tests pass.

1. The first test now says that two laws are supported in **one common finite
   horizon throughout the sequence**.  This is the needed uniform statement;
   merely saying that each approximating law has finite support would have
   been false as a proper-limit criterion.
2. The checked two-player diffuse example has both compactified laws converge
   to Never, so it lies in the zero-proper arm and violates (OT).  Its global
   minimum is zero, exactly as the packet says.
3. In the sharpness table, player `k` receives `-1` at every nonempty terminal
   coalition and player `j` receives zero.  Against `j` quitting at date `n`,
   every pure-time deviation by `k` pays `-1`, while after the limit `j` Never
   makes `k`'s Never payoff zero.  Thus the jump is exactly one with
   `q_{-k}=1` and `s_k=-1`.  The point is attained elsewhere and has minimum
   debt zero, so the packet correctly labels this only a formula-sharpness
   test.

## Required packet repairs

### 1. Correct the actual-sequence adapter quantifier

The current sentence

> For any carrier minimum, the checked theorem
> `exists_profile_sequence_tendsto_minimumTerminalSemanticDebt` supplies the
> actual semantic approximants.

is not the literal statement of that declaration.  It jointly chooses **one**
minimum pair and a realizing sequence; it does not take an arbitrary supplied
minimum pair.  Replace it by:

> For any specified carrier point `z`, hence for any specified carrier
> minimum, the checked theorem
> `exists_terminalProfile_sequence_tendsto_semanticPair reward z hz` supplies
> actual semantic approximants.  Alternatively,
> `exists_profile_sequence_tendsto_minimumTerminalSemanticDebt reward` jointly
> chooses one global minimum and such a sequence.

This restores exact source correspondence without changing the adapter.

### 2. Name the live obligations narrowed by the result

Gate item 4 requires a named live obligation when no downstream consumer is
provided.  In `Conjecture-facing change` and `Adapter and consumer`, link and
name

- `questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`; and
- `questions/FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md`.

State precisely that the theorem narrows their shared **minimum-attainment
seam**: an opponent-tight selected law-limit realizes the minimum, while any
nonattained selected law-limit is forced into the zero-proper or one-proper
negative-singleton residual.  Preserve the current sentence that neither
residual has a checked consumer.  The packet must not suggest that the paid
descent/inert boundary itself has been contracted.

### 3. Record the closest ordinary-mathematics overlap

Add to `Source correspondence` the comparison already established in Euler's
review:

> Propositions 2--3 of
> `notes/CODEX_CEDAR__STOPPING_TIME_COMPACT_GAME.md` already contain the
> late-finite/Never identity and the qualitative negative-singleton boundary.
> They do not prove opponent-tight uniform convergence of unrestricted caps,
> the two-proper realization criterion, or the global-minimum quantitative
> jump bound.

This is needed for a complete novelty audit.  The packet's claimed new content
then remains exactly correct.

For maximal self-containment, the opening statement should also spell out the
standard table type
`r : {S : Finset I // S.Nonempty} -> (I -> Real)`; this is a presentation
repair, not a mathematical objection.

## Gate conclusion

The packet meets the proof, probability/agency, two-review/falsification,
boundary, and Lean-handoff gates.  It contains no convergence-of-Never-mass,
subsequence-uniform exceptional-player, positive-minimum attainment, paid-port
closure, Fin4 closure, or uniform-payoff overclaim.  After the three repairs
above, I recommend **ACCEPT** for the export queue.
