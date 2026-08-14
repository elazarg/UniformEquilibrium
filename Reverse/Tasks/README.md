# Reverse-search tasks

These packets are the current mathematical questions for reverse proof search.
The number is a stable identifier; filenames are deliberately short so that a
task can be referenced from an issue, experiment, or run without repeating its
full title. Individual attempts belong under [`../Runs/`](../Runs/), not in the
task packet.

The packets below were selected from the live question set. They retain the
mathematical setting, known fences, current reductions, and acceptance
criteria. They do not include retired question files, orchestration traces, or
answer archives.

## Current task index

| ID | Task | Current role | Main dependencies |
| --- | --- | --- | --- |
| [Q188](Q188_PAID_ROOT_OR_TAIL_TRANSPORT.md) | Paid root-or-tail transport | Decide whether a reached-row gain can be transported through changed roots and tails without hiding residual error. | Semantic debt and cap--Nash prefix accounts. |
| [Q189](Q189_CANCELLATION_SAFE_AGGREGATION.md) | Cancellation-safe aggregation | Turn eventwise positive Quit advantages into one legal behavioral deviation, or prove the causal obstruction. | Q188's transport accounting; eventwise quitting rows. |
| [Q190](Q190_SINGLETON_TOGGLE_CHRONOLOGY.md) | Singleton toggle chronology | Connect static strict coalition toggles to a reached, state-matched near-minimum chronology. | [`TerminalSemanticOwnStrategyTransport`](../../UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean); [`SurvivalWeightedReachedHistoryAccount`](../../Research/Semantics/SurvivalWeightedReachedHistoryAccount.lean). |
| [Q191](Q191_SINGLETON_TIGHT_MINIMUM_FACE.md) | Singleton-tight minimum face | Test whether the singleton-tight minimum face is invariant under a fixed one-player row. | [`SingletonTightMinimumFaceIteration`](../../Research/Quitting/SingletonTightMinimumFaceIteration.lean). |
| [Q192](Q192_FOUR_BY_FOUR_Q_CLASSIFICATION.md) | Four-by-four Q classification | Classify the full corrected four-player Q core by normalized sign/zero chambers. | Three-player corrected-core boundary and complementarity cones. |
| [Q193](Q193_FOUR_PLAYER_DEBT_INVARIANT.md) | Four-player debt invariant | Find or rule out a positive forward-invariant debt set for Q-admissible four-player tables. | Q192's algebraic filter; semantic prefix dynamics. |
| [Q194](Q194_SEMIALGEBRAIC_BARRIER_COMPLETENESS.md) | Semialgebraic barrier completeness | Determine whether every positive global debt floor has a finite rational semialgebraic certificate. | Q193's barrier perspective; weighted prefix contraction and the debt-safe hull. |

Q194 contains the current reduction, including the exact reduced state system,
the strict-slack wedge, and the remaining [word-level near-spine / Palm--spine
bridge](Q194_SEMIALGEBRAIC_BARRIER_COMPLETENESS.md#6-a-word-level-near-spine-dichotomy).
That bridge is open; the packet is not a claim that the barrier language is
complete.

## Packet conventions

Use `UniformEquilibrium/` and `MathUE/` for trusted production consumers,
`Research/` for compileable but unpromoted Lean, and `Experiments/` for
searches and reproducible computations. A task may cite a research module, but
promotion still requires a reviewed theorem interface and a kernel-checked
proof. A successful search run is evidence for the task, not a theorem.

Each task packet names an exact open obligation or alternative, the verified
consumer chain behind it, semantic fences, regressions, pinned revisions, and
acceptance commands where those are available. When a packet records a
partial answer, it is a current reduction or obstruction to be checked—not a
substitute for the acceptance criterion.
