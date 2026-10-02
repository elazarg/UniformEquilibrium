# Consume four-player minimum return

## Mathematical data

Let the player set have four elements. For a behavioral profile \(\sigma\),
write \(U_i(\sigma)\) for its prescribed terminal payoff and
\(B_i(\sigma)\) for the supremum over all unilateral behavioral replacements,
\(d_i(\sigma)=B_i(\sigma)-U_i(\sigma)\), and
\(D(\sigma)=\sum_i d_i(\sigma)\). Assume

\[
D_*:=\inf_\sigma D(\sigma)>0.
\]

Suppose one minimizing joint semantic/law point has a finite terminal atom of
mass \(\mu>0\), and one fixed actual realizing chronology has cofinally many
marked rows with:

- fixed player roles and marked mass at least \(\lambda>0\);
- a pure forced pair, one zero marked defect, and one best-endpoint gain at
  least \(g>0\);
- exact subtraction of that gain from the mover's unrestricted debt;
- lossless routing of the marked mass and literal preservation of the complete
  post-row behavioral tail; and
- post-row tail debt converging to \(D_*\).

Assume in addition that this same chronology is equipped with the two
source-preserving exhaustive dispatches described below. They are part of the
input; they are not inferred merely from the preceding reduced list of row
properties.

## Question

Prove that the game has a uniform-equilibrium payoff.

Acceptable proof routes include terminal approximate Nash profiles with one
limiting payoff, a positive admissible-payoff near-return, or a
source-preserving finite-rank descent whose terminal states all have closing
consumers.

An explicit four-player reward table with a fixed positive exploitability gap
against every behavioral profile and realizing all the supplied data is an
acceptable negative answer.

## Supplied conditional reductions

Two source-preserving reductions may be used.

First, normalized-prefix minimization yields either a strict off-minimum
unique-all-Continue point or a minimum-return endpoint with an actual finite
endpoint decoder. The decoder may return endpoint debt ascent, a routed
singleton, a prescribed finite atom, strict response ascent, or a compiled
response rectangle.

Second, the canonical maximal-prefix construction yields one of:

1. a minimum-endpoint support handoff;
2. a coherent strict normalized endpoint; or
3. a strict ray stall.

Only the first arm supplies the renewable support-cardinality descent. On that
arm, the descent terminates at positive total tangent slope, flat support
entry, or an off-minimum paid first disagreement. These reductions and their
unconsumed outputs are not final answers.

## Main obstruction

The payer's debt decreases exactly, but another player's unrestricted cap may
rise. Thus total debt can remain at \(D_*\) while debt moves between players.
A horizontal best-endpoint move also need not remain a Nash--Bellman edge after
outer prefixes are recomputed.

The source chronology and joint law must be retained. An unrelated minimizer
or a fresh law representative is not a replacement.

## Nonanswers

- own-debt subtraction without cross-coordinate cap control;
- solving only the conditional support-handoff arm;
- another unconsumed endpoint decoder output or strict-ray refinement;
- a horizontal endpoint cycle called a chronology; or
- a compact minimum point with an independently selected realizing sequence.
