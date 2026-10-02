# Consume four-player uniform tail escape

## Mathematical data

Let the player set have four elements. For a behavioral profile \(\sigma\),
write \(U_i(\sigma)\) for its prescribed terminal payoff,
\(B_i(\sigma)\) for the supremum over all unilateral behavioral replacements,
\(d_i(\sigma)=B_i(\sigma)-U_i(\sigma)\), and
\(D(\sigma)=\sum_i d_i(\sigma)\).

Assume

\[
D_*:=\inf_\sigma D(\sigma)>0.
\]

Suppose one minimizing joint semantic/law point has a finite terminal atom of
mass \(\mu>0\), and one fixed actual realizing chronology has cofinally many
marked rows with:

- fixed player roles;
- marked mass at least \(\lambda>0\);
- a pure forced pair;
- one zero marked defect;
- one best-endpoint gain at least \(g>0\), with exact subtraction of that gain
  from the mover's unrestricted debt;
- lossless routing of the marked mass and literal preservation of the complete
  post-row behavioral tail; and
- post-row tail debt at least \(D_*+\delta\), for one fixed \(\delta>0\).

All profiles, rows, tails, and payoff comparisons belong to this one source
chronology.

## Question

Prove that the game has a uniform-equilibrium payoff.

Acceptable ways to prove this include constructing terminal approximate Nash
profiles with one limiting payoff, constructing a source-matched positive
admissible-payoff near-return, or deriving a contradiction to \(D_*>0\).

An explicit four-player reward table with a fixed positive exploitability gap
against every behavioral profile and realizing all the supplied data is an
acceptable negative answer.

## Supplied reduction

Every displayed tail is supplied with the following maximal exact-root
dispatch:

1. a same-tail return selection whose prefixed debt is within a fixed fraction
   of the escape floor from \(D_*\); or
2. universal same-tail undercharge, together with an all-Continue or singleton
   blocker alternative.

The task is to consume this dispatch, not to reproduce it.

## Constraints

The paid pair row and the off-minimum continuation need not be successive
exact Nash--Bellman edges. Replacing the inner continuation may invalidate the
outer roots, and semantic proximity does not control unrestricted caps. No
unrelated off-minimum profile, atom, or return path may replace the fixed
source chronology.

## Nonanswers

- another off-minimum tail, paid row, or maximal-root dispatch;
- a positively absorbing root without its fixed-point payoff identity;
- a real-valued debt decrease without a return or well-founded rank;
- a compact limit detached from the literal chronology; or
- control only over stationary, bounded-horizon, or bounded-memory deviations.
