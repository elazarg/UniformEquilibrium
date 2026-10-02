# Fin5 face-atom cover and cyclic-alignment barrier

Author: `CODEX_RAMSEY`

Status: `REVIEWED REVISE -> PASS ORDINARY MATHEMATICS; INTERNAL`

Independent review:
[`CODEX_RAMSEY__FIN5_FACE_ATOM_COVER_AND_CYCLIC_ALIGNMENT_BARRIER__BY_CODEX_EULER.md`](../feedback/CODEX_RAMSEY__FIN5_FACE_ATOM_COVER_AND_CYCLIC_ALIGNMENT_BARRIER__BY_CODEX_EULER.md)

This note branches from the review
[`CHATGPT_EXTERNAL__FIN5_FACE_CYCLIC_SEED__BY_CODEX_RAMSEY.md`](../feedback/CHATGPT_EXTERNAL__FIN5_FACE_CYCLIC_SEED__BY_CODEX_RAMSEY.md)
of the supplied cyclic-seed draft.  It records one genuine weakening of the
conditional consumer and two exact producer separations.  It does not produce
a Fin5 counterexample or close the five-to-four reduction.

## 1. Question

Given a finite periodic word of product roots, what coalition data are really
needed for the opponent-Green contraction?  Do the selected codimension-one
quiet-face cells provide that data and also align the five local continuation
thresholds with one cyclic Bellman annotation?

## 2. Cross-phase atom-cover theorem

Let `I` be finite and nonempty, and let a word of length `L>0` consist of
roots `x^t` and annotations `v^t`.  Let `u^t` be the actual terminal payoff
of the periodic profile.  Assume `epsilon,delta>=0` and

\[
 \|v^t-F(x^t;v^{t+1})\|_\infty\le\delta
\]

and that every `x^t` is an `epsilon`-Nash root against `v^(t+1)`.

For every player `i`, suppose there are a phase `tau(i)` and coalition `A_i`
such that

\[
 A_i\ne\varnothing,\qquad i\notin A_i,\qquad
 p_{x^{\tau(i)}}(A_i)\ge\rho_i>0.                 \tag{1}
\]

Put `rhoMax=max_i rho_i`.  Then, for every phase and player,

\[
 D_i^t\le {L\over\rho_i}
 \left(\varepsilon+{L\delta\over\rhoMax}\right).   \tag{2}
\]

Neither `tau(i)=i` nor pure Continue by `i` at that phase is required.

### Proof

The full atom in (1) already contains the factor that `i` Continues.  Forcing
`i` to Continue therefore weakly increases its mass.  Since `A_i` is a
nonempty opponent coalition, the opponent-Continue factor for `i` at phase
`tau(i)` is at most `1-rho_i`.

Choose a player whose `rho_i` is maximal.  Its atom from (1) is nonempty, so
the full all-player survival product around the word is at most `1-rhoMax`.
The Bellman residual telescope
gives

\[
 \|u^t-v^t\|_\infty\le L\delta/\rhoMax.
\]

Tail stability makes every actual coordinate defect at most
`epsilon+L delta/rhoMax`.  The checked one-step opponent-Green inequality,
iterated around the word, has at most `L` defect terms and one factor at most
`1-rho_i`.  Rearrangement gives (2).  All debts use unrestricted behavioral
best responses.  QED.

This is an adapter to `TerminalDebtGreenAccount.lean`, `TailStability.lean`,
and `NashDefect.lean`, not a producer from arbitrary game data.

## 3. Finite set-cover residual of selected face cells

For the five quiet faces, let `A_t` be the cell selected by the quantitative
outsider-gain pigeonhole.  Ignore empty cells and define

\[
 C=\bigcap_{t:A_t\ne\varnothing} A_t,
\]

using `C=I` if every `A_t` is empty.

If `C=empty`, the selected cells themselves satisfy (1): for each player `i`
some selected nonempty cell excludes it.  Thus the atom part of the cyclic
consumer is produced even when some own-face selected cells are empty.

If `C` is nonempty, then for every `i in C`:

1. `A_i=empty`, because a nonempty cell on face `i` must exclude `i`; and
2. every selected nonempty cell on every other face contains `i`.

So the exact residual is a common-participant set whose members have
empty-cell solo/continuation premiums on their own unrelated reached sources.
No checked theorem consumes this pattern: the comparisons, atoms, and local
Nash tails are not co-realized.

## 4. Empty-cell source separation

Let `I=Fin 5` and

\[
 r_i(S)=\begin{cases}|S|,&i\in S,\\0,&i\notin S.\end{cases}
\]

For omitted `t`, at date zero let all four survivors Continue and at date one
let all four Quit.  This is an exact deleted-game terminal Nash profile.  Its
quiet lift gives `t` value zero, while immediate Quit pays `1`.  The selected
first-row cell is empty with mass one, and the root has no nonempty atom.

Thus a nonempty atom cannot be derived from the reviewed reached-face fields.
The table has an all-Quit equilibrium, so the example is only an interface
separation, not a conjecture counterexample.

## 5. Cyclic-alignment separation despite full atom cover

Define instead

\[
 r_i(S)=1
 \quad\Longleftrightarrow\quad
 S=\{i\}\ \text{or}\ (|S|=4\text{ and }i\in S),
\]

with all other coordinates zero.  On face `t`, let `a=t+1 mod 5` Quit at date
zero with probability `1/2`, and on survival let all four survivors Quit at
date one.  This is an exact deleted-game terminal Nash profile.  The omitted
player's positive gain is carried only by the empty cell, but the root also
has the nonempty atom `{a}` of mass `1/2`.  The five singleton atoms have empty
intersection, hence satisfy the cover theorem.

Periodically repeating only the five date-zero roots does not preserve local
Nash.  For player `i`, at its active phase and the following phase the unique
cyclic values obey

\[
 u_i^{i-1}=\tfrac12+\tfrac12u_i^i,
 \qquad
 u_i^i=2^{-4}u_i^{i-1}.
\]

Therefore

\[
 u_i^{i-1}=16/31,\qquad u_i^i=1/31,
\]

and the mixed active root has defect

\[
 \tfrac12(1-1/31)=15/31.
\]

The survival product is `1/32`, so the cyclic Bellman annotation is unique.
Five exact reached local face certificates and a quantitative atom cover do
not produce a cyclic root-Nash annotation.

## 6. Exact remaining producer

The quiet-face route now separates cleanly into two independent seams:

- **atom cover:** eliminate or consume the common intersection `C`; and
- **tail alignment:** relate each reached local continuation threshold to the
  unique continuation generated by the other four selected roots, or consume
  the resulting face/seam/box affine certificate.

The reviewed codimension-one theorem supplies neither relation.  Any positive
producer must add source coupling, not another playerwise selection.

## Declaration audit

- `quittingRootSequenceTerminalDebt_le_actualCoordinateDefect_add`:
  `UniformEquilibrium/Quitting/Root/TerminalDebtGreenAccount.lean`.
- `isεQuittingRootEndpointNash_of_tail_close`:
  `UniformEquilibrium/Quitting/Root/TailStability.lean`.
- `isεQuittingRootNash_iff_coordinateNashDefect_le`:
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`.
- `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate`:
  `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
- `finiteAffineIntervalFeasible_iff`:
  `MathUE/FiniteAffineIntervalFeasibility.lean`.

No named declaration found packages the cross-phase atom cover, produces the
cover from quiet faces, or aligns the five reached continuation scalars.

## Review disposition

The independent audit passed (1)--(2), the set-intersection residual, both
rational separation tables, unrestricted pure-time caps, and the `15/31`
cyclic defect after the explicit nonempty-player/nonnegative-error
qualifications above.  It also supplied the sharper `rhoMax` attachment
constant now used in (2).  The result remains internal because it identifies
a producer-architecture separation rather than a maintained game-class or
rank reduction.
