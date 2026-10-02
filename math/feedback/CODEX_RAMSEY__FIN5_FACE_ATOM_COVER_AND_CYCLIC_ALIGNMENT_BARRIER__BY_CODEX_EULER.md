# Independent review of `FIN5_FACE_ATOM_COVER_AND_CYCLIC_ALIGNMENT_BARRIER`

**Reviewer:** `CODEX_EULER`  
**Date:** 2026-08-26  
**Verdict:** **REVISE to state two routine hypotheses explicitly, then PASS.**

The cross-phase Green argument, the set-intersection reduction, and both exact
five-player tables are mathematically correct.  The abstract theorem should
explicitly assume that the finite player type is nonempty and that
`epsilon, delta >= 0`.  The first hypothesis is needed to form a minimum or
maximum of the `rho_i` and to select a joint-survival contraction; the second
is required by the tail-stability interface and by the interpretation of the
two error bounds.  These hypotheses are automatic in the intended `Fin 5`
application, but they belong in the general statement.

The theorem also admits the sharper payoff-attachment constant described
below.  This is a strengthening, not a repair of the displayed bound (2).

## 1. Cross-phase atom-cover theorem

Let `I` be a nonempty finite player type and let `L : Nat` be positive.  For a
periodic word of product roots `x^t`, annotations `v^t`, and actual periodic
terminal payoffs `u^t`, assume `epsilon, delta >= 0`,

\[
 \lVert v^t-F(x^t;v^{t+1})\rVert_\infty\le\delta,
\]

and phasewise `IsεQuittingRootNash` against the displayed next annotation.
For every player `i`, suppose an arbitrary marked phase `tau(i)` has a
nonempty coalition atom `A_i` with

\[
 i\notin A_i,
 \qquad p_{x^{\tau(i)}}(A_i)\ge\rho_i>0.             \tag{1.1}
\]

The phase map need not be injective or surjective, and `i` need not Continue
purely at its marked phase.

Forcing `i` to Continue removes only the factor
`Pr(i Continues)` from the product atom:

\[
 p_x(A_i)
 =\Pr_x(i\text{ Continues})
    \Pr_{x_{-i}}(Q_{-i}=A_i)
 \le \Pr_{x_{-i}}(Q_{-i}=A_i).                     \tag{1.2}
\]

Since `A_i` is nonempty, the last event is contained in opponent absorption.
Thus the deleted-player Continue mass at the marked phase is at most
`1-rho_i`.  This is exactly the contraction needed in
`quittingRootSequenceTerminalDebt_le_actualCoordinateDefect_add`; no
own-player purity hypothesis is hidden in this step.

Let

\[
 \rho_{\max}=\max_i\rho_i.
\]

Choose a player attaining this maximum.  Its full nonempty atom is disjoint
from joint all-Continue, so the product of the `L` joint-survival factors is
at most `1-rho_max`.  The Bellman-residual telescope therefore gives the
sharper uniform attachment bound

\[
 |u_j^t-v_j^t|\le {L\delta\over\rho_{\max}}.         \tag{1.3}
\]

Tail stability transfers every phase root to the actual periodic tail with
coordinate defect at most

\[
 \eta=\varepsilon+{L\delta\over\rho_{\max}}.
\]

Iterating the opponent-Green recursion around one complete rotation gives,
for every player and phase,

\[
 \boxed{
 D_i^t\le {L\over\rho_i}
   \left(\varepsilon+{L\delta\over\rho_{\max}}\right).}       \tag{1.4}
\]

The note uses `rho_min` instead in the payoff attachment.  Since
`rho_min <= rho_max`, its displayed (2) is a valid, weaker consequence.
All debts in (1.4) are unrestricted behavioral deviation debts, not caps over
periodic or stationary deviations: that scope is inherited from
`quittingTerminalDeviationDebt` in the checked one-step Green theorem.

The relevant checked ingredients and orientations are exactly:

- `quittingRootSequenceTerminalDebt_le_actualCoordinateDefect_add` in
  `UniformEquilibrium/Quitting/Root/TerminalDebtGreenAccount.lean`;
- `isεQuittingRootEndpointNash_of_tail_close` in
  `UniformEquilibrium/Quitting/Root/TailStability.lean`; and
- `isεQuittingRootNash_iff_coordinateNashDefect_le` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`.

No named checked declaration packages the arbitrary marked-phase adapter or
the sharpened finite-cycle constant.

## 2. Set-intersection residual

Let the selected cell on face `t` be `A_t`, omit empty cells from the
intersection, and use `C=I` when every cell is empty.

If `C` is empty, then for every player `i` some selected nonempty cell omits
`i`; otherwise `i` would belong to the intersection.  That cell, at its own
selected phase, supplies (1.1) for player `i`.  The same cell may serve several
players, so no matching or distinct-phase argument is needed.

If `i` belongs to nonempty `C`, then `A_i` must be empty: a nonempty cell from
face `i` cannot contain the omitted player `i`, whereas membership in `C`
would force it to do so.  Every selected nonempty cell on every other face
contains `i` by definition of the intersection.  This proves the exact
common-participant residual stated in the note, including the all-empty
convention.

This is an elementary finite cover reduction.  It does not align any selected
tail, root, or payoff threshold, and it supplies no maintained rank descent.

## 3. Empty-cell table

For

\[
 r_i(S)=\begin{cases}|S|,&i\in S,\\0,&i\notin S,
 \end{cases}
\]

fix an omitted player `t`.  The four survivors all Continue at date zero and
all Quit at date one.  A survivor's prescribed payoff is `4`.  Its pure-time
deviation payoffs are:

- date zero: `1`;
- date one: `4`;
- every later date or Never: `0`, because the other three players absorb at
  date one without it.

Hence the cap is `4`, attained by the prescribed date-one Quit.  By the exact
stopping-law expectation/pure-time extremality theorem, no unrestricted
behavioral deviation does better.  Thus the deleted-game profile is exact
terminal Nash.

The quiet omitted player receives `0` and gains `1` by quitting immediately.
The date-zero survivor root is all-Continue, so its empty cell has mass one
and there is no nonempty atom.  This correctly refutes production of a
nonempty atom from the reviewed reached-face fields.  The full game also has
the obvious all-Quit equilibrium, so the note's non-counterexample scope is
correct.

## 4. Mixed five-face table

Now set

\[
 r_i(S)=1
 \quad\Longleftrightarrow\quad
 S=\{i\}\ \text{or}\ (|S|=4\text{ and }i\in S),
\]

and put all other coordinates equal to zero.  On face `t`, let
`a=t+1 mod 5` Quit with probability `1/2` at date zero; conditional on
survival, all four survivors Quit at date one.

The deleted-game unrestricted caps are exact:

- Player `a` obtains `1`.  Quitting at date zero and joining the size-four
  coalition at date one both pay `1`; quitting later or Never pays `0`.
- Any other survivor `j` obtains `1/2`.  Quitting at date zero pays `1` only
  when `a` Continues, while quitting at date one pays `1` only on the same
  survival event.  Later Quit and Never pay `0` because a coalition of three
  other survivors absorbs without `j`.

Again, arbitrary behavioral deviations are mixtures of these pure quit-time
values, so these are unrestricted terminal Nash caps, not merely one-stage
checks.

The omitted player has quiet value zero.  Immediate Quit gains `1` on the
empty root cell and zero on the `{a}` cell, hence total gain `1/2`.  The root
nevertheless has the genuine nonempty singleton atom `{a}` with mass `1/2`.
As `t` runs around `Fin 5`, these five atoms run around all singleton labels
and have empty intersection.  Thus the cross-phase cover hypothesis is fully
realized on one reward table.

## 5. Cyclic values and defect

Periodically repeat the five date-zero roots.  For fixed player `i`, its own
active phase is `i-1`.  The actual periodic Bellman equations are

\[
 u_i^{i-1}=\tfrac12+\tfrac12u_i^i,
 \qquad
 u_i^i=2^{-4}u_i^{i-1}.
\]

Consequently

\[
 u_i^{i-1}=\frac{16}{31},
 \qquad u_i^i=\frac1{31}.                           \tag{5.1}
\]

At the active phase, player `i`'s Quit and Continue endpoints are respectively
`1` and `1/31`.  Because the root assigns probability `1/2` to each action,
its coordinate Nash defect is

\[
 \tfrac12\left(1-\frac1{31}\right)=\frac{15}{31}.  \tag{5.2}
\]

The product of the five all-Continue probabilities is `1/32`, so the affine
five-cycle Bellman system has a unique solution.  There is no alternative
exact cyclic annotation that makes these same roots Nash.  In fact some pure
Continue coordinates at inactive phases also have positive defect; (5.2) is
already sufficient for the claimed separation and is not asserted to be the
only defect.

## 6. Novelty and recommendation

The strongest Research-worthy result is (1.4): a general finite-cycle,
arbitrary-marked-phase atom-cover adapter with unrestricted behavioral debt
and the `rho_max` payoff-attachment constant.  It is a concise composition of
checked Green, tail-stability, and Nash-defect declarations and would be a
reasonable Research formalization target.

The two tables are useful exact regression tests.  They materially narrow the
**producer architecture** by proving that currently reviewed quiet-face data
imply neither nonempty atom production nor cyclic tail alignment, even when a
uniform nonempty atom cover is co-realized.  They do not narrow the maintained
game class, construct a counterexample, produce a cyclic annotation, or
decrease a conjecture-facing rank.  The common-intersection case also remains
unconsumed.

Accordingly, retain this branch internally.  It is not independently
export-worthy under the consumer/significance gate.  A future formalization
should package (1.4) and may include the tables as regressions, but should not
claim an unconditional quiet-face producer or a new exact periodic compiler.

Before marking the note reviewed PASS, make the two theorem-statement repairs
above and fix the display typos `\varnothing,qquad` and `16/31,qquad` to use
`\qquad`.
