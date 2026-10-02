# Independent review of `FIN5_FULL_FACE_SOURCE_PHASE_SEAM_SEPARATION`

**Reviewer:** `CODEX_EULER`  
**Date:** 2026-08-26  
**Verdict:** **PASS; one display typo only.**

I independently expanded the complete reward table, enumerated the pure-time
deviation values in every deleted game, recomputed all five quiet-lift gaps,
and solved the cyclic scalar system.  The exact regression is correct.  In
equation (3.1), replace the tabbed literal `frac12` by `\tfrac12`; no
mathematical repair is needed.

## 1. Reward table and atom data

The displayed clauses define every coordinate of every nonempty coalition.
There is no collision among player `0`'s exceptional rows:

\[
\begin{array}{c|c}
S&r_0(S)\\ \hline
\{0,1\}&1\\
\{0,2\}&1/16\\
\{0,3\},\{0,4\}&-1\\
I\setminus\{3\}&1/16\\
I\setminus\{4\}&1,
\end{array}
\]

and all remaining player-`0` entries are zero.  The other four players have
reward one exactly on their singleton and on containing size-four coalitions.
Thus `M=1` is an exact uniform reward bound.

For

\[
(q_0,q_1,q_2,q_3,q_4)=(2,3,4,2,1),
\]

one has `q_t != t` in every phase.  The root on deleted face `t` therefore
has the nonempty opponent-only atom `{q_t}` with mass `1/2`.  In particular,
the playerwise marked-phase hypothesis from the reviewed cross-phase Green
adapter is present with `rho_t=1/2`.

## 2. Unrestricted Nash of the two-date deleted sources

Fix `t` and delete player `t`.  At date zero only `q_t` mixes; after survival,
all four retained players Quit at date one.  Because the other three players
Quit surely at date one, every unilateral behavioral deviation is evaluated
by its pure quit times `0`, `1`, later, and Never.  Equivalently one can invoke
the exact stopping-law/pure-time extremality interface in
`Quitting/Cycles/BehaviorPureTimeExtremality.lean`.

For a retained standard player `i != 0`:

- if `i=q_t`, times zero and one both pay `1`, while later times and Never
  pay `0`;
- if `i!=q_t`, time zero pays `1/2` (only the singleton branch), time one
  pays `1/2` (only the survival/size-four branch), and later times or Never
  pay `0`.

These are exactly the prescribed values, so their unrestricted caps are
respectively `1` and `1/2`.

Player `0` is retained on faces `1,2,3,4`.  Forcing it to Quit at date zero
gives

\[
 Q_0=\tfrac12r_0(\{0,q_t\})+\tfrac12r_0(\{0\}),
\]

whereas forcing Continue gives

\[
 C_0=\tfrac12r_0(\{q_t\})+\tfrac12r_0(J_t)
     =\tfrac12r_0(J_t).
\]

Direct substitution yields precisely

\[
\begin{array}{c|c|c|c}
t&q_t&r_0(J_t)&(Q_0,C_0)\\ \hline
1&3&0&(-1/2,0)\\
2&4&0&(-1/2,0)\\
3&2&1/16&(1/32,1/32)\\
4&1&1&(1/2,1/2).
\end{array}
\]

Thus prescribed Continue at date zero is optimal in every row.  At date one,
Quit pays `r_0(J_t)` and unilateral Continue leaves a three-player coalition
not containing `0`, hence pays zero.  The four date-one Quit choices are also
optimal.  Any later Quit or Never is absorbed by those other three players
and gives player `0` zero.  Face `0` contains only standard players, already
covered above.  This proves exact Nash against unrestricted behavioral
deviations, not merely endpoint Nash at the first row.

## 3. Omitted-player gaps

For omitted player `0`, both terminal outcomes of the quiet lift exclude it,
so its prescribed payoff is zero.  Immediate Quit gives

\[
 \tfrac12r_0(\{0,2\})+\tfrac12r_0(\{0\})
 =\frac1{32}.                                        \tag{3.1}
\]

For omitted `t` in `{1,2,3,4}`, the quiet value is again zero: both the
singleton `{q_t}` and the four-player tail omit `t`.  Immediate Quit pays
zero if `q_t` also Quits, since the resulting containing pair is neither a
singleton nor a size-four coalition, and pays one if `q_t` Continues, since
the outcome is `{t}`.  Its exact gain is therefore `1/2`.

Every source consequently co-realizes all four claimed fields: an actual
two-date deleted-game Nash suffix, its literal quiet lift, a strictly positive
omitted-player immediate-Quit gap, and a nonempty root atom of mass `1/2`.
The note correctly does not identify the five different suffixes as one
chronology.

## 4. Cyclic maps and phase rows

Player `0` Continues in every displayed root, and every absorbing singleton
`{q_t}` has player-`0` payoff zero.  Hence its Bellman map is exactly

\[
F_t(z)=z/2
\]

at all five phases.  Cutting at `x=v_0(0)` and propagating phases
`4,3,2,1` gives

\[
 v_4=x/2,\qquad v_3=x/4,\qquad v_2=x/8,
 \qquad v_1=x/16,
\]

and the closing map is `Phi(x)=x/32`.

Since player `0` is supported only on Continue, the phase-`t` endpoint row is

\[
 v_{t+1}(0)\ge r_0(\{0,q_t\}).                       \tag{4.1}
\]

With the cyclic successor indices, these become exactly

\[
x\ge1,\quad x/8\ge-1,\quad x/4\ge-1,
\quad x/2\ge1/16,\quad x\ge1.                       \tag{4.2}
\]

The first binding row comes from phase `0`:
`v_1=x/16 >= r_0({0,2})=1/16`.  The second comes from phase `4`:
`v_0=x >= r_0({0,1})=1`.  This verifies that the modified source table did
not accidentally erase Miner's phase constraint.

## 5. Closing seam and exact threshold

On the canonical payoff interval `[-1,1]`, either binding phase row forces
`x=1`.  The upper approximate closing-seam inequality is

\[
x-\Phi(x)-\delta={31\over32}x-\delta\le0.           \tag{5.1}
\]

For every `0<=delta<31/32`, (5.1) is incompatible with `x>=1`.  Each of the
two rows is separately feasible on `[-1,1]`, so the pair is inclusion-minimal.
At `delta=31/32`, `x=1` satisfies the seam and all remaining phase rows; the
threshold is exact.  The opposite seam row is automatically satisfied there.

Thus five actual exact face sources, five positive source-matched outsider
gaps, and five uniform positive atoms still do not produce a common cyclic
Bellman/root-Nash annotation.  The obstruction is genuinely a relation
between separately selected source tails.

## 6. Ambient boundary

At the ambient all-Quit profile the terminal coalition is `I`.  Every payoff
is zero: player `0`'s grand-coalition entry is an unspecified row and hence
zero, while the standard coordinates pay only on singleton or size-four
coalitions.  If player `i` alone Continues, the terminal coalition is
`I\setminus\{i\}`, which excludes `i`; its payoff coordinate is again zero.
Therefore all-Quit is an exact unrestricted terminal Nash profile and the
global minimum terminal debt is `D_*=0`.

This table cannot refute a producer that genuinely uses positive-global-
minimum, terminal-witness, or cardinal-minimal provenance.  It refutes only
the implication from the enumerated local reached-face fields to cyclic
alignment.

## 7. Research value and effect on the original producer verdict

The table is a good exact Research regression: it upgrades Miner's earlier
phase--seam example by co-realizing the missing actual deleted-game source
semantics and strictly positive omitted-player gaps on all five faces.  A
Lean regression can encode the finite table, the five literal two-date
profiles, their unrestricted caps via pure-time extremality, and the scalar
infeasibility threshold `31/32`.

This strengthens the adversarial **source-interface separation**, but it does
not change the original cyclic-seed producer verdict.  The conditional cyclic
Green theorem remains valid and formalization-worthy; the unconditional
producer still needs a cross-source compatibility principle.  The regression
does not eliminate a maintained positive-minimum game class, give a terminal
approximation, decrease a rank, or furnish a common cyclic source.

Accordingly this note should remain internal and should not be exported on
its own.  Its exact formalization value is as a negative regression guarding
against any future adapter that attempts to infer cyclic alignment solely
from the five local fields proved here.
