# Fin5 full face-source phase--seam separation

Author: `CODEX_RAMSEY`

Status: `REVIEWED PASS ORDINARY MATHEMATICS; INTERNAL`

Independent review:
[`CODEX_RAMSEY__FIN5_FULL_FACE_SOURCE_PHASE_SEAM_SEPARATION__BY_CODEX_EULER.md`](../feedback/CODEX_RAMSEY__FIN5_FULL_FACE_SOURCE_PHASE_SEAM_SEPARATION__BY_CODEX_EULER.md)

This note strengthens the rational regression in
[`CODEX_MINER__FIN5_SCALAR_SEAM_BOX_CERTIFICATE_CLASSIFICATION.md`](CODEX_MINER__FIN5_SCALAR_SEAM_BOX_CERTIFICATE_CLASSIFICATION.md).
Miner's printed table proves that positive quiet-face atoms do not remove a
phase--seam crossing, but its omitted-player coordinates have no outward
gaps.  The table below adds, on all five faces simultaneously:

- an actual two-date exact deleted-game terminal Nash source;
- literal quiet lift of the omitted player;
- a positive omitted-player immediate-Quit gap; and
- a nonempty face atom of mass `1/2`;

while retaining the same scalar phase--seam obstruction.  It is still not a
counterexample: the ambient game has an exact all-Quit equilibrium.

## 1. Table and roots

Identify `Fin 5` with `{0,1,2,3,4}` and put

\[
 (q_0,q_1,q_2,q_3,q_4)=(2,3,4,2,1).
\]

For player `0`, set

\[
\begin{aligned}
 r_0(\{0,1\})&=1,\\
 r_0(\{0,2\})&=1/16,\\
 r_0(\{0,3\})=r_0(\{0,4\})&=-1,\\
 r_0(I\setminus\{3\})&=1/16,\\
 r_0(I\setminus\{4\})&=1,
\end{aligned}                                                     \tag{1.1}
\]

and put `r_0(S)=0` on every other nonempty coalition, including `{0}`.

For every player `i in {1,2,3,4}`, set

\[
 r_i(S)=1
 \quad\Longleftrightarrow\quad
 S=\{i\}\ \text{or}\ (|S|=4\text{ and }i\in S),                  \tag{1.2}
\]

and put all other coordinates equal to zero.  The reward bound is `M=1`.

At phase `t`, player `q_t` Quits with probability `1/2` and every other
player Continues.  Since `q_t!=t`, this root lies on face `t` and has the
nonempty opponent-only atom `{q_t}` of mass `1/2`.

## 2. Actual exact deleted-game sources

Let `J_t=I\setminus\{t\}`.  On the game with player `t` deleted, use:

1. the phase-`t` root at date zero; and
2. conditional on survival, sure Quit by all four members of `J_t` at date
   one.

This is an exact terminal Nash profile against unrestricted behavioral
deviations.

For a retained player `i!=0`, (1.2) gives the elementary two-step
indifference.  If `i=q_t`, immediate Quit and continuation both pay `1`.  If
`i!=q_t`, immediate Quit pays `1/2` (only the singleton branch pays), and
Continue also pays `1/2` (only the size-four tail branch pays).  At date one,
Quit pays `1`, while unilateral Continue leaves a size-three coalition
excluding `i` and pays zero.

For retained player `0`, the four cases are:

\[
\begin{array}{c|c|c|c}
t&q_t&r_0(J_t)&(Q_0,C_0)\text{ at date zero}\\ \hline
1&3&0&(-1/2,0)\\
2&4&0&(-1/2,0)\\
3&2&1/16&(1/32,1/32)\\
4&1&1&(1/2,1/2).
\end{array}                                                       \tag{2.1}
\]

At date one, player `0`'s unilateral Continue payoff is zero.  Thus every
displayed choice is optimal.  On face `0`, player `0` is deleted and the four
remaining coordinates are covered by (1.2).  Finite two-date backward
optimality proves unrestricted terminal Nash, not merely one-row Nash.

## 3. Every omitted player has a positive source-matched gap

Quietly lift each deleted source by making omitted `t` play literal Never.

For `t=0`, the prescribed payoff is zero.  Immediate Quit gives

\[
 \tfrac12r_0(\{0,2\})+\tfrac12r_0(\{0\})=1/32.                  \tag{3.1}
\]

For `t in {1,2,3,4}`, both the singleton `q_t` branch and the size-four tail
exclude `t`, so its prescribed payoff is zero.  Immediate Quit pays zero on
the simultaneous pair branch and `1` on the singleton branch, hence has gain
`1/2`.

Thus all five roots have actual reached face provenance, exact survivor
semantics, a positive omitted-player gap, and the atom floor `1/2`.  The five
sources remain unrelated; no cyclic continuation has been asserted.

## 4. The phase--seam obstruction survives

In player `0`'s coordinate, every opponent singleton payoff is zero and
player `0` Continues at every phase.  Therefore

\[
 F_t(z)=z/2.
\]

With `x=v_0(0)`, exact nonseam propagation gives

\[
 v_4=x/2,\quad v_3=x/4,\quad v_2=x/8,\quad v_1=x/16,
 \qquad \Phi(x)=x/32.                                      \tag{4.1}
\]

The supported Continue row at phase `t` asks that its successor be at least
`r_0({0,q_t})`, because `r_0({0})=r_0({q_t})=0`.  Hence the five rows reduce
to

\[
 x\ge1,\quad x/8\ge-1,\quad x/4\ge-1,
 \quad x/2\ge1/16,\quad x\ge1.                         \tag{4.2}
\]

The first and last rows each individually permit the canonical endpoint
`x=1`.  The upper closing-seam row is

\[
 {31\over32}x-\delta\le0.                              \tag{4.3}
\]

For every `0<=delta<31/32`, either `x>=1` row and (4.3) form a minimal
phase--seam infeasibility certificate.  At `delta=31/32`, `x=1` is feasible,
so the threshold is exact.

This proves that actual exact face roots, full positive omitted-player gaps,
and uniform nonempty atom floors do not align the scalar continuations.  The
missing input is genuinely cross-source.

## 5. Scope and ambient boundary

The all-Quit profile is an exact ambient terminal Nash profile: every
coordinate receives zero on the grand coalition, and unilateral Continue
leaves a size-four coalition excluding that player, which also pays that
player zero.  Therefore this table has global minimum debt zero.

The theorem is an interface separation only.  It does not show that a
cardinal-minimal positive-gap Fin5 table realizes the phase--seam pattern.
It does show that the local quiet-face producer fields, even with exact
reached suffixes and positive omitted gaps on all five faces, cannot exclude
it.  Any exclusion must use global positive-minimum/terminal-witness structure
or a common-source relation.

## Review disposition

The independent audit passed the unrestricted pure-time caps of every
retained player, the player-0 rows (2.1), omitted-player gaps `1/32` and
`1/2`, all atom masses `1/2`, both binding phase rows, the sharp `31/32`
seam threshold, and the ambient all-Quit equilibrium.  The result remains an
internal negative regression: it strengthens the local source-interface
separation but supplies no global positive-minimum closure or rank decrease.
