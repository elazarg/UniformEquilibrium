# Review of the actual Zeno deleted-survival passport

## Verdict: PASS

The deleted-survival identity, the screened/one-host subsequence split, the
host-compression producer, the complete behavioral-cap coalescence estimate,
and the explicit zero-minimum Fin4 regression are mathematically correct at
the stated scope.  The note is careful not to claim that host compression
preserves near-minimality or that the fully screened arm is consumed.

One minor packaging addition is advisable: for a sequence of one-host outputs,
pass once more to a subsequence to freeze the host's chosen Boolean endpoint,
and hence the terminal coalition, when a downstream structure requires a
single fixed terminal label.

## 1. Multi-root survival identities

At every unresolved date of a quitting game there is one public live history.
For a finite literal premark root word, let

\[
  S_i=\prod_t q_{i,t}(C).
\]

Behavioral product independence across players gives joint reach

\[
  M=\prod_iS_i
\]

because the marked root is a pure pair.  If player (i)'s strategy is deleted,
the probability that all opponents survive is exactly

\[
  H_i=\prod_{k\ne i}S_k.
\]

For (i\ne j), direct multiplication gives

\[
  H_iH_j
   =M\prod_{k\ne i,j}S_k
   \le M.
\]

This remains valid with zero factors and uses no division.  If (H_i>0),
then (S_i=M/H_i).  The definitions correctly include both the arbitrary new
prefix roots and all roots of the originating actual profile strictly before
the shifted mark.

The compact subsequence argument is also valid.  Raw decorations can be
chosen with positive mass converging to the positive-mass carrier points and
then diagonally along a chain with masses tending to zero.  The finite vector
((H_i)_i\) lives in a compact cube.  Pairwise products of its limiting
coordinates vanish, so at most one limit coordinate is positive.

## 2. Host compression is an actual producer

If (H_h\ge\eta>0), forcing only (h) to Continue through the premark word
makes the actual probability of reaching the marked row exactly (H_h).
Keeping the other players' pure marked actions and selecting (h)'s better
Boolean endpoint leaves one of

\[
  C,\quad C\setminus\{h\},\quad C\cup\{h\}.
\]

Since \(|C|=2\), the resulting coalition is nonempty.  Its unconditional mass
is (H_h\), and the selected endpoint makes (h)'s marked coordinate defect
zero exactly.  The entire postmark behavioral tail is unchanged literally.

Across an infinite family, the selected Boolean endpoint takes only two
values.  A finite-label subsequence freezes it and the resulting coalition if
the consumer requires a constant terminal.  This is a routine packaging step,
not an additional mathematical hypothesis.

## 3. Full all-behavior cap coalescence

The target and comparison siblings differ only in player (o)'s marked
endpoint.  Their prescribed-payoff difference and law distance are supported
on the marked event, hence scale with (M_n\).

For (o), own-strategy invariance gives cap equality exactly.  For
(i\ne o), couple the opponents under an arbitrary behavioral deviation by
(i).  The two opponent profiles can be distinguished only if every opponent
of (i) survives through the premark word, an event of probability (H_{i,n}).
Thus every deviation payoff differs by at most (2R H_{i,n}), and

\[
  |\sup_\tau V_T(\tau)-\sup_\tau V_S(\tau)|
  \le\sup_\tau|V_T(\tau)-V_S(\tau)|
  \le2RH_{i,n}.
\]

This quantifies over the complete behavioral strategy class.  Never and
arbitrarily late quitting times are included; no attainment of the supremum is
needed.  Therefore all payoff, cap, and law coordinates coalesce in the fully
screened arm.

## 4. Exact audit of the Fin4 regression

For the displayed reward table, the common pure-singleton-
\(\{0\}\) postmark tail has total debt (2): player (0) gains one by
Continuing, and player (1) gains one by joining.  The premark stopping laws
have finite atoms

\[
  p_n=(1-1/n)/n
\]

at each of (n) dates and survival (1/n).  Hence

\[
  M_n=n^{-4},\qquad H_{i,n}=n^{-3}.
\]

The target-minus-comparison gain of player (1) is exactly (M_n), and its
target marked defect is zero because Quit pays (1) while Continue behind
player (0)'s sure Quit pays (0).

The finite-tie union bound is correct:

\[
  \Pr(\text{some finite tie})
   \le6n p_n^2\le6/n.
\]

Together with the vanishing remote mass and symmetry, this gives the uniform
singleton terminal-law limit.  The prescribed payoff limit is consequently
((-1/4,-1/4,-1/4,-1/4)).

For players (0,2,3), Never pays zero and every event on which that player
quits pays (-1), so their full behavioral caps are exactly zero.  For player
(1), any pure date before the remote mark can obtain positive payoff only by
colliding exactly with player (0), an event of probability at most (p_n).
At the remote mark the favorable event has probability at most (n^{-3}),
and later dates are preempted by player (0).  A behavioral strategy is a
mixture of the complete pure stopping times and Never on the unique live
history, so

\[
  0\le B_1\le\max(p_n,n^{-3})\le1/n.
\]

This proves the complete semantic limit claimed in the note.

At cap zero, players (0,2,3) strictly prefer Continue at every product root.
Once they Continue surely, player (1) receives (-1) by quitting alone and
zero by Continuing.  Thus all-Continue is the unique exact cap--Nash root.
All-Never is nevertheless an actual exact terminal Nash profile, so the global
minimum is exactly zero.  The regression therefore reproduces every field it
claims and deliberately fails the positive-global-minimum field.

## 5. Scope

The note justifiably narrows actual Zeno renewal to:

\[
  \text{host-compressed fixed-resolution endpoint}
  \quad\lor\quad
  \text{fully screened prefix escape}.
\]

It does not prove that the first arm satisfies an existing near-minimum
consumer, and it does not eliminate the second arm under positive minimum.
Those limitations are stated explicitly and should remain in any export.
