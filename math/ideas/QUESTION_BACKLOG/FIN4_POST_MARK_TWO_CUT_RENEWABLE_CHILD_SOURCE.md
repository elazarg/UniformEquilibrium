# Consume a reached two-cut exit or paid splice

## Mathematical data

Fix a four-player quitting game whose minimum total terminal-semantic debt is

\[
D_*>0.
\]

Let \(s_n\) be actual behavioral restart profiles whose joint semantic and
terminal-law data converge to \((z_*,\nu)\), where

\[
D(z_*)=D_*.
\]

Fix a finite quitting coalition \(A\) with

\[
\mu:=\nu(A)>0,
\]

and choose \(0<\chi<\mu\). After passing to one subsequence, choose finite
cutoffs \(e_n\) so that the probability under \(s_n\) of absorption in
coalition \(A\) before \(e_n\) is greater than \(\chi\).

Prefix one prescribed all-Continue row to \(s_n\). Use that artificial row as
the marked row, take entry cut \(1\), and take exit cut \(e_n+1\). The entry
suffix is literally \(s_n\), its reached mass is one, and the intervening
block has total marginal quitting hazard greater than \(\chi\).

Put

\[
K=(1-e^{-\chi})D_*,
\qquad
\delta=\frac{e^{\chi}-1}{2}D_*.
\]

Assume the following exhaustive two-cut output.

1. The literal exit suffix has debt at least \(D_*+\delta\); or
2. one fixed player has entry debt greater than \(K/8\), and an actual
   unilateral replacement of the entry suffix has conditional gain greater
   than \(K/16\) and updated entry-suffix debt at most \(K/16\). The same
   replacement in the padded parent has the corresponding exact
   whole-profile payoff gain and subtracts that gain from the mover's debt.

The all-Continue padding row is strategically silent only for the prescribed
profile. Under a unilateral deviation it adds the singleton option, so its
whole-profile cap is

\[
B_i^{\mathrm{pad}}=\max\{r_i(\{i\}),B_i(s_n)\}.
\]

No equality between the padded parent's complete semantic pair and that of
\(s_n\) is assumed.

## Question

Consume both outputs by proving at least one of the following.

1. Terminal approximate Nash profiles with one limiting payoff.
2. A source-attached positive admissible-payoff near-return.
3. A renewable child source with one fixed well-founded rank which strictly
   decreases under every recursive transition and whose terminal states are
   consumed.
4. Incompatibility of the supplied dispatch with positive global minimum
   debt.

An explicit four-player table with a certified positive exploitability gap
against every behavioral profile and realizing the complete supplied data is
an acceptable negative answer.

## Provenance requirements

- The exit suffix and paid replacement must come from the displayed profiles
  \(s_n\) and cutoffs \(e_n\).
- Any regenerated source must be built from a joint semantic/law cluster of
  the same literal target family.
- The artificial marked row must not be interpreted as an original causal
  atom or as positive outer reach through an earlier sure-quitting row.
- The paid arm's small debt belongs to the updated entry suffix. It must not
  be silently promoted to a whole-target small-debt statement.

## Nonanswers

- reproducing the finite-window hazard or entry-reach bound;
- identifying the all-Continue padded cap with the entry cap without proving
  singleton-option neutrality;
- rebuilding a child from an unrelated realizing sequence;
- counting one killed debt coordinate as support descent when another
  coordinate may enter; or
- another source packet with no terminal consumer, renewable rank, or
  backward compiler.
