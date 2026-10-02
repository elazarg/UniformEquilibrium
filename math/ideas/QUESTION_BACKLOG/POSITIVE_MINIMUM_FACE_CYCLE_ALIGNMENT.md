# Align positive-minimum quiet faces into executable cycles

## Mathematical data

Let a finite quitting game have strictly positive minimum terminal-semantic
debt \(D_*>0\). For each \(n\), suppose a finite family of exact deleted-game
terminal Nash profiles has been lifted to ambient quiet-face sources. At every
ambient phase retain the literal product root, continuation payoff, local
ambient Nash error, a positive nonempty coalition atom excluding the omitted
player, and that player's positive immediate-Quit gap.

Let \(K_n\) be the number of selected phases, \(\varepsilon_n\) their local
Nash error, \(\delta_n\) their Bellman seam error, and \(\rho_{i,n}>0\) the
relevant atom floors. Put \(\rho_n=\min_i\rho_{i,n}\).

## Question

Use positive global minimality to prove one of:

1. the phase families can be selected and ordered into actual cyclic
   Nash--Bellman words satisfying, for every participating player,

   \[
   \frac{K_n}{\rho_{i,n}}
   \left(\varepsilon_n+
     \frac{K_n\delta_n}{\rho_n}\right)\longrightarrow0;
   \]

2. terminal approximate Nash profiles with one limiting payoff; or
3. a contradiction to \(D_*>0\).

In Output 1, the cyclic estimate must imply terminal debts tending to zero;
after selecting a convergent payoff subsequence it must therefore yield one
fixed uniform-equilibrium payoff.

Every root, tail, omitted-player gap, atom, phase order, and closing seam must
come from the same indexed actual family.

An exact positive-gap table defeating these alternatives is an acceptable
negative answer.

## Finite subproblem

In the four-player specialization, a terminal strict-toggle class reaches a
pair coalition. At an actual induced persistent-base Nash point for that pair,
prove the missing-face sign-and-mass inequality needed by pair-base softening,
or derive a terminal consumer. Mere background sign cancellation is
insufficient.

## Nonanswers

- a scalar recurrence without actual face provenance;
- an unindexed finite family followed by an asymptotic claim;
- another infeasibility certificate with no terminal or rank consumer; or
- a zero-minimum example.
