# Consume the adjacent-deadline large operational-effect residual

## Mathematical data

Fix a four-player quitting reward table whose reward coordinates have
absolute value at most \(M>0\). Let \(\gamma,\delta>0\). Consider two adjacent
finite stopping-law profiles, called old and new, which agree before one
boundary deadline and differ only in the action newly exposed at that
deadline. Fix an observer \(i\).

Let \(P\) be the old timing law after inclusion into the successor clock
space, and let \(R^c\) be the corresponding inclusion of the censored new
law. Graft both timing laws to the same literal behavioral tail \(\tau\).
Assume

\[
U_j(\tau)-r_j(\{j\})\ge\frac{\delta}{2}
\qquad(j=0,1,2,3).
\]

Put \(a=\gamma/M\). Assume that the observer has positive old Never mass and

\[
1-P_i(\mathrm{Never})<\frac a8.
\]

Define the selected boundary-effect gauge between \(P\) and \(R^c\) as the
maximum of:

1. the largest absolute discrepancy of any player's Never coefficient; and
2. the absolute discrepancy of observer \(i\)'s newly exposed boundary gain,
   divided by \(4M\).

Assume that this gauge is at least \(a/8\). No lower bound on raw total
variation between the two censored timing laws is assumed.

## Question

Construct from these same timing laws and the same literal tail at least one
of the following.

1. A unilateral behavioral update with a positive gain floor depending only
   on the reward table, \(\gamma\), \(M\), and \(\delta\), together with exact
   equality outside the mover's strategy and exact subtraction of the gain
   from the mover's terminal semantic debt.
2. A source-preserving transition to a positive charged return or a renewable
   finite-rank state, with all chronology and return hypotheses proved from
   the displayed adjacent source.
3. Terminal approximate Nash profiles with one limiting payoff, hence a
   uniform-equilibrium payoff.

A counterexample satisfying the displayed data and refuting every such
source-attached output is an equally complete negative answer.

## Supplied boundary

When the selected operational effect is small, a reverse-participant
alternative gives a literal unilateral update with an explicit positive gain
floor. In the robust four-player form the floor is

\[
\frac{27\delta}{4096}\left(\frac{\gamma}{M}\right)^4,
\]

and under exact selected-coordinate equality it improves to

\[
\frac{7\delta}{256}\left(\frac{\gamma}{M}\right)^3.
\]

These alternatives do not consume the large-effect branch posed here.

There are exact timing-law examples in which raw censored total variation is
large while the two grafted profiles have the same terminal coalition law and
the same complete payoff-and-cap semantics for every common tail. Therefore
raw total variation cannot replace the selected operational-effect gauge.

## Required provenance

The output must retain:

- the old and new timing laws and their common pre-boundary part;
- the identity of the one updated player;
- the same literal post-boundary tail on both sides;
- the exact relation between the two stopping laws after the update; and
- the complete unrestricted behavioral best-response comparison.

## Nonanswers

- returning only a raw total-variation lower bound;
- assuming the desired source-specific paid update as an input;
- returning the large selected-effect hypothesis unchanged;
- a response square with no common-tail source or return attachment;
- a multi-player payoff difference with no unilateral mover;
- an arbitrary paid edge unrelated to \(P\) and \(R^c\);
- debt transport without proving that only the mover's strategy changed; or
- an asserted minimum return, renewal, rank descent, terminal approximation,
  or uniform equilibrium without constructing it.
