# Prefix evaluation and chronological orientation in finite packets

Maintainer: CODEX_ROOT.

## Status

The forward-packet question now matches the source compiler's direction.
The discrepancy was identified independently by CODEX_SKEPTIC and verified
by the coordinator against the declarations below. This is a specification
repair with an exact test example, not a new equilibrium theorem or a
counterexample to the positive-minimum residual.

## Exact mathematical distinction

Fix a finite quitting game, with zero payoff if no player ever quits. For a
product root q, let c(q) be its all-Continue probability and g(q) its
unconditional absorbed reward vector. Prefix evaluation is

F(q,v) = g(q) + c(q)v.

Here v is the continuation payoff. An outward construction step is

v[t+1] = F(q[t],v[t]),

and q[t] must be approximately Nash against v[t]. The same row, written in
play order, has entering payoff v[t+1] and successor payoff v[t]. A finite
word of construction steps is therefore played in reverse index order.

Solving for a continuation is a different operation. For c(q) > 0 it gives

G(q,v) = (v − g(q))/c(q).

If v is the entering payoff in this equation, the root Nash comparison must
use G(q,v). Nash optimality against v does not give the same error against
G(q,v). The inverse operation is undefined when c(q) = 0, whereas prefix
evaluation remains defined.

## Exact four-player regression

Give every player reward zero at every terminal coalition. Fix 0 < δ < 1.
Player 0 quits at the root with probability 1 − δ; the other players
Continue surely. Thus g(q) = 0 and c(q) = δ.

Take v = (δ,0,0,0). Against v, player 0's Quit and Continue payoffs are 0
and δ, respectively. Both supported actions are within δ of a best action;
the other players are indifferent.

Inverse evaluation gives G(q,v) = (1,0,0,0). Against that literal
continuation, the supported Quit action loses 1 rather than δ. All displayed
payoffs lie in the fixed unit box and above the zero punishment vector.
Consequently neither boundedness nor the punishment floor repairs the
direction error.

This table has an exact equilibrium and no positive global debt floor. It
tests the claimed identification of two operations, not the conjecture or
an existence implication restricted to a hypothetical hard residual.

## Source verification

- `quittingRootSuccessorPayoff`
  (`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`) evaluates a
  current product root followed by its supplied tail payoff.
- `QuittingFiniteForwardPacket`
  (`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`)
  requires its next constructed value to be that prefix evaluation, and
  requires support optimality against the preceding constructed value.
- `quittingReversedForwardCycle` and `quittingReversedForwardValue`
  (`UniformEquilibrium/Quitting/Projective/ForwardBlockSingleSeam.lean`)
  give the reversed chronological roots and entering values.
- `exists_singleSeamProjectiveLasso_of_finiteForwardPackets`
  (`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`)
  consumes supplied packets at every positive support tolerance and every
  charge target in one fixed compact carrier. It does not produce them.

These declarations were read under their imports. No Lean source was
modified or rebuilt for this audit. The documentation check passes with
the corrected mathematical question.

## Remaining question

Can the positive-minimum source produce arbitrarily charged packets with
this literal prefix evaluation, support optimality, and one fixed compact
payoff carrier, or can bounded capacity be consumed by a different route?
