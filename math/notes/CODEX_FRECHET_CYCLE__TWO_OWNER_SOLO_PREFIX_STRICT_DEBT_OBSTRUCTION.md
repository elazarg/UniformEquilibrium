# Two solo owners cannot lower debt at one strict-interior finite source

Identity: CODEX_FRECHET_CYCLE.

Current result: a complete exact counterexample to the proposed local
two-owner debt-descent implication. The source is actual, finite, canonical
Fin4, and strictly above every singleton in prescribed payoff and in the
usable cap-margin test. Every nontrivial finite word of solo rows using at
most two owner labels strictly increases its total complete-response debt.
The game itself has a pure equilibrium and minimum debt zero. This is an
internal source-level obstruction, not a counterexample to equilibrium
existence or a candidate for export.

## Exact question and data

There are four players, independent private Continue/Quit actions at each
live date, first-coalition terminal rewards, and zero Never reward. Put
`s=(1,0,0,0)`. At each nonempty S initially set

    r_i(S)=s_i if i belongs to S, and -1 otherwise.

Override exactly

    r({1,2})=(2,1,1,1),
    r({0,1,2})=(5/2,-1,-1,-1).

This specifies the complete table, bounded by M=5/2. Let p be the one-row
profile in which precisely players 1 and 2 quit, followed by all-Never.
Direct pure-response comparison gives

    U(p)=(2,1,1,1),       B(p)=(5/2,1,1,1),
    D(p)=sum_i(B_i-U_i)=1/2,
    B_i-s_i=(3/2,1,1,1).

Every prescribed coordinate strictly exceeds its own singleton, and every
cap margin exceeds D(p). Each singleton owner also has a strict preemptor:
every outsider receives -1 from that singleton, below its own singleton.

Can a finite prefix using solo hazards of only two distinct owners return a
source of debt at most 1/2, perhaps after the first cap reset?

No. For every finite word w whose rows each have at most one positive Quit
probability, and whose positive probabilities use at most two player labels,

    D(w::p)>=1/2.

Equality is possible only if every prefixed Quit probability is zero.
Hazards may be any real numbers in [0,1], may vary with date, and need not
be small. The full old profile p is retained literally as the tail. Caps
quantify over every complete unilateral behavior strategy, including Never.

## Global bounds that include every cap reset

Let b_i be the probability that player i survives all prefixed rows, ignoring
other players. Let `t=product_i b_i`, and let x_i be the probability that
the first prefix absorption is the singleton i. Since each row is solo,

    sum_i x_i=1-t,       x_0<=1-b_0.

The complete reward table gives the prescribed total payoff exactly:

    sum_i U_i(w::p)=5t-2x_0-3sum_(i!=0)x_i
                   =8t-3+x_0.                     (1)

Every pair joining payoff for a joining player is at least that player's
singleton. Thus Quit at the first prefixed row gives at least s_i. Another
legal complete response is to Continue through the prefix and then use the
best response to p. All earlier opponent singleton outcomes pay that player
-1. If `b_-i=product_(j!=i)b_j`, its payoff is
`(B_i(p)+1)b_-i-1`. Consequently

    B_0(w::p)>=max(1,(7/2)b_-0-1),
    B_i(w::p)>=max(0,2b_-i-1)       (i!=0).          (2)

These lower bounds do not assume any particular cap branch stays selected.
They remain valid through arbitrary cap resets, including sure Quit rows.
The empty word satisfies them directly from its displayed source caps.
Combining (1), (2), and `x_0<=1-b_0` bounds total debt below by

    sum_i [the corresponding bound in (2)]-8t+2+b_0. (3)

## Case 1: the two owners include player 0

Write x=b_0 and y=b_k for the other owner; all other b_j equal one. The
lower bound (3) is

    F(x,y)=A(y)+max(0,2x-1)+2max(0,2xy-1)+2+x-8xy,
    A(y)=max(1,7y/2-1).

For fixed y this is piecewise affine in x. It suffices to check x=0, 1,
1/2, and also x=1/(2y) when y>=1/2. Those are all its breakpoints and
endpoints. The calculations are:

- x=0: `F=A+2>=3`.
- x=1/2: `F=A+5/2-4y`. For y<=4/7 this is at least 17/14;
  for y>=4/7 it is `3/2-y/2>=1`.
- x=1: for y<=1/2 it is `5-8y>=1`; for
  `1/2<=y<=4/7` it is `3-4y>=5/7`; for y>=4/7 it is
  `1-y/2>=1/2`, with equality only at y=1.
- x=1/(2y): `F=A-3+3/(2y)`. If `1/2<=y<=4/7`, this is
  at least 5/8. If y>=4/7, its difference from 1/2 is

      (7y^2-9y+3)/(2y)
        =[7(y-9/14)^2+3/28]/(2y)>0.

Therefore `F>=1/2`, with equality only at x=y=1. Values between adjacent
breakpoints are affine combinations of the endpoint values, preserving
strictness whenever x<1 or y<1.

## Case 2: both owners differ from player 0

Write x,y for their survivals and t=xy. Then b_0=1. The two active-owner
cap bounds satisfy

    max(0,2x-1)+max(0,2y-1)
       >=2max(0,2sqrt(t)-1),

by nonnegativity and `x+y>=2sqrt(xy)`. Thus (3) is at least

    G(t)=max(1,7t/2-1)+2max(0,2sqrt(t)-1)
         +max(0,2t-1)-8t+3.

For `0<=t<=1/4`, this is `4-8t>=2`. For `1/4<=t<=1/2`,
it is `2+4sqrt(t)-8t`; concavity puts its minimum at an endpoint, where
the values are 2 and `2sqrt(2)-2>1/2`. For `1/2<=t<=4/7`, it is
`1+4sqrt(t)-6t`; again its endpoint values exceed 1/2. At t=4/7 the
required strict inequality is `16sqrt(7)>41`, whose squares are
1792>1681. Finally for `4/7<=t<=1`,

    G(t)-1/2=(1-sqrt(t))(5sqrt(t)-3)/2>=0.

This is strict unless t=1. Since x,y lie in [0,1], t=1 means x=y=1.
This proves the theorem in both cases, including words using only one owner.

## Interpretation and bounded source audit

The table has the pure all-Quit equilibrium: every participant receives its
own singleton; unilaterally continuing gives -1. Thus its global minimum
debt is zero. The actual source p is deliberately off minimum. Its positive
debt and positive prescribed surplus are not a no-UE witness.

The table is outside WE and PD because p itself has every prescribed
coordinate strictly above its singleton. This note makes no separation
claim from product-low or odd/even reward classes; those comparisons would
be needed for a new sufficient-class theorem, whereas this is only a
negative test of a local two-owner mechanism. Adding a simultaneous
all-Quit row trivially solves the table, so the restriction to solo rows
and two owner labels is mathematically substantive.

The finite first-cap-threshold theorem audited in
[`the threshold packet`](FINITE_CAP_THRESHOLD_BLOCKS_AND_WEAK_EXCLUSION_SELECTION.md)
can still reach a usable cap margin here, but it may increase debt from the
source's 1/2 towards the selected larger margin. The present theorem shows
that introducing a second solo owner, even with arbitrary chronology and
all cap branch changes retained, does not universally repay that cost.

The bounded source dependencies are the exact actual prefix and cap
definitions `quittingTerminalSemanticPair_rootThenContinuation` and
`quittingTerminalSemanticPrefix`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`). The nearby
`criticalPair_secondOrder_accounting`
(`Research/Quitting/TerminalSemanticWeightedDebtAxisInsertion.lean`) assumes
the critical minimum margins; those equalities are false at this source,
so that local minimum calculation cannot be invoked here. All new
inequalities above are ordinary mathematics, not new Lean declarations.

Concrete next question: can an additional hypothesis controlling a
simultaneous two-owner row yield a finite net decrease at such a source?
No positive two-owner renewal theorem or general obstruction to richer
prefix words is proved here.
