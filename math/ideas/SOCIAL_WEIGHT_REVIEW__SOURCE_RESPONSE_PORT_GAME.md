# Source--response port game

Status: **idea only; no degree-of-freedom reduction proved.**

The surviving Fin4 handoff can be written as an asymmetric arena.  Its exact
state is the tuple of four marginal first-stopping laws on
`N union {Never}` (equivalently the Fin4 order-three labelled
counterfactual-law state), together with the fixed reward table and source
ancestry.

* A tester move replaces one player's stopping law.  A cap-attaining move
  gains exactly that player's debt and kills that debt.
* A controller move prefixes an exact cap--Nash product root.  At a positive
  global minimum with two debtors this is only all Continue; off minimum it
  may spend debt through absorption.

Every finite arena play maps literally to actual behavioral profiles, and
conversely.  A controller return in the punishment-floor charged relation has
the existing UE consumer.  A tester edge is only horizontal and has no such
consumer.

This is not presently a simplification.  Exact online replacement closure in
Fin4 retains the full marginal stopping laws/order-three counterfactual state,
and literal suffixing also needs ancestry or a program-dependent modulus.
The finite-dimensional controller--tester ledger gives the exact offline
value, but does not update the source after a tester response.  Until a
smaller congruent state or an orientation theorem is proved, the arena merely
restates the noncommutation between paid response and exact prefixing.

Relevant established boundaries are
`formalized/COUNTERFACTUAL_MARKOV_ORDER_AND_SUFFIX_COMPACTNESS_NO_GO.md` and
`exports/QUITTING_CONTROLLER_TESTER_VALUE_AND_BARRIER_DUALITY.md`.
