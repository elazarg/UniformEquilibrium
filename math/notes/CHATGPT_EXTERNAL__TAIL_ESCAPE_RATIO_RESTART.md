# Tail-escape atom/debt ratio restart: conditional lemma and failed application

Source: external proposal `../FIN4_TAIL_ESCAPE_CONSUMER_PROOF.md`

Independent reviews:

- `feedback/FIN4_TAIL_ESCAPE_CONSUMER_PROOF__BY_ATLAS_FALSIFIER.md`
- `feedback/FIN4_TAIL_ESCAPE_CONSUMER_PROOF__BY_ATLAS_GATEKEEPER.md`

## Status

The proposed Fin4 tail-escape consumer is false from the stated atlas data.
The underlying multiplicative ratio lemma is correct under an additional
co-realization premise that the current `TailEscapeSubsequence` does not
supply.

## Correct conditional invariant

Suppose one actual behavioral suffix `tau` carries both total semantic debt
`D(tau)>0` and a literal suffix event of mass `m(tau)>0`.  If an exact
cap--Nash root with Continue mass `s` is prefixed literally, then

\[
D(q\triangleright\tau)=sD(\tau),
\qquad
m(q\triangleright\tau)=sm(\tau).
\]

Consequently `m/D` is invariant under every finite stack of such roots.
Global positive minimum debt and a uniform upper debt bound then give a fixed
positive lower bound for the retained suffix-event mass.  The weighted
absorption telescope

\[
\sum_{k<K}D_k a_k=D_0-D_K
\]

is exact as well.

## Why it does not apply to the current tail-escape leaf

In `TailEscapeSubsequence` from
`Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`, the fixed stage
atom belongs to the near-minimum `prefixedProfile` at its marked row.  The
high-debt object is `tailPair`, the continuation strictly after that row.
Cutting to the escaped tail removes the atom.  Thus no supplied profile has
both inputs of the ratio invariant.

Even if such co-realization were added, two further implications in the
proposal would remain unsupported:

1. convergence of total debt to `D_*` is not coordinatewise prescribed-payoff
   near-return in the punishment-floor path interface;
2. replacing the marked row by a pure coalition sibling can change suffix
   caps, so the copied past roots need not remain cap--Nash and the sibling
   does not instantiate the current low-tail, concentrated-singleton, or
   monodromy structures.

A natural-valued rank assigned to these unconsumed stall siblings is therefore
only a relabeling, not a well-founded atlas descent.

## Surviving reusable mathematics

- the conditional atom/debt ratio invariant above;
- the exact weighted absorption telescope;
- a scalar spending-versus-stall dichotomy for a genuinely co-realized suffix
  event;
- the static pure-coalition sink/singleton/cycle dispatch at one literal row,
  with exact own-debt subtraction and common-tail preservation.

These facts should be used only with explicit source fields.  The missing
producer remains either a co-realized high-debt suffix atom, or a different
chronological bridge that retains the pre-tail atom while spending the escaped
continuation debt.
