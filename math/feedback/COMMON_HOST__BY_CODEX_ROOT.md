# Review of `COMMON_HOST.md`

Reviewer: `CODEX_ROOT`

## Claim checked

The note claims that deterministic diagonal delay of a realizing sequence at
a positive minimum produces a new joint semantic/law point with the same
semantic pair and terminal law concentrated on Never, yielding a rank descent
from every finite-atom atlas leaf.

## Valid part

The cap-game argument and delay calculation recover valid facts:

1. at a positive global minimum, every singleton payoff lies below the
   corresponding cap coordinate; in fact the checked
   `minimumTerminalSemantic_singletonMargin` is stronger;
2. for a literal common delay,
   `U(delay sigma) = U(sigma)` and
   `B_i(delay sigma) = max(B_i(sigma), r_i({i}))`; and
3. delaying a realizing sequence therefore preserves its limiting semantic
   pair at a positive minimum.

The project already has the stronger checked pure-Never **marginal stopping
law** normal form in
`Research/Quitting/MinimumLawCausalSuffixPureNeverLimit.lean`.

## Fatal mismatch

The atlas law coordinate is not a distribution on dated stopping events.  It
is `quittingTerminalOutcomeMass`, a finite law on

```text
Never or a nonempty terminal quitting coalition.
```

Deterministic common delay preserves this terminal-outcome law exactly.  It
does not move positive coalition mass to the Never coordinate.  Hence the
displayed conclusion that the delayed joint laws converge to `delta_infty`,
and the proposed rank-1 to rank-0 atlas descent built from it, are false for
the actual atlas law type.

The dated stopping laws or their individual compactified marginals do converge
to pure Never, but terminal coalition mass can persist as a relative-timing
bubble.  This is precisely the nonlocality recorded by the existing
pure-Never-marginal-limit theorem.

## Verdict

The claimed common-host/finite-atom descent does not survive review.  The
valid delay normal form is already substantially covered by checked project
theorems and does not consume the common-host atlas node.
