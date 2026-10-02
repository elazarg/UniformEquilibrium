# Review of Corollaries 6T and 6U

Reviewer: `CODEX_EULER`

Verdict: **BOTH VALID ordinary mathematics with the stated frozen-head
limitations.**

## Corollary 6T

The sequence quantifiers check out.

- `exists_frozenRadialLiteralFiniteProfilePackets` first fixes the radial
  weights, two distinct positive-weight movers `first,second`, and `kappa`,
  and then gives an eventual packet at every sufficiently late rank.
- Applying
  `exists_quantitativeStrongVanishingDebtAtomAlternative_of_mover` to that
  already fixed `first` fixes one observer `o`, one positive charge `q`, and
  an eventual atom alternative for the same rankwise source and full
  replacement.
- Intersecting these two eventual sets, and the eventual smallness condition
  used by Proposition 6S, leaves an eventual set.  Any infinite branch/terminal
  subsequence is unbounded, so deleting its finite initial segment preserves
  infinitely many strictly enumerable ranks inside this intersection.
- The alternative has two branches.  After making one witness choice at each
  rank, infinite pigeonhole fixes a branch; finite pigeonhole on the nonempty
  terminal-coalition type then fixes the displayed terminal.  The rectangle
  pure-time witness cannot be frozen by this argument because `Option Nat` is
  infinite, exactly as the note says.
- Along the strict ranks, the decoder error tends to zero and
  `frontier.scale rank -> 0`; therefore the error
  `decoderError(q,rank)+4M|I|h` tends to zero.  Proposition 6S retains charge
  `q/2` and the same terminal branch at each selected whole frozen packet.

Thus (6T.1)--(6T.2) are correct.  This remains a subsequence of independently
frozen heads; no actual-successor compatibility or conditioned-port restart
is obtained.

## Corollary 6U

Suppose the selected observer `o` were outside
`frontier.positiveDebtSupport`.  For every active mover `j`,
`frontier.tangent_inactive_nonneg` then makes `tangent(j,o)>=0`.  The
circulation weights are nonnegative.  The selected `first` has strictly
positive weight, while quantitative atom selection makes
`tangent(first,o)>0`.  Hence the finite weighted sum in coordinate `o` is
strictly positive, contradicting the coordinatewise circulation balance.
Therefore `o` is in the active reset face.

The proof gives no positivity of `weight(o)`: once `o` is active, the inactive
sign theorem no longer controls all entries in coordinate `o`, so balance can
be achieved with zero observer weight.  The stated nonclaim that 6U does not
identify `o` with `second` is necessary and correct.

