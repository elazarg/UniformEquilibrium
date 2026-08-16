# Cap–Nash endpoint transport audit

## Verdict

The source note's proof is semantically sound.
The auxiliary continuation is the coordinatewise unilateral cap, but the
executed continuation remains the one common suffix.  The existing literal
root/profile splice theorem confirms the exact recursion used in the note.

No denominator or infimum gap was found:

- `D_* > 0` makes every displayed division legal;
- `D(σ) >= D_*` follows from the definition of the infimum;
- the prefixed profile is executable, so `D_* <= c D(σ)` is legitimate;
- that inequality forces `c > 0`, hence every player's Continue action has
  positive support and is a best response in the auxiliary Nash equilibrium;
- `a_i >= c` has the correct direction.

The final prose overstates what the estimate closes.  A positive literal debt
coordinate does not by itself supply the stopping-time-compatible occupation
or matched transfer label needed by the current compiler.  The estimate is a
valid provenance bridge, not yet the conjecture-level chronological bridge.

## Sharpness and finite regression

`cap_nash_endpoint_transport_search.py` checks the scalar inequalities with
exact rational arithmetic and gives a two-player local saturation witness:

- `r_0({0}) = 1`, `r_0({1}) = 0`, `r_0({0,1}) = -1`, `b_0 = 0`;
- player 0 Continues surely and player 1 Continues with probability `1/2`;
- player 0 is indifferent, the joining loss is `L_0 = 1`, and
  `r_0({0}) - b_0 = L_0(1-c)/c = 1`;
- the literal suffix in which both players Quit has total debt `D = 1`, and
  the prefix has debt `cD = 1/2`.

Taking the formal lower bound `D_* = 1/2` saturates every scalar step.  It is
not a global positive-infimum example: the same two-player quitting game has
a debt-free profile.  Producing an actual game with `D_* > 0` would amount to
producing a counterexample to the target conjecture, so local sharpness is the
honest regression target.

## Stronger consequence

Shifting the auxiliary cap gives a more useful exact inequality.  Let `P` be
a minimum semantic pair, let `D_min` be its total debt, and let a carrier pair
`X` have total debt `D`.  If `x` is exact Nash against `X.cap - h`, then

```text
D * collision(x)
  + sum_i singletonMass_i(x) * (D - h_i)
<= D - D_min.
```

For the canonical choice `h_i = d_i(X)`, the auxiliary target is exactly the
prescribed payoff of `X`:

```text
D * collision(x)
  + sum_i singletonMass_i(x) * (D - d_i(X))
<= D - D_min.
```

This has been formalized in
`../../UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCapNashDebtSupport.lean`.  In particular, if every
coordinate is at least `κ` away from carrying the whole debt, then

```text
κ * absorption(x) <= D - D_min.
```

Hence exact Nash roots over near-minimizing profiles converge to all Continue
uniformly on every compact subset of the normalized debt simplex away from
its vertices.  If absorption does not vanish, debt must collapse toward one
full-debt coordinate and collision mass must vanish.

## Random-deviation audit reading

For `n` players under the uniform audit law,

```text
score(σ) = D(σ) / n,
auditValue = D_min / n.
```

Thus a Coordinator profile with score at most `auditValue + η` satisfies

```text
D * collision
  + sum_i singletonMass_i * (D - d_i)
<= n η.
```

If all normalized debt shares obey `d_i / D <= 1 - τ` and the positive audit
value is `V`, then `D >= nV` and

```text
absorption <= η / (τ V).
```

The note's unshifted endpoint estimate also becomes

```text
r_i({i}) - b_i(σ) <= L_i * (score(σ) - V) / V,
```

so every cap of a near-optimal Coordinator profile asymptotically dominates
its singleton endpoint.

This is genuine audit-game leverage: persistent absorption forces a
one-debtor tangent.  It is not a player-cardinality reduction.  Zero-debt
outsiders still occur in reward coalitions and retain Nash/blocker constraints,
and the audit's ex-ante symmetry does not make the reward table symmetric.
At most it reduces the positive-debt support to one player along an absorbing
subsequence; it cannot honestly reduce an `n`-player game to four players.
