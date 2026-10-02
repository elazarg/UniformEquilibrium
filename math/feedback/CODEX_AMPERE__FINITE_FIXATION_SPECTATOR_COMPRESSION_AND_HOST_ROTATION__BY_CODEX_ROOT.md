# Review of finite-fixation spectator compression

Reviewer: `CODEX_ROOT`

## Claim reviewed

The note fixes one player whose literal stopping clock is supported through a
finite date, re-equilibrates the complementary players in the induced finite
timing game, and concludes that all complementary unrestricted behavioral
debts vanish while the fixed player's cap is attained in a finite
Quit-time/`Never` menu.  It then classifies a strict `Never` repair and claims
that consecutive strict `Never` deletions last at most four steps.

## Verdict

The finite-anchor complementary Nash theorem and the exact `Never` sign
identity are valid.  The claimed four-step bound on host rotation is not.
After removing that claim, the note gives a useful source-attached
normalization, but not a consumer of the finite-fixation obstruction.

## Valid finite-anchor argument

If player `h` Quits by date `T` almost surely whenever play remains live,
then every complementary player's unilateral behavior is payoff-equivalent
to a distribution on

```text
0, 1, ..., T, Never.
```

Indeed, under every such unilateral deviation the fixed clock of `h` still
terminates the game by `T`; a later stopping time is therefore equivalent to
`Never`.  A mixed Nash equilibrium of this finite timing game is behaviorally
realizable by the standard hazard representation.  Its Nash inequalities
then control the full behavioral deviation class, not merely finite or
stationary deviations.  Thus all complementary debts are exactly zero.

The complementary equilibrium uses no finite clock after `T`.  For `h`, all
finite stopping times strictly after `T` consequently have one common value,
represented by `Q_(T+1)`, while `Never` remains a separate endpoint.  Hence
`h`'s unrestricted cap is the maximum of the stated finite menu.  Under a
terminal exploitability witness, its debt is at least the witness gap because
all other debts vanish.  Replacing `h` by a maximizing menu action kills its
own debt exactly.

The identity

```text
V_h(Q_(T+1)) - V_h(Never) = rho * r_h({h})
```

is also exact, where `rho` is the probability that all complementary clocks
are `Never`.  Thus a strict uniquely `Never` late endpoint requires both
`rho > 0` and a negative own singleton reward.  Punishment normality does not
exclude that sign.

## Fatal gap in the finite host-rotation bound

The statement that consecutive strict `Never` updates can occur at most four
times silently treats a deletion as permanent.  It is not permanent under the
proposed operation.

After one host changes to `Never`, the construction chooses a new finite host
and **re-equilibrates the other three players**.  The previously deleted
player belongs to those three.  Its newly selected complementary-equilibrium
strategy may again have a finite clock.  It can therefore become a later host
and again strictly change to `Never`.  The fact that a player currently
prescribed `Never` cannot strictly improve by replacing that same strategy by
`Never` is irrelevant after its strategy has been changed by the intervening
re-equilibration.

Accordingly neither the number of strict `Never` moves nor the number of host
revisits is bounded by the player cardinality.  Host labels can cycle while
the semantic pair and the other three strategies change.  A four-step bound
would require an invariant preserved by complementary re-equilibration—for
example a permanently frozen `Never` set—which the construction does not
have.

## Correct surviving conclusion

The checked input is reduced source-faithfully to

```text
one fixed finite owner clock
  -> three zero spectator debts
  -> one finitely attained owner debt
  -> finite paid repair or signed strict-Never repair.
```

This is stronger in literal clock provenance than an independently selected
singleton-base source.  It does not preserve the other three source
strategies, the marked law, the minimum fibre, or a monotone host state.  It
therefore supplies neither a semantic return nor a well-founded rank.  The
remaining question is whether positive-minimum provenance controls a choice
of complementary equilibrium strongly enough to prevent semantic host
cycling; host cardinality alone does not.

