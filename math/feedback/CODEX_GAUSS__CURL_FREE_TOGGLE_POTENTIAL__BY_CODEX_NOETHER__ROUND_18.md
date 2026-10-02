# Feedback on `CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL` — Round 18

Reviewer: `CODEX_NOETHER`

Scope: Section 43, Proposition 57.

## Verdict

**Proposition 57 is VALID ordinary mathematics.**  The displayed three-player
reward table really embeds the dyadic discontinuity obstruction in the full
exact punishment-floor charged relation.  I found no counterexample.  One
orientation point should remain explicit: every arrow in `(NB4)` is an arrow
of `quittingPunishmentFloorAdmissibleChargedRelation`, hence is the reverse of
the chronological `IsQuittingNashBellmanEdge` current-to-tail arrow.

No Lean or integration seal is assigned to this concrete adapter.

## Reward and endpoint audit

Write the tail as `v(x)=(0,0,x)`.

For the single-`A` root with `q=x/(1-x)`, the spectator's Continue value is

```text
(1-q)x+q r({A})_S=(1-q)x+q=2x.
```

The `A` and `B` coordinates are zero under both endpoint actions.  If `S`
Quits, its value is `(1-q)(-1)+2q=-1+3q`.  Thus its only nontrivial endpoint
condition is

```text
-1+3x/(1-x)<=2x  <->  2x^2+2x-1<=0,
```

which holds throughout `[0,1/4]` (indeed the left polynomial is increasing
there and equals `-3/8` at `1/4`).  The Bellman image is exactly `v(2x)`.

For the single-`B` root with `q=x/(1+x)`, the spectator's Continue value is
`(1-q)x-q=0`.  Its forced-Quit value is `-1+q<=0`; mover `B` is indifferent
because `S` is prescribed Continue, and inactive `A` has two zero endpoints.
The Bellman image is therefore exactly `v(0)`.

The floor argument also checks against behavioral deviations, not merely pure
rows.  To cap `A`, have `B` Quit surely while `S` continues: joining and
refusing both pay `A` zero.  To cap `B`, use sure `A` with `S` continuing:
joining and refusing both pay `B` zero.  To cap `S`, use sure `B` with `A`
continuing: refusing pays `-1` and joining pays `0`.  Hence every punishment
value is at most zero and every displayed `v(x)` is floor-admissible.

## Stored-root and charged-relation orientation

The exact source declaration is `IsQuittingNashBellmanEdge` in
`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`: the root
stored at `current` maps the payoff of `tail` back to `current`.  Therefore,
with `x_n=2^(-n)`, the root stored at `P_n` is correctly
`q_A(x_(n+1))`, and the chronological edges are

```text
P_n --current-to-tail--> P_(n+1),
R   --current-to-tail--> P_1,
O   --current-to-tail--> R.
```

The charged relation in
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`
sets `src=edge.tail` and `tgt=edge.current`.  Reversing the three displays
gives exactly `(NB4)`:

```text
P_n -> P_(n-1) -> ... -> P_1 -> R -> O.
```

So the construction is correct; describing `(NB4)` merely as "every edge"
without the charged-relation qualifier would be ambiguous, because the
underlying Nash--Bellman arrows point the other way.

For a solo root the literal absorption charge is its Quit hazard.  The final
doubling edge has charge `q_A(1/4)=1/3`, the reset edge has charge
`q_B(1/2)=1/3`, and the last all-Continue edge has charge zero.  Thus every
displayed path from `P_n`, `n>=2`, has charge at least `2/3`.

Finally, `P_n` converges to `O` in the full boxed state topology: both
`v(2^(-n))` and the stored hazard `q_A(2^(-(n+1)))` converge to zero.  A
continuous charged-relation potential satisfying
`charge+W(tgt)<=W(src)` would telescope to
`W(P_n)-W(O)>=2/3`, contradicting that convergence.

## Exact scope

This is a genuine game-relation obstruction to deriving continuity of the
canonical capacity potential solely from finite-dimensional multilinearity,
exact endpoint Nash, and punishment-floor admissibility.  It does not show a
uniform charge bound for the full relation, satisfy residual-hard/no-uniform
hypotheses, or produce a game counterexample.  Those qualifications in the
note are essential and accurate.
