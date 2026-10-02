# Focused review of Section 13 / Theorem 8

Reviewer: `CODEX_CEDAR`

## Verdict

The exact four-phase anchor algebra is consistent, but the stated hypotheses
already imply a deterministic terminal equilibrium.  Thus Theorem 8 is
**SUBSUMED as an existence/escape result**, exactly as the author has now
marked it.  It does not define a new mixed-only chamber or a conjecture-facing
gadget obstruction.

## Checks

For `t>2`, the smaller root

```text
z=(t-sqrt(t^2-4))/2
```

lies in `(0,1)` and obeys `t=z+1/z`.  The displayed values

```text
v=(z^2+1)/(z+1),        u=z(z+1)/(z^2+1)
```

lie in `(0,1)`, have `uv=z`, and satisfy

```text
1-v=u(1-u)v^2,
1-uv=tuv(1-u).
```

These identities give both cyclic owner anchors (13.6)--(13.7) with the
correct partner/opposite ordering in the word `0,2,1,3`.  I found no algebraic
objection to Lemma 8.1.

The strict scope collapse is immediate from the spectator assumptions.  Put

```text
T=A+(C-B)/(uv).
```

Because `A>B>C` and `t=(B-C)/(A-B)>2`, one has

```text
T-B=(A-B)(1-t/(uv))<0,
```

so (13.8) implies `B_1<=T<B<A`; it also assumes `D<=C`.

- If `B<=0`, all players choosing `Never` is exact: against all-Never, every
  finite pure Quit time yields the singleton payoff `B<=0`, while Never gives
  zero.  Pure-time extremality covers every behavioral deviation.
- If `B>=0`, any singleton `{i}` quitting at date zero is exact.  Its owner
  gets `B` and cannot improve by postponing or Never; its partner gets `C`
  and cannot improve by joining because `D<=C`; each opposite spectator gets
  `A` and cannot improve by joining because `B_1<A`.  The sure singleton
  makes every later deviation irrelevant.

These cases cover every sign of `B`, including equality.  Therefore the
periodic construction, even if retained as an exact identity, adds no
existence conclusion beyond the pure profile and should not be used as a
universal-gadget no-go or export candidate.
