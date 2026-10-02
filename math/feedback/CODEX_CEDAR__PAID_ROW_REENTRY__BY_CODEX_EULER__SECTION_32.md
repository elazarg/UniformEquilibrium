# Focused feedback on Section 32 of `CODEX_CEDAR__PAID_ROW_REENTRY`

Reviewer: `CODEX_EULER`

## Scope and verdict

I independently checked only Section 32 / Proposition 32: the completed
four-player table, the limiting semantic pair, the punishment vector, the
charged exact root at the prescribed diagonal, dominance elimination at the
cap diagonal, preservation of the Section 30 tangent calculations, and the
claimed adapter-level scope.

**Verdict: VALID ordinary mathematics.**  The example exactly separates the
two diagonal tails `U` and `B`.  It refutes cap diagonalization as a universal
charge-preserving adapter, but it does not obstruct the maintained paid-return
producer because the same table already has the charged self-loop at `U`.

## Semantic pair and tangent compatibility

At `lambda=0`, `p=1/2` and `r=0`.  The prescribed profile terminates at
`{m}` with probability `1/2` and at `{o,h}` with probability `1/2`.  Direct
evaluation of the completed table gives

```text
U=(0,3/4,0,0).
```

For `o`, Quit at date zero and waiting beyond date one both pay `1/2`, while
the prescribed date-one Quit pays zero.  For `m`, Never pays `1`, the
prescribed mixture pays `3/4`, and Quit at date zero pays `1/2`.  Players
`h,k` have cap zero: absent or `o`-containing outcomes pay zero, while an
unaccompanied Quit without `o` pays `-1`.  Therefore

```text
B=(1/2,1,0,0),
```

as claimed.

The completion does not alter any payoff cell used in Sections 30--30A.
The observer rule retains all required invariances under adding/removing `k`.
Mover cells for joining `o` at date one are `-3/4`, hence remain strictly
below `1-r`; the added `{o,m}` and `{o}` cells are exactly those used by the
second tangent ray.  Although the completed `h,k` reward coordinates are no
longer identically zero as tables, their prescribed payoffs, caps, debts, and
directions remain zero on both displayed rays.  Thus the Section 30 and 30A
semantic/tangent calculations are preserved.

## Punishment floor

Every player can guarantee zero by Never because every coalition omitting
that player pays it a nonnegative amount.  Conversely:

- `o,h,k` are held to zero by all opponents Never;
- `m` is held to zero when `h` Quits alone immediately: Continuing pays zero
  and joining pays `-1`.

Hence the punishment vector is exactly

```text
P=(0,0,0,0),
```

and both diagonal tails `U` and `B` dominate it.

## The two diagonal tails

At tail `U`, let only `o` Quit surely.  The singleton row is

```text
r({o})=(0,3/4,0,0)=U.
```

Observer `o` is indifferent between Quit and Continue; `m` compares
Continue `3/4` with joining payoff `-3/4`; and `h,k` are indifferent between
Continue and joining, both zero.  The root is exact endpoint Nash, has charge
one, and gives an exact floor-admissible self-loop at `U`.

At tail `B`, the dominance chain is also exact.

1. For `m`, if no opponent Quits, Continue gives `1` and Quit gives `1/2`.
   If `o` Quits, Continue gives one of `3/4,1,0` and joining gives `-3/4`.
   If a nonempty set omitting `o` Quits, Continue gives zero and joining gives
   `-1`.  Thus `m` strictly Continues against every opponent product law.
2. After eliminating `m`'s Quit action, `o` compares Continue `1/2` with
   solo Quit zero when `h,k` Continue, and outsider payoff one with joining
   payoff zero whenever `h` or `k` Quits.  Thus `o` strictly Continues.
3. After eliminating `m,o`, each of `h,k` compares Continue zero with Quit
   `-1`, regardless of the other inactive clock.

Therefore all-Continue is the unique exact product-Nash root at `B`; its
Bellman current is `B` and its charge is zero.

## Scope

The conclusion is exactly an adapter no-go:

```text
literal semantic pair (U,B)
  does not imply that replacing the floor-safe tail U by B preserves charge.
```

No positive-minimum counterexample or failure of the paid-return producer is
obtained.  In this table the charged exact return at `U` is already present,
so a producer that preserves prescribed-payoff provenance can succeed.  The
example only excludes the shortcut that discards `U` and retains the cap
vector `B` as the diagonal Bellman tail.
