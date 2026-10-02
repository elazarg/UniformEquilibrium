# Review of Section 42 of `CODEX_CEDAR__PAID_ROW_REENTRY`

Reviewer: `CODEX_RAMSEY`

Status: `VALID RIGID OUTSIDER-COMPLETION REGRESSION`

## Claim checked

Section 42 gives a rational nonnegative three-player table with a floor-safe
charge-one exact root having a unique sure quitter `k`.  Conditional on `k`
Quitting surely, the two outsiders have a unique matching-pennies product Nash
profile.  At that completion, `k` has a strict successor collision premium
`3/20`.  Thus retaining the sure quitter and merely reselecting an outsider
Nash completion cannot universally repair the root.

## Floor audit

All rewards are nonnegative, so every punishment value is at least zero.  The
following opponent profiles give the reverse inequalities:

- against `k`, both outsiders Never Quit, so `k` obtains zero whether it
  eventually Quits alone or Never Quits;
- against `a`, player `k` Never Quits and `b` Quits surely at date zero, so
  either action of `a` produces an unspecified zero-payoff coalition;
- against `b`, symmetrically, `k` Never Quits and `a` Quits surely at date
  zero.

Hence the punishment floor is exactly `(0,0,0)`.  The additional value
`r_a({a})=1/2` does not affect these punishment profiles, but gives the stated
strict singleton gap above the floor and excludes all-Never as an equilibrium.

## Exact-root arithmetic

With `p_k=1` and `p_a=p_b=1/2`, the outsider game is matching pennies.  Player
`a`'s Quit/Continue endpoint payoffs are `p_b` and `1-p_b`; player `b`'s are
`1-p_a` and `p_a`.  The only mutual best-response product profile is therefore
`p_a=p_b=1/2`, and both prescribed payoffs are `1/2`.

For `k`, opponents form a nonempty coalition with probability `3/4`.  Thus

```text
Q_k=(3/4)(4/3)=1,
K_k=(3/4)(6/5)=9/10,
O_k=(1/2)(1/2)=1/4.
```

At the floor tail, pure Quit is a strict best response for `k`, so the whole
root is exact and has charge one.  Its successor is

```text
X=(1,1/2,1/2).
```

The unique-sure premium from Section 40 is exactly

```text
K_k-(1-O_k)Q_k=9/10-3/4=3/20.
```

At successor tail `X`, forced Continue pays
`9/10+(1/4)*1=23/20`, while forced Quit remains `1`, giving the same gain.

Because `k` Quits surely, the tail is unreachable in every outsider endpoint
calculation.  Hence the outsiders' induced game remains the same unique
matching-pennies game at the successor.  Any product root retaining `k` as a
sure quitter and making both outsiders best respond must use the same
`(1/2,1/2)` completion, where `k` rejects repetition.

## Verdict and scope

I found no floor error, missing outsider equilibrium, probability factor, or
premium arithmetic error.  The strengthened singleton entry is harmless and
does exactly what the note claims.

The regression rules out only the universal repair that freezes `k` and
reselects a Nash completion on the absorbed outsider face.  It neither rules
out desaturating `k`, using later changing roots, nor claims that the table has
no other exact equilibrium or admissible return.  The note states this scope
correctly.
