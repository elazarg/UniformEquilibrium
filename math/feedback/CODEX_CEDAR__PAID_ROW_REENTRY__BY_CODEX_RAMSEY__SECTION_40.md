# Review of Section 40 of `CODEX_CEDAR__PAID_ROW_REENTRY`

Reviewer: `CODEX_RAMSEY`

Status: `VALID EXACT SURE-ROOT SELF-CLOSURE WITH SHARP UNIQUE-QUITTER PREMIUM`

## Claim checked

Section 40 considers a floor-admissible tail `U` and an exact endpoint-Nash
product root `q` having at least one sure quitter.  With

```text
X=Succ(U,q),
O_i=product_(j != i)(1-p_j),
Q_i=QuitPayoff_i(q,0),
K_i=ContinuePayoff_i(q,0),
```

it claims that the same root is exact at successor tail `X` automatically
when at least two players Quit surely.  With a unique sure quitter `k`, it is
exact at `X` exactly when

```text
K_k <= (1-O_k)Q_k.
```

When this holds, `(X,q)` is a charge-one floor-admissible self-loop.  The
section also gives a rational two-player floor edge for which the omitted
premium is exactly `1/8`, and repairs that example by changing the outsider
Quit probability from `1/2` to `3/4`.

## Algebra and support audit

The root has joint Continue mass zero.  Root successor dependence on a tail
is exactly joint Continue mass, so

```text
Succ(X,q)=Succ(U,q)=X.
```

For any player who is not the unique sure quitter, one of its opponents Quits
surely.  Hence its opponent Continue mass is zero and both endpoint values are
tail-independent.  Its exact Nash inequality at `U` therefore transports
unchanged to `X`.  With two or more sure quitters this covers every player,
including each sure quitter.

If `k` is the unique sure quitter, its successor coordinate is exactly
`X_k=Q_k`.  Its Quit-minus-Continue endpoint difference at the successor is

```text
Q_k-(K_k+O_k X_k)=(1-O_k)Q_k-K_k.
```

All other coordinates transport automatically, so the displayed scalar
inequality is both necessary and sufficient.  If it fails, the Continue
premium is exactly its negative,

```text
K_k-(1-O_k)Q_k>0,
```

with no hidden tail or provenance term.

The floor conclusion uses precisely
`quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge` from
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorForward.lean`.
The edge can therefore be packaged by
`QuittingPunishmentFloorAdmissibleEdge.ofExactEdge` in
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`.
Because a sure quitter makes absorption charge one and current and tail are
both `X`, the reflexive return path gives the claimed positive admissible
return with zero payoff seam.

## Rational regression

For

```text
r_k({k})=0,  r_k({j})=3/4,  r_k({k,j})=1,
```

and zero rewards for `j`, the punishment floor is `(0,0)`: nonnegative
rewards give the lower bound, while `j=Never` holds `k` to zero and `j` is
identically zero.

At the root where `k` Quits surely and `j` Quits with probability `1/2`,

```text
Q_k=1/2,  K_k=3/8,  O_k=1/2,
X=(1/2,0).
```

The root is exact at the floor tail, while its successor Continue premium is

```text
3/8-(1/2)(1/2)=1/8.
```

At outsider probability `3/4`, the successor is `(3/4,0)` and

```text
Q_k=3/4,
K_k=(3/4)(3/4)=9/16,
O_k=1/4,
K_k+O_k Q_k=3/4,
```

so the repaired root is an exact charge-one self-loop.  Player `j` remains
indifferent throughout.

## Verdict and scope

I found no missing support case, probability factor, floor condition, or
error in the example.  The result closes the sure-root subcase exactly.  It
does not treat a wholly mixed positive-charge root, and a unique sure quitter
with positive premium remains a genuinely nonlocal re-entry problem, exactly
as the note states.
