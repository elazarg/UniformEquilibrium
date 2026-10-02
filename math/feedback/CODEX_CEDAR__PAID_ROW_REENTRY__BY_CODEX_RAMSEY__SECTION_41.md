# Review of Section 41 of `CODEX_CEDAR__PAID_ROW_REENTRY`

Reviewer: `CODEX_RAMSEY`

Status: `VALID EXACT FIXED-ROOT NORMALIZATION CRITERION AND WHOLLY-MIXED NO-GO`

## Claim checked

Section 41 fixes a floor-admissible tail `U` and a positive-absorption product
root `q` that is exact endpoint Nash at `U`.  It defines

```text
C=product_i(1-p_i),
A=Succ(0,q),
Z=A/(1-C),
O_i=product_(j != i)(1-p_j),
Delta_i(v)=QuitPayoff_i(q,0)-ContinuePayoff_i(q,v),
```

and claims an exact coordinatewise criterion for the same root to be exact at
its normalized delivery `Z`.  If the criterion holds, `Z` is floor-admissible
and gives a positive exact self-loop.  For a wholly mixed root the criterion
forces `Z=U`, so fixed-root repetition succeeds only when the original edge
was already a payoff self-loop.

## Affine and support audit

The prescribed root successor has the affine form

```text
Succ(v,q)=A+C*v.
```

Since `C<1`, the chosen `Z` is its unique fixed point.  Forced Quit is
tail-independent, whereas forced Continue for player `i` has tail coefficient
`O_i`.  Therefore

```text
Delta_i(Z)=Delta_i(U)-O_i*(Z_i-U_i).
```

Applying the pure/mixed support alternatives at `Z` gives exactly

```text
p_i=0:        Delta_i(U) <= O_i*(Z_i-U_i),
0<p_i<1:      O_i*(Z_i-U_i)=0,
p_i=1:        Delta_i(U) >= O_i*(Z_i-U_i).
```

These inequalities are necessary and sufficient under the standing
assumption that `q` is already exact at `U`; they do not silently assume a
sign for `Z_i-U_i`.  All three support cases are present.

If the criterion holds, exactness at the two endpoints `U,Z` transports along
the full segment because every endpoint difference is affine in the tail.
The sequence

```text
U_n=Z+C^n*(U-Z)
```

satisfies `U_0=U` and `U_(n+1)=Succ(U_n,q)`.  Repeated application of
`quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge` from
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorForward.lean`
keeps every `U_n` above the punishment floor.  Closure of the floor box and
`U_n -> Z` give the claimed floor admissibility of `Z`.  The self-loop has
charge `1-C>0`.

For a wholly mixed root, each `O_i>0` and every coordinate is governed by the
middle support equality.  Hence `Z_i=U_i` for all `i`, so `Z=U` and

```text
Succ(U,q)=C*U+(1-C)*Z=U.
```

Thus the stated no-go is exact: repetition of one wholly mixed moving root
cannot create a new re-entry.

## Symmetric two-player regression

For each player `i`, with the other player denoted `j`, take

```text
r_i({i})=0,  r_i({j})=3,  r_i({i,j})=3.
```

The punishment floor is `(0,0)`: rewards are nonnegative, and an opponent who
Never Quits holds the player to payoff zero.  At `U=(0,0)` and
`p_1=p_2=1/2`, forced Quit and forced Continue both pay `3/2`; hence the root
is exact and wholly mixed.  Its joint Continue mass is `1/4`, its absorption
charge is `3/4`, and

```text
A=(3/2,3/2),
Z=A/(3/4)=(2,2).
```

At `Z`, forced Continue pays `3/2+(1/2)*2=5/2`, while forced Quit remains
`3/2`.  At the first successor `(3/2,3/2)`, forced Continue already pays
`3/2+(1/2)(3/2)=9/4`.  The numerical regression is therefore exact.

## Verdict and scope

I found no missing support case, normalization factor, floor-induction gap, or
error in the rational example.  The use of the affine delivery identity is
consistent with
`quittingRootSuccessorPayoff_eq_survival_mul_add_absorption_mul_delivery` in
`UniformEquilibrium/Quitting/Cycles/CollisionAwareFiniteReturn.lean`.

The result is a complete fixed-root criterion and rules out universal
wholly-mixed repair by repeating that same root.  It does not rule out changing
the product root along the return path and does not produce a source-matched
paid re-entry; the note states both limitations correctly.
