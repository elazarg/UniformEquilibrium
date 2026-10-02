# Review of Proposition 28.1

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

## Source signs

The `e` coordinate records the old `x` action at `e=0` and its toggle at
`e=1`, so the definition using `i xor e` handles both values of the old action
without changing signs.  The paid leave gives `J_0<=-gamma`; failure of the
base-deleted old action gives `E_0>0`; and its original stability with both
base members present gives `E_1<=0`.  Thus (28.3) has the correct orientation
for both `i=0` and `i=1`.

## Binary Nash classification

With `J_e` the Present-minus-Absent advantage of `c` and `E_h` the
new-minus-old advantage of `x`:

- `J_1<=0` makes `(h,e)=(0,1)` a Nash cell;
- `J_1>0,E_1=0` makes `(1,1)` a Nash cell;
- `J_0<0<J_1` and `E_1<0<E_0` is strict matching pennies with no pure cell.

These cases exhaust `J_1` and the allowed weak value of `E_1`.  In the mixed
case the indifference probabilities are

```text
Pr(h=1)=E_0/(E_0-E_1),
Pr(e=1)=-J_0/(J_1-J_0).
```

Their product numerators are exactly the four `W_he` in (28.5), all are
strictly positive, and their sum is
`H=(E_0-E_1)(J_1-J_0)>0`.  The two boundary cases correctly use `H=1` and a
single unit cell.

## Remaining free player and owner floor

`O_he` always contains `d`, so `Delta_y^he` is an ordinary nonempty-coalition
Quit-minus-Continue difference.  Its expected value is `N_y/H`; the two signs
in (28.9) are exactly the Nash support conditions for deterministic action
`j`.

If sure owner `d` Continues, the other quitters are `T_he`.  A nonempty
`T_he` pays `r_(T_he)(d)`, while an empty set invokes the exact punishment
value `chi_d`.  If `d` Quits, the coalition is `T_he union {d}`.  Therefore
`k_d^he` is exactly the cellwise Continue-minus-Quit owner-floor excess and
`K_d/H` is its mixed value.  The empty cell is neither omitted nor assigned a
fictitious terminal reward.

The selected `{c,x}` equilibrium, the exact `y` sign, and `K_d<=0` together
give a Nash point on the full free set `{c,x,y}` with persistent singleton
base `{d}`.  There is no additional outsider in the four-player instance.
Hence `nonempty_quittingSingletonBaseCertificate_of_inducedNash` applies, and
its checked consumer covers arbitrary behavioral deviations and
accuracy-dependent punishment, not merely the displayed root actions.

Since `H>0` in every arm, negating the two weak conditions in (28.9) gives
exactly (28.10), including equality on the accepted side.

## Scope

The result re-equilibrates the paid former owner and the failed free label; it
does not claim the old actions remain stable.  It consumes only this pure
base-deletion failure and leaves the `N_y` sign, owner premium, empty premium,
and mixed branch explicit.  No repair is required.
