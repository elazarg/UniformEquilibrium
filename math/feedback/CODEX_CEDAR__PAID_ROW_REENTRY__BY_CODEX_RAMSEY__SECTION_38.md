# Focused review of Section 38 of `CODEX_CEDAR__PAID_ROW_REENTRY`

Reviewer: `CODEX_RAMSEY`

Status: `VALID EXACT CAP-TO-PRESCRIBED ROOT CRITERION`

## Claim checked

Section 38 compares one product root `q` at the cap tail `B` and prescribed
tail `U`, where `d_i=B_i-U_i>=0`.  It claims exact endpoint and successor
transport identities, an exhaustive three-case support criterion for an exact
cap-Nash root to remain exact at `U`, automatic transport in the sure-Quit
case, and zero debt on every active coordinate in the non-sure case.

I independently attempted to falsify each boundary case.  The statements and
inequality directions are correct.

## Tail identities

Player `i`'s forced-Quit payoff does not read its continuation coordinate.
Its forced-Continue payoff reads that coordinate precisely when every opponent
Continues, with coefficient

```text
O_i(q)=product_(j!=i)(1-p_j).
```

Therefore lowering the tail from `B_i` to `U_i=B_i-d_i` lowers Continue by
`O_i(q)d_i` and leaves Quit fixed.  With
`Delta_i=Quit_i-Continue_i`, this gives exactly

```text
Delta_i(U,q)=Delta_i(B,q)+O_i(q)d_i.
```

The prescribed successor reads the tail only after unanimous continuation,
so

```text
Succ(B,q)_i-Succ(U,q)_i=C(q)d_i,
C(q)=product_j(1-p_j).
```

The signs, deleted-player versus joint-survival coefficients, and absence of
any extra factor are all correct.

## Three support cases

For an exact binary-action Nash coordinate at tail `B`:

- `p_i=1` implies `Delta_i(B,q)>=0`;
- `0<p_i<1` implies `Delta_i(B,q)=0`; and
- `p_i=0` implies `Delta_i(B,q)<=0`.

At tail `U`, the same root has endpoint difference
`Delta_i(B,q)+O_i(q)d_i`.  Hence:

- a pure quitter remains optimal automatically;
- a mixed coordinate remains indifferent exactly when `O_i(q)d_i=0`; and
- a pure continuer remains optimal exactly when
  `-Delta_i(B,q)>=O_i(q)d_i`.

These conditions are individually necessary and sufficient, so their
coordinatewise conjunction is necessary and sufficient for the whole product
root to remain exact.  Ties at the pure endpoints are included correctly.

## Sure-Quit transport

If some player `k` Quits surely, then `O_i(q)=0` for every `i!=k`, while
coordinate `k` is in the automatic pure-Quit case.  Thus every coordinate
transports from `B` to `U`.  Also `C(q)=0`, so the prescribed successor is
identical at the two tails.  Since a sure quitter makes absorption charge one,
separately supplied punishment-floor bounds on both the tail and this common
successor do indeed turn the transported root into a charge-one exact
floor-admissible edge.

The note correctly does not infer those floor bounds or produce the sure-Quit
root from paid-row data.

## Non-sure active support

If no player Quits surely, finiteness gives `O_i(q)>0` for every player.  Any
active coordinate has `p_i>0`, hence `0<p_i<1`; the mixed-coordinate criterion
then forces `d_i=0`.  Equivalently, every positive-debt player must Continue
purely and must possess the exact slack

```text
-Delta_i(B,q)>=O_i(q)d_i.
```

Thus “active only on the zero-debt face” is exact provided `active` means
positive Quit probability, as it does in the section.  It does not assert
that a zero-debt active root exists.

## Boundary example and scope

The two-player example is correct.  If player `i` earns one whenever it Quits,
the other player earns zero, `B_i=1`, `U_i=0`, and the other player Continues,
then player `i` is indifferent at `B` and may mix strictly.  At `U`, Quit gives
one and Continue gives zero, so that same mixed root is not exact.  Here
`O_i d_i=1`, realizing the transport toll sharply; replacing the mixture by
pure Quit lands in the automatic sure-Quit arm.

Section 38 is a supplied-root criterion, not the paid excursion/re-entry
producer.  Its concluding alternatives preserve that scope: the paid source
still must produce either a floor-safe sure-Quit cap root or a positive cap
root supported on zero-debt coordinates with all inactive slacks.  I found no
unresolved mathematical objection.
