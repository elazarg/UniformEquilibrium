# Focused review of Section 39 of `CODEX_CEDAR__PAID_ROW_REENTRY`

Reviewer: `CODEX_RAMSEY`

Status: `VALID EXACT UPWARD-TAIL TRANSPORT CRITERION AND FLOOR SPECIALIZATION`

## Tail identities and sign

Let `V>=U` be an arbitrary coordinatewise lift and put
`e_i=V_i-U_i>=0`.  Raising player `i`'s tail
coordinate leaves its forced-Quit payoff fixed and raises its forced-Continue
payoff by exactly `O_i(q)e_i`.  Therefore, for endpoint difference
`Delta_i=Quit_i-Continue_i`,

```text
Delta_i(V,q)=Delta_i(U,q)-O_i(q)e_i.
```

The prescribed successor reads the lift only after unanimous continuation,
so

```text
Succ(V,q)_i-Succ(U,q)_i=C(q)e_i.
```

Both signs and survival coefficients in (39.1)--(39.2) are correct.

## Support criterion

At the original exact `U`-root:

- a pure continuer has `Delta_i(U,q)<=0`; subtracting the nonnegative toll
  preserves Continue automatically;
- a mixed coordinate has `Delta_i(U,q)=0` and remains mixed-exact exactly when
  `O_i(q)e_i=0`; and
- a pure quitter has `Delta_i(U,q)>=0` and remains optimal exactly when
  `Delta_i(U,q)>=O_i(q)e_i`.

Thus the three clauses in (39.3) are individually and jointly necessary and
sufficient.  Endpoint ties are handled correctly.

If no player Quits surely, every `O_i(q)>0`; hence every active coordinate is
strictly mixed and must have `e_i=0`.  For the specialization
`V=U vee P`, this is equivalent to `U_i>=P_i`; deficient coordinates may occur
only among pure continuers.  This is the exact dual of Section 38's zero-debt
active-support statement.

## Sure-Quit boundary

If `k` Quits surely, then every coordinate `i!=k` has `O_i(q)=0` because its
opponent set contains `k`.  Those coordinates transport automatically.  The
only potentially nonzero toll is the sure quitter's own, giving exactly

```text
Delta_k(U,q)>=O_k(q)(P_k-U_k)_+.
```

If another player also Quits surely then `O_k=0` as well, which is correctly
included.  In particular `U_k>=P_k` makes the own lift zero and transport is
automatic.  A sure quitter gives `C(q)=0`, so the successor is unchanged by
floor clipping and the transported root has charge one.  Because `V>=P` and
an exact Nash predecessor of a floor-admissible tail is floor-admissible by
`quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge`, the claimed
floor-admissible edge conclusion is sound; no extra unmentioned current-floor
hypothesis is needed.

## Sharpness and scope

Section 33 realizes the own-coordinate obstruction exactly for an arbitrary
upward lift: its sure quitter is indifferent at `U`, so
`Delta_o(U,q)=0`, while any positive lift has `O_o e_o>0`; the same root
immediately fails the pure-Quit condition.  As the note now states explicitly,
that perturbation is not a floor clip because the original moved coordinate
already equals its punishment floor.  It proves sharpness of the generic
pure-Quit toll, while (39.4) is the correct below-floor specialization.  The
stronger dominance calculation removes alternative positive roots but is not
needed for Proposition 39's criterion.

Proposition 39 remains a supplied-root transport theorem.  It neither creates
an exact prescribed-tail root nor proves one of the four concluding source
alternatives from paid-row/frontier data.  I reviewed the repaired arbitrary-
lift statement and floor specialization and found no unresolved mathematical
objection.
