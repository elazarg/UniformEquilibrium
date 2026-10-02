# Review of Proposition 6BC

## Claim checked

I checked the finite/Never localization of one affine source--replacement
contrast, the quantitative localization of the replacement endpoint debt,
and the prescribed-atom and mover-gain specializations.

## Verdict

**PASS in the stated one-contrast, fixed-opponent scope.**  The four-term
identity and constants are exact.  The displayed `(F,F)` cell supplies a
zero-Never component pair for one localized contrast, but it does not by
itself supply the simultaneous common-source radial packet required by 6BB.

## Four-cell localization

Write `A=sum_u a_u A^u` and `R=sum_v r_v R^v`, with both coefficient pairs
summing to one.  Affinity gives

```text
sum_(u,v) a_u r_v [Phi(A^u)-Phi(R^v)]
=sum_u a_u Phi(A^u)-sum_v r_v Phi(R^v)
=Phi(A)-Phi(R).
```

Multiplication by the selected sign does not change the identity.  If the
sum is at least `q`, one of four summands is at least `q/4`.  For that cell,
put `omega=a_u r_v` and
`d=s(Phi(A^u)-Phi(R^v))`.  Then `omega d>=q/4>0`, so both the weight and the
oriented contrast are positive.  Oscillation gives `d<=L`; hence

```text
omega>=q/(4L).
```

Since `omega<=1`, it also gives `d>=q/4`.  This proves all three bounds in
`(6BC.5)` without assuming that the other three summands are nonnegative.

## Endpoint debt

With opponents fixed, the mover's unrestricted cap `B_m` is independent of
the mover's prescribed stopping law.  Every component `R^v` is itself an
admissible deviation, so `B_m-U_m(R^v)>=0`.  Affinity of prescribed payoff
therefore gives the exact nonnegative decomposition

```text
B_m-U_m(R)=sum_v r_v [B_m-U_m(R^v)].
```

For the selected cell, `r_v>=a_u r_v=omega`; consequently

```text
B_m-U_m(R^v)
 <=epsilon/r_v
 <=epsilon/omega
 <=4L epsilon/q.
```

No cap convexity or interchange of a supremum and a mixture is being used;
only cap invariance under the mover's own strategy and payoff affinity are
needed.

## Two specializations

For one prescribed terminal event and observer coordinate,

```text
Phi(mu)=r_o(C) Pr_(update source m mu)(C)
```

is affine and has oscillation at most `|r_o(C)|<=M`.  Thus the atom cell has
oriented contribution and contrast at least `q/4`, weight at least
`q/(4M)`, and selected replacement debt at most `4M epsilon/q`.  If the
reward coefficient is zero, a positive `q` premise is impossible, so there
is no omitted boundary case.

For mover payoff, the range is `[-M,M]`, so the oscillation bound is `2M`.
Reversing the contrast orientation yields exactly the gain `g/4`, weight
`g/(8M)`, and endpoint-debt `8M epsilon/g` constants stated in the note.

## Exact remaining mismatch

The `F` conditional law has zero Never mass, while `N` is pure Never; a
zero-weight conditional component is never selected because the winning
cell has positive product weight.  Thus the four type labels are literal.
The `(F,F)` cell can be full-support smoothed and then meets the zero-Never
law condition used by 6BB for this one pair.

This is not yet the 6BB packet.  The atom localization and a gain
localization can choose different cells.  The second retained label has no
copy of the same atom localization, and independently chosen source
components can change the fixed opponent profile under which the first
contrast was computed.  In addition, replacing the original laws by
conditional components is generally an order-one source move; base,
tangent, and other packet fields are not preserved merely by the positive
mixture weights.  The note explicitly refuses the first two inferences; the
last is the same nearby-source/arbitrary-entry limitation already attached
to 6BB.  Subject to those nonclaims, the reduction from a continuum of laws
to four exact finite/Never cells is valid.

## Source inspected

- `notes/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md`, current
  Proposition 6BC and the immediately preceding 6BB context.
