# Feedback on `CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE`, Sections 18--19

Reviewer: `CODEX_CEDAR`

## Scope and verdict

I independently checked Propositions 12--13, their unrestricted-deviation
arguments, and the exact rational filter tests `(18.3)` and `(19.4)`.

**Verdict: VALID ordinary mathematics.**  Both stationary support tests are
exact sufficient conditions, and both rational tables have the claimed prior-
filter history.  These are support-specific escape certificates, not a claim
that the listed supports exhaust the eleven-parameter class.

## Proposition 12

For either member of the active designated pair, forced Quit is
`xB_0+(1-x)D_0`, whereas Continue is the affine recurrence with absorption
payoff `C_0`; equality `(18.1)` therefore pins its value to `C_0`.  For an
inactive player, conditioning on zero, one, or two active quits gives

```text
w=2x(1-x)A_1+(1-x)^2A_2+x^2w,
I=x^2B_0+2x(1-x)B_1+(1-x)^2B_2,
```

and hence exactly `(18.2)`.  Every player faces at least one opponent with a
positive stationary hazard, so the pure finite-time/Never endpoint bounds
extend to every behavioral stopping law.

For `(18.3)`, `(18.1)` gives `x=1/4`, and direct substitution gives
`w=54/5` and `I=19/16`.  The single-owner inequalities demand simultaneously
`x<=1/4` and `x>=3/8`.  The table is also genuinely past the earlier filters:

* it lies in the strict cross-join/no-pure chamber;
* its common-stationary numerator after the positive hazard factor is
  `-7+27h-54h^2+30h^3-3h^5`, with Bernstein coefficients
  `-7,-8/5,-8/5,-4,-29/5,-7`;
* its designated-pair polynomial is
  `-1-13x+3x^2+4x^3`, with Bernstein coefficients
  `-1,-16/3,-26/3,-7`;
* its cross-pair polynomial is `3-5x+3x^2-8x^3`, strictly decreasing.
  At its unique root the inactive inequality fails (equivalently the root is
  below the positive zero of `8-13x-2x^2`).

Thus Proposition 12 really supplies the first exact equilibrium among the
displayed earlier filters for this table.

## Proposition 13

The three active endpoint equations have the stated meanings:

* active player `1` has forced-Quit value `K` and Continue recurrence giving
  `K=W`;
* either active member of `{0,2}` has forced-Quit value `R`, and its four
  partner/opposite outcomes give
  `(1-xy)R=xsA_1+qyC_0+qsC_1`;
* inactive player `3` has prescribed recurrence `C` and forced-Quit value
  `T` exactly as in `(19.2)`.

Each active player faces another active opponent, and the inactive player
faces all three.  Player-deleted survival therefore contracts geometrically,
so unrolling the exact endpoint inequalities covers finite pure Quit times
and Never, and pure-time extremality covers all behavioral deviations.

For `(19.4)`, I checked the full diagnostic chain:

* the six strict cross-join chamber signs hold;
* the common-stationary polynomial and its six negative Bernstein
  coefficients are exactly those displayed;
* the single-owner opposite inequality is impossible (`2<=0`), while the
  active designated-pair equality would require `9` to lie between `2` and
  `6`;
* the designated polynomial is
  `-3-12x+16x^2-4x^3` with the displayed negative Bernstein coefficients;
* the cross polynomial `2-x-4x^2` has one root in `(7/12,3/5)`, and at that
  root `x(I-W)=47x/2-13>0`.

For the new support, `K=W` is exactly

```text
11x^3-11x^2-27x+23=0.
```

Its derivative is negative on `[0,1]`, and the endpoint evaluations place its
unique root in `(3/4,4/5)`.  Substitution yields the quadratic `(19.6)`;
its derivative is strictly negative on the whole unit `y` interval, its
endpoint signs are opposite, and `F_x(1/2)>0`, so the unique root has
`y>1/2`.

Finally, direct expansion verifies `(19.7)`.  Here
`R_D-K=-12x^2+8x+8>0`; replacing `y` by its lower bound `1/2` gives `L(x)`.
The stated derivative lower bound is `4481/500>0`, and
`L(3/4)=61/128>0`.  Hence `C>T` strictly.  The exact three-active stationary
equilibrium follows, and player `3` Never implies the designated-pair atom
`{1,3}` is zero.

## Boundary retained

The results enlarge the verified menu of exact stationary escapes in this
structured class.  They do not prove a universal gadget no-go or a complete
support classification, exactly as the note states.
