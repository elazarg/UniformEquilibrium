# Feedback on `CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE`, Sections 16--17

Reviewer: `CODEX_CEDAR`

## Claim checked

I independently checked the rational diagnostic table `(16.1)` against the
pure, common-stationary, designated-pair, and cross-pair filters, and checked
Proposition 11's single-owner stationary interval against every unilateral
behavioral deviation.  I did not review the later support extensions here.

## Verdict

**VALID ordinary mathematics.**  The table in Section 16 really survives the
four displayed filters, but Proposition 11 then gives an exact unrestricted-
behavior terminal equilibrium for every `x in [1/7,2/7]`.  Thus Section 16 is
correctly presented only as a diagnostic survivor of the earlier finite menu,
not as a counterexample or residual hard instance after Proposition 11.

## Section 16 arithmetic

For

```text
(A_1,A_2)=(7,10),
(B_0,B_1,B_2)=(1,8,-7),
(C_0,C_1,C_2)=(-4,2,8),
(D_0,D_1,D_2)=(-6,6,-1),
```

the six strict inequalities in chamber `(14.3)` are immediate, so the
reviewed pure-orbit classification excludes all pure outcomes.

Substitution in the common stationary numerator gives

```text
G(h)=-7+24h-60h^2+52h^3-21h^4+3h^5.
```

Its degree-five Bernstein coefficients are exactly

```text
-7, -11/5, -17/5, -27/5, -36/5, -9.
```

All are strictly negative, hence `G<0` on the whole unit interval.  Likewise
the designated-pair polynomial is

```text
-2-9x-3x^2+7x^3,
```

whose degree-three Bernstein coefficients are `-2,-5,-9,-7`; it has no root
on `[0,1]`.

The cross-pair polynomial is `1-x-7x^3`.  Its derivative is
`-1-21x^2<0`, while its values at `2/5` and `9/20` have opposite signs, so it
has exactly one root `xStar` in that interval.  At the root,

```text
w=1/xStar,
I=6-10xStar+5xStar^2.
```

Using `7xStar^3=1-xStar` gives

```text
xStar*(I-w)=(-2+37xStar-70xStar^2)/7.
```

The numerator is a concave quadratic and is positive at both interval
endpoints (`8/5` and `19/40`, respectively), hence it is positive throughout
the interval.  The unique active cross-pair root therefore strictly fails the
inactive-player inequality, exactly as claimed.

## Proposition 11 and unrestricted deviations

Let the sole owner continue each live date with probability `x<1`; all other
players Never.  Survival through `N` dates is `x^N`, so absorption at the
owner singleton is almost sure.

* Every finite owner Quit time pays `B_0`, and owner Never pays zero.  Thus
  `B_0>=0` controls every owner stopping law.
* The designated partner obtains `C_0` if the owner absorbs before its chosen
  Quit date.  Conditional on reaching that date, forced Quit pays
  `xB_0+(1-x)D_0`.  Hence every pure-time payoff lies on the segment between
  these two endpoints, and the second inequality in `(17.1)` makes Never
  optimal.
* An opposite player has the identical calculation with prescribed endpoint
  `A_1` and forced-Quit endpoint `xB_0+(1-x)B_1`.  The last inequality in
  `(17.1)` makes Never optimal.

Against fixed opponent clocks, any behavioral stopping law is a probability
mixture of the finite pure Quit times and Never.  The endpoint bounds above
therefore cover unrestricted behavioral deviations, including the terminal
Never atom; no one-shot-deviation shortcut is being used.

For `(16.1)`, the two passive inequalities become

```text
7x-6 <= -4,       8-7x <= 7,
```

or `x<=2/7` and `x>=1/7`.  Since `B_0=1`, every
`x in [1/7,2/7]` satisfies Proposition 11.  Only one player ever quits, so
both designated-pair outcome atoms are indeed zero.

## Scope

This is a complete verification of the single-owner filter, not a universal
classification of the eleven-parameter table.  Its use is to add the explicit
failure of every single-owner interval to the conditions any later hard table
must satisfy.
