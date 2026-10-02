# Review of Sections 14--15 / Propositions 9--10

Reviewer: `CODEX_CEDAR`

## Verdict

**VALID ordinary mathematics, with one display-level chamber qualification.**
The six pure outcome orbits are classified exactly.  No-pure tables fall into
the two displayed strict `D_0` chambers, and the cross-pair polynomial has the
claimed IVT root.  Proposition 10 correctly asserts a full all-behavior
equilibrium only after the inactive spectator inequality (15.4) is supplied.
The rational table (15.6) passes the pure, periodic, and common-stationary
checks.

In the designated-join arm, the full no-pure hypothesis additionally forces
`B_1<A_1`; this sign is omitted from (14.2).  The stated implication “no pure
implies one of (14.2)--(14.3)” remains true, and Proposition 7 does not need
the omitted sign.  The patterns should not be read as an iff characterization
without restoring it.

## Pure-orbit classification

For a non-singleton date-zero coalition, a member who leaves still faces
immediate absorption by the remaining coalition, and an outsider can affect
the outcome only by joining at date zero.  The five coalition orbit checks
are therefore exactly:

```text
singleton:        owner B_0>=0; partner D_0<=C_0;
                  opposite join B_1<=A_1;
designated pair:  member D_0>=C_0; opposite join B_2<=A_2;
cross pair:       member B_1>=A_1; partner-side join D_1<=C_1;
triple:           designated members D_1>=C_1;
                  remaining member B_2>=A_2; outsider D_2<=C_2;
grand:            member D_2>=C_2.
```

For a singleton owner, postponing gives either the same singleton payoff
`B_0` or Never payoff zero, hence the extra condition `B_0>=0`.  Against
all-Never, every finite pure time gives `B_0`, so all-Never is exact exactly
when `B_0<=0`.  Pure-time extremality supplies unrestricted behavioral
coverage in these two boundary cases.

With no pure equilibrium, `B_0>0` and `D_2<C_2`.  If `D_0>C_0`, avoiding a
designated-pair sink forces `B_2>A_2`; avoiding a triple then forces
`D_1<C_1`; and avoiding a cross pair also forces the omitted
`B_1<A_1`.  This implies (14.2).  If `D_0<C_0`, avoiding singleton, cross,
and triple sinks successively forces

```text
B_1>A_1,  D_1>C_1,  B_2<A_2,
```

which is (14.3).  At equality `D_0=C_0`, avoiding singleton and designated
pair forces both `B_1>A_1` and `B_2>A_2`; avoiding cross forces `D_1>C_1`,
after which the triple is stable because `D_2<C_2`.  Thus equality is
impossible.  This proves the claimed chamber exhaustion, conditional on the
separately reviewed common-stationary boundary used for (14.4).

## Cross-pair active algebra

At a phase where one cross pair is active, forced Quit pays

```text
Qx=x B_0+(1-x)B_1,
```

and forced Continue pays `(1-x)A_1+xw`.  Direct enumeration gives

```text
v=(1-x)x B_0+(1-x)^2 B_1+x(1-x)A_1+x^2w,
w=x(1-x)(C_0+A_1)+(1-x)^2 C_1+x^2v.
```

Substitution of `v=Qx=(1-x)A_1+xw` yields precisely (15.1).  Its endpoint
values are

```text
Px(0)=B_1-A_1,
Px(1)=3B_0-C_0-2A_1,
```

so (15.3) gives an interior root by IVT.

At the inactive phase the active players are respectively the spectator's
designated partner and one opposite player.  Forcing the spectator to Quit
produces rewards `B_0,D_0,B_1,D_1` with probabilities
`x^2,x(1-x),x(1-x),(1-x)^2`, exactly the left side of (15.4).  Thus (15.4),
and not merely the active polynomial, is the required spectator condition.
With it, every endpoint inequality holds.  Deleting any player leaves at
least one positive-hazard active owner in each two-phase block, giving the
strict player-deleted contraction needed to pass from all pure times and
Never to unrestricted behavioral deviations.

## Rational regression (15.6)

The table lies strictly in (14.3):

```text
B_0>0, D_2<C_2, D_0<C_0, B_1>A_1, D_1>C_1, B_2<A_2.
```

Its cross polynomial is

```text
Px=1+x-3x^2-4x^3.
```

At every interior root, `w=1/x`, while the inactive forced-Quit payoff is
`x^2+2x(1-x)+(1-x)^2=1`; hence (15.4) is strict.  For a common stationary
hazard `h`, direct evaluation gives Quit-minus-Never numerator

```text
G=-5+19h-26h^2+4h^3+10h^4-5h^5
```

over a positive denominator.  Its degree-five Bernstein coefficients are
`(-5,-6/5,0,-1,-9/5,-3)`, so `G<0` on the whole closed interval: at the
endpoints a negative endpoint coefficient is active, and in the interior all
Bernstein basis functions are positive.  Together with the pure-orbit check,
this rules out the common stationary endpoints as well.  The exact periodic
cross-pair equilibrium is therefore genuinely additional for this table,
while the final residual-wall paragraph correctly stops short of claiming
that the remaining inactive walls exhaust all periodic supports.
