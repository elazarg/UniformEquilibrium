# Review of Propositions 25.1--25.5

Reviewer: `CODEX_RAMSEY`

Verdict: **REVISE**.  The matrix, packet, stationary, and scope claims check,
and the two claimed simple directed four-cycles really are exhaustive.  Two
entries in the purportedly complete pure-toggle audit must be corrected before
the section is exact.

## Matrix and LCP audit

For

```text
M = [ 0  3 -1  3
      2  0  1 -3
     -2  2  0 -1
      3 -2  1  0 ],
```

the principal determinants in (25.2) recompute to

```text
01:-6, 02:-2, 03:-9, 12:-2, 13:-6, 23:1,
012:-10, 013:-39, 023:-3, 123:-4, 0123:-23.
```

Each row has the stated distinct negative witness, so induction through the
definition of `normalLayer` leaves all four coordinates at every layer.  A
homogeneous complementary solution with support of size at least two is
excluded by the corresponding nonzero principal determinant.  A singleton
support is excluded by the negative entry in each column.  Thus the normal
core is full and the homogeneous branch is absent.

For `q*=(1,1,2,1)`, exhaustive support solution gives exactly the three
feasible standard-LCP points in (25.3): empty support, `{0,2}` with weights
`(1,1)` and outside residual `(4,5)`, and `{1,3}` with weights
`(1/2,1/3)` and outside residual `(7/2,8/3)`.  All their positive weights and
outside residuals are strict, so `q*` is a regular value of the piecewise
linear map.  The local derivative determinants are `1,-2,-6`, hence the
degree is `1-1-1=-1`.  Since positive homogeneity plus
`Phi^{-1}(0)={0}` makes `Phi` proper, the nonzero global degree proves
surjectivity and therefore standard `Q`.

The `{0,2}` restriction is exactly `[[0,-1],[-2,0]]`.  At projective
right-hand side `(-1,-1)`, its two residual inequalities are
`-c-z>=0` and `-c-2x>=0`; nonnegativity forces all normalized weights to
zero.  This is a valid nonprojective principal and therefore proves failure
of full projective `Q-bar`.  Proposition 25.1 realizes the stated
`ResidualHardClass` matrix fields.

## Packet and punishment audit

The singleton rows of (25.6), after subtracting each player's own singleton
payoff one, reproduce (25.1).  The half-half mixture of owners `0,1` is
`(5/2,2,1,3/2)`, dominates `(1,1,1,1)`, and pins both positive owners.  All
solo payoffs equal one and the crossed inequalities (25.8) are exact.

The four stated punishment roots use sure opponents `2,3,0,1`.  The
Continue/Join endpoint pairs for players `0,1,2,3` are respectively
`(0,1),(-2,1),(-1,1),(-1,1)`, so arbitrary behavioral deviation collapses
to the first absorbed row and gives `chi_i<=1`.  Immediate Quit guarantees at
least one for players `0` and `2`, because every coalition containing the
respective player pays it at least one; hence `chi_0=chi_2=1`.  These facts
verify every field of `QuittingNormalizedSingletonSourcePacket`, including
the unrestricted punishment-floor field.

## Required pure-toggle repairs

The adjacency list (25.9a) omits one strict edge:

```text
3 -> 23,
```

because player `2` receives `r_23(2)=1>0=r_3(2)`.  Thus the entry

```text
3:{13}
```

must read

```text
3:{13,23}.
```

There is also an arithmetic typo in the gain list following (25.9).  The
chosen edge `01->1` is toggled by player `0` and has gain

```text
r_1(0)-r_01(0)=4-1=3,
```

not `2`.  The claimed lower bound by one is unaffected.

I re-enumerated all directed four-step returns after inserting `3->23`.
There are still exactly the two simple directed four-cycles in (25.10), up to
cyclic rotation:

```text
0 -> 02 -> 012 -> 01 -> 0,
2 -> 02 -> 012 -> 12 -> 2.
```

Thus the omission does not create a third four-cycle, but the proof must use
the corrected complete list.

For the first cycle, the active indifference equations give
`p_2=2/3` and `p_1=2/21`; the blocker-Continue distribution is
`(19,2,38,4)/63` and its payoff is `67/63>1`.  For the second,
`p_0=1/2`, `p_1=1/10`; the distribution is `(9,9,1,1)/20` and the blocker
payoff is `23/20>1`.  Both blocker-continuation failures are exact.

## Stationary-support audit

Direct expansion of the stationary endpoint differences gives (25.16).  If
all four rates are positive, `H_3=0` implies
`p_2=2p_1-3p_0<2p_1`, and substitution gives
`H_0<-p_1-3p_3<0`; hence no full-support solution exists.

For Proposition 25.5, on `p=(0,x,2x,z)` direct expansion gives exactly

```text
H_1=3z-2x-6xz^2-12x^2z+12x^2z^2,
H_2=z-2x+4xz^2+4x^2z-4x^2z^2,
H_3=0,
H_0=-3z-x-14x^2(1-z).
```

Also `H_1-3H_2=2x[2-9z^2-12xz(1-z)]`.  On
`7/20<=z<=3/8`, the displayed `x(z)` is positive and below `1/2`, so all
three active rates `x,2x,z` lie strictly between zero and one.  Multiplying
`H_2` by `[12z(1-z)]^2` after substitution gives exactly (25.20), with

```text
P(7/20)=-5731817/16000000,
P(3/8)=32955/65536.
```

The IVT root is therefore in the open interval and makes all three active
differences zero.  The passive expression `H_0<0` is equivalent to the strict
passive no-join inequality because `H_0=delta(J_0-U_0)` with `delta>0`.
Each player has at least two positive-rate opponents, so playerwise opponent
contraction holds.  Proposition 12.1 and the checked stationary endpoint
compiler therefore give an exact terminal Nash profile against unrestricted
behavioral deviations and a uniform-equilibrium payoff.

## Scope

After the two finite-table corrections above, the intended scope is exact.
The table is a joint boundary test for the crossed packet, residual-hard
matrix data, pure-sink screen, four-cycle dispatcher, and full-support
stationary screen.  Proposition 25.5 positively solves the table on another
stationary support.  It is not a terminal exploitability witness and does not
show completeness of stationary strategies or any counterexample to the
quitting-game conjecture.
