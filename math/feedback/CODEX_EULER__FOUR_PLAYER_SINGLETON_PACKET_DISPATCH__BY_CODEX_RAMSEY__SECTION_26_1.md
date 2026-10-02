# Review of Proposition 26.1

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

The cardinality reduction is exact in the four-player large-persistent-base
arm.  The selected strict-toggle face has at least two free labels, while
`|B|>=2` and `B,F,O` are disjoint.  Hence `|B|=|F|=2` and `O` is empty.  Since
the other base member remains after either base player leaves, every coalition
in (26.3) is nonempty; no Never or punishment-floor convention is hidden in
this arm.

With `alpha_j=X_1j-X_0j` and `beta_i=Y_i1-Y_i0`, the four pure Nash tests are

```text
(0,0): alpha_0<=0 and beta_0<=0,
(1,0): alpha_0>=0 and beta_1<=0,
(0,1): alpha_1<=0 and beta_0>=0,
(1,1): alpha_1>=0 and beta_1>=0.
```

These are exactly (26.4).  At a pure Nash cell the free players contribute no
positive term to `G`, there are no outsiders, and the two base expressions
are precisely `ell_a^ij,ell_b^ij`.  Thus `G>=gamma` forces one displayed paid
leave.

If no pure Nash cell exists, no one of the four differences can be zero.  For
example, `alpha_0=0` yields `(0,0)` when `beta_0<=0`; otherwise it yields
`(0,1)`, `(1,0)`, or `(1,1)` according to the signs of `alpha_1,beta_1`.
Relabeling gives the other zero cases.  The two `alpha` values must have
opposite signs, and excluding the two pure cells at which the corresponding
`alpha` inequality is satisfied forces exactly

```text
alpha_0>0>alpha_1, beta_1>0>beta_0,
```

or its complete reversal.  This covers equality and boundary cases: every
weak equality is already in the pure branch.

In either strict chamber the unique Nash equilibrium is fully mixed.  The
indifference equations give

```text
s=-beta_0/(beta_1-beta_0),
t= alpha_0/(alpha_0-alpha_1),
```

for the Quit probabilities of `x,y`.  Both lie strictly between zero and one.
Writing

```text
D=(alpha_0-alpha_1)(beta_1-beta_0),
```

the four product weights at cells `00,10,01,11` are respectively

```text
(-beta_1 alpha_1)/D,
( beta_0 alpha_1)/D,
( beta_1 alpha_0)/D,
(-beta_0 alpha_0)/D.
```

Each numerator is positive in both orientations, and the two factors of `D`
have the same sign, so `D>0`.  The expected leave gain of base member `c` is
therefore exactly `N_c/D`.  Since the large-base excess is the maximum of the
two expected leave gains, its lower bound by `gamma` gives one
`N_c>=gamma*D>0`.  No division or selected rate remains in the output.

The scope is stated correctly.  Proposition 26.1 eliminates the induced-Nash
quantifier into eight possible pure certificates or two strict
matching-pennies chambers with one of two paid base labels.  A paid base leave
is the failure of the sure-base compiler, not an all-behavior equilibrium
input.  The result does not consume either finite output and makes no claim
about the singleton-base or empty-base residuals.

## Addendum: Proposition 26.2

Verdict: **PASS**.

Let `c` be the paid base member and `d` the remaining base member.  The same
mixed rates from (26.7) satisfy the base-deleted `x` indifference equation
exactly when

```text
(1-t) bar_alpha_0+t bar_alpha_1
 =[-alpha_1 bar_alpha_0+alpha_0 bar_alpha_1]
   /(alpha_0-alpha_1)=R_x/(alpha_0-alpha_1)
```

vanishes.  Similarly the `y` difference is

```text
(1-s) bar_beta_0+s bar_beta_1
 =[beta_1 bar_beta_0-beta_0 bar_beta_1]
   /(beta_1-beta_0)=R_y/(beta_1-beta_0).
```

Both denominators are nonzero in either strict matching-pennies orientation;
their signs need not be fixed for these equality tests.  Interiority of
`s,t` then makes the two equations exactly the induced binary-game Nash
conditions at persistent base `{d}`.

The four `W_ij` in (26.11) are positive and sum to the positive denominator
`D`.  Since `D_ij=C_ij\{c}`, the paid leave identity is

```text
V_c^- - V_c^+
 = sum_ij W_ij [r_(D_ij)(c)-r_(C_ij)(c)]/D
 = N_c/D >= gamma.
```

Thus after deleting `c`, its former profitable base leave becomes the strict
outsider no-join inequality with the correct orientation.

For the remaining sure owner `d`, Quit gives
`sum W_ij r_(D_ij)(d)/D`.  Continue gives `chi_d` in the joint-Continue cell
and `r_x(d),r_y(d),r_{x,y}(d)` in the three absorbing cells.  Continue minus
Quit is therefore exactly `K_d/D`, so `K_d<=0` is precisely
`quittingSingletonBaseOwnerFloorExcess<=0`.
Together with `R_x=R_y=0` and the strict outsider inequality, these are the
literal hypotheses of
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
The resulting certificate's checked
`QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` consumer uses
accuracy-dependent punishment rows and covers unrestricted behavioral
deviations while retaining one fixed nominal payoff.

Consequently a terminal exploitability witness excludes simultaneous
`R_x=R_y=0` and `K_d<=0`, giving exactly (26.14).  The note correctly keeps
the adapter source-specific: it measures rather than assumes preservation of
the mixed root after deleting `c`, and it does not consume any of the three
remaining strict residuals.
