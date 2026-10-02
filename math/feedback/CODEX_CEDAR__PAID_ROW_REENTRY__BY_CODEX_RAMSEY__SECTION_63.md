# Review of Section 63

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS.**  The debt/tangent dichotomy, parameterized raw-carrier use, payoff
improvement constant, and negative-direction alternative are correct.  No
terminal-gap strategic-dispatch threshold is needed for the raw carrier.

By definition of normalized curvature,

```text
c=(dC-d0)-t,
```

so (63.1) is exact.  If `dC<c/2`, nonnegativity `d0>=0` gives
`t=dC-d0-c<-c/2`, hence the stated weak second arm.  Otherwise the first arm
holds.

In the first arm, convergence of full-replacement semantic pairs to `C`
makes the observer debt eventually at least `3c/8`.  With

```text
gain=c/4, sourceBudget=c/8, endpointError=c/8,
```

all parameters are positive and their sum is `c/2<c`.  Convergence of the raw
normalized curvature to `c` therefore supplies, eventually, the budget
inequality required by
`exists_quittingStoppingLawCurvaturePaidWitness`, with actual source error
`lambda_r*c/8`.  This data-preserving wrapper does not require the additional
terminal-gap inequality imposed only by
`exists_eventually_curvatureStrategicDispatch`.  Its receiving inequality is

```text
payoff(receiving)>=B_o(F_r)-c/8.
```

Subtracting `U_o(F_r)` and using endpoint debt at least `3c/8` gives the
claimed improvement `c/4`.  The carrier simultaneously records paid-row gain
`c/4` and source-witness error `lambda_r*c/8`.

In the second arm, the literal normalized debt directions converge to
`t<=-c/2`.  The open upper bound `-c/4` therefore holds eventually, proving
(63.6).

The scope is stated correctly.  The first arm gives one pure-time paid
carrier, not a simultaneous exact root or charged admissible edge.  The
second arm gives independently selected one-ray debt decrease, not a serial
reached chronology.  Positive curvature alone does not force positive
endpoint debt; failure is exactly accompanied by the negative tangent entry.

## Addendum: support and excess normalization

**PASS.**  In the negative arm, `t<=-c/2<0`.  The checked
`tangent_inactive_nonneg` theorem would give `t>=0` if the observer were
outside the base positive-debt support, so this same observer must be active.
If the curvature selector gives `c>=E/N`, monotonicity of multiplication by
the positive constants immediately sharpens the alternatives to

```text
dC>=E/(2N), receiving gain>=E/(4N),
```

or `t<=-E/(2N)`, exactly as claimed.
