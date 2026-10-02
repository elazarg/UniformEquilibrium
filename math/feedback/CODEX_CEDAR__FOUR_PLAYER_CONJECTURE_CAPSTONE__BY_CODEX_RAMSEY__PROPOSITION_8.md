# Independent falsification of Proposition 8

Reviewer: `CODEX_RAMSEY`

Source reviewed:
[`CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md`](../notes/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md), Section 11.

## Claim checked

In the repayment arm of Proposition 6, let `q_1` be the exact root at the
literal first-successor tail `V_1`, put

```text
x = q_1(k)(Quit),
H = sum_(j notin {k,i}) q_1(j)(Quit),
c = r_{ki}(i)-r_k(i),
eta = alpha*g_a/2,
d = Gamma/(4M).
```

The proposition claims a fixed absorption floor

```text
A(q_1) >= eta/(eta+2M),
```

and then either a third label has Quit marginal at least
`rho=d*alpha*g_a/(16M)`, or, in the negative-`c` arm, the old owner's
marginal has increased by at least `alpha*g_a/(8M)`.

## Verdict

**PASS, with no mathematical or textual repair.**  The endpoint orientation,
one-sided coupling estimate, thresholds, and derivative constants are all
correct.  The proposition's explicitly noniterable two-row scope is also
accurate.

## Source interfaces checked

I inspected the exact fixed-tail estimate
`gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash` in
`UniformEquilibrium/Quitting/Boundary/Repair/FixedTailUniformAbsorption.lean`
and the marginal cap
`exactFloorRoot_quitProbability_le_one_sub_terminalGap_div_four_mul` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/TerminalGapExactRootMarginalCap.lean`.
The first needs only exact endpoint Nash and the displayed singleton deficit;
the second needs the same boxed floor tail, the terminal witness, and exact
root Nash.  The Proposition 6 orbit supplies these hypotheses literally at
`V_1`.

## Detailed check

Proposition 6 gives

```text
V_1(i)=Q_i <= s_i-eta.
```

Thus the fixed-tail theorem applied to player `i` yields
`A(q_1)>=eta/(eta+2M)`.  No support or single-active-player assumption is used
in this step.

The exact-floor marginal cap gives every player Continue probability at least
`d`; equivalently every Quit marginal is at most `1-d`.  In particular player
`i` has positive Continue support.  Exact endpoint Nash therefore makes its
Quit-minus-Continue endpoint difference in the actual opponent environment
nonpositive.

After forcing the two players outside `{k,i}` to Continue while retaining
`k`'s actual Quit marginal `x`, that difference is

```text
F(x)=(1-x)(s_i-Q_i)+x(b-R_i),
b=r_{ki}(i),  R_i=r_k(i).
```

This orientation is exact: when `k` continues the two forced endpoints are
`s_i` and `Q_i`; when `k` quits they are `b` and `R_i`.  Player `i`'s own
mixing rate is irrelevant to a forced-action endpoint comparison.

The endpoint-difference integrand is bounded in absolute value by `2M`.
Couple each of the two remaining Bernoulli marginals with pure Continue.  The
two environments differ with probability at most `H`, and on the mismatch
event the two values of the integrand can differ by at most `4M`.  Hence

```text
|F(x)-D_actual| <= 4M H.
```

Since `D_actual<=0`, the claimed one-sided inequality `F(x)<=4MH` follows.
This explains why the conservative factor is `4M`, rather than `2M`; no
independence or total-variation factor is omitted.

If `c=b-R_i>=0`, then `x<=1-d` and `s_i-Q_i>=eta` give

```text
F(x)>=(1-x)eta>=d eta.
```

Thus `H>=d eta/(4M)`.  Literal `Fin 4` leaves exactly two labels outside
`{k,i}`, so one has marginal at least

```text
d eta/(8M)=d alpha g_a/(16M)=rho.
```

If `c<0`, the old solo-root identities give

```text
F(p)=p(Q_i-R_i)>=alpha*g_a.
```

When `H>=alpha*g_a/(8M)`, the same two-label pigeonhole gives a marginal at
least `alpha*g_a/(16M)>=rho`, because the already supplied interval
`0<alpha<=p<=1-d` implies `0<d<1`.  Otherwise `F(x)<F(p)/2`.  Moreover

```text
F'(x)=c-(s_i-Q_i)<0,
|F'(x)|=(s_i-Q_i)-c<=4M,
```

where each of the two endpoint differences contributes at most `2M`.
Consequently `x>p` and

```text
4M(x-p) >= F(p)-F(x) > F(p)/2 >= alpha*g_a/2,
```

which is stronger than the displayed weak bound
`x-p>=alpha*g_a/(8M)`.

## Scope and export assessment

The result is a valid literal two-row reduction: every anchored repayment
extension immediately spends a second fixed charge and reaches either fixed
third-label support or a fixed upward displacement of the old owner's rate.
It does **not** show that the third-label marginal is collision mass, preserve
the terminal-semantic carrier at the new row, regenerate the same gate after
the owner-rate increment, decrease a well-founded invariant, or produce a
payoff return.

For that reason I recommend keeping Proposition 8 **internal**, rather than
exporting it as a standalone packet.  It becomes export-qualified if a later
result consumes one of its two alternatives or makes the rate displacement
iterable with source provenance.  In its present form it is a sharp and
correct support-wall diagnostic, but it does not by itself eliminate a named
paid-near-return branch.
