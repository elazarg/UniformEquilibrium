# Review of CODEX_CEDAR paid-row re-entry, Section 55

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS in the stated source-matched scope.**  I checked the actual
tail/prefix semantics, the Continue-support use, and every displayed
constant.  I found no mathematical objection.

## Claim checked

For an actual continuation profile `sigma`, let `U,B,d=B-U` be its literal
terminal semantic pair.  Assume

```text
U_g <= r({g})_g-delta,   delta>0,
```

and let `q` be exact endpoint Nash at tail payoff `U`, with positive Continue
probability for `g`.  Writing `O` for opponent Continue mass and `A=1-O`, the
section claims

```text
A >= delta/(delta+2M),
d'_g=O*d_g,
DebtSum(sigma') <= DebtSum(sigma)-A*d_g,
delta <= d_g+2M*A_src,
```

and hence the debt-drop/source-hazard dichotomy (55.7)--(55.8).

## Checks

1. Continue support is exactly the needed support hypothesis.  Exact endpoint
   Nash gives `Q_g<=C_g`, and because Continue has positive prescribed
   probability the prescribed successor coordinate is `U'_g=C_g`.  The
   outsider decomposition

   ```text
   Q_g-C_g=O*(r({g})_g-U_g)+J_g
   ```

   and `|J_g|<=2M*A` therefore give

   ```text
   delta*(1-A) <= -J_g <= 2M*A,
   ```

   which rearranges exactly to `A>=delta/(delta+2M)`.

2. The cap recursion is literal and uses unrestricted behavioral deviations.
   At the prefixed profile, forced Continue transports the actual tail cap:

   ```text
   C_g(B)=C_g(U)+O*(B_g-U_g)=C_g+O*d_g.
   ```

   Since `d_g>=0` and `Q_g<=C_g`, the maximum defining the prefixed cap is
   `C_g+O*d_g`.  Subtracting `U'_g=C_g` proves `d'_g=O*d_g`; no stationary-
   deviation restriction or hidden approximation is present.

3. Exact-root prefixing weakly decreases every other nonnegative literal debt
   coordinate by the named block-action/prefix inequality.  Summation then
   loses at least `A*d_g` in the `g` coordinate, proving (55.5).

4. The source coupling is correct even with simultaneous collisions.  If `g`
   deviates to Quit at the first source date, the all-opponents-Continue event
   pays `r({g})_g`; on its complement both that solo payoff and the realized
   collision payoff lie in `[-M,M]`, so the loss is at most `2M` times the
   opponent-absorption probability.  Thus

   ```text
   d_g >= Q_src-U_g,
   r({g})_g-Q_src <= 2M*A_src,
   ```

   and (55.6) follows.

5. If `d_g>=delta/2`, multiplying by the first bound gives the exact decrement
   `delta^2/(2*(delta+2M))`.  Otherwise (55.6) gives the strict inequality
   `A_src>delta/(4M)`, so the displayed weak lower bound is valid.  The use of
   `M>0` is explicit.  At a global minimum, applying the minimum-debt lower
   bound to the literal prefixed profile justifies (55.9).

## Scope retained

The second arm is first-row opponent absorption in the **original actual
source**, not the charge of `q` or of any later exact edge.  The first arm is
total semantic-debt descent and does not orient prescribed payoff motion.
Accordingly the proposition does not supply payoff re-entry, a paid block, or
a return path.  The note states all three limitations correctly.
