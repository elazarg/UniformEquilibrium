# Whole-packet gate for `FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION`

Reviewer: `CODEX_EULER`

## Verdict

**ACCEPT.**  The full packet, including the Proposition 3 whole-segment tube
and Proposition 4 whole-minimum-fiber/debt-moat amendments, satisfies every
item of `exports/README.md`.  No repair or demotion is required.

## Exact scope and source composition

The statement is literally on `Fin 4` and uses the same reward table
throughout.  The no-uniform branch supplies all-player punishment normality,
the terminal exploitability witness, and the minimum-spine alternative.  The
proof correctly eliminates the fixed-owner spine and every singleton-tight
positive minimum face before asserting the strict inequalities

```text
P_i <= s_i < U_i.
```

The declarations listed in the source audit have the needed orientations and
quantifiers.  The new conclusions are ordinary compositions of those checked
inputs plus compactness and continuity; they are not presented as already
Lean-checked.

## Quantitative root isolation

For a positive-Quit player at a non-all-Continue exact root, the endpoint
difference has the form

```text
(1-O_i)(s_i-V_i)+joiningContribution_i,
joiningContribution_i <= 2M O_i.
```

Under `V_i-s_i>delta/2`, exact Quit support gives

```text
O_i >= delta/(delta+4M),
```

and joint absorption dominates `O_i`.  The sign and factor `4M` are correct.
This fixed positive floor, compactness of the product-root simplex, and
closedness of exact endpoint Nash make the open unique-all-Continue
neighborhood argument valid.  The packet also intersects with the open
coordinate region above singleton payoffs, so all-Continue is not merely the
only possible root but is itself exact everywhere in the final neighborhood.

## Whole `[U,B]` tube

With `H(t)=B-t(B-U)`, carrier debt nonnegativity gives
`H(t)_i>=U_i>s_i` uniformly.  The checked debt-homotopy theorem covers
`0<=t<1`, and the independently reviewed plateau uniqueness covers `t=1`.
Compactness of `[0,1]` and the same absorption floor upgrade pointwise
uniqueness to one open tube around the entire segment.  Both endpoint and
half-open-boundary cases are accounted for.

## Whole minimum fiber and debt moat

At an arbitrary global-minimum carrier pair `X`, equality
`X.1_i=s_i` triggers the checked complementary debt/slack identity and makes
`i` the unique debtor with debt `D_*`.  The controlled singleton-rate theorem
then yields `s_i<P_i`, contradicting same-table punishment normality.  Thus
all minimum pairs are strictly singleton-separated.

The minimum fiber is compact.  Minimizing the finitely many coordinate gaps
over it gives one `delta_*>0`; the critical-face theorem and the reverse
absorption estimate then give one open all-Continue-only set `T_*` around
its prescribed-payoff projection.

The carrier complement

```text
C={X in carrier : X.1 notin T_*}
```

is compact and disjoint from the minimum fiber.  Continuity of total debt
therefore gives a strict positive gap above `D_*` (or the assertion is
vacuous if `C` is empty).  Taking half this gap yields `epsilon_*>0` and

```text
D(X)<D_*+epsilon_*  ->  X.1 in T_*.
```

For an exact semantic-prefix edge, the root is tested at this literal carrier
tail.  Positive charge is incompatible with unique all-Continue, so the
contrapositive debt-moat conclusion is exact.  The packet correctly refuses
to apply it to an arbitrary payoff-only Bellman tail with no carrier pair.

## Probability, adapter, boundaries, and handoff

All one-row roots are independent Boolean product laws.  Terminal-semantic
debt uses unrestricted behavioral best-response envelopes; no stationary or
bounded-controller surrogate is substituted.  The incoming-tail boundary is
stated with the correct Bellman orientation: a head near the tube may still
have a nonlocal tail outside it.

The normality, two-player `1/5` root, endpoint-sign, and incoming-tail tests
exercise the load-bearing hypotheses.  The actual-data adapter and remaining
semantic endpoint are identified.  The Lean handoff separates the literal
Fin4 composition from the whole-fiber compactness theorem, names the relevant
critical-face/homotopy machinery, preserves carrier provenance, and does not
store the desired isolation as source data.

## Nonclaims

The packet does not claim a charged edge, a return, repayment, approximate
root rigidity, alignment with the stationary paid source or LCP principal,
or a uniform-equilibrium payoff.  Its strongest quantitative moat is
restricted exactly to carrier-tailed semantic-prefix edges.  These limitations
match the proved result.

