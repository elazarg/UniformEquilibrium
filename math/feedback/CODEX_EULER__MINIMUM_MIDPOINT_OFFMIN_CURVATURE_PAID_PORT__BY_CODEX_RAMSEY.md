# Review of minimum-midpoint off-minimum curvature paid port

Reviewer: **CODEX_RAMSEY**  
Source:
[`CODEX_EULER__MINIMUM_MIDPOINT_OFFMIN_CURVATURE_PAID_PORT`](../notes/CODEX_EULER__MINIMUM_MIDPOINT_OFFMIN_CURVATURE_PAID_PORT.md)  
Verdict: **PASS; internal/no export**  
Date: 2026-08-26

## Claim checked

For one literal stopping-law chord `S_n,H_n,E_n`, with `H_n` the half
mixture, assume the source and midpoint limits have total debt `D_*` and the
full endpoint has total debt `D_*+Delta`.  The note claims that all midpoint
curvature lies off the mover coordinate, one fixed opponent carries normalized
curvature at least `Delta/(card I-1)` after a subsequence, and in Fin4 this
produces a gain-`Delta/12` curvature-paid row on the literal full endpoint.
The checked cap lift then yields charged return, quantitative descent, or
inert stall.

The proof and composition are correct.  The inert alternative is not excluded
by the two-minimum-point provenance.

## 1. Chord curvature and mover coordinate: PASS

Coordinatewise stopping-law debt convexity gives

```text
kappa_(n,j)=(d_j(S_n)+d_j(E_n))/2-d_j(H_n) >= 0.
```

Semantic convergence and the three total-debt assumptions imply

```text
sum_j kappa_(n,j) -> Delta/2.
```

For the mover, changing only its complete strategy leaves its unrestricted
best-response envelope invariant, while its prescribed payoff is affine in
the stopping-law mixture.  Hence its debt is affine and `kappa_(n,o)=0`
exactly, not just asymptotically.

Among the `N=card I-1` opponent coordinates, choose a maximal curvature at
each sufficiently late index and pass to a subsequence on which its label is
fixed.  Along that subsequence its liminf is at least `Delta/(2N)`.  At
`lambda=1/2`, normalized curvature is

```text
C_(n,i)=d_i(E_n)+d_i(S_n)-2d_i(H_n)=2*kappa_(n,i),
```

so its liminf is at least `Delta/N`.  This justifies the note's “after a
subsequence” formulation; without that subsequence, one fixed coordinate
need not have the asserted liminf because the maximal coordinate can rotate.

## 2. Fin4 budgets and literal profile: PASS

For Fin4, `N=3`, so eventual normalized curvature exceeds every
`c<Delta/3`.  The current choices

```text
c=Delta/6,
gain=Delta/12,
sourceError=endpointError=Delta/48
```

have total budget `Delta/8<Delta/6`.  At half weight, the hypothesis of
`exists_quittingStoppingLawCurvaturePaidWitness` is exactly

```text
gain + endpointError + sourceError <= C_(n,i).
```

All three parameters are positive.  Thus the decoder applies eventually.
Its `row` is explicitly a
`QuittingPaidFirstDisagreementRow` on

```text
Function.update sigma_n o tau_n = E_n's literal actual profile,
```

not on the midpoint, a compact representative, or a reselected law point.
The source and receiving approximate-pure-time fields also stay attached to
that same literal chord.

## 3. Cap-port and trichotomy handoff: PASS

`QuittingStoppingLawCurvaturePaidWitness.nonempty_capLiftedSummablePort`
requires only a supplied positive global minimum, its global lower-bound
property, and positive row gain.  The tangent-family wrapper supplies those
fields directly but is not mathematically essential.  The resulting paid
source uses the literal full endpoint as its profile.

`QuittingPaidCapLiftedSource.exactTrichotomy` gives the pairwise-disjoint
alternatives:

```text
ChargedNearReturn or QuantitativeDebtDescent or InertStall.
```

The charged branch stores an actual uniform-equilibrium payoff, so a terminal
exploitability witness excludes it.  The resulting honest hard-residual
conclusion is therefore quantitative descent or inert stall.

## 4. Inert scope: PASS

No checked declaration found in the named dependency chain turns source and
midpoint minimum provenance into positive absorption of an exact cap root at
the off-minimum endpoint.  Curvature compares behavioral caps along the
source/full-replacement chord; the cap lift subsequently selects exact roots
against `B(E_n)`.  Those roots may all be all Continue.  In that event every
cap prefix is literally inert while the paid row persists.

The stronger claim “positive midpoint curvature forces descent or charged
return” is therefore not proved.  The note correctly states only the exact
three-way port and, under the terminal witness, descent or inertness.

## 5. Novelty and disposition

The checked tangent-family full-replacement theorem already gives a stronger
asymptotic curvature dispatch in its native flat-column setting.  The useful
new ordinary statement here is the transparent fixed-half common-chord
identity and its exact minimum/midpoint versus off-minimum endpoint split.
It complements the common-chord support-collapse theorem:

- a minimum full endpoint can feed strict support re-extraction;
- an off-minimum full endpoint with minimum midpoint feeds a literal paid
  port, but may remain inert.

**PASS, internal/no export.**  It is source-honest and formalization-ready as
a narrow wrapper, but it does not eliminate the surviving inert arm or show
that Prop8's forced source and midpoint lie on the minimum fiber.
