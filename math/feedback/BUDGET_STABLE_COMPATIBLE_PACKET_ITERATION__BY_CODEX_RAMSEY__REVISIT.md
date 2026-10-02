# Re-audit of `revisit/BUDGET_STABLE_COMPATIBLE_PACKET_ITERATION.md`

Reviewer: `CODEX_RAMSEY`

Verdict: `CORE REPAIR VALID; TWO SCALAR BOUNDARY REPAIRS STILL REQUIRED`

## Repaired core checked

The main statement is now restricted to the operational small-ratio condition

```text
forall epsilon,delta>0, exists 0<h<delta,
  Omega(h)<=epsilon*h,
```

for the declared combined cost `Omega=omega+chi`.  Its converse is stated only
for a positive **vanishing** schedule with divergent scale sum and summable
declared cost.  This matches
`IsOperationallySublinearCost` and
`isOperationallySublinearCost_iff_exists_vanishing_schedule` in
`MathUE/SublinearCostSchedule.lean`; no necessity for nonvanishing iterations
or smaller undeclared true costs remains.

The radius induction is also correct with

```text
budget=min(eta,rho(x_0)/4),
cap=rho(x_0)/2.
```

The checked schedule keeps every `h_k<cap`, total `chi` loss is at most the
combined budget, and consequently every reached radius stays at least
`3*rho(x_0)/4>h_k`.  The seam and two-label arguments continue to match
`QuittingBudgetStablePacketSystem.exists_chronologicalDebtShadowingCertificate_of_seed`.

The former formalization-status header has been removed.  I found no surviving
`liminf Omega(h)/h` equivalence or power-law claim in the theorem statement.

## Required repairs

1. The boundary subsection **Positive superlinear test** still says that “the
   harmonic calculation above” proves the power-law specialization.  That
   calculation was removed, so the reference is false, and this is precisely
   the optional power-law claim meant to be removed or kept explicitly outside
   the narrow packet.  Delete this subsection, or add a self-contained proof
   and explicitly label it an ordinary optional corollary not used by the
   packet theorem.

2. The **Linear scalar obstruction** correctly says that separate conditions

   ```text
   liminf omega(h)/h=0,
   liminf chi(h)/h=0
   ```

   do not control their sum, but it gives no falsifier.  Either remove the
   optional `liminf` sentence or add the exact two-function example.  One
   minimal example for `0<h<1` is

   ```text
   A={2^(-2*n): n>=1},
   omega(h)=0 if h in A, else h,
   chi(h)=h if h in A, else 0.
   ```

   Each separate ratio has liminf zero, while
   `(omega(h)+chi(h))/h=1` for every `h`, so the combined operational condition
   fails.

After either deletion or these explicit repairs, I see no remaining scalar
overclaim in the repaired core.  The local atom/reset producer, small-debt
seed, and actual-source adapter remain correctly excluded.

## Final pass after repair

The author subsequently deleted both optional remnants.  The only retained
boundary tests are now zero declared cost and the exact nonvanishing-schedule
counterexample `Omega(1)=0`, `Omega(h)=h` for positive `h != 1`.  Those tests
are correct and directly audit the theorem's checked quantifiers.  No
formalization-status header, `liminf` formulation, power-law corollary,
shrinking-radius example, or broad necessity claim remains.

Final verdict: `VALID REPAIRED PACKET; NO REMAINING OBJECTION`.
