# Review of Fin4 eventual literal inert minimum approximation

**Reviewer:** CODEX_RAMSEY  
**Date:** 2026-08-25  
**Verdict:** **PASS**, internal narrowing; no export recommendation

## Claim reviewed

I independently checked
[`CODEX_EULER__FIN4_EVENTUAL_LITERAL_INERT_MINIMUM_APPROXIMATION.md`](../notes/CODEX_EULER__FIN4_EVENTUAL_LITERAL_INERT_MINIMUM_APPROXIMATION.md).
The theorem composes the actual-profile paid-cap minimum approximation with
the literal `Fin 4` open unique-all-Continue tube.  It strengthens
`A_n,rho_n→0` to eventual exact `A_n=0` and a literal `InertStall` for every
late canonical cap port.

The composition is mathematically correct.  I found no quantifier,
orientation, or source-alignment defect.

## Same-table selection and tube projection

`exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff`
returns one minimum carrier pair `X_*=(U_*,B_*)` and one open tail tube
containing the full debt segment.  In particular the endpoint at parameter
zero is `B_*`, so `B_*` belongs to the tube.

The actual-profile approximation theorem accepts that supplied minimum pair.
Thus its profile sequence may be chosen with

```text
Sem(sigma_n) -> X_*
```

for the *same reward table and the same minimum*, not for an independently
reselected plateau.  Continuity of the second projection gives
`B(sigma_n)→B_*`; openness therefore gives eventual membership of the actual
cap coordinate in the exact-root tube.  The proof correctly uses `B`, not the
prescribed coordinate `U`.

The terminal exploitability witness is only the actual full-gap paid-row
producer.  On the Fin4 no-uniform arm its existence and positive gap are
checked, so no extra plateau/gap premise is hidden.

## Canonical prefix induction

Fix a late `sigma`.  At depth zero the semantic pair is `Sem(sigma)`.  If the
depth-`m` semantic pair is still `Sem(sigma)`, then the canonical selected cap
root is exact Nash against exactly `B(sigma)`.  Tube uniqueness identifies it
with the literal all-Continue root.

The checked equivalence

```text
quittingTerminalSemanticPrefix_allContinue_eq_self_iff_isZeroNash_at_cap
```

then returns the whole semantic pair, not only its cap coordinate.  This
closes the induction and ensures that every shifted prefix again queries the
same tail `B(sigma)` in the tube.  There is no circular use of the desired
zero-absorption conclusion.

Every selected root is therefore literally all Continue, so every summand in
the nonnegative total-absorption series is zero.  The total is exactly zero.
`QuittingPaidCapLiftedSource.inertStall_of_totalAbsorption_eq_zero` then
packages the claimed fixed semantic pairs, cap displacement, unit observer
reach, and losslessly shifted paid rows for the already selected summable
port.  This is stronger than merely applying convergence of `A_n`.

## Scope checks

The note correctly separates this carrier-density sequence from the
singleton-base reset/repair double port.  Neither construction supplies a
field identifying its source profiles with the other's profiles or locating
the double-port source pairs in the open tube.  Even such an identification
would still permit the checked double-inert alternative.

Likewise the Fin5 retained atom and paid row live in the unchanged literal
suffix law.  They do not force absorption of an outer cap-Nash root, so they
are compatible with this theorem.  The note makes no Bellman-edge, return,
rank-descent, or uniform-payoff inference from the retained row.

## Novelty and export assessment

The checked approximation currently records only
`totalAbsorption→0` and `capDisplacement→0`; the inspected open-tube theorem
does not itself mention actual paid profiles.  Their composition to eventual
literal inertness is therefore a genuine new statement.

It sharpens the named paid residual in the unfavorable direction but does not
eliminate or consume the inert stall, construct a restart, or reach an
accepted near-return output.  Under the current `exports/README.md` standard,
this is a useful internal boundary theorem rather than an export packet: its
downstream consumer is precisely the still-open problem.  I recommend keeping
the note internal until a theorem uses the eventual exact inert sequence to
produce a uniform payoff, a contradiction, or a regenerating descent.

