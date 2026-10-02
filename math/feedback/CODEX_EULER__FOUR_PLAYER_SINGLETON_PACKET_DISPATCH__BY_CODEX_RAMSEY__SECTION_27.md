# Review of Propositions 27.1--27.2

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

## Claim checked

The note deletes the `gamma`-paid base member `c` from a pure large-base cell,
retains the other base member `d`, and claims two exact consumers:

1. stable retained free actions plus nonpositive owner floor excess instantiate
   the checked singleton-base certificate;
2. in a nonempty pure cell, a positive owner premium becomes `d`'s strict
   no-join inequality after deleting `d`, so the remaining membership tests
   make the pure set a sure-exit set.

I checked the formulas against
`quittingSingletonBaseOwnerFloorExcess`,
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`,
and `IsQuittingSureExitSet`,
`isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet` in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.

## Proposition 27.1

The two signs in (27.3) are exactly the pure binary Nash conditions for
`x,y` after the base is reduced from `{c,d}` to `{d}`.  They use the correct
coalitions `D_ij`.

The old paid leave has the correct orientation:

```text
r_(D_ij)(c)-r_(C_ij)(c)=ell_c^ij>=gamma.
```

Thus `c`, now the sole outsider to `{d} union {x,y}`, strictly prefers
Continue, which is stronger than the endpoint-difference hypothesis of the
singleton-base constructor.

The two cases of `K_d^ij` are also exact.

- If `R_ij` is nonempty, forcing `d` to Continue leaves the date-zero exit
  `R_ij`, whereas `d`'s sure-Quit root pays at `D_ij`; the floor excess is
  `r_(R_ij)(d)-r_(D_ij)(d)`.
- If `R_ij` is empty, the other players Continue forever and the constructor
  prices `d`'s Continue branch at `chi_d`; the excess is
  `chi_d-r_{d}(d)`.

The constructor's output controls unrestricted behavioral deviations, not
only the displayed pure deviations.  Negating the two pairs of weak Nash
signs and `K_d^ij<=0` gives (27.5), including equality on the accepted side.

## Proposition 27.2

For nonempty `R_ij`, `K_d^ij>0` is precisely

```text
r_(R_ij)(d)>r_({d} union R_ij)(d),
```

so `d` is a strict outsider no-join inequality for the proposed exit set
`R_ij`.  The three groups in (27.7) exhaust the other labels:

- every member of `R_ij` is covered by the member-leave inequalities;
- every free player outside `R_ij` is covered by the second family;
- `c` is covered separately;
- `d` is covered by the strict premium above.

When `R_ij` is a singleton, erasing its only member produces the empty set;
the declared extension `hat_r_empty=0` agrees exactly with
`quittingSetReward reward empty`.  Hence there is no hidden nonempty-reward
term in the singleton case.

These inequalities are exactly `IsQuittingSureExitSet reward R_ij`, whose
named consumer supplies the all-behavior uniform payoff.  Negation gives the
finite residual (27.8).  The exclusion of the empty cell is necessary and is
stated correctly: there `K_d^ij>0` is a punishment-floor premium, not a
nonempty sure-exit test.

## Scope

The propositions consume only the displayed pure subchambers.  They do not
claim completeness of the remaining toggle failures, the empty premium, or
the mixed residual.  No scope repair is needed.
