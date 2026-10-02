# Independent review of global-minimum singleton/Never elimination

Reviewer: `CODEX_ADVERSARY`  
Date: 2026-08-31  
Verdict: **PASS — the branch elimination and Fin4 two-arm reduction are mathematically valid**

## Claim checked

I independently checked
[`CODEX_SOURCE_GATE__GLOBAL_MINIMUM_EXCLUDES_SINGLETON_NEVER_CHAMBER.md`](../notes/CODEX_SOURCE_GATE__GLOBAL_MINIMUM_EXCLUDES_SINGLETON_NEVER_CHAMBER.md),
especially:

1. promotion of a law-tight hull minimum to a global semantic-debt minimum;
2. the hypotheses, direction, and coordinate of
   `minimumTerminalSemantic_singletonMargin`;
3. compatibility with the current Fin4 hard-residual source; and
4. the known rational singleton/Never hull regression.

No mathematical gap or counterexample survives the stated global-minimum
hypothesis.

## Exact rederivation

Let `origin.1=s` be globally minimum in the semantic carrier and let `z`
minimize debt on the hull based at `origin`.

- `quittingLawTightCapNashSaturationHull_origin_mem` puts `origin` in its
  hull, so hull minimality gives `D(z)<=D(s)`.
- `z.mem`, `quittingLawTightCapNashSaturationHull_subset_carrier`, and
  `terminalSemanticLawCarrier_fst_mem_carrier` put `z.1` in the semantic
  carrier, so global minimality of `s` gives `D(s)<=D(z)`.

Thus `D(z)=D(s)`, and `z.1` is itself globally minimum against every semantic
carrier candidate.

The exact checked conclusion of
`minimumTerminalSemantic_singletonMargin` is

\[
 D(z)\le z.\mathrm{cap}_i-r_i(\{i\})
\]

for every player `i`, under precisely semantic-carrier membership, global
minimality, and `D(z)>0`.  The theorem concerns the cap coordinate, not the
prescribed payoff, and its inequality points in the required direction.

At the chamber owner,
`QuittingSingletonNeverBindingCycleChamber.cap_binding` makes the right side
zero.  Hence `0<D(z)<=0`, a contradiction.  The support and collision-cycle
fields are unnecessary.

## Fin4 attachment

Inside the proof of
`finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber`, the locally
named field `hsourceMinimum` is exactly the required global semantic-carrier
minimum for `origin.1`; `horigin` supplies joint-carrier membership, and the
hull minimum and positivity are already present.  Therefore the third
disjunct cannot occur in the actual no-uniform-payoff construction.

The correct source-attached conclusion is

\[
 (\forall i,\ d_i(z)>0)
 \quad\lor\quad
 \text{a reset-rigid same-law return}.
\]

The note correctly observes that the present theorem statement does not
export `hsourceMinimum`; elimination should therefore happen inside the
source construction, or the global-minimum field must be exposed.

## Counterexample audit

The rational singleton/Never example with hull debt `6/5`, cap vector
`(0,0,0,1)`, and singleton binding is not a counterexample.  It is only a
minimum of its canonical hull and law fibre.  Its explicit stationary exact
behavioral equilibrium supplies a semantic carrier point of debt zero, so
the displayed point is not globally minimum.  This is exactly the hypothesis
needed by `minimumTerminalSemantic_singletonMargin` and exactly where the
regression exits the proof.

## Strengthening worth retaining

Before specializing to the chamber owner, the proof yields the quantitative,
dimension-free moat

\[
 z.\mathrm{cap}_i-r_i(\{i\})\ge D(s)>0
 \qquad(\forall i).
\]

I recommend making this the primary generic lemma and deriving chamber
exclusion as a one-line corollary.  It is strictly stronger and may be useful
in the two surviving arms.  This is a strengthening recommendation, not a
required correction.

## Source declarations inspected

- `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`;
- hull origin membership and carrier inclusion in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashSaturationHull.lean`;
- `IsQuittingLawTightCapNashSaturationMinimum.mem` and `.debt_le` in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashMinimumFace.lean`;
- chamber `cap_binding` and the three-arm classification in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashStrictMinimum.lean`;
- the actual Fin4 source proof in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourLawTightCapNashStrictMinimum.lean`.

**Final verdict:** PASS.  The singleton/Never arm is not live under the actual
positive global-minimum Fin4 source.
