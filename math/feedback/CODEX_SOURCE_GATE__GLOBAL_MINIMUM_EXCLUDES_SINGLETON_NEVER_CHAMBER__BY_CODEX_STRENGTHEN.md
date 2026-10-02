# Strengthening audit: global minimum excludes singleton/Never

**Reviewer:** `CODEX_STRENGTHEN`  
**Date:** 2026-08-31  
**Verdict:** **PASS, with a stronger generic formulation.**  The proposed
Fin4 elimination is correct.  The singleton/Never arm is impossible at the
actual no-uniform-payoff source.  The surviving reset-rigid arm is not
excluded by the same argument.

## 1. Claim checked

The note claims that the hull minimizer `z` selected from the actual Fin4
hard source is itself a positive **global** terminal-semantic debt minimizer.
Consequently the checked singleton-margin theorem gives

\[
 D(z.1)\le z.1.2(i)-r_i(\{i\})
 \qquad\text{for every player }i.                 \tag{1.1}
\]

Because `QuittingSingletonNeverBindingCycleChamber` supplies an owner `o`
with

\[
 z.1.2(o)=r_o(\{o\}),                              \tag{1.2}
\]

(1.1) contradicts `0 < D(z.1)`.

I checked the orientation, carrier projections, quantifiers, and exact
chamber field.  They match.  In particular, (1.1) concerns the displayed
**cap** coordinate `pair.2`, not the prescribed-payoff coordinate `pair.1`.

## 2. Exact transfer from source globality to hull globality

Let `origin` belong to `quittingTerminalSemanticLawCarrier reward`, assume
`origin.1` globally minimizes debt over
`quittingTerminalSemanticCarrier reward`, and let

```text
hminimum : IsQuittingLawTightCapNashSaturationMinimum
  reward origin z.
```

The checked
`quittingLawTightCapNashSaturationHull_origin_mem` puts `origin` in its
canonical hull.  Therefore `hminimum.debt_le` gives

\[
 D(z.1)\le D(origin.1).                              \tag{2.1}
\]

Conversely, `hminimum.mem`,
`quittingLawTightCapNashSaturationHull_subset_carrier`, and
`terminalSemanticLawCarrier_fst_mem_carrier` put `z.1` in the semantic
carrier.  Global minimality of `origin.1` gives

\[
 D(origin.1)\le D(z.1).                              \tag{2.2}
\]

Thus the debts are equal, and for every semantic-carrier candidate `y`,

\[
 D(z.1)=D(origin.1)\le D(y).                         \tag{2.3}
\]

If the origin debt is positive, so is the hull-minimum debt.  Hence all
hypotheses of `minimumTerminalSemantic_singletonMargin` apply literally to
`z.1`, proving the stronger uniform moat

\[
 \boxed{D(origin.1)=D(z.1)
   \le z.1.2(i)-r_i(\{i\})\quad\forall i.}           \tag{2.4}
\]

The contradiction uses only `cap_binding`; none of the singleton/Never law,
unique-root, or collision-cycle fields is needed.

## 3. Strongest generic form

The clean dimension-free theorem should not be phrased merely as exclusion
of one structure.  It should first package globality and the quantitative
moat.

> **Generic positive-global-origin moat.**  If a joint-carrier origin has
> globally minimum positive semantic debt and `z` minimizes debt on its
> law-tight cap--Nash saturation hull, then `D(z)=D(origin)`, `z.1` is a
> global semantic minimizer, and for every player `i`,
> `D(origin) <= z.cap_i - reward({i})_i`.

The same conclusion holds for **every point of the hull minimum face**:
face equality gives its debt equal to `D(z)=D(origin)`, hull containment puts
its semantic projection in the carrier, and the preceding argument applies.
Thus no minimum-face point can have a singleton-binding cap coordinate.

There is a still stronger hull-level version when combined with the
independent hull-collapse theorem proved in Section 14 of
[`CODEX_STRENGTHEN__FINITE_SOURCE_FAITHFUL_CHRONOLOGICAL_QUOTIENT_NO_GO.md`](../notes/CODEX_STRENGTHEN__FINITE_SOURCE_FAITHFUL_CHRONOLOGICAL_QUOTIENT_NO_GO.md):
for a positive global-minimum origin the entire canonical hull equals the
fixed-law global-minimum fibre.  Hence every hull point, not only a chosen
minimum-face point, has debt `D(origin)`, the same law as the origin, a unique
all-Continue exact cap root, and the moat (2.4).  This hull equality is
ordinary mathematics from the checked hull definition and debt-scaling
identity; it is not yet a named checked declaration.

For the smallest Lean handoff I recommend three declarations:

```text
IsQuittingLawTightCapNashSaturationMinimum.eq_originDebt_of_origin_globalMinimum
quittingLawTightCapNashSaturationMinimumFace_singletonMargin_of_origin_globalMinimum
lawTightStrictSaturation_fullDebt_or_resetRigid_of_origin_globalMinimum
```

The second should return the quantitative inequality for every player, not
only `not cap_binding`.  The third can invoke the existing three-way theorem
and eliminate its last arm through the quantitative lemma.

## 4. Actual Fin4 capstone

The proof of
`finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber` already obtains:

- `horigin`, joint-carrier membership;
- `hsourceMinimum`, global semantic debt minimality of `origin.1`;
- `hinf` and `horiginDebt`, which make the origin debt positive;
- the hull minimizer `minimum` and its retained positive finite atom; and
- the existing strict three-way classification at `minimum`.

Therefore the strongest immediate checked-source wrapper retains the origin,
minimum, atom, source globality, debt equality/positivity, and the moat, and
contracts the final alternative to

\[
 \boxed{
   (\forall i,\ 0<d_i(minimum.1))
   \quad\lor\quad
   \operatorname{Nonempty}
   (\mathrm{QuittingLawTightResetRigidChamber}\;\cdots).}
                                                               \tag{4.1}
\]

The two arms are mutually exclusive at the selected point because the
reset-rigid arm is produced from an owner with zero debt, whereas the first
arm says all debts are positive.  This exclusivity need not be added as a
separate API field.

This capstone is a carrier/source theorem.  It still does not behaviorally
realize the selected minimum or consume either surviving chamber.

## 5. Why reset-rigid survives

The global singleton margin constrains

\[
 z.cap_i-r_i(\{i\}),
\]

whereas reset-rigidity records a zero **semantic debt** coordinate

\[
 d_i(z)=z.cap_i-z.prescribed_i=0
\]

and positive opponent incidence, followed by a same-law returned pair.  The
two equalities are compatible: they merely imply

\[
 z.prescribed_i=z.cap_i\ge r_i(\{i\})+D(origin).
\]

The reset dispatch does not assert singleton cap binding.  Globality also
makes its returned point another point of the same global-minimum fibre, but
that is horizontal carrier motion, not a contradiction and not an executable
positive-hazard chronology.  Eliminating reset-rigid would require a new
consumer using incidence/transfer/toggle provenance, not the singleton
margin.

## 6. Checked declarations and novelty boundary

The exact declarations inspected were:

- `minimumTerminalSemantic_singletonMargin` in
  `TerminalSemanticAuxiliaryNashBudget.lean`;
- `quittingLawTightCapNashSaturationHull_origin_mem`,
  `quittingLawTightCapNashSaturationHull_subset_carrier`, and
  `quittingLawTightCapNashSaturationHull_sameLaw_of_debt_le` in
  `LawTightCapNashSaturationHull.lean`;
- `IsQuittingLawTightCapNashSaturationMinimum.mem`, `.debt_le`,
  `.minimum_mem_face`, and the definition of the minimum face in
  `LawTightCapNashMinimumFace.lean`;
- `QuittingSingletonNeverBindingCycleChamber.cap_binding` and
  `lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle` in
  `LawTightCapNashStrictMinimum.lean`;
- `exists_finFourHardResidual_minimumLaw_causalSuffixAtom` in
  `TerminalSemanticFinFourMinimumLawFiniteAtom.lean`; and
- the two current Fin4 source theorems in
  `FinFourLawTightCapNashStrictMinimum.lean`.

The branch elimination and quantitative minimum-face moat are new wrappers,
not new proofs of the underlying singleton margin.  They should strengthen
the Fin4 source packet.  They do not justify an export claiming a chamber
consumer or uniform equilibrium.
