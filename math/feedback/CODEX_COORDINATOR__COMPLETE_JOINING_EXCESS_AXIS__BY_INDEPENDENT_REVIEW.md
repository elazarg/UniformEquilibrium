# Complete joining-excess axis: final independent review

**PASS. No corrections required.**

Exact reviewed artifact: `math/notes/CODEX_COORDINATOR__COMPLETE_JOINING_EXCESS_AXIS.md`.
SHA-256: `a9dbb0ae700fd4972e7faaa4dd5bd73d60b2c1810359d0ec314ff15ef100eac4`.

The frozen dependencies read were:

- `math/exports/JOINT_QUITTING_NEGATIVE_VALUE_UNIFORM_EQUILIBRIUM.md`, SHA-256 `c39fc225b49d09609329364b515ff1a7ba816acf1e72d1a47d6265f961e1f772`.
- `math/exports/CORE_FREE_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`, SHA-256 `58ddd1d47cb6b0fe7bf86bb6a9c425a148e3ba8a829c8acf1c34de93dbbcadc5`.

The rational parametrization covers every eta>0 exactly once. Exact symbolic arithmetic verifies the cubic identity, negative eta derivative, endpoint limits, and common guards. The cubic's eta coefficient is `b*(219b^2-1030b-1160)/290`, strictly negative on `(0,1/3)`, so the parametrized root is simple. The first branch `j>100T/3` satisfies every finite-core hypothesis, including the prefix bounds and its already established resonance gluing. The complementary branch `j<=100T/3` satisfies the direct wash/no-wash criterion, including equality. Thus no interval or boundary is omitted. Taking a finite positive maximum of the applicable K bounds supplies the stated `M_eta*(1+|p|)` quantifier for every real p.

The common first prefix guard also follows explicitly from `X1-b/10=-(b+30)*(109b-435)/(10*(7629b+2030))>0`. The ratios `x/((1-x)b)=29/(190b+29)<=1` and `x/(1-x)=29b/(190b+29)<=1` prove the stated p-independent uniform tail bound. Exact substitution verifies both the tail endpoint and its negative transition margin. Since `j'>0` and `T'<0`, and the endpoint transition values are `-1777/42` and `245/1076`, there is exactly one algebraic transition. The example and stationary-free comparison are correctly restricted to the complete canonical table.

The d-sign extension is valid: d enters the strategic equations only through the displayed joint-row3 expression and its algebraic elimination. At the limiting core its x derivative is `-D`; retaining `D>0`, root simplicity, and the other stated hypotheses supplies the same implicit-function argument. The core, wash, final return, and resonance proof use no sign of d.

The topology caveat also passes an independent exact-arithmetic subcheck against the referenced residual partition: witness3 has determinant 7, mixed inverse with positive columns 0,1,3, negative entries in every column, R0 degree +1, and no inverse-positive principal triple. Its sole opposite-sign reciprocal pair is 03, whereas the architecture requires two distinct such pairs. All relabelings therefore fail the singleton prerequisites. The relevant declarations in `NonnegativeInverseCriterion.lean` explicitly require negative determinant, so the note correctly avoids promoting positive inverse alone to the all-completion theorem.

Scope: review of this exact compact note and its use of the two frozen exports, with targeted symbolic/rational checks and independent topology verification. Ordinary mathematics only; no Lean build or Lean-check claim. No tracked edits or Git operations were performed.
