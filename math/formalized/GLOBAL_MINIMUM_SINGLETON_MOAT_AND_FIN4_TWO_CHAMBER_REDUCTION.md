# Global-minimum singleton moat and Fin4 two-chamber reduction

Authors: `CODEX_SOURCE_GATE`, `CODEX_ROOT`  
Independent reviews:
[adversarial review](../feedback/CODEX_SOURCE_GATE__GLOBAL_MINIMUM_EXCLUDES_SINGLETON_NEVER_CHAMBER__BY_CODEX_ADVERSARY.md),
[strengthening review](../feedback/CODEX_SOURCE_GATE__GLOBAL_MINIMUM_EXCLUDES_SINGLETON_NEVER_CHAMBER__BY_CODEX_STRENGTHEN.md)

## Exact statement

Let (I) be a finite player set, let (r) be a finite quitting-game reward
table, and let (s,z) be joint terminal-semantic/law carrier points.  Write
(D(x)) for the total unrestricted behavioral terminal-semantic debt of the
semantic pair (x).

Assume:

1. (s) belongs to the joint terminal-semantic/law carrier;
2. (s.1) globally minimizes total debt over the complete semantic carrier;
3. (z) minimizes debt on the law-tight cap--Nash saturation hull generated
   by (s); and
4. (D(z.1)>0).

Then (z.1) is also a global semantic-debt minimizer,

\[
D(z.1)=D(s.1),
\]

and every player has the quantitative singleton moat

\[
\boxed{
D(s.1)\le z_i^{\mathrm{cap}}-r_i(\{i\}) .}
\tag{1}
\]

The same conclusion holds for every joint point on the minimum equality
level set of that hull.

Consequently, no such positive hull minimum can carry a player whose cap is
equal to that player's singleton reward.

For four players, apply this to the law-tight strict-minimum source produced
under the hypothesis that no uniform-equilibrium payoff exists.  The existing
three-arm classification

\[
\text{full debt support}
\quad\lor\quad
\text{reset-rigid same-law return}
\quad\lor\quad
\text{singleton/Never binding cycle}
\]

contracts to

\[
\boxed{
\text{full debt support}
\quad\lor\quad
\text{reset-rigid same-law return}.}
\tag{2}
\]

The third arm is impossible because its owner satisfies
(z_o^{\mathrm{cap}}=r_o(\{o\})), contradicting (1) and (D(z.1)>0).

## Conjecture-facing change

This strictly narrows the checked source-attached Fin4 law-tight
classification from three chambers to two.  The singleton/Never binding-cycle
chamber is not a live residual of a hypothetical Fin4 counterexample.

The result does not consume the full-debt or reset-rigid chambers and does not
prove four-player uniform-equilibrium existence.

## Definitions and semantic scope

All debts and caps are terminal quantities against unrestricted behavioral
unilateral deviations.  No stationarity, finite horizon, bounded stopping
time, or strategy-class restriction is introduced.  The law-tight hull is the
canonical intersection of closed joint-carrier subsets containing their
origin and closed under exact cap--Nash prefixing and same-law nonincreasing-
debt replacement.  Its minimum level set is only an equality level set; no
convexity is assumed.

The proof uses the cap coordinate, not the prescribed payoff coordinate.  It
does not use the singleton/Never law or the binding cycle after obtaining the
one equality (z_o^{\mathrm{cap}}=r_o(\{o\})).

## Source correspondence

The proof uses these checked declarations under their existing imports:

- `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`;
- `quittingLawTightCapNashSaturationHull_origin_mem` and
  `quittingLawTightCapNashSaturationHull_subset_carrier` in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashSaturationHull.lean`;
- `IsQuittingLawTightCapNashSaturationMinimum.mem`, `.debt_le`, and
  `.minimum_mem_face` in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashMinimumFace.lean`;
- `terminalSemanticLawCarrier_fst_mem_carrier`;
- `QuittingSingletonNeverBindingCycleChamber.cap_binding` and
  `lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle` in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashStrictMinimum.lean`;
- `exists_finFourHardResidual_minimumLaw_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`; and
- `finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourLawTightCapNashStrictMinimum.lean`.

The singleton-margin declaration already proves the difficult global
variational inequality (1).  The new content is the observation and proof
that the hull minimum selected by the Fin4 construction inherits global
minimality from its origin, and the resulting elimination of the third
chamber.

## Proof

### Carrier membership

Hull-minimum membership puts (z) in the saturation hull.  Since (s) is in
the joint carrier, hull inclusion in the joint carrier puts (z) there as
well.  Projection gives

\[
z.1\in\mathcal C_{mathrm{sem}}.
\tag{3}
\]

### Transfer of global minimality

The hull contains its origin (s).  Hull minimality of (z) therefore gives

\[
D(z.1)\le D(s.1).
\tag{4}
\]

Conversely, (3) permits the global-minimum inequality for (s.1) to be
applied to (z.1), giving

\[
D(s.1)\le D(z.1).
\tag{5}
\]

Thus equality holds.  For any semantic-carrier point (y),

\[
D(z.1)=D(s.1)\le D(y),
\]

so (z.1) is itself globally minimizing.  If (w) is any point of the hull
minimum level set, its defining debt equality with (z) gives the same
argument.

### Quantitative moat

Apply `minimumTerminalSemantic_singletonMargin` to (z.1), using semantic-
carrier membership, global minimality, and (D(z.1)>0).  For every player
(i), it gives

\[
D(z.1)\le z_i^{\mathrm{cap}}-r_i(\{i\}).
\]

Substitute (D(z.1)=D(s.1)) to obtain (1).

### Fin4 chamber elimination

The source proof of
`finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber` obtains exactly
the joint-carrier origin, its global minimum property, a positive hull
minimum, and the strict three-arm classification.  In the singleton/Never
arm, `cap_binding` gives

\[
z_o^{\mathrm{cap}}-r_o(\{o\})=0.
\]

Equation (1) would then imply (0<D(s.1)\le0), a contradiction.  Eliminating
that disjunct gives (2).

## Boundary tests

The global-minimum hypothesis is necessary.  There is an exact rational Fin4
regression with

\[
c=(0,0,0,1),\qquad
D=\frac65,
\]

a singleton/Never law, all singleton caps binding, unique all Continue at the
displayed cap, a four-label binding-collision cycle, punishment normality,
and a singleton canonical law-tight hull.  It also has an explicit stationary
exact behavioral equilibrium and hence a semantic carrier point of debt zero.
Its displayed (6/5)-debt point is therefore not globally minimizing.  This
is exactly the hypothesis at which the proof rejects the regression.

Reset-rigidity is not accidentally eliminated.  A reset-rigid point may have
zero debt in one coordinate while its cap remains strictly above its singleton
reward by the moat (1).  No field of that chamber asserts singleton cap
binding.

## Adapter and consumer

The actual-data adapter is the existing no-uniform-payoff Fin4 construction:
it produces the global minimum origin, the positive hull minimum, a retained
finite atom, and the three-arm strict classification in one proof.  No point,
law, atom, or source chronology is reselected.

The consumer is exact branch deletion.  Apply the dimension-free moat to the
selected hull minimum and contradict `cap_binding` in the singleton/Never
disjunct.  The output is the two-arm source-attached classification (2), with
all other source and minimum fields retained.

## Lean handoff

The smallest implementation has two declarations.

1. A generic theorem taking a joint-carrier global-minimum origin, a positive
   law-tight hull minimum (or minimum-face point), and returning

   ```text
   D(origin.1) = D(point.1)
   and
   forall i, D(origin.1) <= point.1.cap_i - r_i({i}).
   ```

2. A Fin4 theorem parallel to
   `finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber` whose final
   disjunction contains only full debt support and
   `QuittingLawTightResetRigidChamber`.

The cleanest implementation consumes the impossible third disjunct inside
the existing source proof, where its locally named `hsourceMinimum` is already
available.  No new structure field, compactness argument, or strategy
construction is required.

## Scope and nonclaims

- This is a dimension-free singleton-moat lemma and a Fin4 branch reduction,
  not a proof of uniform equilibrium.
- It does not eliminate full debt support or reset-rigid same-law return.
- It does not realize a carrier point by one behavioral profile.
- It does not turn a binding collision edge into a chronology.
- It makes no claim about hull minima whose origins are not global semantic
  minima; the exact rational regression shows why that distinction is
  essential.

## Lean formalization record

Pre-formalization packet SHA-256:
`d2b6e7628d3609ed7663ca1184a394e2ba95d2b3dce524f6d174790a72104989`.
The implementation landed in commit
`5387eb0f8bff075ec9a8debf64755c4f32587087`.

The generic origin-debt moat is in
`UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashGlobalMinimumMoat.lean`;
the canonical Fin4 source and compatibility projections are in
`UniformEquilibrium/Diagnostics/Quitting/FinFourLawTightCapNashStrictMinimum.lean`.
The checked declarations are
`lawTightCapNashMinimumFace_globalMinimumOriginDebtMoat`,
`lawTightCapNashMinimum_globalMinimumOriginDebtMoat`,
`finFour_noUniformPayoff_exists_lawTightGlobalMinimumMoatTwoChamber`,
`exists_finFourLawTightSaturationMinimum_of_no_uniformPayoff`, and
`finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber`.

Evidence seals are `M`, `L`, and `A`, with branch-local `C` only for deleting
the singleton/Never chamber.  Full debt support and reset-rigid same-law return
remain unconsumed.  No carrier point is realized by one behavioral profile;
no source chronology, collision-edge chronology, contradiction, or
uniform-equilibrium payoff is produced.  The generic theorem requires a
globally minimizing origin.
