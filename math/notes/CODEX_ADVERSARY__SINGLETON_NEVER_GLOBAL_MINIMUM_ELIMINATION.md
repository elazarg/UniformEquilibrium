# Global minimum eliminates the singleton/Never hull chamber

Author: `CODEX_ADVERSARY`  
Date: 2026-08-31  
Status: **proved ordinary mathematics from named checked declarations; no Lean file changed**

## 1. Claim audited

Let

- `s` be a globally minimum terminal-semantic pair with
  `D(s)>0`;
- `origin=(s,mu)` be a point of the joint terminal-semantic/law carrier;
- `z` minimize total debt on the law-tight cap--Nash saturation hull based at
  `origin`; and
- `o` be the owner supplied by the singleton/Never chamber at `z`.

The proposed elimination is

\[
 z.\mathrm{cap}_o=r_o(\{o\})
 \quad\Longrightarrow\quad
 D(z)\le z.\mathrm{cap}_o-r_o(\{o\})=0,
\]

contradicting the positive global minimum.

**Verdict: valid.**  The only nontrivial step is promoting the hull minimum
`z` to a global terminal-semantic minimizer.  That promotion follows exactly
because the hull contains its origin and is a subset of the joint carrier.
In fact one gets the stronger uniform moat

\[
 z.\mathrm{cap}_i-r_i(\{i\})\ge D(s)>0
 \qquad\text{for every player }i.
\tag{1.1}
\]

Thus no coordinate at `z` can bind its singleton reward, independently of
the singleton/Never law description.

## 2. Exact globality transfer

Write `H=quittingLawTightCapNashSaturationHull reward origin`.  Assume:

1. `horigin : origin` belongs to the joint carrier;
2. `hglobal : D(s)<=D(y)` for every semantic carrier point `y`;
3. `origin.1=s`; and
4. `hz : IsQuittingLawTightCapNashSaturationMinimum reward origin z`.

The checked declaration
`quittingLawTightCapNashSaturationHull_origin_mem` gives

\[
 origin\in H.
\tag{2.1}
\]

Applying `hz.debt_le` to (2.1) gives

\[
 D(z)\le D(s).
\tag{2.2}
\]

On the other hand, `hz.mem` and
`quittingLawTightCapNashSaturationHull_subset_carrier reward origin horigin`
give that `z` is in the joint carrier.  The first-coordinate projection is
therefore in the semantic carrier by
`terminalSemanticLawCarrier_fst_mem_carrier`.  Global minimality of `s`
gives

\[
 D(s)\le D(z).
\tag{2.3}
\]

Hence

\[
 D(z)=D(s)>0.
\tag{2.4}
\]

For every semantic carrier point `y`, combine `D(z)=D(s)` with `hglobal`:

\[
 D(z)\le D(y).
\tag{2.5}
\]

This is precisely the global-minimum hypothesis required by the singleton
margin theorem.  Notice that no convexity, law-fibre comparison, actual
realization, or chronology is used.

## 3. Audit of `minimumTerminalSemantic_singletonMargin`

The exact declaration in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`
is:

```text
minimumTerminalSemantic_singletonMargin
    (pair)
    (hpair : pair in semantic carrier)
    (hminimum : for every carrier candidate,
       D(pair) <= D(candidate))
    (hpositive : 0 < D(pair))
    (who) :
  D(pair) <= pair.cap(who) - reward({who})(who).
```

The direction is exactly the proposed direction: **total minimum debt is a
lower bound on cap minus singleton reward**.  It is not merely the elementary
inequality `singleton<=cap`, and it is not restricted to a selected support
coordinate.

Apply it to `pair=z.1`, using:

- joint-carrier membership of `z` projected to semantic-carrier membership;
- (2.5) for its global minimum hypothesis; and
- (2.4) for positivity.

For every player `i` this gives

\[
 D(s)=D(z)\le z.\mathrm{cap}_i-r_i(\{i\}),
\tag{3.1}
\]

which proves (1.1).

## 4. Contradiction with the chamber field

`QuittingSingletonNeverBindingCycleChamber reward z` contains the field

```text
cap_binding :
  z.1.2 support.owner =
    reward (quittingSingletonTerminal support.owner) support.owner
```

Take `i=support.owner` in (3.1).  The right side becomes zero, so

\[
 0<D(s)\le0,
\]

a contradiction.  None of the chamber's support, Never-mass, uniqueness, or
collision-cycle fields is needed.  Exact singleton binding alone is
incompatible with global positive minimality.

## 5. Fin4 source consequence

The proof of
`finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber` already has all
the required data before invoking the three-chamber classification:

- `origin` is in the joint carrier (`horigin`);
- `hsourceMinimum` says `origin.1` is globally minimum in the semantic
  carrier;
- `hsourcePositive` says its total debt is positive; and
- `hminimum` is the law-tight hull minimum.

Therefore the theorem's third disjunct

```text
Nonempty (QuittingSingletonNeverBindingCycleChamber reward minimum)
```

is impossible.  Its honest conjecture-facing conclusion strengthens to the
two-arm alternative

\[
 \boxed{
   (\forall i,\ d_i(z)>0)
   \quad\lor\quad
   \text{a reset-rigid same-law return}
 }.
\tag{5.1}
\]

This does not consume either surviving arm and does not prove a uniform
equilibrium.  It does remove the singleton/Never binding cycle from the
actual positive-minimum Fin4 gate.

The same argument is dimension-free.  Fin4 is used only by the upstream
source theorem that supplies the globally positive origin and positive
finite atom.

## 6. Counterexample search and why the known regression does not apply

The rational singleton/Never regression in Section 10 of
[`CODEX_SOURCE_GATE__SATURATION_FACE_UE_REGRESSION_AND_MARKED_TWO_PORT_AUDIT.md`](CODEX_SOURCE_GATE__SATURATION_FACE_UE_REGRESSION_AND_MARKED_TWO_PORT_AUDIT.md)
has a singleton canonical hull with debt `6/5` and an owner whose cap equals
its singleton reward.  It is a valid regression against elimination from
**hull minimality alone**.

It does not satisfy the present hypotheses.  Section 10.6 constructs an
explicit stationary profile and checks it against unrestricted behavioral
deviations; its prescribed payoff equals its cap, so its semantic carrier
point has total debt zero.  The displayed hull minimum of debt `6/5` is
therefore not a global terminal-semantic minimum.  Accordingly,
`minimumTerminalSemantic_singletonMargin` cannot be applied to it.  This is
exactly the distinction used in (2.3).

A counterexample to the present elimination would have to satisfy all four
conditions simultaneously:

1. `z` belongs to the semantic carrier;
2. `z` is globally debt-minimal;
3. `D(z)>0`; and
4. one cap coordinate equals its singleton reward.

The checked singleton-margin theorem rules out precisely this conjunction,
so no semantic-pair counterexample exists without falsifying that theorem.

## 7. Declarations inspected

- `minimumTerminalSemantic_singletonMargin`, in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`;
- `quittingLawTightCapNashSaturationHull_origin_mem` and
  `quittingLawTightCapNashSaturationHull_subset_carrier`, in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashSaturationHull.lean`;
- `IsQuittingLawTightCapNashSaturationMinimum.debt_le` and `mem`, in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashMinimumFace.lean`;
- `QuittingSingletonNeverBindingCycleChamber.cap_binding` and
  `lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle`, in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashStrictMinimum.lean`;
- `exists_finFourLawTightSaturationMinimum_of_no_uniformPayoff` and
  `finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber`, in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourLawTightCapNashStrictMinimum.lean`.

## 8. Minimal formalization target

The smallest new checked lemma should be dimension-free:

> If the origin's semantic pair is a positive global debt minimizer and `z`
> is a minimum of the law-tight saturation hull based at that origin, then
> `D(z)=D(origin)` and, for every player `i`,
> `D(origin)<=z.cap_i-r_i({i})`.

The Fin4 two-arm corollary then follows by eliminating
`QuittingSingletonNeverBindingCycleChamber` through its `cap_binding` field.
