# Round 9 Feedback on Quit-Time Compactification

Reviewer: `CODEX_GAUSS`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Section 37, Proposition 34 only.  The canonical-orbit extraction and
the claimed future producers for either residual arm are outside this review.

Status: `VALID_ORDINARY_MATHEMATICS_WITH_ONE_WORDING_CORRECTION`

## Exact claim checked

Let `data : QuittingChargeTangentData reward`, and write

```text
mix_i = quittingSingletonMixture reward data.mass i,
solo_i = r({i})_i,
chi_i = quittingPunishmentValue reward i,
ell_i = max(solo_i,chi_i),
a_i = data.boundary_i-solo_i,
f_i = data.boundary_i-chi_i.
```

For a nonempty finite player type, Proposition 34 asserts the disjunction

```text
uniform payoff exists,
or some mix_i < ell_i,
or some data.mass_i>0 and data.tangent_i>0.
```

This is an ordinary-mathematics consequence of the checked consumer
`exists_uniformEquilibriumPayoff_of_complementarySingletonMixture`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/SingletonMixtureCompiler.lean`).
The strengthened disjunction itself is not a Lean declaration.

## Reconstruction

Assume that the second and third arms fail.  The datum supplies mass
nonnegativity and total mass one.  Failure of the second arm gives
`ell_i<=mix_i` in every coordinate.  By construction, `solo_i<=ell_i` and
`chi_i<=ell_i`, so the compiler's two floor inequalities hold.

It remains only to check active pinning.  If `data.mass_i>0`, the datum field
`positive_mass_pins_boundary` gives

```text
data.boundary_i=solo_i.
```

The datum's punishment inequality also gives `chi_i<=data.boundary_i`, hence
`ell_i=data.boundary_i`.  Therefore failure of the second arm and
`data.tangent_i=mix_i-data.boundary_i` give `data.tangent_i>=0`.  Failure of
the positive-active third arm gives `data.tangent_i<=0`, so the tangent is
zero and

```text
mix_i=data.boundary_i=solo_i.
```

This is exactly the checked compiler's active-pinning hypothesis.  Every
compiler input is now present, so the first arm follows.  The quantifier over
arbitrary finite player sets is correct: despite its path, the named compiler
itself assumes only `Fintype`, `DecidableEq`, and `Nonempty`, not cardinality
three.

The threshold reformulation also checks exactly:

```text
ell_i-data.boundary_i
 = max(solo_i-data.boundary_i,chi_i-data.boundary_i)
 = max(-a_i,-f_i)
 = -min(a_i,f_i).
```

Thus `mix_i<ell_i` if and only if
`data.tangent_i < -min(a_i,f_i)`.

## Algebraic boundary tests

For

```text
r({0})=(1,1/2), r({1})=(0,0),
mass=(1,0), boundary=(1,1), tangent=(0,-1/2),
```

the structure fields hold.  In particular,
`quittingPunishmentValue_le_max_solo` makes the minimal floor exactly
`(1,0)`.  The singleton mixture `(1,1/2)` dominates it, and the only active
coordinate has zero tangent.  The old checked sign dispatch sees a negative
passive coordinate, whereas the strengthened dispatch correctly compiles the
complementary singleton mixture.  Replacing `1/2` by `-1/2` makes the tangent
`(0,-3/2)` and the mixture falls below the second coordinate's own-solo floor
zero, so the underfunded arm is genuine.

For

```text
r({0})=(0,1), r({1})=(1,0), collision reward=(0,0),
mass=(1/2,1/2), boundary=(0,0), tangent=(1/2,1/2),
```

both active-boundary pins and punishment inequalities hold, and both active
tangents are positive.  This correctly demonstrates that the third arm is
not vacuous.  Neither table is a counterexample claim.

## Wording correction and scope

The prose says that the residual negative coordinate “exceeds both available
passive buffers.”  The exact threshold is the **minimum** of the two buffers.
Consequently a negative displacement exceeding `min(a_i,f_i)` need exceed
only the closer one, not both individually.  The accurate wording is that it
exceeds the minimal security buffer, or equivalently breaches at least one of
the own-solo and punishment-floor constraints.  This does not alter the
proposition or proof.

The result sharply removes buffered passive negative tangents from the
universal counterexample frontier.  It does not produce an exact return,
chronological shadow, or repair for either surviving arm, and the note does
not claim otherwise.  The optimized exact-D tail has a checked adapter to the
input datum via `exists_chargeTangentData_of_windows`; the analogous adapter
from the canonical punishment-floor orbit is still stated only as ordinary
finite-dimensional extraction.

## Verdict

Proposition 34 is valid ordinary mathematics with the wording correction
above.  In a hypothetical counterexample, every datum of this exact type has
either positive tangent on an occupied owner or singleton-mixture value below
the minimal coordinatewise floor `max(own solo, behavioral punishment)`.
Arbitrary negative passive drift is not itself a residual obstruction.
