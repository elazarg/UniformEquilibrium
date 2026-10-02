# Review of minimum regeneration, response atoms, and support orientation

Reviewer: `CODEX_STOKES`

## Claim reviewed

I audited three claims in
`notes/CODEX_RIEMANN__MINIMUM_REGENERATION_ORIENTATION_AUDIT.md`:

1. every vertex of an all-minimum literal paid cycle regenerates a complete
   minimum-law source at its own endpoint law;
2. in the common-response arm, positivity of the endpoint/source response
   atom forces the pure stopping time to occur at or after the marked row (or
   to be Never), and the response endpoint retains the full marked live-mass
   floor in one finite terminal atom; and
3. the response endpoint and its stopping-law chord with the mover-reset
   endpoint admit same-law source regeneration, while support maximality gives
   only a conditional and nonrenewable no-entry statement.

## Verdict

Claims 1 and 2 are correct.  Claim 3 is correct after one substantive notation
and hypothesis correction:

> the maximum-support hypothesis must be imposed on the mover-reset endpoint
> cluster `Y`, which is one endpoint of the stopping-law chord, not on the
> incoming/source cluster `X`.

As written, equations (15)--(16) use `X`, although equation (12) constructed
the midpoint between `Y` and the response endpoint `Z`.  There is no chord
between `X` and `Z` in the supplied data.  Replacing `X` by `Y` makes the
argument valid.  Choosing the incoming source point to have maximum support
still does not imply that `Y` has maximum support.

The source-regeneration conclusion can be strengthened from the midpoint to
the entire open stopping-law chord: every fixed mixture weight
`theta in (0,1)` gives a minimum joint point whose debt support is exactly the
union of the endpoint supports and whose routed atom has mass at least
`theta * lambda`.  The endpoint `Z` and every such chord point therefore have
honest same-law minimum-source regenerations.

None of this makes the support drop renewable from the incoming source.  The
next atlas pass may choose a new paid whole-profile cluster whose support is
unrelated to `Z`.

## Audit of the late-or-Never response claim

Let `S_n` and `E_n` be literal siblings which differ only in mover `p`'s
action at the marked date `t_n`.  Let observer `j != p` use the same pure-time
response `Q_(q_n)` in both siblings, and denote the two response profiles by
`S_n^q` and `E_n^q`.

If `q_n < t_n`, both response plays terminate no later than `q_n` whenever
the response player's action matters.  The two underlying siblings are
literal equals at every date before `t_n`; their difference at `t_n` is never
reached.  Hence `S_n^q` and `E_n^q` have identical complete terminal laws.
Every payoff-difference atom between them is zero.

In the rectangle branch of
`HasQuittingStoppingLawVanishingDebtAtomAlternative`, however, one finite
terminal satisfies a strictly positive lower bound for precisely such an
endpoint-response/source-response payoff-difference atom.  Therefore

```text
q_n = Never  or  q_n >= t_n.
```

At the marked row the response action is deterministic: Quit if `q_n=t_n`,
Continue if `q_n>t_n` or `q_n=Never`.  Since `E_n` has a pure nonsingleton
coalition there, routing by either Boolean action leaves a nonempty coalition.
Forcing `j` to Continue before `t_n` can only increase the probability of
reaching that row.  Thus the response endpoint has a finite stage atom of
mass at least the original marked live mass `L_n`, with no `1/8` loss.

There are only finitely many routed coalitions.  A subsequence freezes one
label `T`, and compactification of the actual response joint points gives a
law `nu_Z` with

```text
nu_Z(T) >= lambda.
```

This proof uses the positivity of the endpoint-response/source-response atom,
not merely the existence of a pure-time approximate response.

## Full-chord strengthening

Let the mover-reset endpoint profiles `E_n` converge jointly to `(Y,nu_Y)`
and the response endpoint profiles `R_n` converge jointly to `(Z,nu_Z)`.
Assume

```text
D(Y)=D(Z)=D_*.
```

For fixed `theta in (0,1)`, mix only observer `j`'s complete strategy in
`E_n`, with weight `theta` on the pure-time response used in `R_n`.  Call the
actual mixed profile `H_(n,theta)`.

Terminal laws are exactly affine under a one-player stopping-law mixture, so
every joint cluster `(H_theta,nu_theta)` satisfies

```text
nu_theta = (1-theta)*nu_Y + theta*nu_Z,
nu_theta(T) >= theta*lambda > 0.
```

Coordinate debt is convex under the same mixture.  Taking limits gives

```text
d_i(H_theta) <=
  (1-theta)*d_i(Y) + theta*d_i(Z).
```

Summing yields `D(H_theta) <= D_*`; global minimality gives equality.  Every
coordinate convexity gap is nonnegative and their finite sum is zero, so
equality holds coordinatewise:

```text
d_i(H_theta) =
  (1-theta)*d_i(Y) + theta*d_i(Z).
```

If the response decoder gives `d_j(Y)>=c>0` and `d_j(Z)=0`, then for every
`theta in (0,1)`:

```text
supp+(d(H_theta)) = supp+(d(Y)) union supp+(d(Z)),
supp+(d(Z)) proper-subset supp+(d(H_theta)).
```

The actual laws at `Z` and `H_theta` carry the named atom `T` with positive
mass.  Applying same-point causalization to each joint point gives complete
`FinFourMinimumAtomProducer` objects at their own laws.  This is stronger than
a bare semantic half-chord handoff.

## Correct maximal-support statement

Let `M` be the class of minimum joint semantic/law points carrying some
positive finite atom.  It is nonempty in this branch.  Since the debt support
has only finitely many possible cardinalities, choose the maximum cardinality
attained in `M`; no closedness claim about `M` is needed.

If the mover-reset endpoint `(Y,nu_Y)` itself attains this maximum and `Z` is
also minimum, then `H_theta` belongs to `M` and contains
`supp+(d(Y))` in its union support.  Maximality forces

```text
supp+(d(Z)) subseteq supp+(d(Y)).
```

The observer is positive at `Y` and zero at `Z`, hence the inclusion is
strict.  This is the valid conditional no-entry theorem.

It does not follow from maximum support of the incoming `source.point` or the
edge-source cluster `X`.  Nor does it iterate: regeneration at `Z` supplies
tails approaching `Z`, but the next forced-pair construction may select a new
whole-profile cluster `Y'` with support not contained in that of `Z`.

## Cycle closure and rank audit

For an all-minimum literal cycle, the actual profile equality at the returned
vertex implies equality of both semantic and law limits.  Each vertex law
retains its displayed pure-coalition mass and therefore admits same-law source
regeneration.  A purported rank determined only by the returned semantic
debt vector, its support, finite cycle labels, endpoint law, and table-level
hard residual cannot strictly decrease on every edge: its state is literally
the same after one cycle.

This no-go is exact but narrow.  It does not exclude a rank carrying a
nonperiodic response witness, accumulated chronology, or another datum not
returned by the horizontal loop.

## Source correspondence

The rectangle branch is the second disjunct of
`HasQuittingStoppingLawVanishingDebtAtomAlternative`, and the actual common
response is built by
`hasVanishingDebtAtomAlternative_of_endpointDebtRise`, both in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`.
Its positive atom compares the endpoint-response profile to the
source-response profile.

Stopping-law law affinity is
`quittingTerminalOutcomeMass_stoppingLawMixture_eq`; coordinate debt
convexity is `quittingTerminalSemanticDebt_stoppingLawMixture_le` in
`TerminalSemanticStoppingLawDebtConvexity.lean`.  The exact minimum-fibre
coordinate identity is already isolated as
`quittingTerminalSemanticDebt_stoppingLawMixture_eq_of_minimum_sameDebtSum`
in `TerminalSemanticStoppingLawMinimumFiberAffine.lean`.

Same-point source causalization is
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`.
The actual endpoint-law Fin4 packaging is represented by
`ConcentratedCollisionThreeRoleEndpointLaw.nonempty_finFourRegenerationOrAscent`
and `FinFourThreeRoleMinimumTargetRegeneration` in the Research source.

The new formalization obligations are the response-before-mark law-equality
lemma, the no-loss routed response atom, simultaneous compactification of the
endpoint/response/mixed profiles, and dependent packaging of the regenerated
response and chord sources.

## Export assessment

The corrected response-atom and full-chord same-law regeneration theorem is a
genuine source-provenance strengthening and is suitable for export.  The
uncorrected `X`-based maximal-support statement is not.  The exported scope
must state the maximum-support condition on `Y` and must record explicitly
that the resulting strict support drop is one-time, not renewable from the
incoming source.
