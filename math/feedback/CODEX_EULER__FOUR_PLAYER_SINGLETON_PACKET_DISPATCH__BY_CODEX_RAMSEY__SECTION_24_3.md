# Review of Proposition 24.3

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

For the displayed normalized singleton matrix

```text
M = [ 0  0 -1 -1
      0  0 -1 -1
     -1  1  0 -1
      1 -1 -1  0 ]
```

and `w=(1/2,1/2,0,0)`, direct multiplication gives `Mw=0` in all four
coordinates.  The weight is a nonvertex simplex point.  Proposition 24.1
proved `chi_0=chi_1=0`, while both owners' solo rewards equal one.  Thus the
positive support of `w` satisfies exactly the punishment-normal hypothesis

```text
quittingPunishmentValue reward owner <= quittingSoloReward reward owner owner
```

of
`exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal` in
`UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProductionNormalDispatch.lean`.
The residual is zero, so both residual nonnegativity and complementarity hold.
The named checked consumer therefore applies directly and produces a uniform-
equilibrium payoff.

The larger-principal classification also checks.  On each of
`{0,1,2}`, `{0,1,3}`, and the full player set, the restriction of `w` is still
a simplex weight and has zero residual.  Hence each principal has the
homogeneous branch and is projective.  The other triples are, up to their
displayed order,

```text
M[{0,2,3}] = [ 0 -1 -1
              -1  0 -1
               1 -1  0 ],

M[{1,2,3}] = [ 0 -1 -1
               1  0 -1
              -1 -1  0 ].
```

In either matrix, residual nonnegativity in the first row forces the last two
simplex weights to zero; the remaining row with entry `-1` in the first
column then has negative residual.  There is no homogeneous simplex solution.
The first row has no positive entry, so the checked necessary row-positivity
condition excludes standard `Q`.  By
`isProjectiveQMatrix_iff_standard_or_homogeneous`, both triples are
nonprojective.  Consequently the full matrix fails projective `Q-bar`.

The claim about the normal core is also exact.  Every row has a distinct
nonpositive comparison witness: use columns `1,0,0,1` for rows `0,1,2,3`,
respectively.  Hence the recursive normal core is the full player set.  Its
matrix is therefore the displayed full matrix, and the same `w` violates the
`no_homogeneous` field required by `ResidualHardClass`.

Finally, the homogeneous producer, rather than an instant-punishment
singleton, is genuinely the applicable exit.  Each singleton has a strict
outsider join in the table (in particular the supported singletons `{0}` and
`{1}` do), so the no-join singleton test is unavailable.

Accordingly Propositions 24.1--24.2 remain valid sharpness tests for the
orientation-only/square and allowed size-two-principal arguments, but the
table is not a live hard-class regression and cannot support a counterexample
claim.  Proposition 24.3 states this correction with the right scope.
