# Round 18 Feedback on Quit-Time Compactification

Reviewer: `CODEX_GAUSS`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Sections 52--53, Propositions 49--50.  I checked the sign fork, the
use of Proposition 43, and the generated/LCP trichotomy against the exact
production stationary-family declarations.

Status:

- Proposition 49: `VALID_ORDINARY_MATHEMATICS`, with a simpler proof of the
  conjecture-facing disjunction that avoids the literature normal-player
  adapter.
- Proposition 50: `VALID_ORDINARY_MATHEMATICS`, with a substantially shorter
  proof that avoids auditing the individual LCP constructors.

No Lean or integration seal is assigned to the new propositions.

## Proposition 49

By definition,

```text
IsQuittingZeroSolo reward
  <-> for every i, r({i})_i<=0.
```

Classical negation therefore gives a player `j` with `r({j})_j>0`.  In the
paper notation, `lemma3` (`Literature/Simon2007.lean`) says an abnormal player
has strictly negative solo payoff.  Hence this positive-solo `j` is normal.
The first disjunction `(H1)` is correct, including the one-player boundary.

For `(H2)`, normality is not needed.  On the non-zero-solo branch, the same
definition-level negation already gives a positive solo player.  The audited
ledger of Proposition 43 uses the player only in
`exists_tailSurvival_lt_of_equilibrium_positiveSolo`; it never invokes
normality or the harmed-player relation.  Propositions 44--45 supply the
quantitative normalized-motion/absorption alternative after excluding the
generated and instant branches, and Proposition 42 supplies the crossing
repair.  Thus the conclusion

```text
IsQuittingZeroSolo reward or CyclicOrbitCondition reward
```

is correctly quantified.

This simpler proof of `(H2)` is worth retaining: it removes `lemma3` and the
currently unnamed literature-to-production normal/min--max adapter from the
actual necessity route.  `lemma3` is needed only if the stronger decorative
claim `(H1)` insists that the positive player be labelled normal.

The scope distinction is also correct.  A zero-solo game is consumed directly
by `quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo`
(`UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean`); it need not
have a positive cyclic orbit or a stationarily generated witness.  Hence the
disjunctive interface is appropriate for the positive-existence proof but is
not an inhabitant of a standalone necessity interface which demands a cyclic
orbit on every input.

## Proposition 50: an abstract proof

The proposed trichotomy follows from the already packaged stationary gate
without inspecting any of its internal constructors.

Apply
`hasQuittingStationaryApproximateEquilibria_or_standardQMatrixSide`
(`UniformEquilibrium/Quitting/Classification/LCP/StationaryExistence.lean`).
The standard-Q output gives the third disjunct.  In the other output, suppose
zero solo fails.  Fix a player `j` and `s>0` with

```text
s = r({j})_j.
```

For every sufficiently small `epsilon` with `0<epsilon<s`, the checked
stationary-family output supplies a root `p` whose stationary behavioral
profile is an unrestricted terminal `epsilon`-Nash profile.  Its absorption
must be positive.  Indeed, zero product absorption implies every marginal is
zero, so the profile is all Continue and pays `0`; player `j` can Quit at date
zero and receive `s>epsilon`, contradicting the Nash inequality.

Taking `epsilon` arbitrarily small therefore supplies precisely the premise
of the independently reviewed Proposition 47: stationary unrestricted
approximate equilibria with positive absorption at arbitrarily small errors.
Proposition 47 yields

```text
QuittingStationarilyGeneratedApproximateEquilibria reward.
```

This proves `(I1)`:

```text
IsQuittingZeroSolo reward
or QuittingStationarilyGeneratedApproximateEquilibria reward
or StandardQMatrixSide reward.
```

The proof handles all gate regimes uniformly and does not need to inspect:

- first-layer constructor switching;
- vertex versus nonvertex homogeneous roots;
- two-positive versus isolated ordinary non-Q endpoints; or
- positivity bounds for `laterAbnormalRoot` and `homogeneousScaledRoot`.

Those constructor claims may still be true, but they are not obligations of
Proposition 50.  The abstract stationary family already has full behavioral
strategy coverage by `IsεQuittingStationaryNash` in
`UniformEquilibrium/Quitting/Classification/LCP/StationaryEquilibrium.lean`.

## Boundary checks and exact scope

- If the player type were empty, zero solo holds vacuously, so no positive
  player is selected.
- Zero absorption is exactly all Continue for a finite product row: the
  product of Continue probabilities is one only when every marginal Quit
  probability is zero.
- A positive solo `s` defeats all Continue at every error `epsilon<s`; no
  limiting or attainment argument is needed.
- The stationary root and its positive absorption may vary with `epsilon`,
  exactly as Proposition 47 permits.
- Proposition 50 refines the corrected generated interface, but it does not
  enlarge the already proved off-standard-Q uniform-payoff class.

I found no counterexample.  The shorter proof also makes the source status
cleaner: the only new ordinary-mathematics input beyond checked production
declarations is Proposition 47 itself, already independently reviewed twice.
