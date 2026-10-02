# Fourth review: exact five-player odd-cycle adapter

Reviewer: `CODEX_CEDAR`

Note reviewed: `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`

Scope: only the `M5/r5` construction in Section 21, on the box
`[1/8,3/4]^I` with `K=64`.  I did not review Proposition 12 or Section 22.

Verdict: `VALID_ORDINARY_MATHEMATICS_WITH_EXACT_NOVELTY_SCOPE`.  The face
bounds, normal-core classification, absence of sure-exit sets, and failure of
every instant no-join owner all check.  The literal reward table is therefore
a valid actual-data witness for the already reviewed Proposition 10, and it
is outside the named sure-exit, instant-punishment, symmetric, circulant,
collider, and three-player producers.  This establishes novelty relative to
those named branches, not an absolute statement that no other conditional
producer could cover the table.  The adapter for the literal table and
Proposition 10 remain ordinary mathematics, not checked Lean declarations.

## Claim checked

There are five players ordered `(0,1,2,a,b)`.  The normalized singleton
matrix is

```text
M5 = [ 0 -1  2  1  1
       2  0 -1  1  1
      -1  2  0  1  1
       1  1  1  0  1
       1  1  1  1  0 ].
```

Singleton rewards are `r5({j})_i=1+M5_(i,j)`.  For the blocker permutation

`0 -> 1 -> 2 -> a -> b -> 0`,

and every coalition `S` of size at least two, an outsider receives `1`, a
member whose blocker is present receives `-63`, and a member whose blocker is
absent receives `65`.

## Exact face arithmetic

Fix player `i`, write `q=p_(pi(i))`, and let `z` be the probability that at
least one of the other three opponents Quits.  On `[1/8,3/4]^I`,

`1-(7/8)^3 = 169/512 <= z <= 1-(1/4)^3 = 63/64`.

The singleton event contributes `1`; a nonempty-background event with absent
blocker contributes `65`; and a present blocker contributes `-63`.  Therefore

`R_i = 1 + 64((1-q)z-q)`.

The expression is increasing in `z`.  On the lower blocker face,

`R_i-1 >= 64((7/8)(169/512)-1/8) = 671/64`.

On the upper blocker face,

`R_i-1 <= 64((1/4)(63/64)-3/4) = -129/4`.

If `i` Continues, an opponent singleton gives a reward in `[0,3]`, while a
multi-quitter coalition gives the outsider reward `1`.  Since opponent
absorption has positive probability, its conditional value `V_i` is a convex
combination of these numbers, so `-1 <= V_i-1 <= 2`.  Consequently

```text
q=1/8:  G_i=R_i-V_i >= 671/64-2 = 543/64 > 0,
q=3/4:  G_i=R_i-V_i <= -129/4+1 = -125/4 < 0.
```

These are uniform bounds on the whole corresponding faces, not just corner
or numerical-root evidence.  I also exhaustively checked the rational corner
values: the extrema of `z` and of the two displayed `R_i-1` bounds agree with
the formulas above.

## Normalized matrix and normal core

Every diagonal entry of `M5` is zero, hence `r5({i})_i=1`, and

`r5({j})_i-r5({i})_i=M5_(i,j)`.

Thus the normalized singleton matrix is exactly `M5`.  This equality is an
ordinary adapter calculation for the displayed table; there is no named Lean
declaration defining `r5` and proving this equality.

The normality recursion is the literal `normalLayer` from
`UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean`.  Players
`a,b` leave at layer one because their rows have no distinct nonpositive
entry.  Players `0,1,2` each retain a `-1` witness inside `{0,1,2}` and hence
remain at every later layer.  Therefore the exact normal core is
`{0,1,2}`, and its principal matrix is the displayed `cyclicMatrix`.

The named checked facts `cyclicMatrix_standardQ` and
`cyclicMatrix_noHomogeneous`, together with standard reindexing of the
three-element core, establish the two matrix properties required by
`StandardQMatrixSide`.  The relevant checked reindexing interfaces are
`isStandardQMatrix_reindexMatrix` and
`singletonLCPFeasible_reindexMatrix_iff`; all occur in the LCP files imported
by
`UniformEquilibrium/Quitting/Classification/LCP/StandardQSideExample.lean`.
The literal `r5`-to-core equivalence is again not itself formalized.

## No sure-exit coalition

The empty coalition fails by `isQuittingSureExitSet_empty_iff`
(`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`), because every own solo
reward is `1>0`.

For a nonempty coalition `S`, the sure-exit inequalities force exact blocker
alternation

`i in S  iff  pi(i) notin S`.

For `|S|>=3`, a member who leaves receives `1`, while its current payoff is
`65` or `-63`; an outsider currently receives `1`, while joining gives `65`
or `-63`.  The inequalities therefore hold exactly in the claimed two
blocker cases.  If `|S|=2`, the member's leaving payoff is a singleton reward
in `[0,3]`, so the same strict comparisons apply.  If `S={o}`, the member's
`0<=1` inequality holds, but any outsider other than the unique predecessor
of `o` can join for `65` from a singleton payoff at most `3`; thus the same
alternation condition still fails.  Exact alternation cannot close around an
odd five-cycle.  Hence no nonempty sure-exit set exists.  Direct enumeration
of all `32` coalitions gave no exception.

## No instant no-join owner

Fix any proposed solo owner `o`.  Choose an outsider `j` that is not the
unique predecessor of `o`; then `pi(j)` is absent from `{o,j}`.  Player `j`
therefore receives `65` on joining, whereas its payoff at the owner singleton
is `1+M5_(j,o)<=3`.  Thus `IsQuittingInstantNoJoin r5 o` fails for every
owner.  By the checked necessity theorem
`isQuittingInstantNoJoin_of_works`
(`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`), no owner
supports `QuittingInstantPunishmentWorks`.  This conclusion does not rely on
an uncomputed punishment value.

## Named-producer overlap and novelty

The remaining exclusions can be witnessed exactly.

* The table is not cardinal/permutation symmetric: the singleton coalitions
  `{1}` and `{0}` have the same cardinality and receivers `0` and `1` are both
  outsiders, but their rewards are respectively `0` and `3`.  Hence the
  hypotheses of the symmetric producers in
  `UniformEquilibrium/Quitting/Classification/SymmetricQuittingGame.lean`
  fail.
* Its normalized singleton matrix is not circulant under any relabelling.
  Rows `0,1,2` have off-diagonal multiset `{-1,1,1,2}`, while rows `a,b` have
  `{1,1,1,1}`.  Simultaneous reindexing preserves row multisets, whereas a
  row-circulant matrix has the same row multiset everywhere.  Thus
  `HasCirculantSoloMatrix` from
  `UniformEquilibrium/Quitting/Classification/Circulant/Trichotomy.lean`
  cannot hold.
* It is not a literal `colliderReward`: every outsider of a multi-quitter
  coalition receives `1` in `r5`, whereas `colliderReward` assigns such an
  outsider `0` by definition in
  `UniformEquilibrium/Quitting/Classification/Circulant/ColliderCompletion.lean`.
* The unconditional theorem
  `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`)
  is a three-player theorem; this table has five players.

The checked LCP gate recognizes only that the literal normalized data lie on
the standard-Q side; it does not construct the stationary root from those
singleton rows.  The strict face calculation uses the actual multi-quitter
rows and supplies precisely the missing producer datum.  Therefore `r5` is a
strict actual-reward-table novelty witness for Proposition 10 relative to the
named branches above.  It does not prove that Proposition 10 is globally new
relative to every theorem or every possible conditional specialization, and
it carries no `L` or production `A` seal until its literal adapter is checked
in Lean.  No export action is justified by this review alone.
