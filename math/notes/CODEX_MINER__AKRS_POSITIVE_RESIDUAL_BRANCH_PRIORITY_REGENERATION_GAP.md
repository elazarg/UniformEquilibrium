# AGKRS positive residual under branch priority: the regeneration gap

**Author:** CODEX_MINER  
**Status:** exact interface audit; no hard-residual contradiction proved  
**Date:** 2026-08-25

## 1. Question and answer

What is actually known when
`QuittingPositiveJointPrefixReachNoSureExitResidual` is consumed in
`theorem3_4_of_prioritizedSourceClosures`?  After making branch priority
literal, can the source be iterated to force S.1, S.2, well-supported S.3, or
a well-founded descent?

The current checked consumer signature supplies **no branch failures**.  A
correct hard-case reformulation may assume global failure of exactly:

* `QuittingStationaryεEquilibriumExistence` (S.1);
* `QuittingInstantPunishmentεEquilibriumExistence` (S.2); and
* `QuittingWellSupportedAbsorbingSequenceExistence`, which is checked
  equivalent to the repository's sequentially-perfect absorbing S.3.

Under those three failures my preceding full-support stationary example is
indeed excluded.  I did not derive a contradiction for the remaining hard
residual.  The strongest exact obstruction is regeneration/provenance: the
positive-reach source yields new approximate equilibria and hence regenerates
the global diffuse classification, but neither the actual punishment
endpoint nor its punishment-floor label is preserved by that regeneration.
The checked reduction can return another positive residual or a negative
exceptional-owner residual with no source relation and no decreasing finite
rank.

This note records that boundary rather than counting the regenerated case
split as progress.

## 2. Exact signature audit

The relevant call in
`Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean` has the form

```text
hpositive : forall residual :
  QuittingPositiveJointPrefixReachNoSureExitResidual reward,
  S1 reward or S2 reward or WellSupportedS3 reward
```

In the body of `theorem3_4_of_prioritizedSourceClosures`, the call occurs
after pattern matching first on

```text
fixedCorrectedBranches_or_cofinally_prioritizedResidual
```

and then on

```text
stationary_or_instant_or_wellSupported_or_noSureExit_or_negativeOwner.
```

These are ordinary, nonexclusive `Or` outputs.  Entering their diffuse and
no-sure-exit constructors does **not** add negations of the earlier
constructors to the Lean context.  Thus the comments call the capstone
priority-safe, but the literal `hpositive` argument remains unprioritized.
This is why the stationary example in
[`CODEX_MINER__AGKRS_POSITIVE_ENDPOINT_FULL_SUPPORT_STATIONARY_NOGO.md`](CODEX_MINER__AGKRS_POSITIVE_ENDPOINT_FULL_SUPPORT_STATIONARY_NOGO.md)
is a valid inhabitant of its displayed domain.

## 3. Correct hard-case formulation

For a fixed reward table abbreviate

```text
A := QuittingStationaryεEquilibriumExistence reward
B := QuittingInstantPunishmentεEquilibriumExistence reward
C := QuittingWellSupportedAbsorbingSequenceExistence reward
R := QuittingPositiveJointPrefixReachNoSureExitResidual reward.
```

Classically, the existing consumer

```text
R -> A or B or C
```

is equivalent to the hard contradiction interface

```text
R -> not A -> not B -> not C -> False.
```

The forward implication is immediate.  Conversely, decide `A`, then `B`,
then `C`; only the fourth branch invokes the hard contradiction.  Therefore
adding the three failures does not weaken the theorem-level obligation; it
states its genuine unresolved core without asking a consumer to rediscover
already available branches.

No failure of stationarily generated existence is available.  On the
contrary, the residual literally contains a diffuse stationary-prefix family.
No failure of arbitrary approximate-equilibrium existence is available
either.

### Common small-scale consequence

Each global existence predicate is a `forall positive tolerance` statement,
and its pointwise predicate is monotone in the error.  Hence `not A`, `not B`,
and `not C` give positive failure scales `a,b,c`.  At every positive

\[
             \eta\le \min(a,b,c)
\]

all three pointwise branches fail.  This is the exact quantitative priority
information available for comparing a vanishing-error source.  It supplies
no endpoint identity or source-to-source map.

## 4. What the positive source really regenerates

Let `source` be the source field of `R`, and write `family` for its
`QuittingDiffuseStationaryPrefixFamily`.  Its errors `e_n` are positive and
tend to zero; row `n` has

* a punishment within `e_n` of the labelled punishment value;
* an unrestricted root-sequence Nash inequality at error `2e_n`;
* horizon greater than one; and
* positive one-row live mass.

For any independently requested positive punishment accuracy `delta` and
equilibrium slack `epsilon`, choose `n` with

\[
                 e_n<\tfrac12\min(\delta,\epsilon).
\]

Monotonicity then turns row `n` into a witness of
`QuittingDiffuseStationarilyGeneratedApproximateEquilibriaAt reward delta`
at slack `epsilon`.  Thus the actual source itself implies

```text
QuittingDiffuseStationarilyGeneratedApproximateEquilibria reward.
```

It also implies unrestricted approximate-equilibrium existence directly via
`source.punishment_approximateEquilibriumExistence`.

Under the three global branch failures, applying the checked diffuse regime
theorem to this regenerated existence can only return

```text
another PositiveJointPrefixReachNoSureExitResidual
or a DivergentNegativeExceptionalOwnerResidual.
```

That is a logically valid regeneration, but it is not a consumer and not a
descent.

## 5. Exact provenance loss

There are two distinct losses.

### 5.1 Prefixing loses the punishment-floor endpoint class

Compactify the actually reached punishment profiles along a fixed punished
label.  This gives an eligible diagonal endpoint `E=(U,U)` with

\[
                         U_p=P_p.
\]

Prefixing by the source's finite repeated root sends `E` to another semantic
carrier point `F`.  Vanishing source Nash error can make `F` diagonal as well,
but the prefix absorption rows contribute to its `p` coordinate.  The source
only caps the reached punishment tail; it does not imply

\[
                         F_p\le P_p.
\]

Therefore `F` need not be another
`QuittingPositiveJointPrefixReachPunishmentEndpoint` with the same label.
There is no self-map of the compact endpoint set to iterate.

### 5.2 Re-extraction loses the actual profile

The reached punishment suffixes are actual unrestricted approximate
equilibria.  Reapplying a global stationarily generated extraction may choose
new roots, horizons, labels, and punishment profiles.  The current theorems
do not state that the new family is extracted from those literal suffixes,
nor that its endpoint is `E`, nor that any support/debt quantity decreases.

Consequently the implication needed for a well-founded proof,

```text
hard positive residual at E
  -> hard positive residual at E' with rank(E') < rank(E),
```

is not supplied.  Even `E'=E` is not supplied.  Compactness alone only gives
cluster points and can support recurrent or Zeno motion without a finite
rank.

## 6. Effect of the earlier example

The rational table in
`CODEX_MINER__AGKRS_POSITIVE_ENDPOINT_FULL_SUPPORT_STATIONARY_NOGO.md` has
`R`, every eligible endpoint has a positive coordinate, and S.2 fails, but
S.1 holds.  It is therefore excluded by the corrected hard assumption
`not A` and is **not** a no-go to the hard theorem.

Its surviving lesson is narrower: positivity, no-sure-exit, and positive
reach are not themselves a complexity measure.  The hard proof must use the
global failure of S.1 (and ultimately S.3), not merely re-read fields of `R`.

## 7. Honest theorem-level boundary

I found no contradiction from

```text
R and not S1 and not S2 and not WellSupportedS3.
```

The shortest remaining positive-joint obligation is therefore the
nonexistence of that exact hard residual.  A viable next theorem must provide
one of:

1. a source-faithful endpoint return preserving the punished-floor cap;
2. a literal completely absorbing support-approximately-Nash sequence built
   from the reached suffixes; or
3. a finite rank on source data that is preserved by re-extraction and drops
   strictly.

Merely deriving diffuse generated existence again, or selecting a fresh
positive/negative residual, does not advance the theorem-level closure.

## 8. Requested check

Please verify:

1. the absence of branch-negation hypotheses at the literal `hpositive` call;
2. the propositional equivalence with the triple-failure hard interface;
3. the source-family-to-diffuse-generated reconstruction at independent
   `delta,epsilon`;
4. the precise loss of the punished-floor cap under prefixing; and
5. that no checked declaration in the named lane supplies a same-endpoint or
   decreasing-rank regeneration.
