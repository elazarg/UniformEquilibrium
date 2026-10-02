# Review of Section 12

Reviewer: `CODEX_RAMSEY`

Claim reviewed: a literal strict three-cycle in the quantitative full-support
hard residual has the exact trichotomy: a positive unique-outsider helper, a
negative-determinant literal hard cyclic principal, or a nonnegative-
determinant projective literal cycle forcing every proper hard principal to
contain the unique outsider.  The note also maps the outsider to the marked
owner/collider positions.

## Verdict

**PASS** in the explicitly finite/noncompiler scope.

## Audit

Let the cycle be `a->b->d->a`, let `C={a,b,d}`, and let `x` be its unique
Fin-4 complement.  With the repository matrix convention the three edges are
exactly

```text
M(b,a), M(d,b), M(a,d) <= -gamma < 0.
```

If every `M(i,x)` for `i in C` is nonpositive, full packet support and the
nonnegative row average force the three reverse entries to be strictly
positive.  For example, row `a` has a strictly negative positive-mass `d`
term, zero diagonal, and nonpositive `x` term, so its only remaining `b` term
must be positive.  Rotation proves the other two.  No unmentioned lower bound
on packet mass is needed.

If some `M(i,x)>0`, the predecessor of `i` on the literal cycle supplies the
internal negative owner column, while `C` has complement `{x}`.  These are
exactly the fields of `FinFourHardCardThreeExternalHelper reward C`, proving
arm 1 on the same labels.

Otherwise the six internal signs form one strict three-cycle orientation.  In
that chamber the checked classification gives:

```text
homogeneous simplex solution  <-> determinant=0,
standard Q and no homogeneous <-> determinant>0,
projective Q <-> standard Q or homogeneous.
```

Thus determinant `<0` excludes both homogeneous and standard-Q branches, so
the literal principal `C` is nonprojective and its cyclic-boundary determinant
is strictly negative.  Determinant `=0` makes `C` homogeneous/projective;
determinant `>0` makes it standard-Q/projective.  The negative/nonnegative
split and the prior outside-helper split are exhaustive and disjoint.

In the nonnegative arm, any hard triple omitting `x` would equal `C`, a
contradiction.  Hence every hard triple contains `x` and exactly two cycle
labels.  A hard pair omitting `x` would lie inside `C`; each such pair has one
negative and one positive reciprocal entry in the strict orientation.  But a
nonprojective zero-diagonal pair has both reciprocal entries strictly
negative, by the checked pair classification.  Hence every hard pair also
contains `x`, and cardinality makes it `{x,y}` for exactly one `y in C`.

The marked-role mapping is exact.  In every `oneToThree_*` constructor the
root/collision owner is the unique vertex outside the three-cycle, hence is
`x`.  In `rootedThree_outside`, the marker/collider is the unique outsider,
hence is `x`.  In `rootedThree_first` and `rootedThree_second`, both root and
marker lie on `C`.  The stated arm-by-arm owner/collider incidences follow
without enumerating extra annotations.

## Scope

The result aligns labels inside the finite matrix/principal dispatch.  Its
outputs remain `FinFourHardCardThreeExternalHelper`,
`FinFourHardCardThreeCyclicBoundary`, or a hard principal known to contain
`x`.  None is a Bellman root, reached chronology, all-behavior strategy,
contradiction, or well-founded semantic decrease.  The note correctly stops
instead of treating the finite trichotomy as a compiler.
