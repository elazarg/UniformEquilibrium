# Review of Section 37: nonprojective principal cardinality

Reviewer: `CODEX_RAMSEY`

## Claim reviewed

I independently reviewed Theorem 37.1 and Corollary 37.2 in
`notes/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`.

For a terminal exploitability witness on `Fin 4`, the claim combines the
checked projective-Q-bar Snell consumer, projective Q on the recursive normal
core, the checked full-core theorem, and the Section 36 full-support packet.
It concludes that the same normalized solo matrix has a nonprojective
principal face of cardinality exactly two or three.

## Verdict

**PASS.**  The Q-bar negation, full-principal exclusion, singleton exclusion,
same-table composition, and claimed cardinality alternative are correct.  The
result is a strict finite refinement of the full-support/full-core residual;
it does not treat the selected principal as packet support or as a quitting
subgame.

## Projective-Q-bar and Snell exclusion

The witness's checked `not_exists_uniformEquilibriumPayoff` theorem rules out
every uniform-equilibrium payoff for the same reward table.  The checked
consumer

```text
exists_uniformEquilibriumPayoff_of_projectiveQBar_snell
```

has hypothesis

```text
IsProjectiveQBarMatrix (normalizedSoloMatrix reward)
```

and an unrestricted-behavior uniform-payoff conclusion.  Therefore the
ambient normalized solo matrix `M` is not projective Q-bar.

By the literal definition

```text
IsProjectiveQBarMatrix M
  = forall nonempty K, IsProjectiveQMatrix(principalMatrix M K),
```

its negation exposes a nonempty finite set `K` with a nonprojective principal.
This is also exactly the checked helper
`exists_nonprojectivePrincipalMatrix_of_not_projectiveQBar`; no choice or
closedness assumption is hidden.

## Excluding the full principal

The checked theorem

```text
projectiveQ_of_not_exists_uniformEquilibriumPayoff
```

makes the matrix on the recursive normal core projective Q.  The separate
checked four-player theorem gives

```text
normalCore M=univ
```

under the same no-uniform hypothesis.  The normal-core subtype is therefore
canonically equivalent to `Fin 4`, and `normalizedNormalPlayerMatrix` is the
reindexing of the full ambient matrix along that equivalence.  Projective Q is
invariant under this reindexing.  Hence `M` itself is projective Q.

If the selected `K` had cardinality four, finite-set extensionality on
`Fin 4` would give `K=univ`; its principal matrix would be the same full
matrix up to the canonical subtype reindexing, contradicting its selected
nonprojectivity.  Thus `K.card<4`.  No projective-Q property is inferred for
arbitrary proper principals.

## Excluding singleton principals

For `K={i}`, the principal matrix is the one-by-one zero matrix because

```text
normalizedSoloMatrix_diagonal reward i=0.
```

For every projective right-hand side `q`, define a projective solution with

```text
cemetery=0,
singleton(i)=1.
```

The total mass is one.  The unique residual is

```text
0*q(i)+1*0=0,
```

so residual nonnegativity and complementarity both hold.  Therefore every
singleton zero principal is projective Q.  The note correctly uses the
zero-cemetery homogeneous solution, not the cemetery-only solution that would
require a nonnegative right-hand side.

Since `K` is nonempty, has cardinality below four, and is not a singleton,
its cardinality is exactly two or three.

## Same-table packet composition and analytic waist

Theorem 36.2 independently supplies, from the same witness and reward table,
a quantitative full-support normalized singleton packet, full recursive
normal core, and punishment normality of every player.  The selected
nonprojective face is additional finite matrix data; its set `K` is not
identified with packet support and need not inherit packet mass.

For an arbitrary `Fin 4` game, split on uniform-payoff existence.  In the
negative branch the checked terminal-gap equivalence supplies a witness, so
the preceding construction gives the second arm of (37.4).  Thus the amended
analytic-waist residual is genuinely narrower than an unstructured
full-support matrix: it carries a proper nonprojective principal of size two
or three.

## Boundary and subsumption audit

The paired-singleton matrix is an exact size-two boundary test.  Its checked
Q-bar failure already occurs on the cross pair `{0,2}`, while the full matrix
is standard Q and has full normal core.  Its checked period-two uniform payoff
correctly prevents the example from being advertised as a terminal-witness
instance.

At the opposite boundary, every singleton principal is projective Q solely
from the zero diagonal, so cardinality one cannot be retained as a residual.

The nearby theorem
`PunishmentNormalResidualHardClass.exists_ambient_allNormal_nonprojectivePrincipal`
does produce a nonempty ambient nonprojective principal, but does not perform
the `Fin 4` exclusions of cardinalities one and four.  The full-principal
exclusion needs both checked projective Q on the normal-core matrix and the
full-core identity.  A narrow source search found no existing theorem with the
resulting `card=2 or card=3` conclusion.

The result is finite LCP structure, not a new strategy compiler.  It does not
claim that the principal face is a counterexample subgame, that it inherits
the full packet, or that existing support-two/support-three packet compilers
apply to it.  All-behavior content is confined to the checked Q-bar Snell
consumer and the already reviewed Section 36 terminal-gap construction.
