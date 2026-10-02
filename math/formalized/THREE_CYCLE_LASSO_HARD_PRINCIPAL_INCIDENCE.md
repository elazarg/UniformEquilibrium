# Three-cycle lasso hard-principal incidence

Authors: `CODEX_EULER`

Independent review:
[theorem audit by CODEX_RAMSEY](../feedback/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY__BY_CODEX_RAMSEY__SECTION_12.md),
[whole-packet gate by CODEX_RAMSEY](../feedback/THREE_CYCLE_LASSO_HARD_PRINCIPAL_INCIDENCE__BY_CODEX_RAMSEY__PACKET_GATE.md)

This packet is exported at the user's explicit request for the reviewed finite
alignment results.  Its conclusion is finite incidence data, not a semantic
compiler or a chamber closure.

## Exact statement

Let

\[
r:\{S\subseteq \operatorname{Fin}4:S\ne\varnothing\}
  \longrightarrow \mathbb R^{\operatorname{Fin}4}
\]

be a four-player quitting reward table, let `bound : Real`, and suppose

```text
residual : FinFourQuantitativeFullSupportHardResidual r bound.
```

Put

\[
M(i,j)=r_i(\{j\})-r_i(\{i\}),
\qquad
\gamma=\texttt{residual.witness.terminalGap}>0.
\]

Suppose one of the six length-three constructors of the marked collision-
anchored preemption geometry supplies a literal directed cycle

```text
a -> b -> d -> a,
```

where an edge `i -> j` means

\[
M(j,i)\le -\gamma<0. \tag{1}
\]

Let `C={a,b,d}` and let `x` be the unique player outside `C`.  Choose any
proper hard principal supplied by `residual.residualHardClass`:

```text
K.card = 2 or K.card = 3,
not IsProjectiveQMatrix (principalMatrix M K).        (2)
```

Then the following exhaustive, disjoint proof trichotomy holds.

1. **Literal-cycle outside helper.**  Some `i in C` has `M(i,x)>0`.  On the
   same labels there is

   ```text
   Nonempty (FinFourHardCardThreeExternalHelper r C)
   ```

   whose outsider is exactly `x`.
2. **Literal hard cycle.**  Every `M(i,x)<=0` for `i in C`, and the cyclic
   determinant of the labelled principal on `C` is negative.  Then `C` is
   itself nonprojective and there is

   ```text
   Nonempty (FinFourHardCardThreeCyclicBoundary r C)
   ```

   with the stronger conclusion `cycleDeterminant<0`.
3. **Outsider-containing hard principal.**  Every `M(i,x)<=0` for `i in C`,
   and the same determinant is nonnegative.  Then `C` is projective Q and
   every `K` satisfying (2) contains `x`.  Therefore

   ```text
   K.card=2 -> K={x,y} for exactly one y in C,
   K.card=3 -> K contains x and exactly two labels of C.  (3)
   ```

The marked roles sharpen this finite alternative as follows.

- For `oneToThree_entry`, `oneToThree_second`, and `oneToThree_third`, `x`
  is the collision owner.  Thus arm 1 uses the owner as external helper, and
  every hard principal in arm 3 contains the owner.
- For `rootedThree_outside`, `x` is the collider.  Thus arm 1 uses the
  collider as external helper, and every hard principal in arm 3 contains
  the collider.
- For `rootedThree_first` and `rootedThree_second`, both owner and collider
  lie in `C`.  Arm 2 therefore makes one hard principal containing both.
  No stronger role incidence is asserted in arms 1 or 3.

## Conjecture-facing change

The maintained four-player residual supplies seventeen marked lasso
geometries.  The already checked two-cycle alignment handles the eight
length-two constructors.  This theorem is the finite alignment pass for the
six length-three constructors: each enters a same-label card-three helper,
same-label hard cyclic triple, or a proper hard principal forced to contain
the literal unique outsider.

This is an exact reduction of label freedom.  It does not eliminate those six
semantic geometries, and it does not close the full-support residual.  The
four-cycle constructors remain separate.

## Definitions and assumptions

The normalized singleton matrix is

\[
M(i,j)=r_i(\{j\})-r_i(\{i\}),
\]

so `M(i,i)=0`.  For `P subset Fin 4`, `principalMatrix M P` is the restriction
of `M` to coordinates in `P`.

A projective LCP solution for a matrix `A` and right-hand side `q` consists of
nonnegative `z_0` and `z_i` such that

\[
z_0+\sum_i z_i=1,
\qquad
0\le z_0q_i+\sum_j z_jA_{ij},
\qquad
z_i\left(z_0q_i+\sum_jz_jA_{ij}\right)=0.
\]

`IsProjectiveQMatrix A` means that such a solution exists for every `q`.
A hard principal is one for which this predicate fails.

The packet inside `residual` has masses `p_j>0` for all four labels, total
mass one, and satisfies for every row `i`

\[
0\le\sum_j p_jM(i,j). \tag{4}
\]

Only (1), positivity of all `p_j`, (4), the existence of the proper hard
principal (2), and the marked-constructor identities are used below.  No
stopping law, chronology, or mixed behavioral profile is constructed.

## Source correspondence

The actual-data source is

```text
FinFourQuantitativeFullSupportHardResidual r bound
```

from
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
It retains the terminal exploitability witness, the full normalized singleton
packet, full normal core, punishment-normality, and the nonprojective proper-
principal residual on one reward table.

The finite output structures and existing proper-principal consumers are in
`FullSupportHardPrincipalDispatch.lean`:

```text
FinFourHardCardTwoCrossing
FinFourHardCardThreeExternalHelper
FinFourHardCardThreeCyclicBoundary
FinFourQuantitativeFullSupportHardResidual.cardTwoCrossing
FinFourQuantitativeFullSupportHardResidual.cardThree_externalHelper_or_cyclicBoundary.
```

The three-coordinate matrix equivalences are in
`Quitting/Classification/LCP/ThreeByThreeZeroDiagonalQ.lean`, including
`directedCycleMatrix_hasHomogeneous_iff`, the standard-Q/determinant
classification, and the projective split from `MatrixClasses.lean`.

The maintained lasso constructors and owner/collider equations are in the
collision/preemption geometry imported by
`TwoCycleLassoHardPairAlignment.lean`.  A narrow source search found no
existing theorem aligning a literal length-three lasso with the selected hard
principal.  The new content is precisely the trichotomy and role incidence
above; the component matrix classifications and residual structures are
checked inputs.

No literature theorem is invoked.

## Proof

### 1. Complete the internal sign orientation

Assume first that no cycle row is helped by the outsider:

\[
M(a,x),M(b,x),M(d,x)\le0. \tag{5}
\]

Apply (4) to row `a`.  Its diagonal term is zero.  By the edge `d -> a`, the
`d` term is strictly negative and has positive coefficient.  The `x` term is
nonpositive.  If `M(a,b)<=0`, every term would be nonpositive and one would
be strictly negative, contradicting (4).  Hence `M(a,b)>0`.  Rotating the
argument gives

\[
M(a,b)>0,\qquad M(b,d)>0,\qquad M(d,a)>0. \tag{6}
\]

Together with (1), these are exactly one strict directed three-cycle
orientation of the principal on `C`.

If (5) fails, choose `i in C` with `M(i,x)>0`.  The predecessor of `i` in the
literal cycle gives an internal column with strictly negative entry in row
`i`, while the complement of `C` is exactly `{x}`.  These are exactly the
fields of `FinFourHardCardThreeExternalHelper r C`, proving arm 1.

### 2. Split the strict three-cycle by determinant

Under (5), relabel `C` by `Fin 3`.  The checked strict-cycle classification
states

```text
homogeneous simplex solution <-> cycleDeterminant=0,
standard Q and no homogeneous <-> 0<cycleDeterminant,
projective Q <-> standard Q or homogeneous.          (7)
```

If the determinant is negative, it is nonzero, so the homogeneous branch is
absent; it is not positive, so the standard-Q branch is absent.  The last
equivalence in (7) therefore makes the literal principal on `C`
nonprojective.  Its strict orientation and negative determinant supply
`FinFourHardCardThreeCyclicBoundary r C`, proving arm 2.

If the determinant is zero, the homogeneous branch makes `C` projective.  If
it is positive, the standard-Q branch makes `C` projective.  Thus the entire
nonnegative arm makes `C` projective.

### 3. Force the selected hard principal through the outsider

Let `K` satisfy (2) in the nonnegative-determinant arm.  If `K.card=3` and
`x notin K`, then `K=C`, contradicting projectivity of `C`.  Hence `x in K`,
and the other two labels lie in `C`.

If `K.card=2` and `x notin K`, it is a pair inside `C`.  By (1) and (6), every
such pair has one strictly negative and one strictly positive reciprocal
entry.  But a nonprojective zero-diagonal two-coordinate principal has both
reciprocal entries strictly negative: projective-Q failure excludes the
homogeneous branch, and the checked negative-column lemma forces the unique
off-diagonal entry in each column to be negative.  This contradiction gives
`x in K`; cardinality gives the first line of (3).

The outside-helper split and the negative/nonnegative determinant split are
exhaustive and disjoint.  This proves the trichotomy.

### 4. Read the marked constructor equations

For the three `oneToThree_*` constructors, the root/collision owner is the
unique vertex outside the periodic three-cycle.  For `rootedThree_outside`,
the marker/collider is that unique outsider.  For `rootedThree_first` and
`rootedThree_second`, root and marker are cycle vertices.  Substitution into
the three arms gives exactly the role statements in the theorem.  No choice
of extra annotation is made.

## Probability and behavioral-deviation audit

The proof is deterministic finite matrix algebra.  It introduces no
randomization, observation convention, conditioning, stopping-time choice,
or restricted strategy class.  Packet masses in (4) are the checked
full-support singleton lottery and are used only as positive coefficients.

Upstream, `residual.witness` is an unrestricted terminal exploitability
witness, and the marked strict-preemption inequalities have the same fixed
terminal gap `gamma`.  This theorem preserves those labels and inequalities
but draws no new behavioral conclusion from them.  In particular, its output
structures are not strategies and are not claims about bounded controllers.

## Boundary tests

1. **Positive helper boundary.**  If one `M(i,x)>0`, the proof stops in arm 1
   without imposing any determinant sign.  Replacing `>0` by `=0` moves the
   row into (5), where positive packet mass on the strictly negative
   predecessor still forces the reverse internal entry to be strictly
   positive.
2. **Zero determinant.**  At determinant zero the literal strict cycle has a
   homogeneous simplex solution and is projective Q.  It belongs to arm 3,
   not the hard-cycle arm.
3. **Negative determinant.**  A strict cycle with negative determinant has
   neither the homogeneous nor the standard-Q branch, so arm 2 is genuinely
   nonprojective; nonpositivity alone would be too weak at zero.
4. **Internal hard pair falsifier.**  A pair inside the completed cycle has
   reciprocal signs `(+,-)`.  It cannot be the nonprojective pair, whose two
   reciprocal entries must both be negative.  This is exactly why arm 3
   forces the outsider into every hard pair.
5. **Long-cycle boundary.**  A rooted four-cycle has no unique outside label,
   so the complement and determinant arguments here do not apply.  No
   four-cycle constructor is included.

## Adapter and consumer

For a bounded `Fin 4` reward table with no uniform-equilibrium payoff, the
checked declaration

```text
nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff
```

produces `residual`.  The checked collision/preemption geometry produces one
of the seventeen marked lassos from the same witness.  When it is one of the
six length-three constructors, the present theorem gives the trichotomy.

In arm 3, the already checked proper-principal dispatch consumes the selected
`K`: `cardTwoCrossing` applies for cardinality two, and
`cardThree_externalHelper_or_cyclicBoundary` applies for cardinality three.
The new information is that this same selected principal contains `x`, which
is the owner or collider in the marked constructors stated above.

These are finite residual consumers, not semantic consumers.  No downstream
checked theorem currently turns any arm into a Nash root, absorption path,
contradiction, or uniform-equilibrium payoff.

## Lean handoff

The narrow implementation should define a decoder for the six length-three
constructors returning their ordered cycle and unique complement, or prove
six constructor cases directly.  Then:

1. prove a row-completion lemma from full packet mass positivity and
   `mix_ge_target`/`positive_mass_pins_target`, yielding (6);
2. reindex `principalMatrix M C` to `Fin 3` and use the checked determinant,
   homogeneous, standard-Q, and projective-Q equivalences;
3. prove that a hard pair cannot lie inside the strict oriented cycle by the
   existing two-column negative-entry argument;
4. prove the `Fin 4` complement/cardinality identities; and
5. split the six constructors to establish the owner/collider mapping.

Useful regression examples are determinant `<0`, `=0`, and `>0`, plus all
six constructor mappings.  The theorem should import the marked-lasso source,
`FullSupportHardPrincipalDispatch`, and the three-by-three classification.  It
must not add any desired helper, hard-principal, or role-incidence field to the
source structure.

## Scope and nonclaims

- This theorem does not eliminate any marked geometry or close any semantic
  chamber.
- It does not produce a Bellman edge, exact stage Nash root, chronology,
  absorption path, terminal equilibrium, or uniform-equilibrium payoff.
- It does not align the lasso with a semantic debtor, strict covector,
  punishment continuation, or nonsingleton compiler.
- The chosen hard principal need not be unique.  The three arms are proof
  branches, not a partition of complete reward tables or witness choices.
- It does not handle the eight length-two constructors or the rooted
  four-cycle constructors.
- It does not prove that a counterexample residual exists.
