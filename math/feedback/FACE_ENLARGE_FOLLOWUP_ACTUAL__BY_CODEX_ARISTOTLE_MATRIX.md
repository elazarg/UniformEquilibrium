# Matrix audit of the current `FACE_ENLARGE_FOLLOWUP.md`

Reviewer: `CODEX_ARISTOTLE`

## Verdict

**THE STRICT-BLOCKER MATRIX LEMMA AND THE OUTSIDE-PLAYER
NONDISPENSABILITY THEOREM ARE CORRECT.  THE CLAIM MUST BE SCOPED TO PLAYERS
OUTSIDE THE SELECTED BAD FACE.  THE DISPLAYED RATIONAL EXAMPLE IS NOT A
COMPLETE QUITTING TABLE AS WRITTEN, BUT IT HAS AN IMMEDIATE COMPLETE RATIONAL
REPAIR.  NONE OF THIS MATRIX-ONLY MATERIAL PASSES THE EXPORT GATE.**

The maximal honest new theorem is:

> Let `M` be the normalized singleton matrix of a Fin4 hard residual.  Let
> `P` be a strict blocked principal face of cardinality two or three.  For
> every `j notin P`, if `C=I\{j}` and
> \[
> f_j=\min\bigl(0,\min_{\varnothing\ne S\subseteq C}r_j(S)\bigr),
> \]
> then
> \[
> r_j(\{j\})>f_j.
> \]

Thus no outside blocker helper can satisfy the solo-floor clause of the
checked singleton-block deletion gate.  This is sharp only as a strict sign:
the matrix data provide no positive lower bound on the premium and no
comparison with the terminal gap `gamma`.

This is a useful no-go for one proposed helper mechanism.  It is not a solved
hard-residual arm and does not enlarge the previously checked projective
`Q-bar` or deletion theorems.

## Sources inspected

- `IsStandardQMatrix`, `HasHomogeneousSimplexSolution`, and reindexing facts
  in `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`;
- `normalCore` and `normalPlayerMatrix` in
  `UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean`;
- `standardQ_and_noHomogeneous_iff_orientation_and_determinant` in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeByThreeZeroDiagonalQ.lean`;
- `FinFourQuantitativeFullSupportHardResidual.normalCore_eq_univ` and
  `.residualHardClass` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`;
- `quittingBlockContinueFloor`, `QuittingBlockDispensable`, and
  `quittingGame_exists_uniformEquilibriumPayoff_of_blockDispensable` in
  `UniformEquilibrium/Quitting/Classification/BlockDeletion.lean`.

The strict-blocker production from failure of complete `S_0`/projective
`Q-bar` was already independently audited in
`feedback/FACE_ENLARGE__BY_CODEX_FARADAY.md`.  This review starts with the
explicit blocker and audits the claimed additional matrix consequences.

## 1. Exact strict-blocker statement

For a nonempty principal face `P`, a strict blocker is

\[
y\in\Delta(P),\qquad \eta>0,\qquad
M_P^Ty\le-\eta\mathbf1.
\tag{B1}
\]

This is exactly a strict dual certificate that `M_P` is not `S_0`: for every
nonzero `x>=0`,

\[
y^TM_Px\le-\eta\sum_{k\in P}x_k<0,
\]

so `M_Px` cannot be componentwise nonnegative.  Conversely, finite minimax
produces (B1) whenever `M_P` is not `S_0`.

For a two-element face `P={a,b}`, (B1) forces both reciprocal entries to be
strictly negative.  Indeed,

\[
y_bM_{ba}\le-\eta,
\qquad
y_aM_{ab}\le-\eta.
\]

In particular `y_a,y_b>0`, `M_{ab}<0`, and `M_{ba}<0`.

Failure of projective `Q-bar` supplies some such bad principal face because
complete `S_0` is equivalent to projective `Q-bar`.  In Fin4, the full face
is `S_0` when the maintained full-support packet gives `Mp>=0`, and singleton
faces are `S_0` by zero diagonal.  Hence one may choose `|P|=2` or `3`.

## 2. Row-restriction lemma

The submission's row-restriction lemma is correct.

Let `M` be zero diagonal and standard `Q`.  Fix `j`, put `C=I\{j}`, and
assume

\[
M_{jk}\ge0\qquad(k\in C).
\tag{B2}
\]

For arbitrary LCP right-hand side `q_C`, extend it by `q_j=1`.  If `(z,w)`
solves the full standard LCP, then

\[
w_j=1+\sum_{k\in C}M_{jk}z_k\ge1.
\]

Complementarity gives `z_j=0`; restricting the other coordinates solves the
LCP for `M_C`.  Thus `M_C` is standard `Q`.

If `M` has no homogeneous simplex solution, neither does `M_C`.  Otherwise a
homogeneous direction on `C`, extended by zero at `j`, has nonnegative
residual in the `j` row by (B2), and is a homogeneous direction for `M`.

In the maintained hard residual, standard `Q` and nonhomogeneity are stated
for the normal-player matrix.  The separate field `normalCore_eq_univ`
identifies this principal matrix with the full normalized Fin4 matrix up to
the canonical subtype reindexing.  A Lean version needs to expose that
reindex explicitly; mathematically there is no gap.

## 3. Outside-player nondispensability

Let `P` satisfy (B1), take `j notin P`, and put `C=I\{j}`.  Suppose for
contradiction that the solo-floor clause holds:

\[
r_j(\{j\})\le
f_j:=\min\bigl(0,\min_{\varnothing\ne S\subseteq C}r_j(S)\bigr).
\tag{B3}
\]

For every `k in C`, singleton normalization gives

\[
M_{jk}=r_j(\{k\})-r_j(\{j\})
\ge f_j-r_j(\{j\})\ge0.
\]

The row-restriction lemma makes `M_C` standard `Q` and nonhomogeneous.

### Three-player blocked face

If `|P|=3`, then `C=P`.  This contradicts the strict blocker directly.  For
example, apply standard `Q` to right-hand side `-1`; a solution would obey

\[
0\le y^Tw=-1+y^TM_Pz
\le-1-\eta\sum_{k\in P}z_k<0.
\]

### Two-player blocked face

If `|P|=2`, then `|C|=3`.  The checked complete classification of
zero-diagonal `3 x 3` matrices says standard `Q` plus no homogeneous simplex
solution forces one of the two strict directed-cycle sign orientations.  In
particular every unordered pair has one positive and one negative reciprocal
entry.  But the two-face blocker forces both entries on the pair `P` to be
negative.  Contradiction.

Therefore

\[
\boxed{r_j(\{j\})>f_j\quad\text{for every }j\notin P.}
\tag{B4}
\]

The conclusion is stronger than needed with respect to helper selection: it
holds for every outside player, not only an outside column selected by the
blocker/full-support pairing.

### Scope correction

It is inaccurate to summarize (B4) as “no passive/deletion helper exists in
the hard residual.”  It proves only:

- no player outside this selected bad face passes the **solo-floor clause**
  for deletion of that same player; hence
- no such outside player passes the full `QuittingBlockDispensable` gate.

It does not rule out deleting a player inside `P`, deleting a different
block, or a non-deletion construction in which an outside player is passive
on the realized path without satisfying the table-wide block gate.

Nor is there a quantitative strengthening from the matrix data.  Once the
singleton rows are fixed, a nonsingleton survivor reward can be placed at
`r_j({j})-epsilon` for arbitrarily small positive `epsilon`, changing `f_j`
without changing `M`.  Additional hard-residual semantic hypotheses might
restrict a particular completion, but (B1), standard `Q`, and
nonhomogeneity alone cannot imply `pi_j >= gamma` or any fixed lower bound.

## 4. Audit and completion of the rational example

The displayed matrix

\[
M=
\begin{pmatrix}
0&-2&4&0\\
-2&0&4&0\\
0&0&0&0\\
0&0&0&0
\end{pmatrix}
\tag{B5}
\]

has the claimed properties:

- on `P={0,1}`, `y=(1/2,1/2)` gives
  `M_P^T y=(-1,-1)`, so `M` is not projective `Q-bar`;
- for `p=(1/4,1/4,1/4,1/4)`,
  `Mp=(1/2,1/2,0,0)>=0`;
- player `2` is an outside helper since `y^T M_{P,2}=4`; and
- `e_2` is a homogeneous simplex direction, so this example is correctly not
  claimed to inhabit the nonhomogeneous hard residual.

As written, however, it is not a complete quitting reward table.  It fixes
the normalized singleton matrix and player `2`'s rewards, but leaves the
baselines and the nonsingleton rewards of players `0`, `1`, and `3`
unspecified.

Here is a complete rational repair.  For every player set the own singleton
baseline to zero and define all singleton rows by

\[
r_i(\{k\})=M_{ik}.
\]

For every nonsingleton coalition `S`, put

\[
r_i(S)=0\quad(i\ne2),
\]

and

\[
r_2(S)=
\begin{cases}
-1,&2\in S,\\
0,&2\notin S.
\end{cases}
\]

This specifies all `4(2^4-1)=60` reward coordinates and realizes (B5)
exactly.  For the deleted block `{2}`:

\[
f_2=0=r_2(\{2\}),
\]

and for every nonempty survivor coalition `S subseteq {0,1,3}`,

\[
r_2(S\cup\{2\})-r_2(S)=-1.
\]

Thus player `2` satisfies `QuittingBlockDispensable`.  The survivor game has
three players and therefore has a uniform-equilibrium payoff; the checked
block-deletion producer lifts one to the complete four-player table.

This proves that the union of the already solved projective-`Q-bar` class and
the already solved singleton-dispensability class is a strict union.  It does
not prove that the dispensability class contains the projective-`Q-bar`
class, and “dispensability is a strictly larger class than projective
`Q-bar`” should not be used without the word “union.”

## 5. Maximal honest theorem

The finite matrix contribution can be packaged as follows.

### Fin4 blocked-face outside-floor theorem

Let `M` be a zero-diagonal Fin4 matrix which is standard `Q` and has no
homogeneous simplex solution.  Let `P` have cardinality two or three and
admit a strict blocker (B1).  Let `r` be any quitting table realizing `M` as
its normalized singleton matrix.  Then every outside player `j notin P`
satisfies (B4).

Equivalently, if some outside `j` satisfies its singleton deletion solo-floor
condition, then one of the following must fail:

- full-matrix standard `Q`;
- full-matrix nonhomogeneity; or
- strict blockedness of `P`.

For a maintained Fin4 hard residual, full-core reindexing supplies the first
two premises, so the result applies to every strict blocked face of size two
or three.

The example (B5), with the complete reward completion above, supplies the
correct boundary: once homogeneous solutions are allowed, a strict blocked
pair and a dispensable outside helper can coexist.

## 6. Progress and export verdict

The outside-floor theorem is a genuine algebraic no-go, but it does not
strictly advance the conjecture frontier under `exports/README.md`:

- it excludes an application of an already checked sufficient deletion gate;
- it produces no equilibrium, terminal approximation, admissible chronology,
  paid return, or minimum-fiber rank change;
- it leaves the quantitative near-floor interval `0<pi_j<gamma` completely
  open; and
- its failure does not consume a hard-residual branch.

The rational example is also not a new solved class theorem.  It demonstrates
noncontainment between two already checked sufficient architectures.  The
actual theorem for the union is the immediate disjunction of
`exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` and
`quittingGame_exists_uniformEquilibriumPayoff_of_blockDispensable`.

Accordingly:

\[
\boxed{\text{retain/formalize in Research; do not export matrix-only packet.}}
\]

The later semantic handoff and collision chronology in the source may alter
that verdict, but they were deliberately outside this matrix-only audit.

## 7. Lean handoff

Useful narrow declarations would be:

```lean
theorem standardQ_restrict_compl_of_row_nonneg

theorem noHomogeneous_restrict_compl_of_row_nonneg

theorem finFour_strictBlocker_outside_soloFloor_strict
    (hQ : IsStandardQMatrix M)
    (hhom : Not (HasHomogeneousSimplexSolution M))
    (hblock : PrincipalStrictBlocker M P eta)
    (hcard : P.card = 2 Or P.card = 3) :
    forall j, j notin P ->
      quittingBlockContinueFloor reward {j} j < reward ({j}) j
```

For the game-facing specialization, add a small reindex adapter turning
`normalCore_eq_univ` into standard `Q` and nonhomogeneity of the full matrix.
Do not encode blocker-selected helperhood or the terminal gap in this theorem;
neither is needed for (B4).
