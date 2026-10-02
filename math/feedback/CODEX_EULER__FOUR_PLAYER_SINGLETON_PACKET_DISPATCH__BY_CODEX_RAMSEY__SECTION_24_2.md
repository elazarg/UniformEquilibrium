# Review of Proposition 24.2

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

The normalized singleton matrix uses

```text
M(receiver,quitter)=r_{quitter}(receiver)-r_{receiver}(receiver).
```

All own singleton payoffs in (24.1) equal one.  Subtracting the appropriate
own payoff from the four singleton rows gives exactly

```text
[ 0  0 -1 -1
  0  0 -1 -1
 -1  1  0 -1
  1 -1 -1  0 ].
```

For support owners `{0,1}`, the crossed helped labels are `2` for owner `1`
and `3` for owner `0`.  Thus the checked safe pairs are
`{0,1},{0,3},{1,2}`, and the complementary allowed size-two pairs are
`{0,2},{1,3},{2,3}`.  Restricting the displayed matrix to any allowed pair
gives, up to its subtype ordering,

```text
[0 -1; -1 0].
```

For this matrix a homogeneous simplex weight `(z_1,z_2)` has residual
`(-z_2,-z_1)`.  Residual nonnegativity forces both weights to zero, contrary
to simplex mass one.  Hence there is no homogeneous solution.  It also
cannot be standard `Q`: the checked necessary theorem
`exists_positive_entry_in_row_of_standardQ` would give a strictly positive
entry in each row, while both rows contain only `0,-1`.  The checked split
`isProjectiveQMatrix_iff_standard_or_homogeneous` therefore proves that each
allowed principal is nonprojective.

For completeness, the safe restrictions are

```text
M[{0,1}] = [0 0; 0 0],
M[{0,3}] = [0 -1; 1 0],
M[{1,2}] = [0 -1; 1 0]
```

up to ordering.  The zero matrix has an immediate homogeneous simplex
solution.  In either latter matrix, mass one on the first column has
nonnegative residual `(0,1)`, so those matrices also have the homogeneous
branch and are projective.  This agrees exactly with
`nonprojectivePrincipal_ne_safePairs_of_support_eq_pair`.

Accordingly the table saturates the size-two screen as claimed.  The stated
scope remains exact: it says nothing about existence or structure of a
size-three/four nonprojective principal, supplies no decoder, and does not
upgrade the local regression to a terminal witness or uniform-equilibrium
counterexample.
