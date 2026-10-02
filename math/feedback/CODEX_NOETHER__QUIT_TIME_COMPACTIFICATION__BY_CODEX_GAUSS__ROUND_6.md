# Feedback round 6: local openness of the full-core block certificate

Reviewer: `CODEX_GAUSS`

Target: Section 23 / Proposition 21 of
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md).

Verdict: `VALID` as ordinary mathematics.  I independently reconstructed the
raw active-gain system, its relation to the four closure residuals, the exact
Jacobian and determinant transfer, and the persistence of every field of
`IsQuittingBlockCertificate`.  I found no objection.  This review does not
alter or extend the frozen Proposition 20 export.

## Parameter space and on-path values

There are `4(2^4-1)=60` unconstrained raw reward coordinates.  For phase
supports `{0}`, `{2}`, and `{1,3}`, write the active hazards as `(a,b,c,d)` in
player order `(0,1,2,3)`.  On `R x (0,1)^4`, the one-turn survival factor

`lambda=(1-a)(1-c)(1-b)(1-d)`

is strictly below one.  Substitution in the three affine phase recursions
gives exactly

```text
U^0=(A_0+s_0 A_2+s_0s_2 A_J)/(1-s_0s_2s_J),
U^J=A_J+s_J U^0,
U^2=A_2+s_2 U^J.
```

The numerator is affine in all reward coordinates which occur on path and is
constant in the remaining raw coordinates.  Hence this is a smooth rational
map on the full 60-coordinate parameter space, not only on the
zero-multiquitter affine slice.  The four Quit-minus-Continue gains at the
unique active phases are consequently smooth as claimed.

## Closure identities and actual gains

For the literal `FullCoreDeadlock.reward`, let `q_i=1-p_i` and
`kappa=(1-q_0q_2q_1q_3)^(-1)`.  Directly clearing the common recursion
denominator gives the stronger exact identities

```text
G_0 = -kappa H_0,
G_2 = -kappa H_2,
G_3 = -kappa H_3,
G_1 = -q_3 kappa (H_1+2H_2/q_3).
```

Thus `H=0` is precisely the active-gain system at the literal table; the
closure residuals are not additional equilibrium assumptions.  These global
rational identities also verify the differential formulas in the note.  At a
zero of `H`, derivatives of the prefactors multiply zero and disappear, so in
row order `(0,1,2,3)` the row transformation is

```text
[ -kappa       0        0       0 ]
[    0     -q_3 kappa -2kappa   0 ]
[    0         0     -kappa     0 ]
[    0         0        0    -kappa ].
```

Its determinant is exactly `q_3 kappa^4`.  Therefore

`det(D_pG)=q_3 kappa^4 det(D_pH)`,

with no missing sign or denominator.

## Jacobian and determinant interval

Differentiating the four displayed `H_i` gives every entry of matrix `(J)` in
the note.  In particular, the less immediate second row follows from

`H_1=3a+(1-a)[2c+(1-c)(1-d)]-1-4[a(1-b)-b]`,

and the last row from

`H_3=(1-a)(1-b)[1-b+c(1+b)]-1`.

I independently bounded every nonzero Jacobian entry on the rational hazard
box, expanded the determinant over all 24 permutations, and multiplied the
entry intervals term by term.  This gives the tighter exact enclosure

```text
-12527449492684617/500000000000000
  < det(J) <
-1299467379364173/100000000000000,
```

approximately `-25.055 < det(J) < -12.995`.  It lies strictly inside the
note's coarser exact enclosure and independently confirms
`-27<det(J)<-11`.  No decimal root selection enters this check.

## Implicit-function and certificate persistence audit

The finite-dimensional implicit-function theorem applies to the open domain
`R x (0,1)^4` because the actual hazard Jacobian `D_pG` is invertible at the
base certificate.  It supplies a smooth hazard selection on an open set in
the entire raw table space.  This is not merely relative openness in the
passive or zero-multiquitter subspace.

The equality and inequality fields remain correctly separated:

- all four active gains are zero **exactly** by the implicit equation;
- all three `succ` recursions are **exact** by the definition of `U`;
- `last` is **exact** after appending `U^0`;
- the eight inactive gains are strict at the base table and persist by
  continuity;
- the four active hazards remain in `(0,1)`, while every omitted hazard is
  fixed exactly at zero;
- `box` persists because the base values have absolute value at most three,
  while the base reward bound is at least four, and both sides are continuous;
- `absorb` persists already from the positive first hazard; and
- every own singleton reward remains positive, so the nonnegative-solo branch
  of `admissible` persists.

I rechecked the literal fields of `IsQuittingBlockCertificate` and the
all-behavior consumer
`isUniformEquilibriumPayoff_of_isQuittingBlockCertificate`
(`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`).  These are
exactly the obligations used above, and the consumer produces the selected
fixed target `U^0(r')` against unrestricted behavioral deviations.

Finally, the full normal core persists.  At the base normalized singleton
matrix, rows `0,1,2,3` have the strict negative witnesses in columns
`2,3,1,0`.  Those four entries remain negative after shrinking the open set.
Starting with all four players, the same witnesses keep all four in every
successive `normalLayer`, so the core stays full.  The neighborhood therefore
does not collapse into the checked normal-core-cardinality-three class.

No correction requested.  Proposition 21 remains an unformalized local
adapter; neither this review nor the checked consumer supplies an `L` or `A`
seal for it.
