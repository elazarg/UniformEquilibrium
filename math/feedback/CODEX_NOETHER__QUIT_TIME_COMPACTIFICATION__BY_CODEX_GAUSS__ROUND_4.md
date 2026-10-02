# Fourth review: directed-triangle rates and ambient outsider floors

Reviewer: `CODEX_GAUSS`

Note reviewed: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Section 20, Propositions 17--18 only.

Verdict: `VALID_ORDINARY_MATHEMATICS_WITH_PARAMETER_ORDER_CORRECTION`.
The strict rate system has exactly the claimed cube solutions, the formulas
and determinant boundary check, the outsider halfspace cone is exact, and the
data assemble the named balanced-singleton certificate for arbitrary
nonsingleton rewards and unrestricted behavioral deviations.  The four-player
mixed-sign example and full-normal-core calculation also check.  One source
sentence needs a parameter-order correction: to identify the note's `Delta`
with the checked `cycleGap`, the directed-cycle matrix parameters are

`(a,b,c,d,e,f)=(a_A,b_A,b_B,a_B,a_C,b_C)`,

not the rate-variable order `(a_A,b_A,a_B,b_B,a_C,b_C)`.  The mathematical
classification statement survives after this reordering.

## Strict rate system and uniqueness

The equations under review are

```text
a_A p_B = b_A (1-p_B) p_C,
a_B p_C = b_B (1-p_C) p_A,
a_C p_A = b_C (1-p_A) p_B,
```

with all six magnitudes strictly positive.  If one hazard is zero, cyclic
substitution forces all three to be zero.  Any nonzero solution is therefore
strictly positive.  No coordinate can equal one: for example `p_A=1` makes
the third equation have positive left side and zero right side.

Multiplication and cancellation at a nonzero solution gives

`(1-p_A)(1-p_B)(1-p_C)=a_Aa_Ba_C/(b_Ab_Bb_C)`.

Thus `Delta=b_Ab_Bb_C-a_Aa_Ba_C>0` is necessary.  Conversely, eliminating
`p_B,p_C` gives one linear equation after cancelling positive `p_A`, and its
solution is

`p_A = Delta/[b_B(a_Ca_A+a_Cb_A+b_Cb_A)]`.

Cyclic rotation gives the other two displayed formulas.  Every denominator
is positive.  For the first rate, denominator minus numerator is

`a_C(a_A b_B+b_A b_B+a_A a_B)>0`,

and the other two follow cyclically, so every rate lies in `(0,1)`.  Direct
substitution recovers all three equations.  This proves existence and
uniqueness without a refinement or limiting assumption.

When `Delta=0`, a nonzero solution would force the product of the three
Continue probabilities to be one even though every hazard is positive.  When
`Delta<0`, it would force that product above one.  Hence the zero solution is
the only cube solution on both sides.  The symmetric boundary
`a_o=b_o=1` and the negative-side test `a_o=2,b_o=1` have exactly the stated
behavior.

The strictness warning is substantive.  If, for example, `a_A=b_A=0` and the
other four magnitudes are one, the first equation is vacuous and

`p_A=t`, `p_B=t/(1-t)`, `p_C=t/(1+t)`

is a continuum of solutions for `0<=t<=1/2`.  If exactly one side of an
anchor vanishes while the other stays positive, no interior solution can
satisfy that anchor.

## Checked three-player correspondence

The rate definitions in
`UniformEquilibrium/Quitting/Classification/ThreePlayer/CyclicCompiler.lean`
match

```text
(rightP,rightQ,rightR,rightS,rightT,rightU)
  =(a_A,b_A,a_B,b_B,a_C,b_C),
(rightAlpha,rightBeta,rightGamma)=(p_A,p_B,p_C).
```

The declarations `right_balance_one`, `right_balance_two`, and
`right_balance_three` are the three anchor equations, and the denominators in
`rightAlpha`, `rightBeta`, and `rightGamma` are exactly the cyclic versions of
the formulas above.  Thus the positive three-player producer is already
represented by `rightSingletonCycle_isUniformEquilibriumPayoff`, as the note
states.

For the LCP comparison, however, the definition
`directedCycleMatrix a b c d e f` has rows

```text
[0,-a,b], [c,0,-d], [-e,f,0].
```

Therefore this note's matrix is obtained with

`(a,b,c,d,e,f)=(a_A,b_A,b_B,a_B,a_C,b_C)`.

Under that assignment,

`cycleGap=b*c*f-a*d*e=b_Ab_Bb_C-a_Aa_Ba_C=Delta`.

The claims using `directedCycleMatrix_hasHomogeneous_iff` and
`directedCycleMatrix_standardQ_and_noHomogeneous_iff`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeByThreeZeroDiagonalQ.lean`)
are correct after recording this permutation.  Without it, substituting the
rate-variable list directly into `cycleGap` gives the wrong mixed product.

## Outsider cone and fixed target

Let `Q=q_Aq_Bq_C`.  Since every rate is positive and below one, `1-Q>0`.
The three displayed vectors satisfy exactly

```text
x^A=p_A r({A})+q_A x^B,
x^B=p_B r({B})+q_B x^C,
x^C=p_C r({C})+q_C x^A.
```

For any outsider `i`, subtracting its solo value `s_i` from the numerator of
`x^A_i` gives

`p_A m_A(i)+q_Ap_Bm_B(i)+q_Aq_Bp_Cm_C(i)`.

The weights sum to `1-Q`; hence this is exactly
`(1-Q)(x^A_i-s_i)`.  Cyclic rotation proves the other two identities.  The
three inequalities `(F)` are therefore necessary and sufficient for all
three outsider floors, and are homogeneous closed halfspaces in the margin
triple.  They allow negative margins; no hidden coordinatewise nonnegativity
is used.

For owner `A`, the first anchor makes `x^A_A=x^B_A=s_A`, while

`x^C_A-s_A=p_C b_A>0`.

The other owner floors follow cyclically.  Consequently the displayed coarse
values, owners, hazards, and initial phase satisfy the `arc`, `active`, and
`soloFloor` fields of `BalancedSingletonCycleCertificate`.  Its
`opponentDivergence` field also holds: every rate is positive, and among three
distinct owners every player has a positive-hazard phase owned by someone
else.

The checked theorem
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`)
derives its collision cap from the finite reward bound.  It therefore covers
arbitrary pair and larger-coalition rewards and arbitrary unilateral
behavioral deviations.  The target `x^A` is fixed while the internal mesh is
refined.  No pairwise join cap has been silently assumed.  Such caps would be
needed only for the stronger unrefined solo-periodic profile, exactly as the
note distinguishes.

## Four-player exact test

For the displayed singleton rows, the active triangle has `a_o=1`, `b_o=2`,
so `Delta=7` and all three rates are `1/2`.  The outsider `D` has margins
`(-3,4,4)`.  Multiplying the three floor numerators by eight gives

`0,21,14`,

and the corresponding values are exactly `x^A_D=1`, `x^B_D=4`, and
`x^C_D=3`, all at least `s_D=1`.

The normalized singleton matrix printed in the note is correct.  Each of its
four rows has a distinct nonpositive witness inside the full player set:
`A->B`, `B->C`, `C->A`, and `D->A`.  Induction in the literal `normalLayer`
recursion keeps the full set at every layer, so the normal core has cardinality
four.  This verifies the claimed ambient/full-core distinction.  It does not
by itself classify that four-by-four matrix as standard Q or prove absence of
all other producers, and the note does not need either stronger assertion.

## Novelty and scope

A narrow search found the general balanced-certificate consumer and its
Essential-APS adapter, but no named declaration deriving the three-phase
certificate from one strict directed singleton triangle plus the three raw
outsider halfspaces.  Proposition 18 is therefore a plausible new
ordinary-mathematics actual-data adapter to a checked consumer.  Its
three-player specialization is not new, and no absolute claim against every
conditional producer is justified.  The example shows that the adapter can
reach a full-normal-core ambient table and can tolerate a negative outsider
margin; it is not a solution of the unrestricted full-core or standard-Q
classes.

I found no mathematical counterexample to Propositions 17--18 after the
parameter-order correction above.  This review does not cover the preceding
solo-periodic Proposition 16 or any later extension.
