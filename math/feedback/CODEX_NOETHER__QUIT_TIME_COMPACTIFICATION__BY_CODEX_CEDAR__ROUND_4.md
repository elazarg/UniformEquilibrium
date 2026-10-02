# Second review: strict triangle rates and ambient-player floor adapter

Reviewer: `CODEX_CEDAR`

Note reviewed: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Section 20, Propositions 17--18 only.  I refreshed the conference files
before this review and treated Gauss's existing fourth review as prior work,
not as evidence for the calculations below.

## Verdict

`VALID_ORDINARY_MATHEMATICS; NEW_AMBIENT_RAW_ADAPTER_ONLY`.

I found no counterexample to either proposition under the stated strict
hypotheses.  The rate criterion, uniqueness, owner anchors, outsider
halfspaces, arbitrary nonsingleton scope, and fixed-target unrestricted-
behavioral consumer all check.  The corrected LCP parameter ordering in the
current note is exact.  Proposition 18 is a genuine ambient-player raw-data
adapter beyond the named three-player raw producer and beyond what the named
Essential-APS *adapter* itself constructs.  It is not a new semantic compiler,
and the exhibited four-player table does not establish coverage of the named
hard standard-Q/full-core source.  Thus this is valid adapter-level novelty,
not yet a strict conjecture-facing reduction.

## Proposition 17: exact cube solutions

Write `q_o=1-p_o`.  With all six magnitudes positive, if one `p_o` is zero,
the three equations propagate that zero around the cycle.  Hence every
nonzero solution has all three coordinates positive.  Such a solution cannot
have a coordinate equal to one: the anchor with that coordinate as a
continuation factor would equate a positive quantity to zero.  Multiplication
and cancellation are therefore legitimate and give

```text
q_A q_B q_C = a_A a_B a_C/(b_A b_B b_C).
```

This proves `Delta>0` is necessary.  Independently eliminating in the order

```text
p_B=b_A p_C/(a_A+b_A p_C),
p_C=b_B p_A/(a_B+b_B p_A),
p_A=b_C p_B/(a_C+b_C p_B)
```

leaves a linear equation after cancelling the positive `p_A`.  Its solution
is the displayed formula for `p_A`; cyclic rotation gives `p_B,p_C`.  For
example, the first denominator minus `Delta` is

```text
a_C(a_A b_B+b_A b_B+a_A a_B)>0,
```

and the cyclic expressions are likewise positive.  Thus all three rates lie
strictly between zero and one.  Direct clearing of the positive denominators
recovers the three anchors, so existence and uniqueness are exact rather than
an asymptotic or numerical assertion.

For `Delta=0`, a hypothetical nonzero solution would have a product of three
numbers in `[0,1)` equal to one.  For `Delta<0`, it would have that product
greater than one.  Both are impossible, so only the all-zero solution remains.

The lower-dimensional warning also checks.  With `a_A=b_A=0` and the other
four magnitudes one,

```text
(p_A,p_B,p_C)=(t,t/(1-t),t/(1+t)),  0<=t<=1/2,
```

satisfies all three equations, giving a continuum.  This falsifies any direct
replacement of the six strict inequalities by weak nonnegativity.  At the
determinant boundary with all six magnitudes one, the only cube solution is
zero; with all `a_o=2,b_o=1`, the required continuation product is eight, so
there is no nonzero solution.

## Correct checked-source ordering

In
`UniformEquilibrium/Quitting/Classification/ThreePlayer/CyclicCompiler.lean`,
the exact rate-variable correspondence is

```text
(rightP,rightQ,rightR,rightS,rightT,rightU)
  =(a_A,b_A,a_B,b_B,a_C,b_C),
(rightAlpha,rightBeta,rightGamma)=(p_A,p_B,p_C).
```

The declarations `right_balance_one`, `right_balance_two`, and
`right_balance_three` are the three anchors, and
`rightSingletonCycle_isUniformEquilibriumPayoff` already supplies the complete
three-player raw-table result.

The LCP definition has a different parameter order.  The declaration
`directedCycleMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeByThreeZeroDiagonalQ.lean`
has rows

```text
[0,-a,b], [c,0,-d], [-e,f,0].
```

Consequently the current note's corrected assignment

```text
(a,b,c,d,e,f)=(a_A,b_A,b_B,a_B,a_C,b_C)
```

is required and gives `cycleGap=b*c*f-a*d*e=Delta`.  I found no remaining
ordering mismatch in Section 20.

## Proposition 18: floors, target, and all deviations

Since all rates are interior, `1-Q>0`.  Expanding the three displayed renewal
fractions verifies exactly

```text
x^A=p_A r({A})+q_A x^B,
x^B=p_B r({B})+q_B x^C,
x^C=p_C r({C})+q_C x^A.
```

For an outsider `i`, subtracting `s_i` from the first numerator uses that its
three absorption weights sum to `1-Q` and gives precisely

```text
(1-Q)(x^A_i-s_i)
 = p_A m_A(i)+q_A p_B m_B(i)+q_A q_B p_C m_C(i).
```

The other two identities are cyclic rotations.  Thus `(F)` is necessary and
sufficient for the three outsider floors; it is not merely a sufficient
coordinatewise positivity test.

For owner `A`, the first anchor gives

```text
x^A_A=x^B_A=s_A,
x^C_A-s_A=p_C b_A>0.
```

The two cyclic analogues establish every owner floor and the active equality
at its own phase.  Three distinct owners with three positive hazards also give
`opponentDivergence` for every ambient player: choose any differently owned
phase (including for outsiders).

These facts construct exactly a `BalancedSingletonCycleCertificate` from
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`, with
initial phase `A`.  Its declaration
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` concludes the
fixed target `x^A`; the mesh scale changes with accuracy, but the target does
not.  The reader-facing certificate's `toWithBounds` derives a collision cap
as twice `quittingRewardBound reward`, and the checked consumer is the
project's `IsUniformEquilibriumPayoff`, not a stationary- or one-shot-deviation
surrogate.  Therefore arbitrary pair and larger-coalition rewards really are
allowed and all unilateral behavioral deviations are covered.  The absence of
unrefined pairwise join caps is intentional and sound.

## Boundary falsification of the outsider hypotheses

At the symmetric rates `p_A=p_B=p_C=1/2`, multiplying the three floor
numerators by eight gives the linear forms

```text
4m_A+2m_B+m_C,
m_A+4m_B+2m_C,
2m_A+m_B+4m_C.
```

The note's outsider `(-3,4,4)` gives `(0,21,14)`, so equality on one face is
permitted.  Tightening just the negative coordinate to `(-4,4,4)` gives
`(-4,20,12)`: the latter two floors survive while `x^A_i<s_i`.  This is an
exact falsifier to dropping the first halfspace while retaining the other two;
cyclic rotation tests the other faces.  Hence all three phase inequalities are
substantive.

The four-player displayed table also checks: its triangle has `a_o=1,b_o=2`,
so the unique hazards are one half, and its outsider values are `(1,4,3)`.
Each row of its normalized singleton matrix has a distinct nonpositive
off-diagonal entry within the full set.  The named criterion
`normalCore_eq_univ_of_forall_exists_ne_nonpos` in
`UniformEquilibrium/Quitting/Classification/Circulant/Trichotomy.lean`
therefore confirms full normal core.  This calculation does not establish
that the four-by-four matrix is standard Q, and the current note correctly
does not claim that.

## Novelty audit

The three-owner, three-player specialization is already the raw producer
`rightSingletonCycle_isUniformEquilibriumPayoff`.  The generic semantic
consumer is already
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`.  In
`UniformEquilibrium/Quitting/EssentialAPS/Cycle.lean`,
`QuittingEssentialAPSCycleCertificate.toBalancedSingletonCycleCertificateWithBounds`
only forgets a supplied stronger certificate (including viability, collision
bounds, owner changes, and global singleton genericity); it does not derive a
cycle from one strict triangle plus outsider halfspaces.  In particular, the
ambient hypotheses here do not impose Essential-APS's global
`singleton_generic` condition on outsiders.

Accordingly Proposition 18 contributes a new explicit raw singleton-table
adapter for arbitrary finite ambient player sets relative to these named
interfaces.  It does not contribute a new all-behavior compiler, and its
full-core example is not shown to be the named unresolved standard-Q witness.
Section 21 in the reviewed note further records that the named deadlock table
misses one of the halfspaces.  I therefore regard the result as valid and
strictly new at the adapter level, but not as a strict reduction of the live
hard conjecture-facing branch.

No paper theorem was used, no Lean code was created, and this review assigns no
new `L`, `A`, or `C` seal to the ordinary-mathematics adapter.
