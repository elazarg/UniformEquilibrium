# Feedback on `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION` — Round 42

## Claim checked

I independently audited Section 62, Proposition 82: finite-dimensional
semialgebraic transient branches can have square-root maximal prefix charge,
finite total charge on every path, and a literal one-edge norm displacement
at least the edge charge.

**Verdict: VALID ordinary mathematics.**  I found no mathematical objection.

## Rotation and tame graph

The displayed matrix is the standard rational parametrization of a circle
rotation.  Direct subtraction gives, for every unit vector `v`,

```text
||Rot_e(v)-v||^2 = 4e^2/(1+e^2),
```

so `(N188)` is exact and is at least `e` for `0<=e<=1`.

The launcher, phase, and terminal components are compact semialgebraic.  In
the phase graph, multiplying the rotation equations by `1+e^2>0` gives
polynomial equalities without adding denominator-zero points.  Every graph
piece uses closed weak inequalities, including both edges at the terminal
threshold.  Their finite union is therefore compact, semialgebraic, and
closed.

## Seriality and equality cases

Launchers and `o` have self-loop predecessors.  A phase state with
`t<=e^2` has the stated launcher predecessor.  When `t>=e^2`, the phase
predecessor using `Rot_e^{-1}` lies on the unit circle and maps exactly to the
given state.  For `e=0`, this becomes the same phase state, covering every
`t`; the charge is then zero.  These cases overlap harmlessly at the
boundaries.  Every state has a viable infinite future: positive-`e` phases
exit after finitely many steps, while zero-`e`, launcher, and terminal states
may remain on zero-charge loops.

## Coercivity and charge bounds

On a phase-to-phase edge, the circle-coordinate displacement alone has norm
at least `e`; the additional counter displacement cannot reduce the product
Euclidean norm.  On a phase-to-terminal edge, the label coordinate moves by
one, at least `e`.  Every other edge has source charge zero.  Thus `(N189)`
holds literally, including terminal and zero-parameter edges.

For fixed `e>0`, at most `1/e^2+2` positive phase rows occur, giving finite
total charge at most `1/e+2e`.  An `N`-row prefix contributes at most
`min(Ne,1/e+2e)`.  Splitting at `e=1/sqrt(N)` gives the stated upper bound.
Starting at phase counter zero with this parameter supplies `N` positive rows
and charge exactly `sqrt(N)`, including `N=1`.  Hence every path is finite in
charge while `A_N` has the claimed square-root growth.

## Exact scope

The rotating coordinate is abstract and is not a quitting payoff/root
embedding.  The example nevertheless exactly refutes the inference from
one-edge norm coercivity plus tame compact geometry to a nested divergent
path.  A positive proof needs accumulated directional or semantic control,
not merely a lower bound on each step's norm.
