# Focused audit of Proposition 6AP

Reviewer: `CODEX_CEDAR`

Reviewed note: `notes/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md`

Scope: Proposition 6AP only, with the atom-alternative definitions in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/DebtSlopeAtomAlternative.lean`
and `VanishingDebtAtomAlternative.lean` checked for the rectangle/never
qualification.

## Verdict

**PASS in the stated interface scope.**  The exact first-coalition bound, its
infinite-word summation, the reward-weighted two-law consequence, exponent and
constant, and all stated nominal/rectangle/singleton qualifications are
correct.  No factor two is missing in the difference-of-two-laws step.

## Exact probability bound

Fix `i_0 in C`, where `|C|=k>=2`.  The row-`t` contribution to the exact
first-coalition mass is

```text
S_t * product_(i in C) q_(t,i)
    * product_(j notin C)(1-q_(t,j)).
```

If every marginal hazard is at most `mu`, the `k-1` factors other than
`i_0` contribute at most `mu^(k-1)`, and the outside Continue product is at
most one.  Joint survival is at most player `i_0`'s marginal survival

```text
S^i_t=product_(s<t)(1-q_(s,i_0)).
```

Therefore

```text
p(C)
 <=mu^(k-1) sum_t S^i_t q_(t,i_0)
 = mu^(k-1) Pr(i_0 ever Quits)
 <=mu^(k-1).
```

The equality is the standard first-success decomposition and remains valid
with infinitely many dates and positive Never mass.  No finite-horizon limit
or absorption assumption is hidden.

## Reward-weighted atom and constants

From

```text
|(p_P(C)-p_E(C))*r_o(C)|>=a,  |r_o(C)|<=M,
```

with `M>0`, one gets `|p_P(C)-p_E(C)|>=a/M`.  For nonnegative probabilities,

```text
|p_P(C)-p_E(C)|<=max(p_P(C),p_E(C)),
```

not merely their sum.  Hence

```text
max(p_P(C),p_E(C))>=a/M.
```

There is consequently no missing factor `2`.  If both words have mesh at
most `mu`, the probability bound applies to each word and gives

```text
mu^(k-1)>=a/M,
mu>=(a/M)^(1/(k-1)).
```

The assumptions themselves make `a/M<=1`.  A zero reward at `C` cannot
satisfy the positive premise, while `M=0` is correctly excluded.  The same
argument works for finite-prefix atom masses because the truncated
first-success sum is smaller than the complete one.

## Rectangle and nominal-word qualifications

The distinction in the note is exact.

- `HasQuittingStoppingLawVanishingDebtAtomAlternative` initially stores an
  `Option Nat` pure time.  The checked adapter
  `hasDebtSlopeAtomAlternative_of_hasVanishingDebtAtomAlternative` collapses
  the `Never` (`none`) case into the prescribed-atom arm.
- A genuine rectangle arm of
  `HasQuittingStoppingLawDebtSlopeAtomAlternative` therefore uses
  `some stop`, hence contains a literal sure-Quit row and has mesh one if the
  mesh condition is imposed on the atom-witness override itself.
- This says nothing about the mesh of the nominal packet word.  If only the
  nominal source is constrained, the obstruction applies only in the sign
  orientation in which that source carries the fixed atom; the coarse mass
  may instead lie entirely in the full-replacement word.

For `k=1`, the bound degenerates to `p(C)<=1` and gives no mesh lower bound,
so the explicit nonsingleton hypothesis is essential.  Proposition 6AP also
does not infer that the current checked packet type has an upper-mesh field,
or that the stabilized atom orientation must be nonsingleton.

## Scope

This is a valid exact obstruction to adding a blanket vanishing maximum-root-
hazard field simultaneously to both provenance words while retaining a fixed
nonsingleton atom.  It is not a positive-minimum counterexample, does not
obstruct singleton orientations, and does not convert the existing lower
hazard quota into an upper mesh bound.

