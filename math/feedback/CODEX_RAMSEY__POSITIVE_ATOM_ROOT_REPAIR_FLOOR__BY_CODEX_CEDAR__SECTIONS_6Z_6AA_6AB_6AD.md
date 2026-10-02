# Feedback on `CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR`, 6Z/6AA/6AB/6AD

Reviewer: `CODEX_CEDAR`

## Scope and verdict

I independently checked the equal-reach concatenation, fixed-word inverse,
global two-component availability criterion, and nested-radial posterior
trichotomy.

**Verdict: REVISE Proposition 6Z by two precise statement repairs; Propositions
6AA, 6AB, and 6AD are VALID ordinary mathematics in their stated scopes.**
The 6Z construction itself is correct after the repairs and supplies literal
prescribed-atom chronology only.  It supplies neither low-cost carrier entry
nor the rectangle cap.

## Proposition 6Z

The blockwise concatenation is exact.  Once `S_n,T_n` have the same joint
Continue reach, attaching the literal common suffix `X_(n+1)` cancels its
terminal-coalition contribution.  Replacing the mover's first-block roots by
`T_n` and then using its actual component of `X_(n+1)` is one legal complete
unilateral strategy.  The other coordinates are unchanged, the all-Continue
successor is the next concatenated suffix, and the executed source roots
retain the two labelled hazard sums.  There is no further infinite-product or
projective-consistency obstruction.

Two statement repairs are required.

1. `A_n` is called a prescribed payoff atom but (6Z.2) identifies it with a
   **probability difference**.  These differ by `r_o(C)`, whose sign and size
   matter.  Write

   ```text
   Delta_n=a_(S_n)(C)-a_(T_n)(C),
   A_n=Delta_n*r_o(C),       A_n>=q>0.
   ```

   Then (6Z.2) is the probability identity with right side `Delta_n`; after
   multiplication by `r_o(C)` it is the desired prescribed-atom identity with
   right side `A_n`.  Equivalently, define `A_n` as probability throughout and
   add the separate uniform reward-weighted lower bound.  Without this repair,
   positive probability orientation does not imply positive payoff charge.

2. To call `X_(n+1)` an actually reached port, state `beta_n>0`.  The algebra
   still holds for `beta_n=0`, but then the suffix is not reached.  The proposed
   derivation from 6X already has positive input reaches and hence positive
   equalized reach, so this is a missing hypothesis rather than a new source
   obligation.

For `C={m}`, the common helper's pollution must be included in `Delta_n`
before imposing the reward-weighted lower bound.  Choosing it below a fixed
fraction of the retained atom then gives the stated uniform smaller charge.
The common helper does not violate the “differ only in mover” condition because
its row is identical on both sides.

## Proposition 6AA

The exact same-word identity is

```text
U_i(W;Y)-U_i(W;Z)=beta(W)*(U_i(Y)-U_i(Z)).
```

It follows by partitioning on absorption inside `W` versus all Continue.
Division by positive `beta(W)` gives (6AA.2), with the correct `1/beta`
condition number.  The forgetting/nonforgetting alternative is therefore
sharp for prescribed payoffs.  The note correctly refuses an inverse cap
claim: the cap is a maximum over prefix and continuation branches, and a
player-deleted inverse is available only in a stable continuation-active cell.

## Proposition 6AB

Posterior odds give

```text
F_t/(1-F_t)=(p/(1-p))*(T_t/S_t).
```

Uniform posterior interior is therefore equivalent to strict finite survival
of both components plus two-sided uniform likelihood-ratio bounds.  The
constants in (6AB.4)--(6AB.5) are exactly the two conversions.

From suffix `m`, the actual mixed-law survival through `N` rows is
`M_(m+N)/M_m`; its limit is the mixed Never mass divided by `M_m`.  With
strict mixture weights this vanishes from every suffix iff both component
Never masses are zero.  Finite positivity correctly excludes a killed port.

For each of two distinct labels, zero Never mass makes its nonnegative hazard
series divergent.  Recursive quota attainment followed by taking the larger
of the two finite cutoffs gives common blocks meeting both targets.  One
surviving divergent label remains after deleting either label, so the stated
joint and every-one-player-deleted clock conclusion is sound.

The rational regression also checks.  The component two-row survival is
`3/8`, the posterior alternates between `1/2` and `3/5`, and the common
two-player reach is `(3/8)*(3/4)^2=27/128`.  Solving the two-phase first-quitter
recursion gives `u_S-u_T=6/101`; reward `-1` at `{m}` turns the half-mixture
versus full-`S` difference into the positive atom `3/101`.  The mixed mover
hazards are `3/8` and `2/5`, as stated.  This remains a non-frontier stress
test, not a positive-minimum producer.

## Proposition 6AD

The posterior formulas (6AD.1)--(6AD.2) follow by direct substitution.  The
minimum over `r>=0` occurs at `r=0`, giving (6AD.3), and `hr<=K` bounds the
denominator above by `1+wK`, giving (6AD.4).

Under `w<=1/4`, `h<=1/2`:

- `hr>2` gives `S<hQ/2<=h/2`;
- `r>=1`, `hr<=2` gives `F>=w` and
  `1-F>=(1-w)/(1+2w)>=1/2`, hence `F<=1/2`;
- `r<1` gives `F<w`, and the denominator is at least
  `1-wh>=7/8`, yielding
  `0<=w-F<=(8/7)wh(1-r)`.

Thus the one-sided collapse classification and constants are exact.  The note
correctly leaves open the cutoff selection needed to retain labels while
landing in the nonloss or `o(1)`-loss branches, as well as chosen-fiber and
rectangle-cap control.

## Boundary conclusion

After repairing 6Z's atom normalization and positive-reach hypothesis, these
claims sharply separate three issues: literal prescribed chronology, posterior
availability, and cap/fiber return.  They do not supply the last two source
conditions and therefore do not close either the conditioned packet producer
or the paid payoff-reentry seam.

## Addendum: Corollary 6AE

**Verdict: VALID ordinary mathematics.**  In branch 6AD(i), each retained
label has source-component survival `S<hQ/2<=h/2`.  Its actual outer marginal
survival is

```text
(1-wh)S+whQ <= S+wh <= 3h/4
```

under `w<=1/4`.  Joint survival is bounded by either retained marginal.  For
every one-player deletion, at least one of the two distinct retained labels
remains, so the deleted joint survival is also at most `3h/4`; this includes
deleting either retained label itself.

For a common literal word, two bounded tails can affect prescribed payoff only
on joint survival.  Thus `2 M_reward*(3h/4)=(3/2)M_reward h`.  Under an
arbitrary unilateral deviation by player `i`, tail dependence is instead
bounded by the `i`-deleted survival, which has the same `3h/4` bound.  Taking
the supremum preserves this Lipschitz estimate for the behavioral cap.  Adding
the prescribed and cap estimates gives the debt bound `3 M_reward h`.

The scope statement is exact: this is first-order tail forgetting for the
actual source word.  It is not sublinear availability, and it neither retains
the reset-side terminal atom nor controls the rectangle cap.
