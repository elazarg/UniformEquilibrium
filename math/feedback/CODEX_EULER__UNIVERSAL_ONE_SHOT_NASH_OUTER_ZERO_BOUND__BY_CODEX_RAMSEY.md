# Independent falsification: universal one-shot Nash outer-zero bound

**Reviewer:** `CODEX_RAMSEY`  
**Source:**
[`notes/CODEX_EULER__UNIVERSAL_ONE_SHOT_NASH_OUTER_ZERO_BOUND.md`](../notes/CODEX_EULER__UNIVERSAL_ONE_SHOT_NASH_OUTER_ZERO_BOUND.md)  
**Verdict:** **PASS** as ordinary mathematics, with two explicit
formalization handoffs below.

## Claim checked

For every nonempty finite quitting table with rewards in `[-R,R]`, choose an
exact mixed Nash root of the one-shot game at continuation zero and realize it
literally at date zero, followed by Never.  The resulting actual finite-clock
profile has unrestricted behavioral debt at most `2R/3` in every coordinate.
For normalized tables this gives the diagonal outer witness through
`M <= 3 n(n-1)`, and hence through `M=36` for `Fin 4`.

## Independent calculation

Fix player `i`.  If `a` is the probability that every opponent chooses
Continue at date zero and `s=r_i({i})`, write `Q,C` for the one-shot pure-Quit
and pure-Continue values.  The literal date-zero/Never profile has exactly
three unilateral pure-time values:

```text
time 0:       Q
time >= 1:    L = C + a s
Never:        C.
```

The after-support formula includes the case of sure opponents and the empty
opponent event correctly.  By
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`, these are exhaustive
even against arbitrary behavioral deviations.  Mixed-Nash optimality gives
`U=max(Q,C)` at pure as well as mixed boundary points, so

```text
d = B-U = max(0, L-max(Q,C)).
```

If `s<=0`, then `d=0`.  If `s>0`, comparison with `C` gives `d<=aR`.
Comparison with `Q` cancels the empty-coalition solo term exactly:

```text
L-Q = sum_{S nonempty} pi(S) [r_i(S)-r_i(S union {i})]
    <= 2R(1-a).
```

Thus `d<=min(aR,2R(1-a))<=2R/3`.  No division, positive survival, or
interior-support assumption is used.  The argument remains valid for
`a=0,1`, sure quitters, ties, and `R=0`.

`exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean` is exactly the required
finite mixed-Nash producer at tail zero.  The profile is literally in
`quittingFiniteClockSemanticReachable reward 1`: its stopping laws are
supported on `some 0` and `none`, so it embeds into every larger clock bound.

The diagonal midpoint is at sup-distance `max_i d_i/2 <= R/3`.  With
normalized `R=1`, every radius `n(n-1)/m` for `m<=M` contains this same center
when `M<=3n(n-1)`.  Hence the objective is exactly zero.  For `Fin 4`, the
constant is `36`; the statement about `M=37` is correctly only absence of
this universal certificate.

## Prototype and formalization audit

The `dump-one-shot-universal` output uses the literal `A_1` convention
(`date 0` plus exact Never), emits all supported/after-support/Never cap
values, and adds the two one-shot inequalities `U_i>=V_{i,0}` and
`U_i>=V_{i,Never}`.  Together with the prescribed-payoff mixture equality,
those inequalities are equivalent to binary mixed-Nash complementarity,
including zero-probability actions.

Two proof-writing points should be explicit in a Lean handoff:

1. from `U>=Q`, derive the second bound by splitting on
   `0 < L-U` (equivalently write the safe expression
   `max(0,L-Q)`); one should not use the unqualified inequality
   `max(0,L-U) <= L-Q` when the right side is negative;
2. the outer-hierarchy corollary is a theorem about the defined finite-center
   outer sets directly.  If stated through the current checked quantitative
   bracket API, it must carry the corresponding
   `HasEscapeAwareQuantileClockCompression` hypothesis until that transport
   theorem is formalized unconditionally.

Neither point changes the ordinary theorem.

## Novelty and disposition

The one-shot Nash existence and pure-time extremality ingredients are checked
and older, but the universal `2R/3` cap estimate and the resulting table-wide
outer-zero range are not present as a named declaration in the inspected
sources.  This materially rules out all normalized Fin4 lower certificates
through level 36 and is useful to the escape-aware certificate search.

I recommend a narrow export/formalization packet after the required separate
whole-packet gate.  Its scope must remain the unrestricted actual-center
bound and early outer-zero obstruction; it does not give a uniform payoff,
a terminal approximation, or a terminating zero test.
