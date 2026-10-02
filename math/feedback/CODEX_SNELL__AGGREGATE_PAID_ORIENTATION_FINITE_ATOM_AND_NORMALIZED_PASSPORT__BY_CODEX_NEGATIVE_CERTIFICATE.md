# Review of aggregate paid orientation and normalized atom passport

**Reviewer:** `CODEX_NEGATIVE_CERTIFICATE`  
**Verdict:** PASS as exact ordinary mathematics, with the formalization and
wording qualifications below  
**Scope checked:** Sections 2--6, including the added killed-face saturation
and reset-rigid classification

## Claim restated

For a positive-debt player, compare its actual stopping-law mixture with one
near-cap pure time.  Splitting the whole positive gain by which pure time is
earlier forces either a positive finite atom in the prescribed complete law,
or a positive finite atom in the literal near-cap response law whose selected
player debt tends to zero.  Exact cap-prefixing scales old law mass and total
debt by the same suffix reach, so the atom/debt ratio is nondecreasing.
Intersecting that cone with the killed-face law-tight exact-cap-prefix
saturation yields either same-point global-minimum regeneration or a strict
hull minimizer with unique all-Continue cap root.  In Fin4 the prescribed arm
is forced into the same-law reset-rigid branch; the response arm is either
reset-rigid or has finite law supported only on its killed owner's singleton.

## 1. Aggregate stopping-law split: valid

Write `v(q)` for the pure-time payoff against the fixed opponents and `mu`
for the selected player's actual stopping law.  The checked stopping-law
mixture identity gives

```text
U = E_mu v.
```

The pure-time supremum identity gives a pure `r` with `v(r)>C-eta` even when
the cap is not attained.  Hence

```text
v(r)-E_mu v > d-eta.
```

Replacing each summand by its positive part can only increase the sum.
Distinct elements of `Option Nat`, read with `Never` as infinity, have exactly
one strict orientation.  The equal-time summand is zero.  Thus the positive
sum splits exactly into the two displayed arms and their sum is strictly
larger than `d-eta`.

The edge signs are correct:

* `q<r`: the prescribed/source clock quits first and the receiving clock
  waits, so `(v(r)-v(q))_+ <= 2M L_q`;
* `r<q`: the receiving clock quits first, and the common opponent reach is
  `L_r`, so `(v(r)-v(q))_+ <= 2M L_r`;
* `r=Never`: the second arm is empty;
* finite `r`, `q=Never`: the term belongs to the second arm; and
* `q=r`, including both Never, contributes zero.

The countable sums are absolutely summable because `v` is bounded.  This
small analytic step is implicit in the note but causes no gap.

## 2. Atom type and constants: valid

In the source arm, `mu(q)L_q` is the actual probability that the selected
player's finite stopping clock is `q` and all opponents survive strictly
before `q`.  These events are disjoint in `q`; absorption occurs at `q` and
the terminal coalition contains the player.  Summing over `q<r` therefore
produces complete actual-law mass, not merely a chosen stage atom.

In the response arm, `r` is necessarily finite.  Under the literal pure-time
response, total stage absorption at `r` is exactly `L_r`.  Pigeonholing first
gives a stage coalition containing the responder; the checked pure-time
identity in fact makes its complete terminal-law mass equal to that stage
mass (the weaker checked stage-to-law inequality also suffices).

There are `2^(n-1)` coalitions containing a fixed player.  The orientation
split costs `2`, and the two-payoff bound costs `2M`.  The denominator is
therefore

```text
2 * 2M * 2^(n-1) = 2^(n+1) M.
```

For Fin4, `d>=D_*/4` and `eta<=D_*/8` give `d-eta>=D_*/8`; dividing by
`32M` gives the strict atom floor `D_*/(256M)`.  The constants and strictness
in Section 3 are correct.

Self-cap invariance under replacement of the selected player's own strategy
gives `B_i(P)=C`; consequently `d_i(P)=C-v(r)<eta`.  No cap attainment is
used.

## 3. Compactification and labels: valid

Only finitely many orientation arms and Fin4 coalition labels occur.  Passing
first to an infinite arm and then to a fixed coalition subsequence preserves
cofinality.  A further joint semantic/law compactification retains the fixed
law coordinate by ordinary coordinate continuity.

In the prescribed arm the semantic pairs still converge to the supplied
full-replacement endpoint, so `FullReplacementCluster.mover_debt_eq_zero`
retains the mover as the killed label.  In the response arm the exact bound
`d_i(P_k)<eta_k -> 0` and continuity retain the paid observer as the killed
label.  The latter replacement may reactivate the original mover, exactly as
the note warns.

Diffuse source clocks do not regress the proof: their many small atoms enter
the aggregate sum before coalition pigeonholing.  Nonattained caps do not
regress it either: one independently chooses an `eta_k`-near-cap pure time.

## 4. Exact cap-prefix passport: valid with its stated scope

For each finite root stack, repeated use of
`quittingTerminalOutcomeMass_rootThenContinuation` gives

```text
mu_prefix(S) = fresh_prefix_mass(S) + s_N mu_suffix(S)
             >= s_N mu_suffix(S).
```

The fresh term is nonnegative.  For the same literal exact cap--Nash stack,
`quittingCapLiftedPrefixProfile_debt_eq_suffixReach_mul` gives

```text
D(prefix)=s_N D(suffix).
```

Because positive global minimum implies every displayed debt is positive,
division and the ratio monotonicity are legitimate.  On a convergent joint
semantic/law subsequence, continuity of total debt and of the fixed law
coordinate yields (4.4).  Finite iteration telescopes exactly; a Zeno limit
retains the same lower bound, and an inert step has ratio one.

The regeneration qualification is essential and is correctly stated: the
ratio is preserved only if the complete joint semantic/law endpoint is used
as the next source.  A separately selected horizontal response or unrelated
Nashification need not retain it.

## 5. Killed-face saturation and minimizer: valid ordinary mathematics

The debt-weighted atom cone is closed, contains the origin, is preserved by
exact cap--Nash prefixing, and is downward same-law closed within `d_p=0`.
The last property holds because decreasing total debt only weakens its
right-hand side.  Its intersection with the killed-face law-tight saturation
is therefore nonempty and compact.

At a hull debt minimizer, exact cap-prefix scaling and the positive global
minimum force every exact cap--Nash root to have Continue mass one.  Product
root rigidity makes it literally all Continue; exact root existence supplies
existence and hence uniqueness.  The equality/strict split against `D_*` is
exhaustive.  In the equality branch, the checked same-point minimum-law
causalization keeps the semantic pair (hence the killed debt coordinate) and
its complete law (hence the positive atom).

At a strict minimizer, the arm labels are used correctly:

* prescribed arm: killed `p` is the endpoint mover; the retained `S`
  contains paid observer `i!=p`, so incidence `(p,i)` is at least `mu(S)>0`;
* response arm: killed `p=i`; if any positive finite atom contains another
  player, it supplies positive opponent incidence, and otherwise every
  positive finite outcome is exactly `{i}`, with possible Never mass.

Thus full positive-debt support is impossible once a killed coordinate is
present.  The prescribed arm cannot be singleton/Never at `p` because its
fixed positive atom contains `i!=p`.

Applying the checked fixed-law reset dispatch at positive incidence returns
the same complete law, keeps `d_p=0`, and has debt between `D_*` and the hull
minimum.  Law-tightness puts the return in the hull; hull minimality forces
equality of total debt.  If the dispatch selected its absorbing cap-root
exit, exact-prefix closure would create a lower-debt hull point, a
contradiction.  The all-Continue fixed branch is therefore forced.  The
returned point remains on the hull-minimum face, so unique cap-root rigidity
also applies there.  Consequently `D`, the killed label, every law atom, and
`mu(S)/D` are preserved exactly.

This also validates the no-rank conclusion.  `supported_toggle` is a static
reward-table inequality and the dispatch is allowed to return the same
labels and same law/debt data repeatedly.  The cited fixed-orbit regression
has global minimum zero, so it is only a local-independence regression, not a
counterexample to the positive-minimum conjecture; the note states this
correctly.

## 6. One wording qualification

The sentence saying that a member-leave toggle “does transport a coalition
under the corresponding literal Never replacement” should be read with a
qualification.  If the positive coalition is a singleton, removing its only
member need not produce a finite coalition `S\{member}`; the later terminal
outcome may be Never or another coalition.  For a nonsingleton coalition, the
pathwise transport on that baseline event is literal.  This does not affect
the note's conclusion, because it immediately denies any signed whole-payoff
or killed-coordinate transport and identifies that chronological interface
as missing.

An outsider-join toggle is even more plainly static: an arbitrary terminal
law atom does not by itself give the outsider an executable strategy that
joins exactly that random first-absorption event.  The note correctly leaves
this as the source-attached late-deviation problem.

## 7. Formalization boundary

Already Lean-checked are the stopping-law mixture and pure-time supremum,
first-disagreement edge identities, stage/complete-law identities, exact
cap-prefix debt and law scaling primitives, endpoint mover zero debt, fixed-law
reset dispatch, and the local fixed-orbit regression.

New ordinary mathematics, not yet a named Lean theorem, includes:

* the aggregate two-orientation summation and its finite-label extraction;
* the joint compactified source/response dichotomy as one package;
* the killed-face law-tight saturation with the atom cone;
* its minimizer and arm-sensitive reset-rigid/solo-Never classification; and
* the preservation/no-rank conclusion for the composite passport.

No claim of a terminal Nash profile, uniform payoff, full-debt elimination,
renewal, or executable toggle edge follows.  Subject to the singleton wording
qualification, the note's nonclaims match the actual theorem boundary.
