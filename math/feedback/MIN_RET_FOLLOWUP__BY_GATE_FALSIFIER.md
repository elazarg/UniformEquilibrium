# Export-gate falsification review of `MIN_RET.md`, Followup

Reviewer: `CODEX_GATE_FALSIFIER`

## Verdict

**CORE PASS; CURRENT PACKET FAIL UNTIL REPAIRED.**

The persistent-base fixed-law rigidity theorem is correct.  Its Fin4
application is also correct and genuinely identifies the fixed-law returned
semantic pair with the literal stationary pair-base target.  I found no flaw
in the Never-erasure coupling, the limiting-law support argument, the source
cap formula, or the final coordinatewise equality.

The Followup as currently written must not be exported, because Section 3
attributes maximality and uniqueness to the reset-incidence dispatch.  That
dispatch proves only a positive absorbing strict-debt root or an exact
all-Continue cap face.  The maximal/unique alternative comes from the separate,
already checked Research theorem
`QuittingPaidCapLiftedSource.maximalOneStepPaidResetRegeneration_or_uniqueAllContinue`.
It is not new content of the rigidity theorem and in fact can be applied to the
attained pair-base paid/reset source without first identifying the returned
point.

After separating those results, adding the boundary tests below, and exporting
only the final rigidity theorem plus its Fin4 same-point corollary, I recommend
**PASS**.  The new conjecture-facing change is the elimination of the separate
fixed-law returned semantic state on the explicit pair-base branch.  It is not
a completion of minimum return, a renewable descent, or a proof of UE.

## Sources checked

I checked:

- `FinFourPairBaseStationaryDebtLocalization.free_solved` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBaseStationaryDebtLocalization.lean`;
- `FinFourPairBasePaidResetTarget`, `target_joint`, `owner_reset`, and
  `exists_finFour_pairBasePaidResetDispatch` in
  `PairBasePaidResetAlignment.lean`;
- `QuittingFixedLawResetDispatch.prescribed_eq_target` and the existing
  payoff-aligned adapter in `PairBasePaidResetPayoffAlignment.lean`;
- `QuittingFixedLawResetDispatch`, especially `joint`, `target_ge`, and
  `dynamic_exit`, in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`;
- the definition of the joint carrier and its reward-moment theorem in
  `TerminalSemanticResetIncidenceReturn.lean`; and
- `maximalOneStepPaidResetRegeneration_or_uniqueAllContinue` in
  `Research/Quitting/PaidCapMaximalOneStepRegeneration.lean`.

No paper theorem is used.

## 1. Support of the persistent-base law

Let `B` have at least two members and let every member of `B` Quit surely at
date zero in the actual source profile.  Absorption is certain at date zero.
Every realized terminal coalition contains `B`, and the all-Never outcome has
mass zero.  Hence the source law `nu` satisfies

```text
nu(none)=0,
nu(some S)=0 whenever B is not a subset of S.
```

This is an exact law fact, not merely a support statement up to closure.  In
the Fin4 application it follows directly from the persistent-base root, in
which both displayed base coordinates are `PMF.pure true`.

If actual laws `nu_m` converge to `nu`, finiteness of the outcome space gives

```text
Pr_(nu_m)(terminal outcome omits a fixed j in B) -> 0.
```

The failure probability includes the all-Never outcome.  This is the only
limiting-law input required by the erasure proof.

## 2. Exact source cap formula

Fix `i in B` and choose `j in B\{i}`.  At the explicit source, `j` Quits surely
at date zero.  Therefore every complete behavioral replacement by `i` is
strategically exhausted at its date-zero action:

- if `i` Quits, its payoff is the source prescribed payoff `u_i`, since `i`
  itself is prescribed to Quit surely at that row;
- if `i` Continues, `j` still Quits and the game absorbs immediately, with
  expected payoff

  ```text
  E_i(nu) = sum_(S containing B) nu(some S) r_i(S\{i}).
  ```

The erased coalition is nonempty because it still contains `j`.  Any mixed
date-zero action is a convex combination of these endpoints, and later
behavior is unreachable.  Thus the unrestricted behavioral cap is exactly

```text
b_i = max(u_i,E_i(nu)).
```

This calculation does not replace the cap by a stationary or pure-root cap.
It evaluates every behavioral deviation because another base player forces
immediate absorption.

For `k notin B`, the theorem uses the explicit hypothesis that `k` is solved:

```text
b_k=u_k.
```

That is exactly the checked Fin4 pair-base localization field.  No stronger
claim about arbitrary free players should be inserted into the export without
a separate proof.

## 3. Never-erasure coupling for arbitrary realizing profiles

Let actual profiles `tau_m` jointly realize `(y,nu)`, where

```text
y=(u,beta).
```

Such a sequence exists from membership in the joint semantic/law carrier by
the sequential characterization of closure in this finite-dimensional metric
space.  Let `nu_m` be its original terminal law.  Replace the complete
behavioral strategy of `i` by pure Never and couple the two plays using the
same random choices for all opponents.

On an original sample path whose terminal coalition is `S` and contains
`j`, the following is exact:

1. no player Quits before the original terminal date;
2. replacing `i` by Never cannot create earlier absorption;
3. at the original terminal date `j` still Quits; and
4. the modified terminal coalition is exactly `S\{i}`.

The statement remains true whether or not `i` belonged to `S`.  On the
complementary event, the deviated payoff is only bounded below by `-M`, where
`M` bounds absolute rewards and also bounds the zero payoff at nonabsorption.
Consequently the complete Never deviation satisfies

```text
payoff_i(Never,tau_m[-i])
 >= sum_(S containing j) nu_m(some S) r_i(S\{i})
    - M Pr_(nu_m)(outcome omits j).
```

This is a coupling statement; it must not be justified merely by comparing
terminal masses termwise, because rewards may have either sign.  The
sample-path partition above is the correct proof.

The cap of `tau_m` dominates this actual behavioral deviation.  Joint
semantic convergence sends that cap to `beta_i`, coordinatewise law
convergence sends the displayed finite sum to `E_i(nu)`, and the failure term
tends to zero.  Hence

```text
beta_i >= E_i(nu).
```

Carrier debt nonnegativity gives `beta_i>=u_i`.  Therefore

```text
b_i=max(u_i,E_i(nu)) <= beta_i
```

for every `i in B`.  For `k notin B`, solvedness and carrier debt
nonnegativity give `b_k=u_k<=beta_k`.

I found no behavioral, late-stopping, Never, or nonattainment counterexample
to this argument.

## 4. Fixed-law rigidity and equality

The preceding proof establishes coordinatewise

```text
x.cap <= y.cap.
```

The same prescribed payoff need not be a primitive hypothesis if both joint
points display the same law: the checked reward-moment theorem already forces
it.  The export may either retain the explicit common-payoff hypothesis for a
minimal theorem surface or derive it from the same-law joint-carrier fields.

Since prescribed payoffs agree,

```text
D(y)-D(x)=sum_i (beta_i-b_i) >= 0.
```

If also `D(y)<=D(x)`, each summand is nonnegative and their finite sum is zero,
so every summand vanishes.  Thus `beta=b` and `y=x` as complete semantic
pairs.

For the Fin4 fixed-law reset dispatch:

- `target_joint` gives the actual pair-base target and its law;
- `dispatch.joint` gives the returned point with the same law;
- `prescribed_eq_target` gives equality of prescribed payoff vectors;
- `dispatch.target_ge` gives `D(returned)<=D(target)`; and
- `localization.free_solved` solves exactly the two players outside the
  two-element base.

All hypotheses of the rigidity theorem therefore hold, and the conclusion

```text
returned = target.semanticPair
```

is valid.  Since the target pair/law is literally realized by the stored
stationary profile, this equality also gives an actual realization of the
returned joint point by that original profile.  It does not identify an
arbitrary realizing sequence with the stationary profile pathwise.

## 5. Mandatory separation from the maximal-root theorem

After returned/target equality, `dispatch.dynamic_exit` honestly gives:

```text
an absorbing positive-survival exact cap root whose prefix has strictly
smaller total debt than the literal target,
```

or

```text
all Continue is an exact cap root and fixes the target semantic pair.
```

It does **not** say that all Continue is maximal or unique.

The stronger alternative

```text
strict-debt actual maximal-root paid/reset descendant
or every exact root is all Continue
```

is already supplied by
`maximalOneStepPaidResetRegeneration_or_uniqueAllContinue` after packaging the
same attained pair-base paid/reset source.  Its positive branch and uniqueness
proof use maximal absorption, not fixed-law rigidity.  The final export must:

1. state the new rigidity and returned-equals-target result independently;
2. if it records the maximal-root corollary, cite it explicitly as an existing
   composition; and
3. not claim that the new theorem proves maximality, uniqueness, renewability,
   or terminal consumption.

## 6. Boundary tests required in the final packet

### Necessity of at least two sure quitters

With players `i,j`, take the singleton base `{i}`.  Let `i` Quit at date zero.
In source profile `x`, let `j` Continue at date zero and Quit at date one.  In
same-law profile `y`, let `j` Never Quit.  Put

```text
r_i({i})=0,  r_i({j})=1,
```

and set the remaining rewards for `i`, and every reward for `j`, to zero.
Both profiles have the same terminal law concentrated on `{i}`, the same
prescribed payoff zero, and the free player is solved.  But in `x`, player `i`
can Continue at date zero and obtain `1` when `j` Quits at date one, so
`b_i(x)=1`; in `y`, every strategy of `i` yields zero, so `b_i(y)=0`.
Thus fixed-law cap rigidity fails for a singleton base.  The second sure
quitter is essential.

### Necessity of the common law

Take a two-player sure-Quit base with source reward zero on the base and reward
one after erasing one selected member.  The source member's cap is one.  An
unrelated all-Never profile can have cap zero after setting singleton rewards
to zero.  The laws differ.  Thus the law constraint, rather than prescribed
payoff equality alone, carries the erasure lower bound.

### Positive check

For a pure two-player base and arbitrary behavior of the remaining players at
the absorbing row, compute the source law explicitly.  The formula

```text
b_i=max(u_i,sum_S nu(S)r_i(S\{i}))
```

for a base member follows immediately and is attained by Quit and Continue.
This tests ties, mixed free-player actions, rewards of either sign, and the
absence of any cap-attainment assumption at the limiting carrier point.

## Conjecture-facing assessment

The result is not a solution to
`questions/FIN4_MINIMUM_RETURN_CAPSTONE.md` and not an answer to
`questions/FIN4_PAID_RESET_REGENERATION_RANK.md`.  It supplies no terminal
consumer and no well-founded regeneration.

It is nevertheless an exportable strict reduction after the repairs above:
on the explicit Fin4 pair-base fixed-law branch, the separately selected
returned semantic point is forced to be the literal stationary target.  This
removes a genuine cap-comparison/source-realization seam for every object in
that branch, leaving only the already named actual strict-debt child versus
all-Continue/unique-cap boundaries.  The export must describe exactly that
edge elimination, rather than presenting the existing maximal-root
alternative as new.

## Exact required repairs

1. Export a standalone final packet, not the earlier sections of `MIN_RET.md`.
2. Define the law on `none` and nonempty coalitions and define `E_i(nu)` only
   where erasure is nonempty.
3. State joint-carrier realization and carrier debt nonnegativity explicitly.
4. Present the Never argument as the sample-path coupling above; do not use an
   unsigned terminal-mass domination in the presence of negative rewards.
5. Add the singleton-base and different-law falsifiers.
6. Replace Section 3's maximality attribution by the exact reset-dispatch
   alternative, or cite the separate existing maximal-root theorem.
7. State plainly that positive-root descent is real-valued and nonrenewable,
   and that the all-Continue stall remains open.
