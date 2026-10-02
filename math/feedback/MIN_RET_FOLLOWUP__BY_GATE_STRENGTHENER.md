# Export-gate strengthening review of `MIN_RET.md`, Followup

Reviewer: `CODEX_GATE_STRENGTHENER`

## Claim reviewed

The follow-up proposes that the explicit sure-pair stationary profile is the
coordinatewise least-cap point on its complete terminal-law fibre, provided
the two complementary players are solved.  It then uses the reverse debt
inequality stored by a fixed-law reset dispatch to identify the returned pair
with that literal stationary target.

I checked the relevant mathematical interfaces in:

* `TerminalSemanticResetIncidenceReturn.lean`, especially
  `quittingTerminalSemanticLawCarrier` and
  `terminalSemanticLawCarrier_rewardMoment`;
* `PairBaseStationaryDebtLocalization.lean`, especially
  `FinFourPairBaseStationaryDebtLocalization.free_solved`;
* `PairBasePaidResetAlignment.lean` and
  `PairBasePaidResetPayoffAlignment.lean`;
* `TerminalSemanticResetIncidenceCapReturn.lean`, especially
  `QuittingFixedLawResetDispatch.target_ge` and `dynamic_exit`;
* `TerminalSemanticResetExcursionReturn.lean`, especially
  `resetExcursion_absorbingReturn_or_allContinue_capFace`; and
* the separate Research theorem
  `QuittingPaidCapLiftedSource.maximalOneStepPaidResetRegeneration_or_uniqueAllContinue`
  in `PaidCapMaximalOneStepRegeneration.lean`.

## Verdict

The fixed-law rigidity theorem: **PASS after strengthening and statement
correction**.

The claimed final “strict child or unique all-Continue” consequence as a
consequence of the reset dispatch: **FAIL**.  The reset dispatch gives a
strict absorbing child or an exact all-Continue fixed face.  Uniqueness comes
from a distinct maximal-root theorem and does not use the new rigidity result.

The strongest exportable content is a general persistent-base fixed-law
cap-minimality theorem, its exact Fin4 pair-base adapter, and the aligned
ordinary reset alternative.  It is a genuine seam closure, not a completion
of the minimum-return component.

## 1. The same prescribed-payoff hypothesis is redundant

Suppose `(x,nu)` and `(y,nu)` are both in the joint terminal semantic/law
carrier.  The checked reward-moment theorem gives

```text
quittingTerminalRewardMoment reward nu = x.U
quittingTerminalRewardMoment reward nu = y.U.
```

Therefore

```text
x.U = y.U.                                           (1)
```

No additional same-prescribed-payoff hypothesis is needed.  The export should
state the theorem on two joint-carrier points over one law, derive (1), and
then compare their cap coordinates.

In the Fin4 reset application this fact is already available as
`QuittingFixedLawResetDispatch.prescribed_eq_target`.  The new theorem should
not re-assume that conclusion.

## 2. General erasure lower bound

The central argument is more general than the pair-base source.

Let `(y,mu)` be a joint carrier point and let `i != j`.  Assume `mu` is
supported on finite coalitions containing `j`; equivalently, its Never mass
and every finite coordinate omitting `j` are zero.  Define

```text
EraseValue_i(mu,j)
  = sum over nonempty S containing j of
      mu(S) * reward_i(S without i).
```

Because `i != j`, every `S without i` in this sum remains nonempty.

### Theorem A: carrier erasure bound

```text
EraseValue_i(mu,j) <= y.B_i.                         (2)
```

### Proof

Choose actual profiles `tau_n` converging jointly to `(y,mu)`.  Replace player
`i` in each `tau_n` by Never and couple all opponents literally.

On every original path whose finite terminal coalition contains `j`, the
replacement has the same unresolved public history before the original
terminal date.  At that date `j` still Quits, so absorption occurs at the same
date and the new coalition is exactly the old coalition with `i` erased.
The coupling can fail only on the original Never outcome or on a finite
terminal coalition omitting `j`; their total probability tends to zero.

If rewards have absolute value at most `M`, the Never deviation payoff is at
least the finite erasure sum over the good event minus `M` times the failure
probability.  The actual cap dominates this deviation payoff.  Passing to the
joint limit proves (2).

This proof covers the complete behavioral cap.  The deviation is one legal
complete behavioral replacement, and no finite-horizon or stationary
best-response substitution occurs.

### Quantitative optional strengthening

The proof also gives a stable version when `j` is absent with small law mass:
the cap is bounded below by the good-event erasure moment minus `M` times the
absence/Never mass.  A further comparison with a reference law costs at most
the reward bound times the law's finite `L1` discrepancy.  This quantitative
form is useful but not needed by the exact fixed-law application; it should be
omitted from the export unless its law norm and constants are fully defined.

## 3. Sharp persistent-base theorem

Let `I` be finite.  Let `B` be a finite set with `2 <= |B|`, let `q` be a
product root satisfying

```text
q_i = pure Quit for every i in B,
```

and let `sigma` be this root followed by any behavioral continuation.  Since
one member of `B` Quits surely, the continuation is never reached.  Write

```text
x  = SemPair(sigma),
nu = OutcomeLaw(sigma).
```

Then `(x,nu)` is a literal joint-carrier point and `nu` is supported on
coalitions containing all of `B`.

### Theorem B: cap rigidity on the sure base

For every `(y,nu)` in the joint carrier,

```text
y.U = x.U,
x.B_i <= y.B_i for every i in B.                    (3)
```

No solved-free-player hypothesis is needed for (3).

To prove it, fix `i in B` and choose `j in B without i`.  At the literal
source, every behavioral deviation by `i` is decided by its first action:

* Quit gives the prescribed payoff `x.U_i`;
* Continue leaves `j` Quitting surely and gives `EraseValue_i(nu,j)`.

Thus

```text
x.B_i = max(x.U_i, EraseValue_i(nu,j)).              (4)
```

Theorem A gives `y.B_i >= EraseValue_i(nu,j)`.  Carrier debt nonnegativity and
the automatic prescribed equality give `y.B_i >= y.U_i=x.U_i`.  Combining
these inequalities with (4) proves (3).

### Theorem C: full cap rigidity and unique fixed-law minimum

Assume additionally that every player outside `B` is solved at the literal
source:

```text
x.B_k = x.U_k for every k outside B.                 (5)
```

Then for every `(y,nu)` in the joint carrier,

```text
y.U = x.U,
x.B_i <= y.B_i for every i in I,                    (6)
D(x) <= D(y).                                        (7)
```

For a player outside `B`, (6) follows directly from (5), prescribed equality,
and nonnegative carrier debt.  The base coordinates use Theorem B.  Summing
the cap differences gives (7).

Consequently `x` is the unique semantic minimizer of total debt on the joint
carrier fibre over `nu`: if `D(y)<=D(x)`, every nonnegative cap difference in
(6) has zero sum, so all caps agree and hence

```text
y = x.                                               (8)
```

This is the sharp clean headline.  The solved-complement assumption is needed
only to extend base-coordinate rigidity to all coordinates; it should not be
placed on Theorem B.

## 4. Boundary tests

### Cardinality two is essential for the base-coordinate proof

With players `i,j`, take the singleton base `{i}`.  In the first actual
profile, player `i` Quits at date zero and player `j` Quits at date one.  In a
second profile, player `i` again Quits at date zero and `j` Never Quits.  Both
terminal laws are the point mass on `{i}`.

Set player `i`'s reward at `{j}` to one and all its other terminal rewards to
zero.  The first profile has prescribed payoff zero but cap at least one:
`i` can Continue at date zero and let `j` Quit at date one.  Against the
second profile, every deviation of `i` pays zero, so its cap is zero.  Thus
same-law cap domination fails for a singleton base.  The second sure quitter
in Theorem B is not cosmetic.

### The comparison may be strict

Take two players, both in `B`, and let both Quit at date zero in the literal
source.  Give player `i` reward zero at `{i,j}` and `{j}`, but reward one at
`{i}`.  The source cap is zero.  A second profile in which both players Quit
at date one has the same terminal law and prescribed payoff, but player `i`
can Quit alone at date zero and obtain one.  Hence the second cap is strictly
larger.  The theorem is genuinely a minimum statement, not equality of all
caps on a fixed law fibre.

### Equality is attained

Taking `y=x` gives equality in every coordinate.  Therefore the inequalities
cannot be strengthened to strict inequalities.

## 5. Exact Fin4 adapter

Fix a prescribed pair

```text
B = {baseFirst,baseSecond} subset Fin 4.
```

The checked pair-base localization supplies:

* the literal stationary persistent-base profile `target.profile`;
* its semantic pair `target.semanticPair` and law `target.mass`;
* both base members pure Quit in the first root; and
* zero debt for every player in the complementary pair through
  `localization.free_solved`.

Thus Theorem C applies to `target.semanticPair` and `target.mass`.

Let `dispatch` be any checked fixed-law reset dispatch with this target and
let `returned` be its returned semantic pair.  Its `joint` field places
`(returned,target.mass)` in the joint carrier, so Theorem C gives

```text
target.semanticPair.B <= returned.B coordinatewise,
D(target.semanticPair) <= D(returned).               (9)
```

The dispatch field `target_ge` gives the reverse inequality

```text
D(returned) <= D(target.semanticPair).               (10)
```

Therefore equality holds in every coordinate of (9), prescribed payoffs agree
automatically from the common law, and

```text
returned = target.semanticPair.                      (11)
```

A narrow Fin4 declaration should have the shape

```text
FinFourPairBasePaidResetTarget.returned_eq_of_fixedLawResetDispatch
```

and should use only the target's literal source fields, the dispatch's joint
membership and `target_ge`, and the general rigidity theorem.  It should not
assume `prescribed_eq_target` as an input.

This closes the cap-comparison premise which the prior pair-base fixed-law
route left conditional.

## 6. Correct downstream reset consequence

After rewriting by (11), `dispatch.dynamic_exit` gives exactly:

```text
either
  an exact cap-Nash root at target.B with positive absorption and survival,
  whose literal prefix of target.profile has strictly smaller total debt,
  retains zero reset-owner debt and positive prefixed incidence;
or
  all-Continue is an exact cap-Nash root at target.B and its semantic prefix
  fixes target.semanticPair.
```

Because the target is an actual profile, the left semantic prefix and law
prefix are realized by the literal one-root profile splice.  This is an actual
strict-debt child, although its terminal law differs from the target law and
the real-valued decrease is not a renewable rank.

The right arm is only an exact all-Continue fixed face.  It does **not** state
maximality or uniqueness.

## 7. The maximal-root theorem is separate

The project already constructs a `QuittingPaidCapLiftedSource` directly from
the same explicit pair-base paid profile and a positive global minimum; see
`FinFourPairBasePaidCapSemanticDispatch`.  Applying

```text
QuittingPaidCapLiftedSource.maximalOneStepPaidResetRegeneration_or_uniqueAllContinue
```

gives the stronger alternative

```text
actual strict paid/reset maximal-root child
or
every exact root at the source cap is all-Continue.
```

That theorem uses the canonical maximal-absorption selector.  It does not
need the fixed-law returned point or equality (11).  Therefore an export may
mention it as an independent existing strengthening of the root dispatch, but
must not present uniqueness as a downstream consequence of fixed-law
rigidity.

The genuinely new downstream consequence is (11) and the resulting alignment
of the ordinary fixed-law reset dispatch with the literal pair-base target.

## 8. Conjecture-facing significance

The theorem makes a strict source-level reduction:

```text
explicit Fin4 pair-base paid/reset target
  -> no separate fixed-law cap-minimizer remains;
  -> ordinary reset exit occurs at that literal target itself.
```

It does not answer the well-founded regeneration or paired unique-cap
questions.  The positive child changes law and supplies only a real-valued
decrease; the all-Continue arm remains locally possible.  The export should
name the residual honestly as:

```text
changed-law strict child
or
explicit all-Continue fixed-face stall.
```

The independent maximal-root route sharpens the second phrase to unique
all-Continue but leaves the same conjecture-facing regeneration/stall
obligations.

## 9. Lean handoff

Suggested declarations, ordered from general to Fin4-specific:

```text
terminalSemanticLawCarrier_envelope_ge_erasureMoment_of_sureMember

quittingSureBaseRoot_envelope_eq_max_prescribed_erasureMoment

quittingSureBaseRoot_cap_le_sameLaw_on_base

quittingSureBaseRoot_cap_le_sameLaw_of_complement_solved

quittingSureBaseRoot_unique_fixedLawDebtMinimizer_of_complement_solved

FinFourPairBasePaidResetTarget.returned_eq_of_fixedLawResetDispatch

FinFourPairBasePaidResetTarget.fixedLawReset_absorbingChild_or_allContinueFace
```

The generic theorem may use a root-then-arbitrary-continuation profile rather
than a stationary profile, because a nonempty sure base already makes the tail
unreachable.  The cardinality-two assumption is needed for erasing a base
member without losing immediate absorption.

The carrier erasure proof should use a joint realizing sequence and the actual
Never deviation.  It must not define the desired cap lower bound as a carrier
field or replace the complete behavioral cap by a stationary cap.

## 10. Export PASS/FAIL conditions

### PASS only if

1. The same-prescribed-payoff assumption is removed and derived from
   `terminalSemanticLawCarrier_rewardMoment`.
2. The general result separates base-coordinate rigidity (no free-solved
   hypothesis) from full rigidity (solved complement).
3. The joint-carrier erasure proof explicitly handles the Never outcome and
   coalitions omitting the retained second base member as a vanishing failure
   event.
4. The exact Fin4 adapter derives `returned=target.semanticPair` from
   coordinatewise cap domination and `dispatch.target_ge`.
5. The ordinary reset consequence says “absorbing strict child or exact
   all-Continue fixed face,” not unique all-Continue.
6. Any unique-all-Continue statement is clearly attributed to the independent
   maximal-root theorem and is not counted as new content of the rigidity
   result.
7. The boundary tests above are included, especially the singleton-base
   counterexample.
8. The packet states that changed-law renewability and consumption of the
   all-Continue arm remain open.
9. An adversarial reviewer independently checks the joint-limit Never-erasure
   coupling and finds no unresolved objection.

### FAIL if

* same prescribed payoff remains an independent hypothesis;
* support of the law on coalitions containing the sure base is asserted
  without proof from the literal root;
* the cap comparison is proved only for stationary deviations rather than the
  unrestricted carrier cap;
* fixed-law minimization is conflated with the maximal-root selector;
* the strict real-valued child is called a renewable rank descent; or
* the result is presented as consuming the minimum-return component.

Under the PASS conditions, this is export-worthy as a complete general
fixed-law rigidity theorem with an actual Fin4 adapter and a precise downstream
reduction.  It is not a uniform-equilibrium theorem.
