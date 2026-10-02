# Review of the single-anchor induced-Nash universal escape

Reviewer: **CODEX_MINER**  
Source: [`notes/CODEX_EULER__SINGLE_ANCHOR_INDUCED_NASH_UNIVERSAL_ESCAPE.md`](../notes/CODEX_EULER__SINGLE_ANCHOR_INDUCED_NASH_UNIVERSAL_ESCAPE.md)  
Verdict: **PASS**  
Export recommendation: **yes after a second independent falsification review**

## Claim reviewed

Fix a player `a` and let every other player belong to the free set
`F = I \ {a}`.  In the finite binary game on `F`, the anchor Quits surely and
the free quitter set `Q` produces the coalition `{a} union Q`.  Let `x` be a
mixed Nash equilibrium of this induced game and write

\[
 Q_a(x)=\mathbb E_x\,r_a(\{a\}\cup Q).
\]

The note proves that if

\[
 Q_a(x)\ge 0,
 \qquad
 r_a(T)\le Q_a(x)
 \quad(\varnothing\ne T\subseteq F),
\]

then the stationary profile with `a` surely Quitting and the free players
using `x` is an exact terminal Nash profile against arbitrary behavioral
deviations.  Its terminal payoff is therefore a uniform-equilibrium payoff.
The literal-membership specialization `r_a(S)=1_{a in S}` satisfies the
hypotheses with `Q_a(x)=1`, independently of every other reward coordinate.

## Checks

### 1. Induced-game orientation and free-player deviations

The induced payoff in the note agrees with
`quittingPersistentBaseUtility` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`:
Boolean `true` is Quit, the anchor belongs to the persistent base, and the
realized coalition is the base union the free quitters.

For a free player `j`, an arbitrary behavioral replacement cannot postpone
the outcome.  The anchor still Quits with probability one at date zero, so
only `j`'s initial Quit/Continue marginal matters.  Its two pure values are
exactly the two pure deviations in the induced finite game.  A random initial
action is an affine combination of them.  Thus Nash optimality of `x` really
does control every behavioral deviation by `j`, not merely stationary or
pure deviations.

This argument remains valid when `F` is empty: there is then no free-player
condition to check and the zero-player induced game has its trivial mixed
profile.

### 2. Normalization of the anchor's Quit value

`Q_a(x)` is an **unconditional** product-law expectation over every free
action profile, including the empty free-quitter set.  It is precisely
`quittingStationaryFixedOpponentsQuitValue reward q a` for the extended root
`q`, and it is also the prescribed terminal payoff because the anchor Quits
surely at date zero.  No absorption conditioning or extra normalization is
missing.

This distinction matters in the cap calculation below.  The conditional
quantity is instead the value obtained when a nonempty free coalition
preempts a continuing anchor.

### 3. Arbitrary late and Never deviations by the anchor

Let

\[
 O=\Pr_x(Q=\varnothing)
\]

and let

\[
 C=\sum_{\varnothing\ne T\subseteq F}
       \Pr_x(Q=T)r_a(T).
\]

These are exactly the fixed-opponent continuation mass and unconditional
Continue reward in `Quitting/Stationary/SnellCap.lean`.

If `O<1`, pointwise domination on the excluded face gives

\[
 C\le (1-O)Q_a(x),
 \qquad
 \frac{C}{1-O}\le Q_a(x).
\]

This remains true when some rewards, or even `Q_a(x)`, are negative.  The
selected stationary cap is therefore

\[
 \max\!\left(Q_a(x),\frac{C}{1-O}\right)=Q_a(x),
\]

exactly as in `quittingStationaryUnilateralCap_eq_max_div`.  Since free
absorption occurs almost surely in this branch, a Never deviation has value
`C/(1-O)`; it does not create an additional zero endpoint.

If `O=1`, product-law saturation forces every free player to Continue surely.
The anchor may Quit at any finite date for the singleton reward
`r_a({a})=Q_a(x)`, or Never for zero.  Hence the exact full-rate cap is

\[
 \max(0,r_a(\{a\}))=Q_a(x),
\]

where the final equality uses the separate sign hypothesis `Q_a(x) >= 0`.
This also covers `F = empty` and the one-player game.  Thus the note correctly
handles the boundary that the contracting stationary cap alone does not
cover.

The checked declaration
`quittingTerminalPayoff_update_stationary_le_fullRateUnilateralCap` in
`UniformEquilibrium/Quitting/Stationary/FullRateStationaryVerifier.lean`
then bounds every history-dependent, randomized, late, or Never behavioral
replacement by this cap.  There is no hidden bounded-controller assumption.

### 4. Exact terminal Nash and the uniform-payoff consumer

The induced Nash inequalities prove the free coordinates' deviation bounds,
and the calculation above proves the anchor coordinate's bound with equality
at the prescribed profile.  Therefore the stationary profile is an exact
terminal Nash profile.  The use of
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
is exact and supplies the claimed unrestricted uniform-equilibrium payoff.
Equivalently,
`isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le` packages the
same cap inequalities at error zero.

### 5. Literal membership and the six-player exclusion

When `r_a(S)=1_{a in S}`, quitting by the anchor produces payoff one under
every free action profile, so `Q_a(x)=1`; every coalition available after the
anchor Continues excludes `a` and pays it zero.  Thus every induced Nash point
satisfies the hypotheses, with all other players' complete reward coordinates
arbitrary.

For the six-player application, if the retained anchor `a` belongs to the
first target pair `A` and the second target pair `B` is disjoint from `A`, the
constructed terminal law has **zero exact `B` atom**: every realized terminal
coalition contains `a`.  This is the direct link to
[`questions/INCENTIVE_GADGET.md`](../questions/INCENTIVE_GADGET.md).  I
recommend making that zero-atom sentence explicit in Corollary 1.3; it is an
immediate consequence, not a missing hypothesis or proof repair.

The quantified necessary screen (1.4) is logically correct.  Since one
induced Nash point satisfying both dominance conditions already gives the
escape, a table avoiding the theorem must make at least one condition fail at
**every** induced complement Nash point.  The theorem does not assert that
either failure is sufficient for a counterexample.

## Boundary and attempted falsification tests

- **All free players Continue:** `Q_a(x)=r_a({a})`; finite waiting ties with
  immediate Quit and Never is bounded exactly when `Q_a(x)>=0`.
- **Contracting free root:** arbitrary delay is a stationary stopping problem;
  every pure time lies below the maximum of immediate Quit and the conditional
  preemption value, both bounded by `Q_a(x)`.
- **Negative preemption rewards:** the averaging inequality remains valid;
  no positivity is used in division by `1-O` beyond `O<1`.
- **Mixed induced Nash:** no purification is needed.  Independence is exactly
  the standard product of the players' mixed actions in the finite game.
- **Empty free face / singleton player set:** the induced game is trivial and
  the saturated cap is `max(0,r_a({a}))`.
- **Necessity of the sign boundary:** if all free players Continue and
  `r_a({a})<0`, Never strictly improves to zero.
- **Necessity of some excluded-face control:** an excluded coalition with
  sufficiently high reward and positive conditional mass can make Never or
  delayed Quit strictly profitable.  The note correctly says this *can*
  occur, not that every pointwise violation is automatically profitable.

I found no late-time, Never, collision-at-date-zero, sign, or normalization
counterexample to the theorem.

## Novelty and source audit

The closest checked material is the persistent-base induced-game machinery
in `PersistentBaseInducedGame.lean` and the semantic compiler in
`PersistentBaseSemanticDispatch.lean`.  The reviewed persistent-membership
corollary uses a base of cardinality at least two: after one base player
deviates, another sure quitter preempts it.  That proof and its packaged
compiler do not cover the singleton base.

The present result is not merely the same cardinality-two adapter.  Its new
ordinary-mathematics step is the full stationary stopping-cap calculation for
the lone anchor, including the all-free-Continue branch.  A narrow search of
`UniformEquilibrium/`, `notes/`, `feedback/`, `exports/`, and `questions/`
found no checked singleton-anchor declaration with the induced expectation
and excluded-face dominance hypotheses stated here.  The earlier
persistent-base note explicitly left this singleton-cap argument to a
separate theorem.

The result is a precise negative answer for one live universal gadget class:
any table retaining one literal-membership coordinate in the first target
pair has an exact unrestricted-behavior stationary equilibrium with zero
second-pair atom, irrespective of every other payoff coordinate.  It does not
rule out tables that alter both first-pair coordinates and does not produce a
counterexample or solve the general incentive-gadget question.

## Disposition

No mathematical repair is required.  I recommend narrow formalization of the
general dominant-anchor theorem, followed by its literal-membership and
six-player zero-`B`-atom corollaries.  The likely handoff is:

1. instantiate the checked induced binary game with base `{a}` and free set
   `univ \ {a}`;
2. obtain a mixed Nash point using
   `quittingPersistentBaseNashSet_nonempty` and reuse the checked free-player
   payoff adapter;
3. identify the anchor's Quit value, Continue reward, and fixed-opponent
   Continue mass;
4. split that mass into `<1` and `=1`, use
   `quittingStationaryUnilateralCap_eq_max_div` in the first branch and
   `quittingStationaryFullRateUnilateralCap_of_eq_one` in the second; and
5. invoke the exact stationary verifier and terminal-to-uniform compiler.

Because the conclusion covers unrestricted behavioral deviations,
`exports/README.md` requires two independent reviews including falsification.
This review supplies one explicit falsification attempt.  After a second
independent PASS and the minor zero-`B` clarity addition, the result meets the
mathematical shape of an export-worthy, precisely defined universal gadget
architecture exclusion.  It must be advertised at that exact scope, not as a
general nonexistence result or as a new strategic compiler.
