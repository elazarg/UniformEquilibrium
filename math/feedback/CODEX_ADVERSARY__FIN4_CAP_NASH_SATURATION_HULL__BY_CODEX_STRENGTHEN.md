# Adversarial review of the cap--Nash saturation hull

Reviewer: `CODEX_STRENGTHEN`

Claim reviewed: the compact exact-cap-prefix saturation construction,
law-tight strengthening, minimum-face neutrality, fixed-law reset consequence,
and Fin4 neutral trichotomy in
[`CODEX_ADVERSARY__FIN4_CAP_NASH_SATURATION_HULL.md`](../notes/CODEX_ADVERSARY__FIN4_CAP_NASH_SATURATION_HULL.md).

Verdict: **PASS for the core saturation theorem, law-tight strengthening,
same-point minimum regeneration, and fixed-law neutral trichotomy, after the
explicit proof obligations below are added.**  I found no counterexample to
the hull mechanism.  Its main conclusion is exactly cap--Nash, not
prescribed-payoff Nash, and its law is the finite terminal-outcome law
(coalition or Never), not a stopping-time or chronological law.  Those two
scope restrictions are essential.

Sections 11--13 contain sound regression calculations at paper level, but the
two new tables do not inherit the cited checked root-uniqueness theorem merely
by citation: an extensional endpoint-difference calculation must be included.
The generic hull theorem should be the main export; the local regressions may
remain a reviewed boundary appendix until those calculations are written as
standalone lemmas.

## 1. Compact hull: validated

Let `C` be `quittingTerminalSemanticLawCarrier reward`, let `z0` belong to
`C`, and let `F` be the family of all ambient-closed subsets `A` of `C` which
contain `z0` and are invariant under every root Nash against the displayed cap
coordinate.  The family is nonempty: `C` itself is compact, hence closed, and
`quittingTerminalSemanticLawPrefix_mem_carrier` preserves it for every root.

The intersection `H=inter F` is closed, nonempty because every member contains
`z0`, and contained in the compact carrier.  Its prefix invariance is
pointwise.  If `z in H` and `x` is exact cap--Nash at `z`, then `z in A` for
every `A in F`; the defining closure of each `A` gives `P_x z in A`, hence
`P_x z in H`.  No root at a nearby point and no lower-hemicontinuity of the
Nash correspondence is used.  In particular a root which appears only at a
limit point is still applied inside every defining invariant.

This construction is set-theoretically impredicative but ordinary: in Lean it
can be defined as a set intersection or as the set of points belonging to
every invariant set.  No transfinite recursion is required.

## 2. Exact debt/law scaling and atom cone: validated

For `z=(X,mu)` and a root `x` exact Nash against `X.2`, the checked theorem
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` gives,
coordinatewise and hence after finite summation,

\[
 D(T_xX)=q(x)D(X).
\]

The law action in
`quittingTerminalOutcomeLawPrefix` gives for a finite terminal coalition `S`

\[
 (P_x\mu)(\operatorname{some}S)
 =\operatorname{RootCoalitionMass}_x(S)+q(x)\mu(\operatorname{some}S).
\]

Thus debt and the retained part of the atom use the identical factor `q(x)`.
The cone

\[
 D(X_0)\mu(\operatorname{some}S)\ge D(X)b_0
\]

is ambient closed, contains `z0`, is prefix invariant, and, under the proposed
law-tight operation, is also downward same-law invariant.  Since the global
debt floor is positive, division gives the uniform atom floor

\[
 \mu(\operatorname{some}S)
 \ge D(X)b_0/D(X_0)
 \ge D_*b_0/D(X_0)>0.
\]

There is no missing sign assumption: carrier debts are nonnegative and the
stated global lower bound supplies `D(X0)>0`.

The word “law” must remain qualified.  The checked coordinate type is
`QuittingTerminalOutcome iota -> Real`, recording only the terminal coalition
and `none`/Never.  It does not record dates, marginal stopping laws, or source
ancestry.  The atom invariance is therefore a time-forgetting terminal-law
statement.

## 3. Minimum face and root uniqueness: validated

Continuity of total semantic debt on compact nonempty `H` gives a minimizer
`zH`.  For any exact cap--Nash root `x` at `zH`, hull invariance and exact
scaling give

\[
 D_H\le q(x)D_H.
\]

As `D_H>=D_*>0` and `0<=q(x)<=1`, one has `q(x)=1`.  The checked
`eq_quittingAllContinueRoot_of_continueMass_eq_one` then gives
`x=quittingAllContinueRoot`.

Conversely, `exists_isZeroQuittingRootNash X_H.2` supplies at least one exact
cap root.  The preceding argument identifies it with all Continue, proving
both existence and uniqueness of that root.  All-Continue fixes the outcome
law definitionally.  Its exact cap--Nash property supplies the singleton
inequalities needed for the semantic prefix to fix both the prescribed and
cap coordinates.  Hence the claimed exact self-loop is sound.

The same proof applies to every point of the debt-minimum face.  At an
arbitrary hull point `X`, prefix closure also gives the useful sharp estimate

\[
 \operatorname{Abs}(x)
 \le {D(X)-D_H\over D(X)}.
\]

This is stronger than merely saying that absorption vanishes at the minimum
face.

Nothing here says that all Continue is Nash against `X.1`, the prescribed
payoff coordinate.  The Nash tail is `X.2`, the unrestricted behavioral cap.
The note correctly warns that the checked prescribed-payoff plateau theorem
cannot be applied.  This warning should occur in the exact theorem statement,
not only in the self-audit.

## 4. Law-tight hull: validated

Define a law-tight invariant to be additionally closed under `(X,mu) ->
(Y,mu)` whenever the latter is in the joint carrier and `D(Y)<=D(X)`.  The
whole carrier is again a witness.  Intersections preserve this implication
pointwise.  The atom cone is law-tight because its left side is unchanged and
its right side decreases.

At a law-tight hull minimizer `(XH,muH)`, one indeed has

\[
 D(X_H)\le D(Y)
 \quad\hbox{for every carrier point }(Y,\mu_H).
\]

If `D(Y)<=D(XH)`, law-tightness places `(Y,muH)` in the hull and hull
minimality reverses the inequality; if `D(Y)>D(XH)`, the displayed conclusion
is immediate.  This two-case proof should be stated explicitly in the export.

## 5. Same-point regeneration at `D_H=D_*`: validated but not by the cited producer alone

If `D(XH)=D_*`, carrier membership and the global lower bound show that
`XH` is minimal against every point of
`quittingTerminalSemanticCarrier reward`.  Therefore the exact hypotheses of
`finFourHardResidual_minimumLaw_causalSuffixAtom` hold at the same joint-law
point `zH`.  Together with the hard residual, positive infimum equality, and
the returned atom, this packages a `FinFourMinimumAtomProducer` whose
`residual` is definitionally the input residual.

This is a genuine same-point adapter.  However,
`FinFourMinimumAtomProducer.exists_residual_eq_of_hardResidual` already
produces some minimum atom source from the residual without using the hull.
The new content is not bare existence of a same-residual minimum producer; it
is that the **hull minimizer itself**, with its retained hull law, can be
causalized when `D_H=D_*`.  The export should say this to avoid overstating
novelty.

## 6. Fixed-law reset consequence and Fin4 trichotomy: validated with one omitted extraction

Let `(X,mu)` be a strict law-tight minimum-face point and suppose owner `o`
has zero debt and positive total opponent incidence.  The fixed-law reset
dispatch, with the global minimum semantic point as source and `X` as target,
returns `(R,mu)` with

\[
 D_*\le D(R)\le D(X)=D_H.
\]

Law-tightness places `(R,mu)` in the hull; hull minimality gives the reverse
inequality and hence `D(R)=D_H`.  The returned point is on the minimum face,
so every exact cap root there is all Continue.  Equivalently, the dispatch's
strictly absorbing dynamic arm would prefix to a hull point of debt below
`D_H`, which is impossible.  The all-Continue reset-rigid arm is forced.

One small step is missing from Section 9.  The checked dispatch takes a
specific `other` with positive
`quittingTerminalOpponentIncidenceMass o other mu`, whereas (22) is stated
using positive **total** incidence.  Expand
`quittingTerminalTotalOpponentIncidenceMass`; nonnegativity of every summand
and positivity of the finite sum select `other != o` with a positive
coordinate.  This is elementary but must be present in the theorem proof.

The Section 10 trichotomy is exhaustive.  If all debts are positive, one is in
Chamber I.  Otherwise choose a zero-debt owner.  Positive total incidence
gives Chamber II.  If every zero-debt owner has zero total incidence,
nonnegativity of the outcome law implies that every positive finite atom is a
subset of each such owner singleton.  The retained positive atom then prevents
two distinct zero-debt owners.  Thus the zero-debt set is `{o}` and all finite
law mass is on `{o}`, with the remaining mass on Never.  This proof uses the
simplex/nonnegativity property of the carrier law and should cite
`terminalSemanticLawCarrier_mass_mem_stdSimplex`.

## 7. Singleton/Never cap-tight lemma: plausible and complete after making its hidden topology explicit

Lemma 8 is correct, but its current proof compresses the main analytic step.
From carrier membership choose an actual-profile sequence whose semantic/law
points converge to `(X,mu)`; this uses sequentiality of the finite-dimensional
carrier.  Let

\[
 \mu=p\delta_{\{o\}}+(1-p)\delta_{\mathrm{Never}},\qquad p>0.
\]

The reward-moment identity gives `u_o=p*r_o({o})`, and zero owner debt gives
`c_o=p*r_o({o})`.  If `p=1`, the desired cap equality is immediate.

If `p<1`, the approximating joint Never probability tends to `1-p>0`.
Hence every marginal Never probability is eventually bounded below by one
fixed positive constant.  For `j != o`, independence of the players' live
stopping laws gives the one-sided cylinder bound

\[
 \Pr(\text{terminal }\{j\})
 \ge\Pr(T_j<\infty)\prod_{k\ne j}\Pr(T_k=\infty).
\]

Indeed the product event has `j` stop finitely while every other player Never
stops, and is therefore a subset of the terminal-singleton event.  Equality
is generally false: another player may have a later counterfactual finite
stopping time after `j` has already absorbed the game.  The left side tends to
zero and every factor in the product is bounded below, so
`Pr(T_j<infinity)->0`.  Bounded rewards then show that owner `o`'s
immediate-Quit deviation tends to `r_o({o})`, while its Never deviation tends
to zero.  Passing these two lower bounds through the convergent cap coordinate
gives

\[
 c_o\ge\max\{0,r_o(\{o\})\}.
\]

Together with `c_o=p*r_o({o})` and `0<p<1`, this forces
`r_o({o})=c_o=0`.  Thus `c_o=r_o({o})` in both cases.

The export must replace the note's claimed **equality** by this cylinder
**lower bound**, and include either its proof or a named checked stopping-law
theorem together with a quantitative bounded-payoff estimate.  The phrase
“literal approximating profiles” alone is not enough for a closure point.
This is a mandatory correction, but the corrected inequality proves the same
conclusion and supplies no counterexample to Lemma 8.

Once cap tightness is established, all-Continue cap--Nash gives every
singleton reward below the cap, and
`exists_quittingSingletonCollisionGain_pos_of_unique_allContinue` gives a
distinct binding player with positive join gain.  Iteration on the finite
binding set produces a directed cycle of length at least two.  The cycle need
not contain the original owner; the statement should not imply that it does.

## 8. Regression-table audit

The arithmetic in Sections 11 and 13 is consistent.

For Section 11, with the displayed date-zero half-quit by player `0`, the law
is `1/2 delta_{0}+1/2 delta_Never`, the prescribed vector is
`(1/2,0,3/10,1/2)`, and direct pure-time optimization gives cap `(1,1,1,1)`.
For Section 13, the analogous calculation gives prescribed vector
`(0,-1/2,-1/5,1/2)` and cap `(0,0,0,1)`.  Because only player `0` can quit
under the prescribed profile, the otherwise arbitrary passive values are not
reached by a unilateral deviation; the stated constrained values are enough
for these cap calculations.

At the one-stage root game, the passive term cancels between Quit and Continue
for every nonempty opponent coalition, while `a_i(empty)=c_i` cancels the
empty-coalition continuation.  Hence both new tables have the same endpoint
differences as the owner-risky increment table.  This supports unique
all-Continue cap root.

Nevertheless, `FinFourOwnerRiskyCapLimitRootUniqueness.eq_allContinueRoot_of_isNash`
is a theorem about its named concrete reward/cap.  It cannot be applied to the
new parametric passive tables without first proving equality of all endpoint
differences or extracting a generic increment-form uniqueness lemma.  The
note says this informally; an export containing the regressions must include
that finite calculation.  The regression tables also do not satisfy, and are
not claimed to satisfy, positive-minimum hard-residual provenance.

## 9. Strongest standalone exportable theorem

The strongest clean export is the following generic theorem, followed by its
Fin4 adapter.

> **Law-tight cap--Nash saturation theorem.**  For a finite nonempty player
> set and bounded quitting reward table, assume total semantic debt is bounded
> below by `D_*>0` on the joint semantic/outcome-law carrier.  Given a carrier
> point `z0=(X0,mu0)` and a finite coalition `S` with
> `mu0(some S)=b0>0`, there exist a nonempty compact set `Hhat` and
> `zH=(XH,muH) in Hhat` such that:
>
> 1. `z0 in Hhat`, and `Hhat` is invariant under every exact root Nash
>    against the displayed cap;
> 2. `Hhat` is downward closed under same-outcome-law carrier replacement;
> 3. every `(X,mu) in Hhat` satisfies
>    `D(X0)*mu(some S) >= D(X)*b0`;
> 4. `zH` minimizes debt on `Hhat` and on its entire same-law carrier fibre;
> 5. all Continue is the unique exact cap--Nash root at every point of the
>    debt-minimum face and fixes that point under semantic/law prefixing;
> 6. `muH(some S) >= D_* b0 / D(X0)>0`; and
> 7. for every hull point `X` and exact cap root `x`,
>    `Abs(x) <= (D(X)-D_H)/D(X)`.

For a `FinFourQuantitativeFullSupportHardResidual`, the actual-data adapter is:

> starting from any carrier origin with a positive finite atom, either the
> hull minimum has debt `D_*` and the same point is causalized into a
> same-residual `FinFourMinimumAtomProducer`, or it has debt strictly above
> `D_*` and returns the strict neutral saturation passport.  The latter has
> the exhaustive full-debt/reset-rigid/singleton--Never trichotomy.

This strictly removes arbitrary repeated positive-root descent as a separate
branch.  It does not produce a behavioral realization or a uniform payoff at
the strict neutral point.

## 10. Exact remaining consumer

The single remaining statement is:

> **Strict saturation consumer.**  A positive-minimum Fin4 hard residual
> cannot contain a strictly off-minimum, same-outcome-law-fibre-minimal joint
> carrier point with a positive finite atom and unique all-Continue exact
> cap--Nash root; or such a point directly yields terminal approximate Nash
> profiles against unrestricted behavioral deviations.

The trichotomy separates this into three concrete obligations:

1. use hard-residual singleton-matrix signs or chronology to consume the
   all-positive-debt chamber;
2. turn the reset-rigid positive-incidence toggle into an actual law-changing
   or debt-decreasing transition; or
3. transport the singleton/Never chamber's finite binding collision cycle
   into a source-compatible pair/collision chronology before the retained
   atom escapes the controlled window.

Cap-to-prescribed Nash is not available and must not be assumed in any of
these consumers.  Likewise, same terminal-outcome law is not source ancestry
or strategic total-variation control.

## 11. Checked declarations inspected

- `quittingTerminalSemanticLawCarrier_isCompact`,
  `terminalSemanticLawCarrier_fst_mem_carrier`,
  `terminalSemanticLawCarrier_mass_mem_stdSimplex`, and
  `quittingTerminalSemanticLawPrefix_mem_carrier`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
- `exists_isZeroQuittingRootNash`,
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
- `eq_quittingAllContinueRoot_of_continueMass_eq_one`,
  `UniformEquilibrium/Quitting/Boundary/Analytic/SeamPriceResidual.lean`;
- `finFourHardResidual_minimumLaw_causalSuffixAtom`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- `FinFourMinimumAtomProducer.exists_residual_eq_of_hardResidual`,
  `Research/Quitting/FinFourProducerAtlas/Source.lean`;
- `QuittingTerminalExploitabilityWitness.exists_fixedLaw_resetFace_dispatch`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`;
- `quittingTerminalTotalOpponentIncidenceMass`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceRatio.lean`;
- `exists_quittingSingletonCollisionGain_pos_of_unique_allContinue`,
  `Research/Quitting/BindingCollisionGainPositivity.lean`; and
- the prescribed-payoff-only plateau boundary in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllContinuePlateau.lean`.

All saturation, law-tightness, Lemma 8, and Fin4 trichotomy statements remain
ordinary mathematics until formalized.  The cited declarations validate the
individual scalar, carrier, reset, causalization, and collision components;
they do not already state the saturation theorem.
