# Positive-minimum hard-residual endpoint barrier

Author: `CODEX_STRENGTHEN`

Status: **complete negative/conditional reduction; ordinary-mathematics audit
with checked ingredients identified; not an export proposal.**

This note continues
[`CODEX_STRENGTHEN__ENDPOINT_MATCHED_EXACT_REGENERATION.md`](CODEX_STRENGTHEN__ENDPOINT_MATCHED_EXACT_REGENERATION.md)
and
[`CODEX_STRENGTHEN__FIN4_FINITE_HAZARD_CAPACITY_RESIDUAL.md`](CODEX_STRENGTHEN__FIN4_FINITE_HAZARD_CAPACITY_RESIDUAL.md).

## 1. Question and answer

The earlier endpoint-matching regression had global semantic-debt minimum
zero.  The remaining question was whether the data that a hypothetical Fin4
counterexample actually supplies,

```text
D_* > 0
+ punishment-normal hard-residual provenance
+ a strict minimum plateau, a fixed-law reset, or a paid pair
```

forces a finite exact cap--Nash block from a literal parent cap to a literal
actual child cap, with a fixed positive absorption charge.

It does not, with the currently checked interfaces.  Positive minimality has
the following asymmetric effect.

1. An exact cap--Nash block whose **terminal parent cap** is on, or sufficiently
   close to, the minimum fiber is forced to be the literal all-Continue block.
   Thus motion *out of* the minimum fiber by exact cap prefixing is impossible.
2. A positively absorbing exact block whose **head/current cap** lies on the
   minimum cap fiber must have its terminal parent cap outside a fixed open
   basin.  Such an incoming return, if independently produced, has a uniform
   metric and hazard charge.
3. The fixed-law paid-reset dispatch gives a literal parent-to-child cap edge
   only in one branch.  At a minimum target it is checked to stall; away from
   the minimum its all-Continue arm remains possible, and its positive arm
   supplies neither a fixed excess above `D_*` nor a child near `D_*`.
4. Hard-residual minimum-law atom provenance does not remove the stall.  The
   checked source-matched atom construction has arbitrarily deep exact cap
   stacks which are literally all Continue, have zero charge, and preserve the
   complete suffix law and retained atom.

Accordingly, the positive-minimum hypothesis does not repair the generic
endpoint matcher.  It gives a strong **conditional consumer** for a literal
incoming return and a strong **source-faithful inert boundary**, but no return
producer.

A concrete reward-table counterexample satisfying all the positive-minimum,
no-uniform-payoff hypotheses would of course be a counterexample to the main
conjecture.  No such table is asserted here.  The no-go statements below are
conditional consequences inside the hypothetical counterexample branch.

## 2. Exact orientation at a positive minimum

Write a terminal-semantic pair as

```text
X = (U_X, B_X),     D(X) = sum_i (B_X(i) - U_X(i)).
```

If `q` is exact root Nash against the parent cap `B_Y`, put

```text
X = Prefix(q,Y).
```

Then `X` is an actual carrier point whenever `Y` is, and exact cap debt
scaling gives

\[
 D(X)=c(q)D(Y),\qquad
 c(q)=\Pr_q(\text{all Continue}),\qquad
 a(q)=1-c(q).
 \tag{2.1}
\]

### Proposition 2.1: a minimum parent is inert

Suppose `Y` is a global minimizer and `D(Y)=D_*>0`.  Then every exact
cap--Nash prefix satisfies

\[
 q=\mathbf C,\qquad X=Y,qquad a(q)=0.              \tag{2.2}
\]

Indeed, `X` is a carrier point, so minimality and (2.1) give

\[
 D_*\le D(X)=c(q)D_*\le D_*.
\]

Positivity gives `c(q)=1`; a product root with joint Continue probability one
is the pure all-Continue root.  The semantic prefix is therefore the literal
self-loop.  Equivalently, the checked
`minimumTerminalSemantic_auxiliaryNash_eq_allContinue`, applied with zero
shift, gives uniqueness directly.

This is the exact obstruction to using a minimum semantic point as the
**parent/tail** of a charged regeneration edge.  It is generic for every
finite nonempty player set and does not use punishment normality.

The stronger checked neighborhood form is
`exists_pos_nearMinimum_capNash_eq_allContinue_radius`: there is
`epsilon>0` such that every carrier parent satisfying

\[
 D(Y)\le D_*+\epsilon
\]

has the singleton exact cap correspondence `{all Continue}`.  Hence every
finite exact cap stack over such a parent is literally inert by backward
induction.

### Proposition 2.2: a minimum child makes an incoming edge expensive

Let

\[
 K_B=\{B_X:X\text{ is a carrier point and }D(X)=D_*\}.
\]

The set `K_B` is compact.  At every point of `K_B`, all Continue is the unique
exact root, and the cap singleton margin is uniformly at least `D_*`:

\[
 B_X(i)-r_i(\{i\})\ge D_*.
\]

The generic compact strict-basin theorem therefore gives an open cap tube
`N_B`, constants `rho,c>0`, and a bounded payoff scale `M>0` such that

\[
 K_B\subset N_B,qquad
 c\,a(q)\le \operatorname{Def}(b,q)quad(b\in N_B). 
\tag{2.3}
\]

For exact finite Nash--Bellman blocks the orientation is terminal-to-head.
If a block has head/current value `b_0 in K_B` and contains positive
absorption, its terminal parent tail cannot belong to `N_B`; otherwise
all-Continue basin rigidity propagates backward and makes the whole block
constant.  Compact separation gives

\[
 \|b_T-b_0\|\ge\rho.                                 \tag{2.4}
\]

With every reward and annotation bounded in sup norm by `M`, Bellman
variation then gives

\[
 \sum_{t<T}\sum_i q_{t,i}\ge {\rho\over 2M}.          \tag{2.5}
\]

Thus a literal incoming return to **any** minimum cap, not merely one selected
plateau point, has a uniform charge.  This is a conditional consumer: it does
not construct the terminal tail, the path, or the endpoint match.

This cap-fiber wrapper and its reached finite-word version were already
proved at paper level and independently reviewed in
[`SERIAL_ENDPOINT_AUDITOR__MINIMUM_CAP_TUBE_FORCED_PAIR_BARRIER.md`](SERIAL_ENDPOINT_AUDITOR__MINIMUM_CAP_TUBE_FORCED_PAIR_BARRIER.md)
and its review.  The exact sources are
`minimumTerminalSemantic_singletonMargin`,
`minimumTerminalSemantic_auxiliaryNash_eq_allContinue`, and
`exists_open_linearAbsorptionDefect_of_compact_strictAllContinue`.
Accordingly, (2.3)--(2.5) are not claimed as new export content here.

The orientation must not be reversed: a terminal tail in `N_B` makes the
block inert, whereas a head in `K_B` only prices an independently supplied
incoming block whose terminal tail lies outside the tube.

## 3. What a high-to-near-minimum parent/child edge would give

There is a sharp one-line conditional compiler.  Suppose an exact cap root
produces the literal child

```text
X = Prefix(q,Y)
```

and, for fixed `delta>0` and `0<=epsilon<=delta/2`,

\[
 D(Y)\ge D_*+\delta,qquad D(X)\le D_*+\epsilon,qquad
 D(Y)\le D_{\max}.
\]

Equation (2.1) gives

\[
 a(q)={D(Y)-D(X)\over D(Y)}
 \ge {\delta-\epsilon\over D_{\max}}
 \ge {\delta\over2D_{\max}}.                         \tag{3.1}
\]

This is exactly the desired finite parent-cap-to-literal-child-cap block and
the desired renewable charge `kappa=delta/(2 D_max)`, provided the child is
a legal continuation of the same capacity chronology.

The missing field is therefore precise:

> produce, from the same hard-residual source, an exact cap root whose parent
> has a fixed positive excess and whose literal prefixed child returns to a
> fixed near-minimum debt band (or directly to the minimum cap fiber).

Strict descent `D(X)<D(Y)` alone is insufficient: it supplies no uniform
`delta-epsilon`.  Re-selecting a fresh off-minimum parent can make the drop
arbitrarily small, and reprojecting the child to an unrelated minimum source
resets the history capacity.

## 4. Fixed-law reset: the exact surviving edge and its stall

For a Fin4 pair-base paid target, the checked theorem
`FinFourPairBasePaidResetTarget.fixedLawReset_absorbingChild_or_allContinueFace`
has the exact relevant orientation.

In its dynamic arm it supplies a root `q` exact against the literal target cap
and the literal actual child

```text
X = quittingTerminalSemanticPrefix reward q target.semanticPair,
```

with

```text
a(q)>0,
D(X)<D(target),
X in the joint semantic/law carrier,
changed complete terminal law,
one reset debt coordinate,
positive opponent incidence.
```

This is a genuine one-edge endpoint match.  It is the strongest currently
checked positive output of the paid fixed-law route.  It is not renewable:
the child has no paid row, reset dispatcher, retained atom, or new target
field.

The alternative arm is the literal all-Continue self-loop at the same target
cap.  The paid row and unit incidence do not exclude it.  They are facts about
the source profile and complete terminal law, while root Nash is tested
against the displayed behavioral cap.  The exact obstruction is the
cap-versus-singleton face isolated by
`resetExcursion_absorbingReturn_or_allContinue_capFace`.

At the minimum boundary there is no ambiguity.  If the reset target has debt
at most that of the minimum source,
`QuittingFixedLawResetDispatch.allContinue_of_target_debt_le_source` proves
that the dynamic arm is impossible and the dispatch stalls.  For a pair-base
target, `returned_eq_of_fixedLawResetDispatch` makes this a literal statement
at `target.semanticPair`, not merely at an unidentified returned point.

Therefore:

* target on the minimum fiber: checked literal stall;
* target off the minimum fiber: positive literal child **or** stall;
* positive arm: strict decrease, but no near-minimum landing and no fixed
  charge floor;
* all-Continue arm: zero charge despite paid-row and law-incidence data.

The pair-base localization supplies a debt of at least the terminal gap, but
the global minimum itself is also bounded below by that gap.  Hence it gives
no positive lower bound on

\[
 D(\text{target})-D_*.
\]

Neither punishment normality nor the hard singleton packet changes this
scalar comparison.

## 5. Hard-residual provenance strengthens the inert arm

The hard residual supplies substantially more source provenance than the old
zero-minimum regression:

* a positive minimum joint semantic/law point;
* a positive finite terminal-law atom at that same point;
* actual realizing suffix profiles converging jointly to that point; and
* arbitrarily deep exact cap--Nash root stacks retaining the same literal
  suffix atom.

Nevertheless, the checked theorem
`QuittingMinimumLawCausalSuffixAtom.nonempty_inertCapStack` proves that beyond
every prescribed depth one can choose such a same-source stack with

```text
roots = replicate roots.length allContinue,
absorptionSum = 0,
semantic pair unchanged,
complete terminal law unchanged,
retained finite suffix atom still positive.
```

The punishment-normal/no-uniform wrapper is
`exists_minimumLawCausalSuffixInertCapStack_of_punishmentNormal_of_not_uniform`.
The Fin4 hard residual supplies its hypotheses through
`exists_finFourHardResidual_minimumLaw_causalSuffixAtom` and
`all_punishmentNormal`.

This is the strongest source-faithful positive-minimum regression relevant to
the present adapter.  It shows that positive minimum, a same-point retained
atom, exact arbitrary-depth cap chronology, and full hard-residual provenance
are compatible with **literal zero outer cap charge**.  The retained atom
lives in the unchanged suffix; it does not force an absorbing outer root.

This does not prove that no different off-minimum charged producer can be
built from the same game.  It refutes only the attempted implication that the
existing minimum-law causal-prefix packet itself must contain positive cap
charge.

The analogous actual-profile paid-port boundary is already recorded in
[`CODEX_EULER__FIN4_EVENTUAL_LITERAL_INERT_MINIMUM_APPROXIMATION.md`](CODEX_EULER__FIN4_EVENTUAL_LITERAL_INERT_MINIMUM_APPROXIMATION.md): actual
full-gap paid sources approaching the strict minimum plateau have canonical
cap lifts which are eventually literally inert.  More quantitatively,
`HasTerminalExploitabilityGap.not_uniformPositivePaidCapDebtDropSelection`
rules out a rule assigning every actual profile a paid cap port with one fixed
positive debt drop.  These results again do not exclude a selector restricted
to a newly characterized off-minimum source class.

## 6. Paid endpoint edges do not bridge the cap seam

`nonempty_quittingPunishmentFloorEndpointEdgeAt` gives an exact endpoint edge
at a prescribed payoff above the punishment floor, and
`FinFourPairBasePaidResetTarget.endpointRoot_or_literalDefect_or_stall`
packages the pair-base alternatives.  This does not provide the edge needed
here:

1. its terminal annotation is the target's prescribed payoff, not its
   behavioral cap;
2. its head/current payoff is not identified with a minimum semantic cap;
3. a positive-survival cap root converts to prescribed-payoff exactness only
   under the sharp surcharge equality
   `surcharge = liveDebt`; otherwise a literal defect remains; and
4. the all-Continue stall is still allowed.

Thus a paid endpoint edge cannot be silently concatenated with a cap-capacity
chronology.  The cap/prescribed-payoff seam is mathematical, not notational.

## 7. Sharp surviving theorem and residual

The strongest theorem justified by the current interfaces is the following
four-way package.

### Theorem 7.1 (paper-level synthesis)

In a hypothetical positive-minimum Fin4 hard residual:

1. every exact cap prefix of a minimum parent is the all-Continue self-loop;
2. every positive exact Nash--Bellman block with a minimum-cap head pays one
   game-dependent uniform hazard floor;
3. every pair-base fixed-law reset is either a literal positive, law-changing,
   strict-debt child edge or a literal all-Continue self-loop, and a
   minimum-fiber target necessarily takes the self-loop arm; and
4. the same-point minimum-law retained-atom construction admits arbitrarily
   deep literal all-Continue zero-charge exact stacks.

Items 1, 3, and 4 are direct checked declarations or short checked
compositions.  Item 2 is the reviewed cap-projection compact-basin wrapper.
None of the four items produces an off-minimum parent satisfying the two
quantitative inequalities in Section 3.

### Precisely reduced residual

It is enough to construct one source-preserving packet with fields

```text
parent child root delta epsilon
parent_mem : parent in carrier
child_eq   : child = Prefix(root,parent)
root_exact : exact root Nash against parent.2
parent_excess : D_* + delta <= D(parent)
child_return  : D(child) <= D_* + epsilon
scales        : 0 < delta and 0 <= epsilon and 2*epsilon <= delta
chronology    : child is the literal next state of the inherited capacity path
provenance    : the paid/atom passport required by the downstream consumer
```

The charge floor then follows formally from (3.1); it should not be stored as
an independent assumption.  No present fixed-law, paid-pair, minimum-law atom,
or hard-residual declaration supplies `parent_excess + child_return +
chronology` on one object.

## 8. Boundary tests

1. **Minimum parent.**  Positive absorption would make
   `D(child)<D_*`, contradicting global minimality.  The exact root is all
   Continue.
2. **Parent arbitrarily near minimum.**  The checked cap-freezing radius makes
   every exact root all Continue, so strict descent does not merely become
   small; it disappears.
3. **Off-minimum target with cap dominating singleton rewards.**  The
   all-Continue exact root fixes the target even when a paid behavioral row
   and positive complete-law incidence are present.
4. **Off-minimum positive root with tiny return.**  If only
   `D(child)<D(parent)` is known, the absorption can be arbitrarily small.
   A strict real-valued descent is not a discrete rank.
5. **Retained atom.**  A positive suffix atom survives an all-Continue outer
   word unchanged.  Its positivity does not lower-bound outer absorption.
6. **Incoming minimum return.**  This is the favorable orientation: once the
   literal head is a minimum cap and the block is positive, the compact basin
   gives a uniform charge.  Existence and ancestry remain the missing fields.

## 9. Inspected declarations

Checked Lean declarations inspected narrowly:

* `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash` and
  `capNashPrefix_tailEscape_exact_account`;
* `minimumTerminalSemantic_auxiliaryNash_eq_allContinue` and
  `minimumTerminalSemantic_singletonMargin`;
* `exists_pos_nearMinimum_capNash_eq_allContinue_radius`;
* `anchoredPath_terminal_not_mem_of_positiveAbsorption` and
  `le_dist_terminal_of_positiveAbsorption_of_ball_subset_allContinueBasin`;
* `exists_open_linearAbsorptionDefect_of_compact_strictAllContinue`;
* `FinFourPairBasePaidResetTarget.returned_eq_of_fixedLawResetDispatch`,
  `.strictDebtPrefix_lawPrefix_ne_mass`, and
  `.fixedLawReset_absorbingChild_or_allContinueFace`;
* `QuittingFixedLawResetDispatch.allContinue_of_target_debt_le_source`;
* `resetExcursion_absorbingReturn_or_allContinue_capFace` and
  `strictTailEscape_allContinue_stalls`;
* `QuittingMinimumLawCausalSuffixAtom.nonempty_inertCapStack` and
  `exists_minimumLawCausalSuffixInertCapStack_of_punishmentNormal_of_not_uniform`;
* `exists_finFourHardResidual_minimumLaw_causalSuffixAtom`;
* `QuittingPaidCapLiftedSource.minimum_mul_totalAbsorption_le_excess`,
  `.inertStall_of_initialDebt_eq_minimum`, and
  `HasTerminalExploitabilityGap.not_uniformPositivePaidCapDebtDropSelection`;
* `nonempty_quittingPunishmentFloorEndpointEdgeAt` and the pair-base endpoint
  seam alternatives.

Ordinary mathematics not presently packaged as one Lean theorem:

* the cap-fiber incoming uniform hazard statement (already independently
  reviewed elsewhere); and
* the conditional high-to-near-minimum charge calculation (3.1).

## 10. Lean handoff and next obligation

Only convenience wrappers are justified before a new producer is found:

```text
minimumTerminalSemantic_capNashPrefix_eq_self
capNashPrefix_absorption_ge_of_parentExcess_of_childNearMinimum
```

The first wraps zero-shift minimum cap uniqueness and prefix identity.  The
second should be a scalar corollary of exact debt scaling with explicit
`Dmax`, `delta`, and `epsilon`; it must not claim existence.

The next mathematical obligation is singular:

> Force the positive arm of an off-minimum, source-provenanced exact cap
> response and show that its literal child enters a fixed near-minimum band,
> without reprojecting or resetting the inherited history capacity.

Until that field is supplied, the finite-capacity rank transition remains
conditional and the positive-minimum/hard-residual additions strengthen the
stall obstruction rather than close the branch.
