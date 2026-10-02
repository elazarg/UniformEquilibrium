# Fin4 quantitative tail-escape attack

Author: STRENGTHENER

## Current status

The checked tail-escape data have been unpacked.  No conjecture-facing
consumer has yet been proved.  This notebook records only candidate arguments
which are tested against the exact source chronology; an estimate will not be
promoted unless it produces terminal approximants, an admissible near-return,
or a source-preserving well-founded regeneration.

## Question

Let a Fin4 positive-minimum source retain a nonsingleton terminal atom of
limiting mass `mu>0`, and let `TailEscapeSubsequence` select actual prefixed
profiles and marked stages with

\[
  \operatorname{StageMass}>\lambda=\mu^2/8,
  \qquad
  D(\operatorname{shiftedTail})-D_*\ge
    h=\mu^2D_*/16.
\]

Can this actual subsequence be converted into one of:

1. terminal approximate Nash profiles at every positive tolerance;
2. a positive cumulative punishment-floor admissible near-return; or
3. a regenerated atlas source with a strict natural-valued rank decrease?

The output must retain actual behavioral provenance.  A strict real debt
decrease, a selected exact root, or another undercharge residual does not
answer the question.

## Checked source interfaces inspected

- `TailEscapeSubsequence`, `SelectedRows`, `selectedStageMass`, and
  `selectedTailExcess` in
  `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`;
- `capNashPrefix_tailEscape_exact_account` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticStrictTailEscapeReturn.lean`;
- `capNashTailEscapeReturnSelection_retains_causalSuffixAtom` in
  `Research/Quitting/CausalTailEscapeReturnGate.lean`; and
- the maximal-root chronology, exact debt/mass scaling, summable absorption,
  retained-atom lower bound, exact punishment-floor prefix, and unique
  all-Continue alternative in
  `Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean`;
- `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`
  and `quittingTerminalCapDebtPrefix_projection` in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`;
- `QuittingPositiveDebtDynamicTailWitness.tail_edge` and
  `exists_pos_eventually_endpointDistance_ge_absorptionMass` in the positive
  dynamic-tail/ballisticity modules;
- the source-reselecting pair-base declarations in
  `PairBaseStationaryDebtLocalization.lean` and
  `PairBaseStationaryTwoDebtorHandoff.lean`; and
- `QuittingDynamicDebtCapChargedAnchorCounterexample`, the checked local
  unique-all-Continue charged-anchor regression.

## First exact observations

### 1. The original source segment has fixed absorption

Let `z_0` be the semantic pair at the front of the actual segment ending at
the escaped tail `z_T`, let `P` be joint survival through that segment, and
let the intervening local cap defects be nonnegative.  The Bellman debt
account has the form

\[
  D(z_0)=P D(z_T)+\text{nonnegative defect occupation}.
\]

Thus, when `D(z_0)<=D_*+epsilon` and `D(z_T)>=D_*+h`,

\[
  P\le\frac{D_*+\epsilon}{D_*+h}.
\]

The source segment therefore has a fixed positive absorption probability.
This absorption is not exact punishment-floor charge: its actual rows may
have positive Nash defects.

### 2. Global minimality prices every absorbing actual row

At any actual one-row prefix with tail debt at least `D_*`, if `a` is root
absorption and `delta` is the total local cap defect, then

\[
  D_{\mathrm{current}}=(1-a)D_{\mathrm{tail}}+\delta\ge D_*.
\]

Hence

\[
  \delta\ge aD_* - (1-a)(D_{\mathrm{tail}}-D_*).
\]

At a minimum tail this reduces to `delta>=aD_*`.  Thus replacing actual
absorption by admissible charge requires a strategic conversion; the debt
identity does not make the actual row exact.

### 3. Exact maximal prefixing has one genuine obstruction

Starting from an actual escaped tail, recursively prefixing maximal-absorption
cap--Nash roots gives literal exact punishment-floor prefixes.  Positive
absorption is already executable and preserves any positive suffix atom.
The accumulated charge is nevertheless bounded by the initial excess divided
by `D_*`.  If the first maximal root has zero absorption, maximality forces
every exact root at that cap to be all-Continue.

The remaining local obstruction is therefore a source-matched off-minimum
state whose exact cap--Nash correspondence is uniquely all-Continue.  A
positive atom in its suffix law is not current root absorption.

## Candidate operations under test

1. **Cut and replace the escaped continuation.**  Splice a near-minimum
   continuation behind the literal marked root and test whether the decrease
   of tail debt dominates the induced change of root cap defects.  The
   missing sign is cross-coordinate cap variation.
2. **Rare-root verticalization.**  Dilute a literal absorbing row around an
   inert all-Continue cap and test whether exact complementarity removes the
   first-order Nash cost.  Strict singleton cap walls appear to make defect
   linear while nonsingleton collision is at least quadratic.
3. **Finite active-set change.**  Track which singleton cap inequalities bind
   at an inert escaped tail.  A binding-set transition is finite; what remains
   to prove is that a transition regenerates an actual atlas source or that a
   fixed binding set produces a punishment-admissible chronology.

## Next concrete check

Determine whether the high-tail source segment, together with unique
all-Continue exact roots at its escaped endpoint, forces either a fixed
singleton-wall crossing or a two-coordinate tangent direction with
second-order Nash defect.  Any such statement must be proved on the literal
source segment and then connected to an existing compiler.

## Exact cap-fibre replacement calculation

The autonomous cap--debt recursion gives one useful constraint which was not
visible in the scalar tail-excess statement.  For one root,

\[
  B'=F_q(B),\qquad
  D'=c(q)D+\delta(q;B),
\]

where `delta` is the total root Nash defect against the displayed cap.  Thus,
for a fixed literal word `W`, both the entire cap trajectory and every defect
term depend only on the tail cap.  If two tail carrier points have the same
cap and debts `D` and `Dhat`, their prefixed total debts differ *exactly* by

\[
  P_W(D-\widehat D),
\]

where `P_W` is joint survival through the word.

Let

\[
  V(B):=\min\{D(z):z\in K_r,\ z_2=B\}.
\]

The minimum exists on every nonempty cap fibre by compactness.  Apply the
same literal pre-mark word to a fibre minimizer with the escaped tail's cap.
The result is again a carrier point.  If `D_front` is the selected near-minimum
front and `D_tail` its escaped tail, global minimality therefore gives

\[
  P_W\bigl(D_{tail}-V(B_{tail})\bigr)
  \le D_{front}-D_*.
\tag{22}
\]

Consequently, on any subsequence on which the post-mark joint reach is
bounded below, the escaped tails are asymptotically minimal *inside their own
cap fibres*.  The fixed tail excess is then a genuine cap-fibre premium:

\[
  V(B_{tail})-D_*\ge h-o(1).
\]

This does not yet consume the leaf.  It identifies why replacing the tail by
an arbitrary lower-debt carrier point is illegal: unless its cap agrees, all
upstream defect terms change.  Replacing it by the cap-fibre minimizer is
legal, but (22) says that this improvement has already vanished whenever the
tail remains reached.

### Same cap does not make the marked word exact

Same-cap replacement repairs one mismatch but not the decisive one.  For the
literal word from the escaped post-mark tail back to the near-minimum source,
replacing the tail by another pair with the same cap makes the entire cap
trajectory and every root cap-defect identical.  It follows that every row
which was exact cap--Nash remains exact, but every nonexact row remains
nonexact with exactly the same defect.

The externally added root stack in `SelectedRows` is exact cap--Nash.  The
rows of the original realizing profile through the marked collision are not
asserted exact.  In particular, the marked collision row is an uncontrolled
row.  Therefore the whole word is not a `QuittingPunishmentFloorFinitePrefix`
and is not a window of the independently optimized
`QuittingPositiveDebtDynamicTailWitness`.  The ballistic and cumulative-charge
consumers do not accept it.

A cap-fibre minimizer is also initially a carrier point, not necessarily one
attained by a profile.  Approximation by actual profiles preserves the limiting
cap/debt calculation but does not Nashify the marked row.  Thus same-cap
replacement avoids the old fixed-*law* feasible-direction mismatch while
leaving the exact-*chronology* mismatch untouched.

The checked two-player regression
`QuittingDynamicDebtCapChargedAnchorCounterexample` gives a useful local fence:
at its positive augmented cap, all-Continue is the unique exact Nash root and
every exact predecessor has zero charge, despite positive displayed dynamic
debt.  Its game has an ordinary exact equilibrium and hence does not satisfy
the positive-global-minimum premise, but it rules out any purely local theorem
turning a positive same-cap premium into exact absorption.

## Vanishing-reach normal form

At the marked row write `L` for live mass, `r` for the conditional mass of
the fixed nonsingleton coalition, and `c` for joint Continue mass.  The
checked stage floor gives `L r > lambda`, hence `L>lambda` and `r>lambda`.
If the post-mark reach `Lc` tends to zero, then `c -> 0`.  Product structure
then forces, after a fixed-label subsequence, one member of the collision
coalition to Quit with probability tending to one.  Every other member of
that coalition still Quits with probability at least `lambda`.  Therefore:

* the high tail is asymptotically invisible in prescribed play;
* it is asymptotically invisible to every nonowner's deviations; and
* after the nearly-sure owner deviates to Continue, opponent absorption at
  that same row is still at least `lambda`.

Replacing the post-row opponents by an owner-punishment changes the front
semantics by `o(1)` outside the owner's Continue branch and cannot raise that
branch above the original cap in the limit.  This is a genuine source-side
normalization, but it still leaves all earlier/local Nash defects of the
near-minimum profile.  It does not by itself yield terminal approximants or
an admissible return.

### Existing pair-base and one-owner consumers do not fire

The pair-base unrestricted-deviation collapse requires two players who Quit
surely in the same root.  The normal form above yields only one player with
Quit probability tending to one and a second member with probability bounded
below by `lambda`.  Forcing the second member to Quit surely would create the
right base, but the tail-escape data give no sign showing that this endpoint
update is profitable or debt-nonincreasing.  The checked pair-base source
instead reselects a stationary Nash completion from the table and explicitly
does not preserve chronology.

For owner punishment, prescribed tail reach does tend to zero.  But after the
owner deviates to Continue, tail reach is only bounded above by `1-lambda`,
not by a vanishing quantity.  More importantly, changing the post-row tail
does not control the owner's deviations before the mark or the other players'
pre-mark/local root defects.  The source word is not an exact returned block
and supplies no little-o endpoint error relative to the owner clock.  Hence
the source-anchored one-owner finite-prefix consumer is not applicable.

These are no-gos for the direct compositions, not a proof that a more elaborate
returned repair is impossible.

## Provenance correction: the fixed atom is before the escaped tail

The exact definitions are:

```text
selectedStageMass rows n
  = stage mass of S in prefixedProfile at shiftedStage,

tailPair rows n
  = Sem(allContinueProfileSpine prefixedProfile (shiftedStage + 1)).
```

Thus `tailPair` begins strictly after the marked collision row.  The theorem
`capNashTailEscapeReturnSelection_retains_causalSuffixAtom` requires a positive
atom at a date inside its supplied `continuation`.  Applying it to `tailPair`
cannot retain the selected collision at `shiftedStage`, because that row has
already been removed.  `TailEscapeSubsequence` has no field asserting a later
positive occurrence of the coalition.  The `SelectedRows` fields
`shifted_stage_exact` and `sharp_retention` concern exactly the removed marked
date.  A finite-support source whose mark is its final collision is a boundary
model showing that no later occurrence follows formally.

The maximal-cap theorem can instead be applied to the original source profile,
where it really does retain the atom.  Its state is then the near-minimum
source, not the strict escaped tail, and it yields the already checked
positive-charge versus unique-all-Continue source dispatch rather than a
tail-escape return.

Therefore the strongest corrected return account for the escaped tail is only:

* an exact cap--Nash root whose absorption spends the tail excess produces a
  semantic return near the minimum; and
* if the escaped tail independently carries a positive later suffix atom,
  positive survival retains that atom.

The atlas tail-escape input supplies the first premise but not the second atom
premise.  Its return branch must drop atom-retention language unless a new
post-mark atom theorem is added.

## Current verdict

The tail leaf therefore has a sharper exhaustive *internal* geometry:

* positive post-mark reach forces cap-fibre minimal escaped tails by (22);
* vanishing post-mark reach forces a nearly-sure owner with a uniformly
  absorbing opponent at the marked row.

Neither fact is being claimed as an answer to the atlas question.  The first
still needs a consumer for a strict cap-fibre premium; the second still needs
the one-owner row/punishment construction to remove the earlier source
defects.  No terminal approximation, admissible near-return, or regenerated
finite-rank source has yet been obtained.
