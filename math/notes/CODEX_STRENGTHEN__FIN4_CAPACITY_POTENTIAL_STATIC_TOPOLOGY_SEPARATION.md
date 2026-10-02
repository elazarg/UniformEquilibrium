# Fin4 bounded capacity: capacity potentials, static topology, and what must couple them

**Status (2026-08-30).** Independent ordinary-mathematics attack on the
bounded exact-block hazard-capacity branch under the strict saturation
passport.  The main positive results are a canonical capacity potential, a
charged-cycle obstruction, and a finite-state terminal criterion.  The main
negative result is an exact algebraic separation between the singleton LCP
data and the fixed-cap endpoint-Nash vector field.  Consequently degree,
parity, oriented-matroid, and Boolean-coalition arguments based only on the
static hard data cannot close the branch.  A compact semialgebraic Zeno ledger
also shows why bounded capacity does not by itself yield a discrete decreasing
rank, even with a positive debt floor and a retained atom.

This note does **not** prove the finite-quitting conjecture and does not produce
a counterexample quitting game.  Lean declaration facts below are checked;
the new theorems and constructions are paper-level mathematics.

## 1. Self-contained question

Let `K` be a compact set of exact Nash--Bellman states.  Write

* `s -> t` when the root stored at `s` is an exact one-stage Nash root against
  the payoff annotation of `t`, and the Bellman update gives the payoff
  annotation of `s`; and
* `h(s) >= 0` for the sum of the marginal Quit probabilities in the root at
  `s`.

Assume all finite exact paths in `K` have total charge bounded by one common
constant.  In the Fin4 hard branch, also retain the positive-minimum,
law-tight saturation, hard singleton-matrix, and strict minimum-face data.

The question is whether finite algebraic or topological structure forces one
of the following:

1. a second positive-absorption exact root;
2. a terminal Boolean chamber;
3. a charged exact chronological cycle, contradicting bounded capacity; or
4. a genuinely finite decreasing rank.

The word *chronological* is essential.  A path through roots at one fixed cap,
a same-law replacement chain, or a Boolean coordinate-toggle cycle need not
be a chain of exact Nash--Bellman edges.

## 2. Narrow source audit

### Checked declarations

* `QuittingFiniteExactNashBellmanBlock`,
  `HasBoundedFiniteExactNashBellmanHazardCapacity`,
  `hasBoundedFiniteExactNashBellmanHazardCapacity_iff`, and
  `nonempty_finiteExactNashBellmanHazardReturn_of_unboundedCapacity` in
  `UniformEquilibrium/Quitting/Bellman/Finite/UnboundedExactBlockHazardCapacity.lean`.
  A block has positive finite length, literal exact chronological edges, and
  charge equal to the sum of all marginal Quit probabilities before its final
  annotation.
* `finFour_exists_uniformEquilibriumPayoff_of_unboundedExactBlockHazardCapacity`
  and
  `finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`.
  Unbounded capacity in the canonical box gives a Fin4 uniform payoff, and
  hence the no-uniform-payoff branch has bounded capacity there.
* `quittingEndpointNashBoxBridge` and
  `QuittingEndpointNashBoxBridge.isSolution_iff_isZeroQuittingRootNash` in
  `Research/Quitting/Root/EndpointNashBoxComplementarity.lean`.  At one fixed
  cap, exact unrestricted mixed root Nash is exactly box complementarity for
  the endpoint-difference field.
* `BoxComplementarityProblem.eventually_localCompleteSimplexParity_eq_one`
  in `Research/Topology/BoxComplementaritySpernerEventualLocalParity.lean`.
  Any open region containing the entire solution set has eventual local
  cubical-Sperner parity one.  This is a same-resolution localization theorem,
  not a constructed homotopy-invariant local degree.
* `quittingLawTightCapNashSaturationMinimumFace_rootNash_iff_allContinue`,
  `quittingLawTightCapNashSaturationMinimumFace_allContinue_prefix_eq`,
  `sum_quittingRootAbsorptionMass_le_hullDebtDrop_div_minimum`, and
  `sum_quittingRootAbsorptionMass_le_initialHullDebtExcess_div_minimum` in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashMinimumFace.lean`.
  At a positive minimum, a minimum-face same-law root is Nash exactly when it
  is all Continue; the all-Continue prefix is the identity; and absorption on
  a literal prefix chain is paid by debt drop divided by the positive minimum.
* `FinFourStrictRayForwardExactCapTail.bindingFinset_eq_univ_or_card_eq_three`
  and
  `positiveAbsorptionExactRoot_at_capLimit_or_bindingFinset_eq_univ_or_card_eq_three`
  in
  `Research/Quitting/FinFourProducerAtlas/StrictRayBindingCardinalityExplicit.lean`.
  The parity calculation concerns an actual strict maximal ray and leaves
  full binding or binding cardinality three when the limiting all-Continue
  root is unique.
* `FinFourEventualAllContinueLocalRegression.residualHardClass`,
  `exactRoot_eq_allContinue`, and `terminalDebtSumInf_eq_zero` in
  `Research/Quitting/FinFourEventualAllContinueLocalRegression.lean`.
  This checked rational table simultaneously realizes the hard singleton
  class, a unique all-Continue fixed-cap root, and the advertised local packet,
  but its global minimum is zero and it already has a uniform payoff.
* `FourPlayerPairedSingleton.pairedSingletonMatrix_not_projectiveQBar` and
  `stationaryCompletion_residualHardClass` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`.
* `quittingPunishmentValue_le_max_solo` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`.
* `FinFourOwnerRiskyCapLimitRootUniqueness.eq_allContinueRoot_of_isNash` and
  `quittingRootEndpointDifference_productRoot_eq_collisionForm` (in the same
  namespace), together with the uniqueness corollary, in
  `UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyCapLimitRootUniqueness.lean`.

The exact edge orientation used below is the one in
`QuittingFiniteExactNashBellmanBlock`: the current value is the Bellman
successor payoff of the current root against the *next* value, and the current
root is exact Nash against that next value.

## 3. Canonical capacity potential

### Theorem 3.1 (dynamic capacity potential)

Let `E` be any directed relation on a state set `K`, and let
`h : K -> [0,infinity)` be a nonnegative stage charge.  Suppose a number `C`
bounds the charge of every finite `E`-path.  Define

```
Phi(s) = sup { sum_{k < n} h(s_k) :
               n >= 0, s_0 = s, and s_k E s_{k+1} for k+1 <= n }.
```

The length-zero path is included.  Then

1. `0 <= Phi(s) <= max(C,0)` for every `s`; and
2. for every edge `s E t`,

   `Phi(s) >= h(s) + Phi(t)`.

Consequently every infinite path starting at `s` has total charge at most
`Phi(s)` and hence summable charge.

### Proof

The bounds follow immediately from the empty path and the common bound on
finite path charges.  If `s E t`, prepend that edge to every finite path from
`t`.  Every resulting charge is `h(s)` plus the old charge.  Taking suprema
gives the Bellman inequality.  Applied successively to an infinite path, it
bounds each finite partial sum by `Phi(s_0)`; monotone convergence of the
nonnegative partial sums gives summability.  QED.

For the repository relation, `h(s)` is the literal sum of marginal Quit
probabilities in the root component of `s`.  Bounded exact-block capacity
therefore supplies a canonical bounded real-valued Lyapunov function without
any selection of successors.

### Attainment warning

If `K` is compact, `E` is closed, and `h` is continuous, the maximum charge
among paths of one **fixed** length is attained.  This does not imply that the
supremum over all lengths is attained, continuous, or semialgebraic.  The
path-length union is countable and noncompact in the length coordinate.  Thus
a step of the form “choose a capacity-maximizing continuation and descend”
requires a new theorem; compactness of `K` alone does not justify it.

## 4. Exact cycles and a finite-state terminal criterion

### Theorem 4.1 (positive exact cycles are impossible)

Under bounded finite-path capacity, every directed cycle

`s_0 E s_1 E ... E s_m = s_0`

has total charge zero.  In particular, every state on the cycle has charge
zero.

### Proof

If the cycle charge were positive, concatenating the same cycle `N` times
would give finite paths of arbitrarily large charge.  This contradicts the
uniform capacity bound.  Nonnegativity then makes each individual stage
charge zero.  QED.

For exact Nash--Bellman edges, zero total marginal Quit probability means the
root is literally all Continue.  The Bellman update at all Continue is the
identity, so the payoff annotations are equal around such a cycle.  A bounded
capacity cycle is therefore a zero-charge identity phenomenon, not a hidden
positive return.

### Corollary 4.2 (finite exact automaton consumer)

Suppose `F` is a finite set of actual exact Nash--Bellman states and every
nonterminal state in `F` has a selected exact successor in `F` with positive
stage charge.  Then iterating successors reaches a terminal state in finitely
many steps.

Indeed, otherwise finiteness repeats a state and produces a positive charged
cycle, contradicting Theorem 4.1.  This is the clean finite combinatorial
consumer suggested by bounded capacity.  The hard task is producing a finite
set closed under **literal chronological successors**.  A finite collection
of support labels, binding sets, oriented-matroid covectors, or same-law
replacements is not such an automaton unless an exact edge is attached to
each transition.

## 5. Static fixed-cap topology cannot force a second root

Fix a cap `c`.  Let `q_i` denote player `i`'s Quit probability and let
`G_i(q_{-i})` be Quit payoff minus Continue payoff.  The exact root conditions
are the box-complementarity relations

```
0 <= q_i <= 1,
q_i G_i(q_{-i}) >= 0,
(1-q_i) G_i(q_{-i}) <= 0.
```

The endpoint bridge cited in Section 2 checks that these conditions are
exactly the root-Nash conditions in the project semantics.

Global cubical Sperner parity is odd, but it does not force a second solution.
A unique regular solution can account for the global parity by itself.  In
the actually relevant binding-origin case, all Continue may be degenerate,
so one should not call it a strict or regular complementarity solution.
Nevertheless, if an open neighborhood contains the entire solution set, the
checked same-resolution localization theorem makes its eventual local
cubical-Sperner parity one.  Thus uniqueness/localization alone still gives no
contradiction; one needs an independent zero-parity computation.

This is not merely a formal possibility.  The checked
`FinFourEventualAllContinueLocalRegression` combines the hard residual class
and a unique all-Continue exact root at the relevant cap.  Its defect is
global (`terminalDebtSumInf = 0`), not local topology.  Therefore any degree
argument that never uses positive-minimum/source provenance would also apply
to this regression and cannot establish the desired conclusion.

The strict-ray binding-cardinality theorem is stronger and genuinely
source-facing, but its conclusion is only “full binding or cardinality three”
under limiting uniqueness.  It does not convert either remaining face into a
second root or a chronological edge.  Tucker-type arguments have the same
problem, and there is no natural antipodal symmetry in the endpoint field.

## 6. Active/passive decoupling

The obstruction to using the singleton LCP oriented matroid can be made exact.

### Theorem 6.1 (coalition-layer separation)

Fix a finite player set and a cap vector `c`.  For every player `i`, choose two
functions on coalitions of the *other* players,

```
a_i(B), g_i(B),       B subseteq I \ {i},
```

with `a_i(empty)=c_i` and `g_i(empty)=0`.  Define the payoff to player `i` at
every nonempty quitting coalition `A` by

```
r_i(A) = a_i(A \ {i}) + 1_{i in A} g_i(A \ {i}).                 (6.1)
```

Then:

1. the endpoint difference at fixed cap is

   ```
   G_i(q_{-i}) = sum_{B subseteq I\{i}} P_q(B) g_i(B),           (6.2)
   ```

   where `P_q(B)` is the product probability that exactly `B` among the other
   players Quit; and
2. the normalized singleton matrix has zero diagonal and off-diagonal entries

   ```
   M_ij = a_i({j}) - c_i.                                       (6.3)
   ```

Thus the passive singleton LCP matrix and the active fixed-cap endpoint vector
field can be prescribed independently, subject only to the unavoidable
origin tie `G_i(0)=g_i(empty)=0`.

### Proof

Condition on the coalition `B` of other quitters.  If player `i` Continues,
her payoff is `a_i(B)`.  If she Quits, her payoff is
`a_i(B)+g_i(B)`.  Subtraction cancels the passive layer and averaging gives
(6.2).  At the singleton `{j}`, player `i != j` receives `a_i({j})`; at her own
singleton `{i}`, she receives `a_i(empty)+g_i(empty)=c_i`.  Subtracting the own
solo payoff gives (6.3).  QED.

### Exact Fin4 hard transplant

This theorem gives a concrete finite exact target, not just a dimension count.
Take the checked paired singleton matrix
`FourPlayerPairedSingleton.pairedSingletonMatrix`, set `c=(1,1,1,1)`, and put

```
a_i(empty) = 1,
a_i({j})   = 1 + M_ij,
```

with arbitrary passive values, for example `a_i(B)=1`, on the remaining
coalitions.  Independently choose the active increments

```
g_0(B) = 1_{1 in B} - 2 1_{2 in B} + (1/100) 1_{3 in B},
g_1(B) = 1_{0 in B} - 2 1_{2 in B},
g_2(B) = (2/5)(1_{0 in B}+1_{1 in B}) - (39/100)1_{3 in B},
g_3(B) = -1_{0 in B} - 1_{1 in B} + 1_{2 in B}.
```

Equation (6.2) is the owner-risky additive endpoint field used in the checked
fixed-cap uniqueness example, so its unique exact root is all Continue.
Equation (6.3) is exactly the paired residual-hard matrix.  Every own solo
payoff is one.  The general checked bound
`quittingPunishmentValue_le_max_solo` puts every punishment value below
`max(1,0)=1`, so all players are punishment-normal.  Moreover all own-singleton
constraints bind at the chosen cap.  The uniform distribution over singleton
terminal laws has full support and expected payoff `(5/4,...,5/4)`, since each
row of the paired matrix has sum one before the unit shift.

These last arithmetic claims are direct finite calculations and are not yet
Lean checked for this newly assembled table.  They are included as a precise
regression target.  Crucially, this construction does **not** assert positive
global minimum or absence of uniform equilibrium.  That missing global field
is exactly the point: hard LCP data plus static root topology do not provide it.

### Consequences

* The oriented matroid of the hard singleton matrix does not determine even
  the local sign pattern of the fixed-cap endpoint field away from the origin.
* Any Poincare--Hopf or degree argument must use a semantic coupling between
  the source law/cap/debt and the endpoint increments.  It cannot be a theorem
  of the hard singleton matrix alone.
* A putative “minimum-face incidence forces another root” theorem needs an
  assumption that is false for the independent active/passive construction;
  that assumption should be stated as the missing source coupling.

## 7. Boolean coalition geometry is horizontal

For a pure coalition `B` of other quitters, `g_i(B)` is precisely the payoff
increment on the Boolean edge obtained by toggling player `i` from Continue to
Quit.  Hence equation (6.1) realizes arbitrary orientations of Boolean edges,
apart from ties forced at a binding origin.

A nonempty coalition is a pure terminal Nash chamber exactly when every
member's leave edge and every outsider's join edge point inward (with weak
inequalities).  In other words it is a sink of the corresponding Boolean
orientation.  Such a sink would be a useful sure-exit terminal object.

But a finite orientation need not have a sink; following improving toggles can
enter a directed cycle.  This cycle is **not** an exact Nash--Bellman
chronology.  It compares counterfactual coalitions at one payoff table and one
cap, while a chronological edge updates the continuation payoff.  Bounded
exact-block capacity therefore says nothing about the horizontal cycle.
Promoting it to a contradiction is precisely the missing adapter, not a
combinatorial tautology.

## 8. A positive-minimum semialgebraic Zeno ledger

The canonical potential of Section 3 is real-valued.  The following compact
one-dimensional exact-scaling ledger shows that it cannot generally be
discretized, even after adding the quantitative features furnished by a
positive minimum and retained atom.

Let the state space be `[0,1]`.  Define

```
T(e) = e + (1-e)^2/2 = (1+e^2)/2,
D(e) = 1 + e,
c(e) = D(e)/D(T(e)),
alpha(e) = 1-c(e) = (T(e)-e)/(1+T(e)).
```

For `e<1`, `T(e)>e`; iteration gives `e_n` increasing to `1`.  The debt floor
is the positive number `D*=1`, and the exact scaling identity is

```
D(e) = c(e) D(T(e)).                                             (8.1)
```

Furthermore

```
sum_n alpha(e_n)
  <= sum_n (D(e_{n+1})-D(e_n))
  <= 1-e_0.                                                      (8.2)
```

Thus there is an infinite path with a positive charge at every nonterminal
step and uniformly bounded total charge.  If a retained atom is desired, set

```
m(e) = D(e)/4.
```

It has the uniform mass floor `1/4`, is at most `1/2`, and obeys exact suffix
transport `m(e)=c(e)m(T(e))`.  A zero-charge self-loop at `e=0` may model the
neutral all-Continue identity; the positive edge leaves toward a different
successor, so uniqueness of the static root at the minimum cap does not rule
it out.

All displayed sets and maps are compact semialgebraic.  Therefore:

* semialgebraic stratification alone need not make chronology finite;
* no natural-number rank can strictly decrease on every positive edge of this
  path; and
* the omega-limit at `e=1` is neutral, so a Conley-index or Poincare--Hopf
  argument requires an isolating/exit hypothesis not supplied by bounded
  capacity.

This is a regression for an abstract exact-debt ledger, not a constructed
quitting game.  It proves the sharp logical no-go: **bounded capacity + positive
debt floor + exact debt scaling + a uniformly retained atom do not by
themselves imply a finite rank or a charged return.**  A game-semantic theorem
must exploit additional coupling of the active root field to the source law.

## 9. Finite certificates that really would decide a candidate

### 9.1 A sufficient bounded-capacity certificate

Let a bounded function `V` on the exact state carrier satisfy

```
L <= V(s) <= U,
V(s)-V(t) >= h(s)        for every exact edge s -> t.            (9.1)
```

Then every finite path has charge at most `U-L`, by telescoping.  This is a
finite Lyapunov certificate when `V` is chosen from a finitely representable
class.

For rational quitting rewards, the exact root constraints are polynomial
box-complementarity inequalities and the Bellman equalities are polynomial
after product probabilities are expanded.  Hence a rational polynomial `V`
together with rational Positivstellensatz/SOS identities proving (9.1) on the
compact semialgebraic edge set is a checkable sufficient certificate of
bounded capacity.  It need not equal the possibly irregular canonical `Phi`.

This paragraph is a certificate target, not an assertion that a fixed-degree
SOS search is complete.  A Positivstellensatz implementation must also include
the carrier equations/inequalities and an Archimedean compactness certificate.

### 9.2 A finite unbounded-capacity certificate

A rational literal exact chronological cycle with positive total charge is a
finite certificate of unbounded capacity: repeat it.  In the integrated Fin4
pipeline, the checked unbounded-capacity branch supplies the positive
conclusion.  A rational finite exact automaton as in Corollary 4.2 is likewise
a finite positive certificate once its terminal consumer is attached.

### 9.3 What a genuine negative certificate must cover

A static rational reward table with hard singleton matrix and unique cap root
is not a counterexample certificate.  A genuine negative certificate must
establish a fixed positive exploitability/debt lower bound against **all
behavioral profiles**, including profiles that Quit arbitrarily late.  A
plausible finite target would be a sound compact polynomial relaxation of the
full terminal-semantic carrier together with a rational Positivstellensatz
identity certifying `D >= gamma > 0`.  Whether such a complete relaxation
exists is open; bounded-controller enumeration is insufficient.

## 10. Strongest surviving reduction

The bounded-capacity branch becomes finite once one proves the following
source-coupling producer.

> **Finite chronological quotient producer.**  From the positive-minimum Fin4
> hard source and strict saturation passport, produce a finite set `F` of
> actual source-faithful Nash--Bellman states such that every nonterminal
> member of `F` has a positive-charge exact Nash--Bellman successor in `F`.

Corollary 4.2 then forces a terminal member, with no degree or recurrence
argument left.  More generally it is enough to produce a finite label map
whose repeated label gives a *literal endpoint-matched exact splice*; ordinary
horizontal equality of labels is not enough.

The missing theorem must couple both layers:

1. the passive/source layer: actual terminal law, cap, positive global debt,
   retained-atom ancestry, and strict saturation/minimum-face incidence; and
2. the active layer: the endpoint increment field determining exact root
   responses against the next value.

Theorem 6.1 proves that the hard singleton LCP matrix alone does not couple
them.  The Zeno ledger proves that real capacity and retained mass alone do not
make the chronology finite.  Same-law hull replacements, support drops, and
Boolean toggles become useful only after an exact chronological edge or splice
is supplied.

## 11. Recommended next obligation

Work at the level of the actual positive-minimum source and prove one of these
two sharply separated statements:

1. **Finite source-faithful successor selection:** strict saturation has a
   positive-charge exact successor in one of finitely many canonical actual
   states, unless a terminal profile already exists; or
2. **Endpoint-matched recurrence:** every infinite source-faithful exact path
   with the retained atom has two occurrences that agree in all data needed to
   splice the later suffix to the earlier endpoint with positive intervening
   charge.

Either result closes the branch via Theorem 4.1/Corollary 4.2.  A theorem only
about equality of caps, laws, supports, binding sets, or oriented-matroid signs
does not.

## 12. Honest status table

| Claim | Status |
|---|---|
| Canonical potential and edge inequality | Proved here, ordinary mathematics |
| Positive chronological cycle obstruction | Proved here, ordinary mathematics |
| Finite exact automaton terminal criterion | Proved here, ordinary mathematics |
| Active/passive decoupling formula | Proved here, ordinary mathematics |
| Concrete paired-matrix/owner-risky transplant | Exact finite calculation proposed; not Lean checked as one assembled table |
| Static parity does not force a second root | Proved by degree logic and supported by checked regression |
| Positive-floor retained-atom Zeno no-go | Proved as an abstract semialgebraic ledger, not a quitting-game instance |
| Finite chronological quotient producer | Open and identified as the next obligation |
