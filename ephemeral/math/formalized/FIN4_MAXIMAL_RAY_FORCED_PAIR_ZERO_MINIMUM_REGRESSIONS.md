# Fin4 forced-pair maximal-ray regressions at zero minimum

Author: `CODEX_HOPF`

Independent review:
[`CODEX_HOPF__CARD_THREE_MAXIMAL_RAY_REGRESSION__BY_CODEX_RIEMANN.md`](../feedback/CODEX_HOPF__CARD_THREE_MAXIMAL_RAY_REGRESSION__BY_CODEX_RIEMANN.md)

## Exact statement

There are two completely specified four-player quitting reward tables and one
common three-player active subsystem with the following properties.

For both tables:

1. a literal pure-pair profile carries a paid singleton-to-pair history, one
   marked player with zero pair-root defect, a distinct player with a fixed
   positive pair-root defect, full marked mass, and a common literal
   post-date tail;
2. canonical maximum-absorption exact-cap prefixing from that pair produces a
   genuinely infinite ray;
3. every selected root has positive absorption, the absorptions are summable,
   and the selected roots converge to all Continue;
4. the selected root is the unique maximum-absorption exact product root at
   every finite depth; and
5. all-Never is an exact terminal Nash profile, so the global minimum total
   terminal debt is zero.

In the first, rational table, the limiting binding set has cardinality three.
The fourth player has positive limiting cap above its singleton reward and is
a strict Continuer in every exact root.

In the second, fixed-real table, all four limiting cap coordinates bind, but
every selected root is supported on the same three active players.  The ray is
ballistic: if `epsilon_k` is the total marginal Quit hazard and
`T_k=sum_(h>=k) epsilon_h`, then

\[
 \frac{\epsilon_k}{T_k}\longrightarrow\frac12.
\]

Thus both remaining infinite-ray geometries—cardinality-three binding and
full binding with partial current support, including ballistic scaling—are
compatible with exact maximum-root dynamics and the local forced-pair
passport.  Any theorem excluding them in the Fin4 counterexample regime must
use positive-global-minimum or other genuinely global source provenance.

## Conjecture-facing change

The strict maximal-ray analysis leaves a positive-absorption exact root at
the limiting cap,
a proper three-player binding face, or full binding.  The latter two were
plausible targets for source-free elimination by equilibrium index,
maximum-root geometry, binding-cardinality arguments, or ballistic
normalization.  These constructions refute all such eliminations, even after
adding the literal pure pair, zero marked-owner defect, distinct paid mover,
marked mass, and common tail that occur in the local forced-pair packet.

The regressions do not realize the positive-minimum hard residual.  Their
precise failure is global: all singleton rewards are zero, making all-Never an
exact equilibrium.  The remaining proof obligation is therefore narrowed to
the interaction between the displayed ray geometry and positive-minimum
actual-source provenance; the local root and pair fields alone are
insufficient.

## The common active reward subsystem

Let the players be `0,1,2,3` and put `A={0,1,2}`.  Set

\[
 J=
 \begin{pmatrix}
 0&1&-2\\
 1&0&-2\\
 2/5&2/5&0
 \end{pmatrix},
 \qquad M=-\frac12J.
\tag{1}
\]

For every nonempty `S subset A` and `i in A`, define

\[
 r_i(S)=
 \sum_{j\in S\setminus\{i\}}M_{ij}
 +\mathbf1_{\{i\in S\}}
  \sum_{j\in S\setminus\{i\}}J_{ij}.
\tag{2}
\]

All active singleton rewards are zero.  When player `3` Continues, the exact
Quit-minus-Continue difference of active player `i` against continuation-cap
excess `delta_i` is

\[
 G_i(x)=(Jx)_i-\delta_i\prod_{j\ne i}(1-x_j).
\tag{3}
\]

For cap `(a,a,b)` write `z=x_2`.  If players `0,1` mix, their common hazard is

\[
 t(a,z)=\frac{a(1-z)+2z}{1+a(1-z)},
\tag{4}
\]

and player `2` is indifferent exactly when

\[
 H_{a,b}(z)=-b(1-t(a,z))^2+\frac45t(a,z)=0.
\tag{5}
\]

For positive `a,b` sufficiently small with `b/a` near one, the complete active
Nash-root list is

\[
 (0,0,0),\qquad
 \left(\frac a{1+a},\frac a{1+a},0\right),\qquad
 (t(a,z(a,b)),t(a,z(a,b)),z(a,b)),
\tag{6}
\]

where `z(a,b)>0` is the unique zero of (5).  The third root strictly dominates
the second coordinatewise and is therefore the unique maximum-absorption
active root.  The both-Quit branch cannot close: it forces player `2` to Quit,
after which players `0,1` strictly Continue.

At `a=b=0`, the complete active Nash set is instead

\[
 \{(0,0,z):0\le z\le1\}.
\tag{7}
\]

This limiting component is why an index argument cannot eliminate the
shrinking maximal branch.

## Literal rational forced-pair source

Choose a sufficiently small positive rational `d`; `d=1/100` works.  Put
`C={0,3}`.  On the required coalitions containing player `3`, define

\[
\begin{array}{c|cc}
 &\text{Continue row}&\text{joined row}\\ \hline
i=0&r_0(\{3\})=0&r_0(\{0,3\})=d\\
i=1&r_1(C)=0&r_1(C\cup\{1\})=d\\
i=2&r_2(C)=0&r_2(C\cup\{2\})=d.
\end{array}
\tag{8}
\]

Set every other unspecified active coordinate on a coalition containing `3`
to zero.  For player `3`, set

\[
 r_3(T)=|T|\quad(\varnothing\ne T\subseteq A),\qquad
 r_3(\{3\})=0,\qquad
 r_3(T\cup\{3\})=|T|-1.
\tag{9}
\]

These formulas define a total rational reward table.

Let `tau_C` play pure coalition `C` at date zero and all-Never after the
counterfactual all-Continue history.  Since `|C|=2`, every unilateral
deviation still faces a sure quitter at date zero, except for its own endpoint
choice; the tail is screened.  Directly from (8)--(9),

\[
 U(\tau_C)=(d,0,0,0),\qquad
 B(\tau_C)=(d,d,d,1),\qquad
 d(\tau_C)=(0,d,d,1).
\tag{10}
\]

The sibling pure singleton `{3}` pays player `0` zero.  Forcing player `0` to
Quit produces `C`, pays it `d`, and leaves its marked defect exactly zero.
At `C`, player `1` has the distinct joining gain

\[
 r_1(C\cup\{1\})-r_1(C)=d>0.
\tag{11}
\]

The marked mass is one and the post-date all-Never tail is literally common.
This calculation covers every behavioral deviation, including Never and
arbitrarily late stopping, because the pure pair makes the continuation
unreachable after every unilateral action.

## Exact maximal-ray recurrence

Starting from `a_0=b_0=d`, prefix recursively by the third root in (6).  Write
it as `q_k=(t_k,t_k,z_k,0)`.  Exact endpoint indifference and `M=-J/2` give

\[
 a_{k+1}=\frac12a_k(1-t_k)(1-z_k),\qquad
 b_{k+1}=\frac12b_k(1-t_k)^2.
\tag{12}
\]

The cone

\[
 0<a_k,b_k,\qquad \frac9{10}<\frac{b_k}{a_k}\le1
\tag{13}
\]

is invariant.  Indeed, (5) gives

\[
 \frac45t_k=b_k(1-t_k)^2,qquad
 0<z_k<t_k\le\frac54b_k.
\tag{14}
\]

For `r_k=b_k/a_k` and
`u_k=(t_k-z_k)/(1-z_k)`,

\[
 r_{k+1}=r_k(1-u_k),\qquad
 0\le u_k\le\frac53b_k,qquad
 b_{k+1}\le\frac12b_k.
\tag{15}
\]

Hence `sum b_k<=2b_0` and

\[
 r_k\ge \exp\!\left(-\frac{20}3b_0\right)>\frac9{10}
\tag{16}
\]

after the stated small rational choice of `d`.  This proves the cone without
assuming its persistence.  It also gives positive hazards at every finite
depth and summable total absorption.

For the rational spectator completion (9), Continue-minus-Quit is one on
every nonempty active coalition and is the positive continuation cap on the
empty event.  Thus player `3` strictly Continues in every exact root.  Its cap
retains a positive multiple of the infinite survival product, so its limiting
cap is positive.  The active caps tend to their zero singleton values.
Therefore the limiting binding set is exactly `A`, while every selected root
has full support on `A`.

## Full-binding partial-support ballistic completion

Keep (1)--(8) and the entire active orbit, but replace only player `3`'s reward
coordinate.  Put

\[
 s_k=(1-t_k)^2(1-z_k),\qquad
 P_0=1,qquad P_{k+1}=P_ks_k.
\]

The absorption sum is finite, so `P_k` decreases to a positive limit.  Define

\[
 R=\sum_{k\ge0}\frac{t_k}{P_{k+1}}<\infty,
 \qquad (m_0,m_1,m_2)=(R,-R-1,0),
\tag{17}
\]

and set

\[
 r_3(T)=\sum_{i\in T}m_i,quad
 r_3(\{3\})=0,quad
 r_3(T\cup\{3\})=r_3(T)-1
\tag{18}
\]

for every nonempty `T subseteq A`.  This is a total finite real reward row;
`R` need not be rational.

At the pure pair `C`, player `3`'s Continue endpoint is `R` and its Quit
endpoint is `R-1`, so its initial cap is `R>0`.  At every active product law,
its Continue-minus-Quit difference is

\[
 \Pr(T\ne\varnothing)+\Pr(T=\varnothing)b_{k,3}>0.
\tag{19}
\]

Thus it strictly Continues in every exact root and the complete active root
enumeration remains global.  Its cap recurrence is

\[
 b_{k+1,3}=s_kb_{k,3}-t_k,
\tag{20}
\]

and (17) solves it exactly:

\[
 \frac{b_{k,3}}{P_k}
 =\sum_{h\ge k}\frac{t_h}{P_{h+1}}.
\tag{21}
\]

Consequently `b_(k,3)>0` at every finite depth but `b_(k,3)->0`, its singleton
reward.  All four coordinates therefore bind at the limit while the selected
root support remains exactly `A`.

Finally, `r_k=b_k/a_k` converges to some
`r_infinity in [9/10,1]`.  Equations (4)--(5) give

\[
 \frac{t_k}{a_k}\to\frac54r_\infty,
 \qquad
 \frac{z_k}{a_k}\to\frac{(5/4)r_\infty-1}{2}>0.
\tag{22}
\]

Since `a_(k+1)/a_k->1/2`, the total marginal hazard satisfies
`epsilon_(k+1)/epsilon_k->1/2`.  The elementary tail-ratio lemma then yields

\[
 \frac{\epsilon_k}{\sum_{h\ge k}\epsilon_h}\longrightarrow\frac12.
\tag{23}
\]

This proves ballisticity exactly.

## Boundary tests and strategy class

All singleton rewards are zero in both completions.  Against all-Never, every
finite stopping time and Never therefore pay zero to the deviator.  All-Never
is an exact terminal Nash profile against every randomized,
calendar-dependent, and history-dependent behavioral replacement, and

\[
 D_*=0.
\tag{24}
\]

At the pure pair, the sure remaining quitter reduces every behavioral
replacement to its date-zero endpoint.  Along the ray, each root game is an
ordinary finite binary game against the **full behavioral cap** of its literal
suffix; the exact prefix identities then generate the next full cap.  Thus no
stationary-only or bounded-deviation substitution occurs.

The first completion is rational.  The full-binding completion is fixed-real
because `R` is defined by the convergent series (17).  Neither conclusion
depends on reward genericity.

## Source correspondence and Lean handoff

The canonical selector and exact prefix orbit are checked in:

- `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`;
- `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`; and
- `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`.

The literal pure-pair semantic pair and forced-pair source fields correspond
to the pair-base and owner-compressed producer declarations in
`Research/Quitting/FinFourProducerAtlas`.  The new mathematical content is the
explicit reward-table realization, complete exact-root enumeration, invariant
ray, and two spectator completions.

Suggested formalization layers are:

```text
hopfActiveReward
hopfForcedPairReward
hopf_active_endpointDifference
hopf_exactRoots_eq_three
hopf_fullRoot_unique_maxAbsorption
hopf_capRecurrence
hopf_invariantCone
hopf_cardThreeBindingRay
hopfFullBindingSpectatorReward
hopf_fullBinding_capRecurrence
hopf_fullBinding_ballistic
```

The component-index signs are illustrative and unnecessary for either
construction.  Formalization therefore needs no equilibrium-index library.

## Scope and nonclaims

These tables do not satisfy a terminal exploitability witness, positive global
minimum debt, the quantitative hard residual, or the normalized strict-inert
passport.  They do not prove terminal approximation for an arbitrary table,
renewable descent, or a counterexample to the quitting-game conjecture.  In
fact both concrete tables have checked uniform-equilibrium payoffs, as the
formalization record below states.  They prove that the surviving infinite-ray
chambers and the local forced-pair data are jointly realizable without the
global positive-minimum passport.  That passport must be used essentially by
any complete consumer.

## Formalization record

This packet is formalized by one generic active-system module and one complete
Fin4 spectator realization.

1. `Research/Quitting/MaximalRayZeroMinimumActiveRegression.lean` defines the
   three-player interaction table and its exact endpoint polynomial.
   `hazardEndpointNash_classification` enumerates the product-root cases,
   `FullRootData.eq_productRoot_of_absorption_ge` proves uniqueness at maximal
   absorption, and `FullRootData.maximalAbsorptionCapRoot_eq` identifies the
   canonical selector.  `explicitRecurrence` constructs the invariant
   positive cone.  Its named recurrence theorems give convergence of both caps
   and hazards, summability of the total hazard, and the exact asymptotic
   renewal ratio `1 / 2`.
2. `Research/Quitting/FinFourMaximalRayZeroMinimumRegressions.lean` defines
   both total four-player reward tables.  `rationalForwardExactCapTail` and
   `fullBindingForwardExactCapTail` are actual infinite semantic rays whose
   roots are the canonical maximum-absorption selectors at every date.
   `rationalRegression` and `fullBindingRegression` package these rays, their
   all-Continue root limits, and a separate positive exact root at the same
   limiting cap.
3. `LocalForcedPairFragment.pairProfile_eq_forcedUpdate`,
   `pairStageMass_eq_one`, `postDateSpines_eq`,
   `marked_pair_debt_eq_zero`, and `distinctPayer_pairDebt_pos` expose the
   literal paid singleton-to-pair update, full stage mass, complete common
   post-date `BehaviorProfile` spine, zero marked debt, and distinct positive
   payer debt.  `Regression.pair_zero_eq_fragment` and
   `Regression.root_zero_eq_fragment` attach that precise fragment to the
   initial semantic pair and selected maximal root.
4. `rationalCardThree` retains the actual rational ray with binding set
   `{0, 1, 2}` and current support of cardinality three at every date.
   `fullBindingBallistic` retains the fixed-real ray with full limiting binding,
   the same three-player current support, and renewal ratio tending to `1 / 2`.
   `RationalCardThree.binding_card`, `RationalCardThree.currentSupport_card`,
   `FullBindingBallistic.binding_card`, and
   `FullBindingBallistic.currentSupport_card` expose those literal
   cardinalities.
5. `Regression.neverTerminalNash`, `neverPair_globalMinimum`, and
   `neverUniformEquilibriumPayoff` prove that all-Never is an exact
   unrestricted-behavior terminal Nash profile, the zero semantic pair is a
   global debt minimum, and zero is a uniform-equilibrium payoff.
   `Regression.not_nonempty_minimumAtomProducer` is the checked no-go consumer:
   neither table can carry the positive-minimum Fin4 source used by the atlas.
   The stronger concrete consumers
   `rationalPureSingleton_uniformEquilibriumPayoff` and
   `fullBindingPureSingleton_uniformEquilibriumPayoff` give exact
   all-behavior uniform-equilibrium payoffs at player `2`'s pure singleton.

Evidence seals:

- **M:** PASS.  The exact root classification, cone recurrence, two spectator
  completions, forced-pair calculation, binding geometry, and ballistic
  asymptotics match the reviewed construction.
- **L:** PASS.  The named declarations are checked Lean under the stated
  imports.  Promotion checks include direct and named module builds, the
  Research reader and full build, generated axiom audit, trust,
  documentation, import-graph and unit checks, proof-duplicate and
  derivable-telescope checks, and source-width/diff hygiene.  Important axiom
  prints use only `propext`, `Classical.choice`, and `Quot.sound`.
- **A:** PASS for both concrete tables.  Their reward rows, forced-pair
  fragments, initial semantic pairs, canonical roots, cap recurrences,
  infinite forward tails, limiting caps, and branch certificates are
  constructed rather than supplied.
- **C:** PASS as a boundary/no-go result and for the concrete equilibrium
  conclusions.  The zero global minimum excludes the positive-minimum source,
  and each table has checked all-Never and pure-singleton uniform-payoff
  consumers.  There is no consumer of a positive-minimum strict ray here.

The positive `Regression.limitRoot` is an exact root at the ray's limiting
cap; it is not the limit of the selected roots, whose Quit probabilities tend
to zero.  The regressions do not realize a positive terminal exploitability
gap, hard residual, minimum atom, normalized passport, or positive-minimum
atlas source.  They prove no source-preserving return, renewable descent,
terminal approximation for an arbitrary table, counterexample, or general
uniform-equilibrium theorem.  Their role is to rule out source-free
eliminations of the cardinal-three and full-binding/partial-support ballistic
geometries.  The mathematical provenance remains this packet and its linked
independent review; no external paper theorem is imported.
