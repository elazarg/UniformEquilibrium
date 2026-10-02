# Punishment-anchored singleton graph: canonical columns and the no-fork barrier

Author: `STRENGTHENER`

## Current status

Punishment anchoring gives a clean finite semantic reduction, but it does not
verticalize the singleton toggle graph.

For every punishment-normal owner `j`, pure singleton play followed by
near-optimal `j`-punishment converges to a canonical point of the terminal
semantic carrier.  Its owner debt is zero and every outsider debt is exactly
the positive singleton-joining gain.  Hence every singleton join column has
total positive part at least the global minimum debt.  Equality produces a
minimum-fiber carrier point with explicitly known debt support; strict
inequality is a finite, table-computable off-minimum wall.

The tempting next step—concatenate these four punishment-anchored singleton
states—is unavailable for an exact reason.  A sure singleton root permits an
*arbitrary* punishment tail because its all-Continue reach is zero.  As soon
as the root is softened enough to reach a successor, that successor is also
the tail seen by the owner's Continue deviation.  Semantic prefixing is
injective in the successor payoff at every positive-Continue root.  There is
no separate observable event on which opponents can use one on-path successor
and another off-path punishment.  A semantically neutral tail replacement is
not ruled out, but its payoff equality and owner-cap compatibility must be
proved; punishment existence alone gives neither.

Thus the finite graph does not give a chronology for free.  A vanishing-clock
repair with sublinear Bellman and endpoint error is already forbidden in the
Fin4 hard residual by the checked returned-block homogeneous-tangent
obstruction.  The remaining producer must pay a macroscopic successor seam,
retain a positive-survival block, or turn a first-order seam/normal-work term
into support descent or exact charge.

This is ordinary mathematics plus a declaration-level audit.  The composed
canonical-column and no-fork statements below are not yet packaged as Lean
theorems.

## Question

In the Fin4 hard residual, choose for each owner `j` a near-optimal actual
`j`-punishment and place it behind the pure singleton `{j}`.  Positive minimum
debt forces an outsider to join.  Pure-collision screening then gives a finite
same-stage route back to a singleton.  Can the resulting finite graph of
punishment-anchored singleton states be compiled into terminal approximants,
an exact charged return, or a minimum-fiber support descent?

The answer supplied here is:

* there is a finite canonical minimum/wall test at every singleton;
* the positive outsider join is already available in stronger checked form;
* independent punishment anchors cannot be concatenated into one live
  chronology without an explicit successor seam; and
* no terminal approximation or support descent follows from the graph alone.

## Declarations inspected

### Punishment and instant singleton completion

`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`

* `quittingInstantRoot`
* `quittingTerminalPayoff_eq_soloReward_of_liveRoot_eq_instant`
* `exists_quittingStationaryPunishmentRoot_lt_add`
* `quittingInstantPunishmentWorks_of_conditions`

`UniformEquilibrium/Quitting/Stationary/MinMax.lean`

* `quittingPunishmentValue`
* `quittingStationaryPunishmentValue`
* `quittingPunishmentValue_eq_stationaryPunishmentValue`
* `quittingPunishmentValue_le_stationaryUnilateralCap`

`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`

* `quittingContinuationBestResponseValue_rootThenContinuation_eq_max`

### Exact root and semantic identities

`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticReachedRowDebtLocalization.lean`

* `quittingTerminalSemanticDebt_prefix_eq_coordinateNashDefect_of_other_sureQuitter`

`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`

* `quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul`

`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`

* `quittingRootSuccessorPayoff_sub_eq_continueMass_mul`

`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`

* `quittingTerminalSemanticPair_rootThenContinuation`
* `quittingTerminalSemanticCarrier_isCompact`

### Existing stronger join and chronology boundaries

`UniformEquilibrium/Quitting/Boundary/Repair/PunishmentNormalAtomicCollision.lean`

* `QuittingTerminalExploitabilityWitness.exists_atomicCollision_gain_of_normal`

`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StaticCycleChronologyBarrier.lean`

* `quittingJointSurvivalWeight_naiveStaticCoalitions_eq_zero`
* `quittingRootContinuePayoff_pureSingleton_eq_tail`

`Research/Quitting/FinFourProducerAtlas/MonodromyImpossible.lean` and the
reviewed export `FIN4_PURE_NONSINGLETON_COLLISION_SCREENING.md` provide the
finite pure-collision screen.

`formalized/RETURNED_BLOCK_HOMOGENEOUS_TANGENT_OBSTRUCTION.md` records the
checked returned-block obstruction used in Section 5.

## 1. Canonical punishment-anchored singleton carrier points

Let `I` be finite, let `r` be a quitting reward table, and suppose total
terminal-semantic debt has a positive global minimum

\[
 D_*>0.
\]

Fix a punishment-normal owner `j`:

\[
 \chi_j\le s_j:=r_j(\{j\}).
\tag{1}
\]

For `i!=j`, put

\[
 a_{ji}:=
 \bigl[r_i(\{i,j\})-r_i(\{j\})\bigr]_+,
 \qquad
 H_j:=\sum_{i\ne j}a_{ji}.
\tag{2}
\]

Define the canonical semantic pair `z^j=(u^j,b^j)` by

\[
 u^j_i=r_i(\{j\}),
\tag{3}
\]

\[
 b^j_j=r_j(\{j\}),
 \qquad
 b^j_i=\max\{r_i(\{j\}),r_i(\{i,j\})\}
 \quad(i\ne j).
\tag{4}
\]

### Theorem 1: canonical anchor

The point `z^j` belongs to the terminal-semantic carrier and

\[
 d_j(z^j)=0,
 \qquad
 d_i(z^j)=a_{ji}\quad(i\ne j),
 \qquad
 D(z^j)=H_j.
\tag{5}
\]

Consequently

\[
 \boxed{H_j\ge D_*.}
\tag{6}
\]

#### Proof

Choose `epsilon_n>0` tending to zero.  The stationary punishment theorem gives
a product row `y_n` such that its stationary unilateral cap for `j` satisfies

\[
 \chi_j\le \Phi_j(y_n)<\chi_j+\varepsilon_n.
\tag{7}
\]

Let `pi^j_n` be the actual one-stage punished profile whose date-zero root is
the instant pure singleton `{j}` and whose continuation is the stationary
profile generated by `y_n`.

The prescribed payoff is exactly (3), because the root absorbs surely.  If
`i!=j` deviates, player `j` still Quits surely at date zero.  Every behavioral
deviation therefore collapses to `i`'s binary date-zero choice, and

\[
 B_i(\pi^j_n)
 =\max\{r_i(\{j\}),r_i(\{i,j\})\}.
\tag{8}
\]

For the owner, the exact root/continuation cap formula gives

\[
 B_j(\pi^j_n)=\max\{s_j,\Phi_j(y_n)\}.
\tag{9}
\]

Equations (1) and (7) imply

\[
 0\le d_j(\pi^j_n)<\varepsilon_n.
\tag{10}
\]

Thus `Sem(pi^j_n)->z^j`.  Every semantic pair is in the carrier and the
carrier is compact, hence closed, so `z^j` belongs to it.  Equations (5)
follow from (3)--(4).  Global minimality then gives (6).  This proof uses the
full behavioral cap formula; it does not assume punishment-cap attainment.

### Corollary 1: finite minimum/wall dichotomy

For each owner `j`, exactly one of the following holds.

1. `H_j=D_*`.  Then `z^j` is a global minimum and

   \[
   \operatorname{supp}_+d(z^j)
   =\{i\ne j:r_i(\{i,j\})>r_i(\{j\})\}.
   \tag{11}
   \]

2. `H_j>D_*`.  Every sufficiently accurate punishment-anchored singleton
   approximation at `j` lies in a fixed strict off-minimum band.

On `Fin 4`, the support in (11) has cardinality at most three.  Therefore an
equality anchor gives an immediate support-cardinality descent from any
rank-four minimum source.  More generally it gives a descent whenever the
strict-joiner set in (11) is smaller than the retained minimum source's debt
support.  The standard minimum-fiber tangent re-extraction may then be used.

Since there are only four owners, if every `H_j>D_*`, then

\[
 \eta:=\min_j(H_j-D_*)>0
\tag{12}
\]

is a uniform table-computable punishment-singleton wall.

## 2. The outsider-join step is not new

Equation (6) implies that some outsider has

\[
 a_{ji}\ge {D_*\over |I|-1}.
\tag{13}
\]

For the Fin4 hard residual this conclusion is strictly dominated by the
checked theorem

```text
FinFourQuantitativeFullSupportHardResidual
  .exists_terminalGap_collision_at_singleton
```

or, generically, by

```text
QuittingTerminalExploitabilityWitness
  .exists_atomicCollision_gain_of_normal.
```

Those declarations give a distinct outsider whose literal join gain is at
least the full fixed terminal gap.  Therefore punishment anchoring does not
create a new collision sign.  Its genuine extra content is the canonical
carrier point (3)--(6), not the first graph edge.

Starting from the forced pair, pure nonsingleton collision screening gives a
finite same-stage profitable route and then a pair-to-singleton route.  The
post-date tail stays equal to the punishment selected for the *old* owner.
Replacing it by a punishment of the new singleton owner is a new suffix
replacement, not a literal edge of that route.

## 3. Exact no-free-punishment-fork theorem

Let `x` be any product root and put

\[
 c(x):=\Pr_x(\text{all Continue}).
\]

For payoff continuations `u,v`, the checked exact transport identity is

\[
 F_r(x;u)-F_r(x;v)=c(x)(u-v).
\tag{14}
\]

### Theorem 2: reachable successor versus hidden punishment

If `c(x)>0`, semantic prefixing by `x` is injective in its prescribed
continuation payoff:

\[
 F_r(x;u)=F_r(x;v)\quad\Longrightarrow\quad u=v.
\tag{15}
\]

If `x` is the singleton clock of owner `j`, with every opponent Continuing
surely and `j` Quitting with probability `p`, then

\[
 c(x)=1-p.
\tag{16}
\]

Moreover `j`'s unrestricted Continue endpoint at the root uses the actual
successor cap `b_j`.  If the successor semantic pair is `z=(u,b)`, then

\[
 d_j(F_xz)
 =\operatorname{Def}_j(x;b)+(1-p)d_j(z),
\tag{17}
\]

and explicitly

\[
 \operatorname{Def}_j(x;b)
 =(1-p)(s_j-b_j)_++p(b_j-s_j)_+.
\tag{18}
\]

Thus there are only two regimes.

* If `p=1`, an arbitrary punishment tail may be chosen independently, but its
  reach is zero.  No later graph state is visited.
* If `p<1`, the next state has positive reach, but it is also the continuation
  against which refusal by `j` is evaluated.  Replacing it by an independently
  selected `j`-punishment changes the current prescribed value by exactly
  `(1-p)(u-v)` and changes the owner endpoint through its actual tail cap.
  The prescribed-value seam vanishes only when the continuation payoffs
  coincide; even then, owner-cap compatibility remains a separate obligation.

#### Proof

Equation (15) follows immediately from (14) by division by the positive
scalar `c(x)`.  Equation (16) is the product law.  Equation (17) is the
checked arbitrary-root cap-debt decomposition.  With all opponents Continuing
surely, `j`'s two pure endpoints are `s_j` and `b_j`; the elementary Bernoulli
complementarity identity gives (18).

At the strategy level the same fact has an information interpretation.  The
unique live history after date zero is “everyone Continued.”  It does not
record whether `j` followed a randomized Continue recommendation or deviated
to Continue.  Opponents therefore cannot condition two different tails on
those two events.  The semantic identity (14) is the exact quantitative form
of that observation.

This is a formalizable no-go, not a heuristic claim about provenance.

## 4. Consequence for a finite punishment-anchored graph

Fix one near-optimal punishment root for every singleton owner and run the
pure same-stage screen after every strict join.  Finiteness certainly gives a
repeated singleton label or a repeated nonempty coalition.  It does not give
a Nash--Bellman chronology:

1. keeping every singleton root pure makes the first vertex absorb surely;
2. softening a vertex exposes its actual successor rather than its separately
   selected owner punishment, by Theorem 2;
3. changing to the next owner's punishment is a suffix replacement, not an
   edge of the original same-tail screen; and
4. the positive outsider join means the pure singleton root is not Nash even
   though its owner is punishment-disciplined.

The checked naive-static-cycle theorem proves item 1.  Theorem 2 proves that
items 2--3 cannot be repaired merely by declaring the punishments to be
off-path.

The only automatic rank output is Corollary 1: if an equality column has
smaller support cardinality than the retained minimum, use `z^j`.  In the
strict-wall case, or when every equality column has support rank at least the
retained rank, the graph supplies no descent.

## 5. Vanishing clocks are already excluded

Suppose one attempts to replace the pure graph by returned finite product
blocks with total hazard tending to zero, bounded payoff annotations, and
Bellman plus endpoint-Nash error sublinear in total hazard.  The checked
returned-block homogeneous-tangent theorem produces a homogeneous simplex-LCP
solution for the normalized singleton matrix.

The Fin4 hard residual's `ResidualHardClass.no_homogeneous` field excludes
that conclusion on the full normal core.  Hence punishment anchoring does not
open a hidden vanishing-clock outlet.  Normality supplies the off-path
individual-rationality inequality, but Theorem 2 forces the actual on-path
successor back into the Bellman account.

The remaining source-faithful producer is therefore sharply one of:

1. a positive-survival returned block with actual Bellman and endpoint
   control;
2. a macroscopic payoff excursion and return;
3. a seam or binding-normal-work term comparable to total exposure, together
   with a consumer that turns it into exact charge or inactive-safe support
   descent; or
4. one equality anchor from Corollary 1 whose explicit joiner support is
   strictly smaller than the retained minimum rank.

Items 1--3 are not produced here.

## 6. Boundary tests

### Re-equilibrating outsiders does not contradict positive minimum

If the outsiders at the sure singleton root are re-equilibrated in their
finite induced game, their debts vanish.  But the owner's prescribed Quit
payoff is then the expected reward of `{j}` together with the outsiders'
mixed quitting coalition, not necessarily `s_j`.  Punishment normality only
compares `chi_j` with `s_j`.  The owner can carry the entire positive debt.
This is exactly the one-active wall in
`ATLAS_GATEKEEPER__PURE_SINGLETON_REEQUILIBRATION.md`; it prevents a false
zero-debt conclusion.

### The canonical point is a carrier point, not necessarily attained

The near-optimal punishment infimum need not be attained by one stationary
root.  The proof uses a convergent sequence of actual semantic pairs and the
closed terminal-semantic carrier.  It does not claim that one behavioral
profile realizes `z^j`.

### A positive join graph is insufficient

The hard-residual atomic collision theorem already supplies a positive
outgoing join at every singleton.  Better-response cycles can still occur,
and pure vertices kill survival.  The exact flat-curvature and common-host
regressions in the maintained monodromy notes show that finite label closure
does not imply a returned block.  Those regressions have global minimum zero;
they are boundary tests for the compiler, not counterexamples to Fin4.

### Punishment is opponent data, but it is still not a separate branch

Only the opponents' components of a punishment plan matter to `j`'s cap.
This does not invalidate Theorem 2.  Once the all-Continue history has positive
probability, the successor opponents are exactly the opponents faced by a
Continue deviation.  A proposed construction may use a successor that itself
punishes `j`, but it must prove that compatibility; an independently selected
punishment does not supply it.

## 7. Narrow Lean handoff

The canonical result can be packaged by defining the finite pair

```text
quittingPunishmentAnchoredSingletonSemantic reward owner
```

with coordinates (3)--(4), and proving:

```text
quittingPunishmentAnchoredSingletonSemantic_mem_carrier_of_normal

quittingPunishmentAnchoredSingletonSemantic_debt_owner

quittingPunishmentAnchoredSingletonSemantic_debt_other

minimumDebt_le_sum_pos_singletonJoinGain_of_normal
```

The proof should use `epsilon_n=1/(n+1)`,
`exists_quittingStationaryPunishmentRoot_lt_add`,
`quittingTerminalSemanticPair_rootThenContinuation`, the exact cap formula,
and `quittingTerminalSemanticCarrier_isCompact.isClosed.mem_of_tendsto`.

The no-fork result should be a small generic theorem near the existing
successor transport identity:

```text
quittingRootSuccessorPayoff_injective_of_continueMass_pos
```

and a singleton-clock specialization giving (16)--(18).  No new strategy
class or chronology structure is needed.

Do not encode the finite punishment-anchored graph as an admissible path: its
edges have not been proved root-Nash or Bellman-composable.

## Scope and nonclaims

This note does not produce:

* terminal approximate equilibria or a uniform-equilibrium payoff;
* an exact charged path or near-return;
* a source-attached target below the global minimum;
* no-new-support at an equality anchor;
* a vertical realization of the pure toggle graph; or
* an actual Fin4 positive-gap counterexample.

It proves the exact finite reduction

\[
\boxed{
\text{normal singleton owner}
\Longrightarrow
\begin{cases}
\text{canonical minimum anchor with explicit joiner support},\\
\text{strict punishment-singleton wall},
\end{cases}}
\]

and the exact architectural no-go

\[
\boxed{
\text{zero successor reach}
\Longrightarrow
\text{arbitrary punishment replacement is hidden};
\quad
\text{positive successor reach}
\Longrightarrow
\text{payoff injection and actual-successor cap control}.}
\]
