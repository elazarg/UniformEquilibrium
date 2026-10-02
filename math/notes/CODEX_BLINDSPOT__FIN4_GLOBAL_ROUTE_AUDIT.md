# Fin4 global-route blind-spot audit

Author: `CODEX_BLINDSPOT`

## Status

Adversarial route audit, 2026-09-03.  This note contains one elementary exact
calculation and three exact finite-dimensional reformulations, followed by
four proposed attacks.  The attacks are **not proofs** of the Fin4 conjecture
and are not Lean-checked.  No counterexample table or positive invariant
barrier is claimed.

The main conclusion is not that the current cap-clock/paid-port work is
incorrect.  Its source-reprojection obstruction is real.  The portfolio is,
however, overconcentrated on repairing that obstruction inside the same proof
language.  Two pieces of information are repeatedly discarded before the
last step:

1. the simultaneous subgradient of the **whole exploitability objective** at
   one actual minimizing source, including a probability law on all tied cap
   witnesses; and
2. one self-generating object containing both macroscopic product-root jumps
   and infinitesimal singleton flow, including nested Zeno accumulation.

The highest-value redirection is therefore a full jump--flow essential-APS
program, with a same-source finite-clock KKT program as its adversarial dual.
The cleanest negative parallel is to synthesize a reward table and a semantic
barrier simultaneously, rather than continuing to screen proposed tables by
restricted strategies.

The current theorem-level status remains unchanged: the four-player
uniform-equilibrium conjecture is open.  The exact target is

\[
 \eta(r)=\inf_\sigma\max_i\bigl(B_i^r(\sigma)-U_i^r(\sigma)\bigr)=0
 \tag{0.1}
\]

for every Fin4 reward table.  A positive answer needs actual terminal
approximate Nash profiles at every error; a negative answer needs one table
with a fixed positive gap against all behavioral profiles.

## 1. Scope and sources inspected

I read `SOURCES.md`, `GOAL.md`, `questions/README.md`, the direct-decision,
approximate-forward-packet, escape-aware-certificate, and cardinal-minimal
questions, together with the maintained `docs/FRONTIER.md`, `docs/STATUS.md`,
`docs/TOOLKIT.md`, and `docs/ESSENTIAL_APS.md`.  I used the architecture notes
on semantic barrier duality, chronological occupation duality, state
topologies, recurrence, neutral chronology, and suffix information.

The exact project interfaces inspected were:

- `quittingUniformEquilibriumPayoffConjecture` in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingControllerTesterValue_eq_minimum_rawMaximumDebt` and
  `quittingControllerTesterValue_eq_zero_iff_exists_uniformEquilibriumPayoff`
  in `UniformEquilibrium/Quitting/ControllerTester/ControllerValue.lean`;
- `nonempty_closedInvariantBarrier_iff_le_controllerTesterValue` in
  `UniformEquilibrium/Quitting/ControllerTester/BarrierDuality.lean`;
- `terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable` in
  `UniformEquilibrium/Quitting/Root/NeverGeneratedSemanticCarrier.lean`; and
- `quittingFiniteClockSemanticReachable_eq_range_fold` and
  `quittingFiniteClockSemanticReachable_isCompact` in
  `Research/Quitting/FiniteClockTerminalSemantics.lean`.

The selected conference audits included the exact nested-response-menu
tightness theorem, the compact stopping-game/Reny no-go, the finite marked
order compactness and diffuse-clock no-go, the neutral calibrated-occupation
collapse, the finite-source chronological quotient no-go, the max-debt
contact conditions, the equilibrium-degree-at-infinity audit, and the
escape-aware quantile-clock hierarchy.

For the newest external direction I checked Ashkenazi-Golan, Krasikov,
Rainer, and Solan, *The APS approach for undiscounted quitting games*,
International Journal of Game Theory 55 (2026), article 19,
<https://doi.org/10.1007/s00182-026-00982-6>.  Its essential APS operator
characterizes a class of singleton-flow absorption paths under additional
conditions.  The paper explicitly leaves extension to more general strategy
families and to all subgame-perfect equilibrium payoffs for future work.  Its
discussion also records FAPs whose switch sets have accumulation structure
beyond one ordinary sequence.  The project formalization has a strong
conditional compiler on a compact, functional, unique-live singleton-flow
component, but `docs/ESSENTIAL_APS.md` expressly leaves full jumps and
arbitrary-game component production open.

## 2. What the dominant route forgets

The cap-clock state `(U,B)` is an exact sufficient state for further semantic
prefixing.  It is not an exact sufficient statistic for how a *minimum of the
global exploitability functional* resists all simultaneous perturbations of
the four stopping laws.

More precisely, the repeated compressions are:

| Compression | Information retained | Information discarded |
| --- | --- | --- |
| full pure-time obstacle `V_i(t)` to cap `B_i` | maximum value | the active maximizer face and the convex weights by which its kink balances other coordinates |
| actual law source to semantic pair | payoff and four caps | derivative of all four caps with respect to each marginal atom at that same source |
| exact jump roots and singleton-flow APS treated separately | a valid local compiler in each stratum | a greatest self-generating family in which a jump can land directly in a flow component and conversely |
| ordinary sequence of rows | one chronological scale | limit-of-limit/Zeno strata, such as an `omega` cycle accumulating at a point from which another cycle starts |
| fixed reward table search | upper witnesses or a barrier template | the freedom to let an exact solver design the table and its all-behavior barrier together |

The first loss is why a paid response can reduce its mover debt while raising
several spectator caps.  A single selected cap witness cannot see the
simultaneous balance.  The second pair of losses may be why source
reprojection keeps reappearing: the proof first leaves the self-generating
object and then attempts to reconstruct it from a semantic port.

## 3. Exact calculation: growing clocks solve a pure response cycle

This calculation is included both as a positive clue and as a filter against
false novelty.

Consider the two-player table

\[
\begin{array}{c|ccc}
 & \{1\}&\{2\}&\{1,2\}\\ \hline
r_1&-1&0&1\\
r_2& 1&1&0.
\end{array}
\tag{3.1}
\]

The four pure profiles with clocks in `{0,Never}` form the familiar strict
best-response cycle.  Hence a horizontal response-cycle argument does not
give a Lyapunov function.

Fix `N >= 0`.  Let player 1 play Never.  Let player 2's quitting time have
law

\[
 \Pr(T_2=k)=2^{-(k+1)}\quad(0\le k<N),
 \qquad
 \Pr(T_2=N)=2^{-N}.
\tag{3.2}
\]

Player 2 quits surely, receives its solo reward one, and already obtains its
cap.  Player 1's prescribed payoff is zero.  If player 1 quits at `t<N`, its
gain over Never is

\[
 \Pr(T_2=t)-\Pr(T_2>t)
 =2^{-(t+1)}-2^{-(t+1)}=0.
\tag{3.3}
\]

At `t=N` the gain is `2^{-N}`, while every later finite time and Never have
gain zero.  Pure-time extremality therefore gives the exact unrestricted
exploitability

\[
 E(\sigma^N)=2^{-N}.
\tag{3.4}
\]

Replacing (3.2) by the infinite geometric law
`Pr(T_2=k)=2^{-(k+1)}` makes every equality in (3.3) exact at every date and
gives an exact terminal Nash profile.

This proves three useful points.

1. A pure response cycle is not evidence for a counterexample.
2. The missing positive datum can be an every-cut tail-balance equation
   `atom(t)=mass(after t)`, not another local coalition sign.
3. Nested response menus are not a new blind spot: the project already has
   an exact double-oracle tightness/escape theorem.  What remains is the
   structure of its non-tight boundary, not the fact that old responses
   should be remembered.

## 4. Attack A: a full jump--flow essential APS operator

**Classification:** concrete conjectural program; highest priority.

The new 2026 essential-APS approach and its project formalization work on a
singleton-flow stratum.  Current cap-prefix work handles macroscopic product
roots.  No inspected source supplies one greatest-family operator which
contains both operations and proves coherent execution without leaving that
family.

### Self-contained target

Let `G` be a family of compact payoff sets, indexed by the finite mode needed
to record the live Flesch component and the current jump face.  Define one
essential predecessor operator with two literal clauses.

1. **Jump clause.**  There are a continuation `w in G` and a product root
   `x` which is exact root Nash against `w`, with

   \[
   v=F_r(x,w).
   \tag{4.1}
   \]

   This retains the entire root, its nonempty quitting-coalition law, and the
   exact continuation port.
2. **Flow clause.**  There are an owner `i`, `p in (0,1)`, and a continuation
   `w` in a permitted successor fibre such that

   \[
   v=p\,r(\{i\})+(1-p)w,
   \tag{4.2}
   \]

   with the Flesch activity and successor inequalities.

All-Continue and zero-length segments must be removed by the essential
iteration rather than counted as progress.  The desired Fin4 theorem is:

> Every nonempty greatest full-APS family either reaches a terminal point or
> admits one coherent jump--flow absorption path with deleted-player
> survival, hence terminal approximate Nash profiles.  If the greatest
> family is empty, the eliminating iterates yield a controller barrier or a
> finite strict separator.

This attacks the source seam at its origin.  A paid jump lands in the same
self-generating family that supplies its continuation; no horizontal
minimum-source regeneration is required.

### First bounded tests

1. Extend the current essential-APS code only by **one** full product-root
   jump followed by a unique-live singleton-flow component.  Prove compactness
   and execution for that one-jump class.
2. Reverse the order: a proper singleton segment followed by one full jump.
   Check that the continuation cap used in the jump is the literal segment
   endpoint, not a reselected sibling.
3. Run both constructions on the checked neutral-plateau regression.  A
   zero-mass all-Continue self-loop must not falsely certify absorption.
4. Run them on the passive-padded Solan periodic-certificate no-go.  The
   operator may produce an aperiodic or growing-scale path; it must not imply
   a universal bounded exact period.
5. Run them on the Solan--Vieille cyclic boundary table.  The known positive
   path must survive the essential pruning.

### Kill criterion

The program should be abandoned if even the one-jump/one-flow class fails to
have a closed predecessor graph after retaining the literal continuation
port, or if its execution requires a fresh source not contained in the same
greatest-family witness.  Merely taking the union of the existing jump and
flow certificates is not the target.

## 5. Attack B: transfinite/Zeno execution rather than one-scale recurrence

**Classification:** concrete topological extension of Attack A; speculative
but sharply testable.

An ordinary infinite run handles switch times of order type at most `omega`
when their absorption parameters tend to one.  It does not handle a cycle
whose switch times accumulate at `a<1`, followed by a new cycle after `a`, or
iterated accumulation of that form.  The essential-APS paper explicitly
exhibits the relevance of switch sets beyond its basic ordinal range.  In the
current project, these layers tend to be recorded as a remote bubble,
all-Continue phantom, or nonrenewable source boundary.

### Self-contained target

Define an executable APS trace indexed by a countable ordinal `alpha`.

- At successor ordinals use one literal jump or proper flow edge.
- At a limit ordinal take the compact limit of payoff and cumulative
  absorption data, retain the incoming source genealogy, and restart only if
  the remaining survival is positive.
- Require the sum of absorption increments before every limit to agree with
  the limiting absorption parameter.  No mass may disappear at a limit.

The first Fin4 theorem to seek is a dichotomy, not unrestricted transfinite
existence:

> A greatest-family point has an ordinary absorbing run, or it has a
> minimal positive Cantor--Bendixson rank.  At the first limit level, either
> the continuation descends to a proper successor component, or the limit
> lies on an explicit simple-circuit face satisfying finite algebraic
> equalities.

The simple-circuit face is then a finite input to the existing APS
face-avoidance and semialgebraic machinery.  Finiteness of the player graph
does not by itself bound the ordinal rank; that bound, if true for Fin4, is
the mathematical content to prove.

### Exact tests

1. Build owner words of types `omega`, `omega+omega`, and `omega^2` on a
   two- and three-cycle, with prescribed absorption increments summing to
   successive limits.  Verify the payoff arc equations at every limit.
2. Test whether an `omega^2` trace in one strongly connected component can be
   flattened to an ordinary trace without changing its initial payoff and
   sequential-perfection inequalities.  A proof would kill the transfinite
   extension as unnecessary; a counterexample would expose a real missing
   state variable.
3. Specialize to all directed graphs on four owners.  Classify which limit
   transitions can remain inside the same SCC under strict Flesch signs.

## 6. Attack C: KKT/needle conditions for actual exploitability minimizers

**Classification:** exact finite-dimensional reduction; limiting theorem
open.

For `K>=1`, let `X_K` be the product of the four simplexes of stopping laws
on

\[
 \{0,1,\ldots,K-1,\mathsf{Never}\}.
\]

Against such opponents, a pure response has only the finitely many payoff
classes `0,...,K-1,K,Never`, where `K` is after-support Quit.  Therefore

\[
 E_K(x)=\max_i\left(\max_t V_{i,t}(x_{-i})-U_i(x)\right)
\tag{6.1}
\]

is a finite maximum of multilinear polynomials on a compact polytope.  It has
an actual minimizer `x^K`.  Censoring/finite-clock density and the uniform cap
modulus give

\[
 \min_{x\in X_K}E_K(x)\downarrow\eta(r).
\tag{6.2}
\]

At `x^K`, the nonsmooth Fermat rule gives simultaneous multipliers:

- `theta_i>=0`, supported on the players with maximal debt, with
  `sum_i theta_i=1`; and
- for each such player, `rho_(i,t)>=0`, supported on its cap-active response
  times, with `sum_t rho_(i,t)=1`,

such that

\[
 0\in
 \sum_i\theta_i\left(
     \sum_t\rho_{i,t}\nabla V_{i,t}-\nabla U_i
   \right)
 +N_{X_K}(x^K).
\tag{6.3}
\]

This is an exact finite-dimensional necessary condition, subject only to the
standard Clarke subgradient/Fermat theorem.  It is materially stronger than
the current terminal costate identities.  Equation (6.3) balances the effect
of changing every marginal atom on every player's prescribed payoff and cap,
at one actual common source.  A single paid cap witness throws away the
probability vector `rho`; a debt vector throws away all cross-gradients.

### High-value target

Assume `eta(r)>0` and extract a limit of the primal--dual systems (6.3) after
common-quantile reparametrization.  Prove one of:

1. the limiting stationarity system is incompatible with the Fin4 hard
   residual and the max-debt contact equations;
2. it yields a full jump--flow APS component from Attack A; or
3. it yields a positive semantic barrier, turning a hypothetical
   counterexample into a finite or measure-valued dual certificate.

The first computational experiment should not optimize another strategy
class.  It should solve the exact KKT system for the global `E_K` minimizer on
small `K`, retaining all active response multipliers, and look for stable
support patterns as `K` grows.

### Kill criterion

If rational examples exhibit arbitrary cycling of the multiplier measures
with no compact quantile representation and no stronger condition than the
already known semantic contact inequalities, the route has merely restated
the carrier minimum.  The comparison must be made on the checked
finite-response-cycle and diffuse-clock regressions.

## 7. Attack D: synthesize the table and the barrier together

**Classification:** exact negative search program; certificate soundness is
already available, existence is unknown.

The project has an exact all-behavior barrier language and an escape-aware
semialgebraic hierarchy, but most experimental effort has searched for small
exploitability profiles of preselected tables.  That is asymmetric: a true
counterexample is an open reward-table phenomenon, and the solver should be
allowed to choose the table which best fits a simple invariant barrier.

### Finite search problem

Choose a small semialgebraic template for a closed set

\[
 P=\{z:g_a(z)\ge0,\ a=1,\ldots,L\}
\]

or a finite union of such cells.  Treat the sixty normalized Fin4 reward
coordinates, the coefficients of the `g_a`, and `gamma>0` as unknowns.  Ask
an exact real-algebraic solver for

\[
 e_\infty(r)\in P,
 \qquad T_x^r(P)\subseteq P\quad\forall x\in[0,1]^4,
 \qquad d(z)\ge\gamma\quad\forall z\in P.
\tag{7.1}
\]

Any solution of (7.1) is already an all-behavior counterexample certificate;
there is no bounded-clock completeness gap.

The search should add the exact necessary conditions at a max-debt contact:

- all four debts equal the positive contact value in the strict singleton
  moat;
- each singleton moat is at least that value;
- the harmonic inequality
  `eta * sum_i 1/kappa_i <= 1`; and
- every nonsingleton coalition has a member-leave or outsider-join toggle of
  size at least `eta`.

These constraints do not prove a barrier, but they remove vast regions of
reward space which cannot support one.  Use counterexample-guided refinement:
an invalid invariance implication returns a concrete state/root pair, which
is added to the next template.  Start with piecewise-affine/min-of-affine
barriers, then quadratic cells.

### Mandatory regressions

1. The neutral-plateau and local-regression tables have global minimum zero;
   every positive template must fail on them.
2. The passive-padded Solan table refutes universal bounded-period
   certificates but has a positive conclusion; it must not yield a barrier.
3. The certificate must quantify over the full root cube and use the exact
   cap maximum.  Sampling roots or fixing a tester menu is not acceptable.
4. A solver output is useful only with a rational/real-algebraic proof of all
   universal implications in (7.1).

This is not a claim that semialgebraic barriers are complete.  It is a change
in experimental objective: search directly for the exact negative endpoint,
with the reward table endogenous.

## 8. A lower-priority coordinate test: projective clock transforms

This is a concrete implementation suggestion for the already recognized
multiscale compactification problem, not a fifth claimed theorem.

For a finite-time marginal law put

\[
 A_i(z)=\sum_{t<\infty}\mu_i(t)z^t.
\]

A common calendar translation by `L` multiplies every `A_i` by `z^L`, so the
projective tuple `[A_1:...:A_4]` removes the irrelevant common delay while
retaining relative offsets.  For example, the laws `delta_n` and
`delta_(n+1)` both converge weakly to Never, but

\[
 A_n(z)=z^n,
 \qquad A_{n+1}(z)=z^{n+1},
 \qquad A_{n+1}(z)/A_n(z)=z.
\tag{8.1}
\]

Thus the one-date staggering which changes tie/preemption payoffs survives
projectivization, while the one-point compactification erases it.

A serious version must also store survival transforms and the Hadamard
products which compute first-opponent events.  Diffuse packets at scales `n`
and `n^2` show that one fixed complex variable is insufficient; the correct
test uses boundary blow-ups `z=exp(-s/a_n)` and a countable bubble tree.  The
route should be killed unless those transformed limits reconstruct all four
pure-response obstacle functions and have an executable tight subcategory.
Its value is as a coordinate system for the multiscale source law, not as a
standalone compactness slogan.

## 9. Ideas which are already killed or already present

The following should not be advertised as newly missing routes.

1. **Plain weak compactness/Reny security.**  A two-player exact table has
   Nash profiles with both clocks escaping to infinity and graph-limit payoff
   `(1,1)` over a non-Nash all-Never profile.  Closure-payoff security fails.
2. **Fixed finite tester menus.**  Every fixed menu can be defeated by placing
   a profitable time later.  The exact nested double-oracle theorem already
   proves tightness implies terminal Nash and otherwise selects a moving
   payer/opponent clock escape.
3. **Static parity or one-stage equilibrium index.**  Total degree can escape
   to the Late boundary, and the all-Continue apex can carry the entire local
   parity.  Essential co-source Late signs do not cancel mod two.
4. **Positive invariant occupation of exact cap-prefix edges.**  On the
   positive-debt carrier, `-log(total debt)` is an exact subaction and every
   invariant occupation has zero absorption, supported on all-Continue
   self-loops.
5. **Finite-period universality.**  The passive-padded perturbed Solan table
   has no exact bounded absorbing admissible block certificate at any period.
6. **Debt support, scalar social surplus, or a finite label rank.**  Exact
   response examples rotate debt among four coordinates and close a cycle.
7. **A generic semialgebraic verifier without a producer.**  Sound barrier
   and quantile-clock certificate languages already exist.  The new content
   in Attack D is endogenous table-plus-barrier synthesis.
8. **Exact cardinal deletion.**  A positive gap cannot survive deletion from
   Fin4 to at most three players, because the deleted game has the checked
   three-player uniform-payoff theorem.  Cardinal work must be a compiler or
   a guarded boundary transfer, not a claimed positive-gap face.

## 10. Ranked recommendation and next question

1. **Full jump--flow essential APS:** best chance to avoid the current seam
   instead of repairing it.
2. **Same-source KKT systems for `E_K` minimizers:** best source of new
   necessary equations and the natural adversarial dual to APS.
3. **Joint reward/barrier synthesis:** best exact negative experiment; any
   success settles the conjecture rather than another strategy-class screen.
4. **Transfinite APS execution:** pursue immediately if the one-jump/one-flow
   operator closes but ordinary coherent runs stall at an interior
   accumulation point.

The next concrete mathematical question is:

> For a compact essential singleton-flow component `G`, does adjoining one
> exact nontrivial product-root predecessor whose continuation lies in `G`
> preserve compact essentiality and produce a literal executable
> jump--then--flow absorption path, including unrestricted deviation guards?

A positive answer is the first genuinely new bridge between two independently
successful proof languages.  A negative answer should exhibit the exact
one-jump source/cap discontinuity and would tell the KKT and barrier searches
which missing variable must be retained.
