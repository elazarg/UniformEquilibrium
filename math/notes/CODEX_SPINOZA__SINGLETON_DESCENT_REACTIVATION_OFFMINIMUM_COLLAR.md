# Singleton descent reactivation crosses the positive-minimum cap collar

Author: `CODEX_SPINOZA`

## Status

**Complete ordinary-mathematics theorem, not checked in Lean.**  This note
consumes one field missing from the reviewed tropical two-Never chronological
descent.  In the Fin4 hard residual, a descendant whose leading hazard
support has become a singleton always has a fixed negative singleton-column
blocker.  That blocker's Quit-now response is eventually its exact complete
behavioral cap.  Moreover the descendant lies a full positive-minimum debt
unit away from the global minimum fibre in that cap coordinate.

Thus every literal stationary singleton descendant in the stated hard class,
regardless of the support cardinality or construction from which it came,
has a literal source-attached paid response at a macroscopic off-minimum cap
collar.  This does **not** assert that any particular prior descent produces
such a singleton, and it does **not** yet make the descent renewable.
Installing the blocker as a
sure date-zero quitter changes its terminal law to a singleton but leaves the
old survivor in the blocker's deleted law.  The resulting target is not a new
one-owner diffuse source to which the same argument can be reapplied.

## Question

Given any literal stationary descendant with exactly one leading owner in the
no-uniform-equilibrium Fin4 hard class, can positive global minimum, the
singleton margin, or the hard singleton matrix charge a reactivating player?

Yes, in the exact sense of a fixed off-minimum cap collar and an eventual
exact-cap Quit-now edge.  No additive return/descent follows without a new
source-reprojection theorem.

## Sources inspected

- `notes/CODEX_SNELL__TROPICAL_TWO_NEVER_CHRONOLOGICAL_SUPPORT_DESCENT.md`:
  the finite-\(n\) exact Never caps, literal two-step descendants, and the
  duplicated-cyclic reactivation regression.
- `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`:
  `exists_negative_entry_in_column_of_noHomogeneous`.
- `UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`:
  `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` and its
  `no_homogeneous` field.
- `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`:
  `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`,
  which identifies the normal principal matrix with the full Fin4 singleton
  matrix.
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`:
  `minimumTerminalSemantic_singletonMargin`.
- `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`:
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime`.
- `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`: compactness of
  the terminal semantic carrier and continuity of total semantic debt.

## 1. The singleton descendant

Let (I=\operatorname{Fin}4\), let

\[
 s_i=r_i(\{i\}),\qquad A_{ik}=r_i(\{k\})-s_i,                         \tag{1.1}
\]

and suppose the table has no uniform-equilibrium payoff.  The checked
standard-Q-side theorem, followed by the checked Fin4 full-normal-core
identity, gives

\[
 \neg\operatorname{HasHomogeneousSimplexSolution}(A),
 \qquad A_{ii}=0.                                                     \tag{1.2}
\]

Suppose a literal chronological Never descent produces stationary profiles
\(\tau_n\) with one leading owner (k):

- player (k)'s stationary hazard is (q_n>0);
- every other retained positive hazard has total (o(q_n));
- some players may already be literal Never; and
- (q_n\to0).

These hypotheses describe the support-one output of the reviewed descent from
initial support two or three, but the theorem is origin-independent: any
sequence satisfying them is an input, including a singleton later produced
from a different literal chronological construction.  The hypotheses imply

\[
 \operatorname{Law}(\tau_n)\longrightarrow\delta_{\{k\}},
 \qquad U_i(\tau_n)\longrightarrow r_i(\{k\}).                       \tag{1.3}
\]

The lower-order retained hazards are kept in the statement because deleting
the leading owner can magnify them.  No owner-cap limit is asserted below.

## 2. The hard column supplies a quantitative blocker

By `exists_negative_entry_in_column_of_noHomogeneous`, for every (k) there
is a label (b(k)\ne k) such that

\[
 A_{b(k),k}<0.                                                        \tag{2.1}
\]

Fix one choice for every column and put

\[
 g_0=\min_k\bigl(-A_{b(k),k}\bigr)>0.                                \tag{2.2}
\]

The positivity is uniform because there are four columns.

### Theorem 2.1 (eventual exact-cap reactivation)

For the support-one descendant (1.3), player (b=b(k))'s unrestricted cap
is attained by Quit at date zero for every sufficiently large (n), and

\[
 B_b(\tau_n)-U_b(\tau_n)\longrightarrow -A_{bk}\ge g_0.              \tag{2.3}
\]

In particular the literal one-player replacement

\[
 \tau_n\longrightarrow\widehat\tau_n
 \quad\text{(player (b) Quits surely at date zero)}                 \tag{2.4}
\]

is source-attached, cap-attaining, and has gain at least (g_0/2) for all
large (n).

#### Proof

Against (b), the opponents are stationary.  Therefore every pure quitting
time lies in the exact interval between Quit-now and Never, as in the
stationary envelope used by the chronological descent theorem.

The leading owner (k) Quits before all lower-order opponents with
probability tending to one.  Hence literal Never for (b) tends to
(r_b(\{k\})).  Quit now pays (s_b+o(1)): the chance of a simultaneous
opponent Quit in the date-zero row tends to zero.  By (2.1),

\[
 s_b-r_b(\{k\})=-A_{bk}\ge g_0>0.                                    \tag{2.5}
\]

Thus the two endpoint values are strictly separated for all large (n),
Quit now is the exact pure-time maximum, and behavioral pure-time
extremality makes it the unrestricted cap.  Combining (1.3) and (2.5) gives
(2.3).  \(\square\)

If the first owner removed by the two-step descent itself satisfies
(A_{ik}<0), Theorem 2.1 charges exactly that predecessor's reactivation.
If it does not, homogeneous infeasibility still supplies another fixed
reactivating label (b(k)).  The theorem does not conflate those two claims.

## 3. Positive minimum makes the endpoint macroscopically off-fibre

Let \(\mathcal C\) be the compact terminal semantic carrier.  Write

\[
 D(z)=\sum_i\bigl(B_i(z)-U_i(z)\bigr),
 \qquad
 D_*=\min_{z\in\mathcal C}D(z)>0,                                   \tag{3.1}
\]

and let

\[
 \mathcal F=\{z\in\mathcal C:D(z)=D_*\}                             \tag{3.2}
\]

be the global minimum fibre.  Pass to any terminal-semantic cluster point
\(y\) of the actual descendants \(\tau_n\).  Theorem 2.1 gives

\[
 U_b(y)=r_b(\{k\}),qquad B_b(y)=s_b.                                \tag{3.3}
\]

For every (z\in\mathcal F), the checked singleton-margin theorem gives

\[
 D_*\le B_b(z)-s_b.                                                  \tag{3.4}
\]

Combining (3.3)--(3.4) yields the coordinate collar

\[
 \boxed{B_b(z)-B_b(y)\ge D_*
        \qquad\text{for every }z\in\mathcal F.}                      \tag{3.5}
\]

In particular (y\notin\mathcal F).  Since the cluster set of the sequence
is compact and every cluster point has (3.3), there is also a sequence- and
table-dependent number \(\delta>0\) such that

\[
 \boxed{D(\tau_n)\ge D_*+\delta}
 \qquad\text{for all sufficiently large }n.                         \tag{3.6}
\]

#### Proof

Equation (3.4) is
`minimumTerminalSemantic_singletonMargin`, applied at the genuine minimum
point (z) and label (b).  At the descendant cluster, (3.3) says the same
cap coordinate is exactly the solo value.  This proves (3.5) and excludes
membership in \(\mathcal F\).  Compactness of the cluster set and continuity
of (D) then give the positive minimum excess in (3.6).  \(\square\)

This is stronger than saying merely that the blocker has positive debt.  The
positive global minimum locates the whole descendant on the far side of one
fixed cap-coordinate collar.  Punishment normality is not needed once the
hard no-homogeneous column theorem is available.

## 4. Why this still does not renew

The cap response (2.4) makes (b) Quit surely at date zero.  Therefore

\[
 \operatorname{Law}(\widehat\tau_n)\longrightarrow\delta_{\{b\}}.  \tag{4.1}
\]

It is tempting to regard this as a new support-one state and follow the
negative column of (b).  That is invalid.  If player (b) is deleted from
\(\widehat\tau_n), the old leading owner (k) is exposed again.  Thus the
player-deleted law of the apparent singleton-(b) target converges to
\(\delta_{\{k\}}), not to the lower-order background law of a genuine
diffuse one-owner-(b) source.

To reapply Theorem 2.1 one would have to perform at least two further changes:

1. turn (k) to Never; and
2. replace (b)'s sure date-zero Quit by a vanishing stationary hazard.

Neither change is a unilateral cap response furnished by (2.4), and no
checked source-reprojection theorem performs them while retaining the paid
gain or the minimum collar.  Terminal-law equality (4.1) is therefore too
coarse; the deleted-law ancestry is the exact field that fails.

Likewise, (3.6) is a state separation, not an additive budget.  A later
global re-equilibration may return from (D_*+\delta) to (D_*), and the
same bounded debt potential can oscillate across this collar indefinitely.
Without a Bellman/chronological account for that return seam, repeated
reactivations cannot be summed as fresh charge.

## 5. Conjecture-facing dispatch

Every literal stationary support-one descendant satisfying Section 1 has now
been reduced to a checked-interface-compatible alternative:

\[
\boxed{
\begin{array}{c}
\text{literal support-one descendant}\\
\Downarrow\\
\text{fixed exact-cap Quit-now response of gain at least }g_0/2\\
\text{from a point separated from the minimum fibre by the cap collar }D_*.
\end{array}}
\]

This is a genuine use of all three requested global fields:

- hard homogeneous infeasibility chooses the negative-column blocker;
- positive global minimum supplies the macroscopic collar; and
- the singleton margin proves the endpoint is not a disguised minimum point.

It still lands at the known paid-port/source-reentry waist.  A closing theorem
must now control the return from the sure-Quit target to a diffuse
minimum-attached source while retaining the blocker's deleted-law ancestry.
Repeating only the debt inequality or the negative-column graph would ignore
the failure in Section 4.

## Exact nonclaims

- The first removed predecessor need not be the hard-column blocker.
- No theorem here claims that an arbitrary support-two or support-four
  descendant reaches a singleton.  The collar applies once some literal
  chronological construction has actually produced the Section 1 input.
- The source tropical profile is not claimed to lie in the global minimum
  fibre.
- Off-minimum separation is not claimed to be a summable charge without a
  returned chronological seam.
- A terminal law close to \(\delta_{\{b\}}\) is not treated as a renewable
  one-owner source when its (b)-deleted law exposes (k).
- No new uniform-equilibrium consumer is claimed.

## Next exact question

Can the sure-Quit target (2.4), together with its exposed old-owner deleted
law, be connected back to a minimum-attached diffuse source by one exact
Nash--Bellman block whose seam is (o(g_0)), or does the collar (3.5) force a
positive charged return accepted by the existing paid-port consumer?
