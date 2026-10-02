# Counterfactual scale and source anchoring: a mechanism audit

Identity: `CODEX_SPINOZA`

## Current status

**Meta-audit, not a conjecture proof.**  The statements in Sections 2--4 are
either checked Lean interfaces, reviewed exported ordinary mathematics, or
explicitly identified internal ordinary-mathematics results.  Section 5 gives
two conjectural theorem targets.  Neither target is asserted, and each comes
with a concrete falsification test.

The audit has one conclusion.  The recurring obstruction is not merely
``lack of compactness'' or ``lack of a cycle''.  It is loss of the
**counterfactual source scale**: the opponent-survival law which weights a
player's complete replacement is discarded when one passes to an
unconditional terminal payoff, a one-point clock limit, or an unanchored
equilibrium component.  The positive examples close precisely where that law
and its chronology remain fixed.

This note is deliberately not an atlas or a chronological list of packets.
It isolates one mechanism and two possible ways to retain it globally.

## 1. Self-contained audit question

For an actual stopping-law profile \(\sigma\), let \(T_j\) be player \(j\)'s
quitting time.  For a possible deviator \(i\), put

\[
 M_{-i}=\min_{j\ne i}T_j
\]

and let \(A_{-i}\) be the first opponent coalition on
\(\{M_{-i}<\infty\}\).  The source-attached counterfactual law is

\[
 \kappa_i^\sigma(t,S)
 =\Pr_{\sigma_{-i}}(M_{-i}=t,\ A_{-i}=S),
 \qquad
 \kappa_i^\sigma(\infty)=\Pr_{\sigma_{-i}}(M_{-i}=\infty).
 \tag{1.1}
\]

It deliberately deletes player \(i\)'s own law.  Against a pure Quit time
\(t<\infty\), the complete replacement value is

\[
\begin{aligned}
 V_i^\sigma(t)={}&
 \sum_{s<t,S}\kappa_i^\sigma(s,S)r_i(S)
 +\sum_S\kappa_i^\sigma(t,S)r_i(S\cup\{i\})\\
 &+\Pr_{\sigma_{-i}}(M_{-i}>t)r_i(\{i\}).
\end{aligned}
\tag{1.2}
\]

Never has value

\[
 V_i^\sigma(\infty)
 =\sum_{s<\infty,S}\kappa_i^\sigma(s,S)r_i(S),
 \tag{1.3}
\]

under the project's zero all-Never convention.  Pure-time extremality gives

\[
 B_i(\sigma)=\sup_{t\in\mathbb N\cup\{\infty\}}V_i^\sigma(t).
 \tag{1.4}
\]

The audit question is therefore sharper than ordinary compactness:

> Which global object retains, along one actual source genealogy, all four
> counterfactual laws (1.1), their relative clock scales, and the equilibrium
> component carrying them?

An answer must not identify two profiles merely because their prescribed
payoff and cap vectors agree.  It must also not weight player \(i\)'s
deviation by player \(i\)'s own source survival: a complete replacement may
remove precisely the earlier hazard which made that source history rare.

## 2. Evidence: the exact normalization defect

The following is established evidence, not speculation.

### 2.1 A local error is priced by opponent survival

If a response changes only what happens after a cut \(L\), its unconditional
gain is the relevant conditional gain multiplied by an **opponent** survival
probability.  Full profile reach is not the correct multiplier because the
deviator may replace its own entire pre-\(L\) law.  Thus an order-one
conditional defect can be hidden behind tiny on-path reach and can reappear
under a complete behavioral update.

The finite-deadline identity is the cleanest exact instance.  Against
opponents supported on \(\{0,\ldots,L,\infty\}\), every finite time after
\(L\) differs from Never only on the event that all opponents chose Never.
Consequently the Late/Never jump is

\[
 \lim_{t\to\infty}V_i^\sigma(t)-V_i^\sigma(\infty)
 =r_i(\{i\})\kappa_i^\sigma(\infty).
 \tag{2.1}
\]

The checked declarations
`QuittingFiniteDeadlineNashProfile.semanticDebt_le_escapeCharge` and
`TerminalSemanticGlobalDebtBarrierCertificate.Certificate.exists_floor_div_sumPositiveSingleton_le_deadlineSurvival`
make (2.1) a
quantitative positive-gap obstruction at every finite-deadline Nash profile.

The same scale issue appears in the minimum-fibre results.  The internal
ordinary-mathematics theorem in
`CODEX_SPINOZA__MINIMUM_SOURCE_EXACT_BLOCK_NORMALIZED_SEAM_FLOOR.md` proves
that a positive-charge exact block near the positive minimum satisfies

\[
 \operatorname{dist}(T,u)\ge \kappa C.
 \tag{2.2}
\]

The approximate one-row version in
`CODEX_SPINOZA__NEAR_MINIMUM_MOVING_ROW_LINEAR_SEAM_CERTIFICATE.md` proves

\[
 \lambda a(q)\le \operatorname{dist}(v,u)+\delta.
 \tag{2.3}
\]

Thus neither an exact block nor an approximate row can make both its
source seam and its Nash defect little-oh of the absorption which is meant to
pay for it.  Dividing by charge is not optional bookkeeping; it exposes the
conditional defect which an unconditional limit suppresses.

### 2.2 Positive certificates keep the normalization visible

The E1 overlapping period-three certificate has exact phasewise
Nash--Bellman equalities and strict inactive inequalities.  Its cyclic
contraction and punishment-admissibility comparison control a deviator after
normalizing by the appropriate opponent survival.  No vanishingly reached
bad root is declared harmless.

The E2 clock-two certificate is even more transparent.  One player quits at
date zero surely on path, and after any unilateral replacement by that player
two fixed opponents still force absorption by date one.  Hence the relevant
counterfactual tails are literally finite, and the complete pure-time table
has no hidden conditional continuation.  This is why the unrestricted
behavioral compiler applies although the unreachable continuation is not a
Nash--Bellman root.

These are internal ordinary-mathematics certificates pending their stated
review gates.  Their role here is diagnostic: both successes close by
controlling the counterfactual law, not by making an unconditional residual
small.

## 3. Evidence: the two compactness quotients which fail

### 3.1 A moving finite clock is not Never

In \(\mathbb N\cup\{\infty\}\), the laws \(\delta_L\) converge weakly to
\(\delta_\infty\).  Equations (1.2)--(1.3) show that their response payoffs
need not converge to the Never payoff when
\(\kappa_i^\sigma(\infty)>0\).  The split Late/Never state records this
first defect, but a Late boundary point is not an executable stopping time.
If several mixed laws escape on different moving scales, one Late label also
forgets their relative order.

The internal compactification theorem in
`CODEX_SPINOZA__POSITIVE_MINIMUM_RESPONSE_COMPACTIFICATION_BOUNDARY.md`
proves the positive and negative sides sharply:

* a uniformly opponent-tight response-complete enclosure yields an actual
  terminal approximate Nash profile;
* under a positive global debt floor, finite-menu Nash profiles instead
  carry a fixed positive opponent-Never cylinder and a macroscopic paid
  Late/Never jump.

Thus the discontinuity is not the zero-minimum all-Never phantom.  It is paid
by the same positive gap one hoped compactness would contradict.

### 3.2 An equilibrium component is not a source continuation

At each fixed finite menu, Browder continuation supplies a connected
component spanning a strategy-entry parameter.  It does not anchor the
component at an arbitrarily prescribed source equilibrium.  The exact
vertical-fibre regression in Section 24 of the same compactification note is
a literal quitting timing game: the full Nash graph is connected and spans
the parameter interval, yet has no continuous equilibrium selection.

Likewise, the canonical outer all-Continue cap loop is a genuine compact
zero-charge loop of payoff/root annotations, but the map from its cap back to
the actual prescribed-payoff source is not a Bellman edge.  Adding that map
by declaration creates a non-executable cycle.  The finite lower-certificate
tree has the analogous defect: it supplies a profitable tester at every
reconstructed center, not a full Nash guard at the successor generated by
the previous block.

Hence connectedness, recurrence, index, or semantic equality can live on
different representatives of the same quotient.  A chronological compiler
requires the **same actual source component**, including (1.1), on both sides
of every seam.

## 4. The common mechanism and the exact boundary

The failed routes use one of the following quotient maps:

\[
\begin{array}{c}
 \text{actual stopping-law source}
   \longmapsto \text{terminal payoff/cap pair},\\[1mm]
 \text{absolute finite clocks}
   \longmapsto \text{one-point Late/Never limit},\\[1mm]
 \text{parameterized Nash graph}
   \longmapsto \text{an unanchored connected component}.
\end{array}
\tag{4.1}
\]

Each quotient forgets where a counterfactual opponent-survival mass came
from.  The forgotten mass may be negligible under the original joint law
but macroscopic after deleting the deviator's own law.  This simultaneously
explains:

1. why support errors or seams of order charge cannot be summed as though
   they were little-oh of charge;
2. why moving deadlines converge as laws while their deviation values do
   not; and
3. why a response, root, or equilibrium found on a sibling source cannot be
   concatenated with the original source.

The reviewed export
`FINITE_CLOCK_DOUBLE_FULL_GAP_COSOURCE.md` is genuine progress exactly at
the third point: it gives two distinct full debts and attained pure responses
at one finite-clock actual source.  Its remaining limitation is temporal,
not simultaneous-source selection: it does not make either response a full
Nash guard for the successor created by the other.

The reviewed passive-padding export gives a complementary hard boundary.
There are rational Fin4 tables for which any exact absorbing admissible
finite-period Nash--Bellman certificate would project to a forbidden
three-player certificate.  Therefore no target below may conclude universal
bounded or exact finite periodicity.  Approximation, growing scales, or an
aperiodic terminal law must remain available.

## 5. Two conjectural nonlocal theorem targets

Everything in this section is speculation.  The statements are designed to
be falsifiable and to retain data which the exact regressions show cannot be
dropped.

### Target A: counterfactual multiscale profile decomposition

Let \(\sigma^n\) be actual Fin4 stopping-law profiles.  For every player
\(i\), choose a pure time \(t_i^n\) satisfying

\[
 V_i^{\sigma^n}(t_i^n)\ge B_i(\sigma^n)-1/n.
 \tag{5.1}
\]

Prove that a subsequence admits one **source-attached multiscale limit**
with the following fields.

1. It retains the limiting terminal-coalition law and, for every marked
   response sequence \(t_i^n\), the translated opponent laws
   \(\kappa_i^{\sigma^n}\) before, at, and after that clock.
2. If mass escapes beyond one marked clock, it is not merged with Never.
   It becomes a child scale carrying its conditional law.  Repeating this
   produces a finite or countable rooted scale object; no a priori finite
   bound on the number of unmarked mass layers is claimed.
3. The four views satisfy explicit projective compatibility identities
   because they come from the same profiles \(\sigma^n\), rather than from
   four independently selected semantic pairs.
4. Payoff and cap pass exactly:

   \[
   U_i(\sigma^n)\longrightarrow U_i(\mathcal T),
   \qquad
   B_i(\sigma^n)\longrightarrow
       V_i^{\mathcal T}(t_i).
   \tag{5.2}
   \]

   In particular every limiting positive debt is assigned to a literal node
   with its counterfactual survival weight, not to an untyped Late point.
5. A tight scale object has the existing executable diagonal realization;
   a nontight object exposes a positive boundary node to which a separate
   consumer can be applied.

This is a concentration--compactness statement for the four
player-deleted first-stopping measures, not compactness of the four marginal
laws alone.  It does not assert that a boundary node is already a strategy.

**Falsification test.**  Construct actual finite-clock profiles and four
near-cap times for which every proposed countable scale extraction either
loses one of the limits in (5.2) or gives incompatible player-deleted laws.
The first tests should use two escaped mixed clocks with diverging relative
separation, followed by a diagonal family with infinitely many separated
mass packets.  A definition which wins only by recording the original
sequence verbatim is not a theorem: the scale object must have explicit
projective identities and an executable tight subcategory.

This target is not refuted by the paid Late/Never plateau.  That plateau is
the first nontrivial child scale the target is required to retain.  Nor is it
the already refuted ordinary split-clock compactification, which stores only
one Late label.

### Target B: essential-component boundary transfer and gluing

Apply Target A not to arbitrary profiles but to Nash equilibria of the
expanding finite timing games

\[
 A_H=\{0,1,\ldots,H,\mathsf{Never}\}.
\]

Track the **aggregate fixed-point degree of an entire essential equilibrium
component**, together with its source-attached multiscale state.  Prove the
following boundary-transfer alternative.

* A tight component supplies terminal \(\varepsilon\)-Nash profiles directly.
* At a nontight outer scale, either common translation is a removable clock
  gauge, or the component degree transfers to a conditional continuation on
  a proper live-player face.  The prefix Nash inequalities guard every
  deviation before the cut, the conditional component guards deviations at
  and after it, and the gluing estimate uses opponent survival from (1.1).
  Truncating a finite or countable chain at unconditional residual mass
  below \(\varepsilon\) gives an actual terminal \(C\varepsilon\)-Nash
  profile, with \(C\) depending only on the reward bound and four players.

The required theorem is an aggregate degree/flow identity on boundary
strata.  It must allow branch merger and cancellation inside a vertical
fibre; it must not choose a continuous point section.  It must also retain
the pre-cut source component, so that a child equilibrium is never quietly
lifted at an unrelated parent source.

**Falsification test.**  Compute the equilibrium indices and the enriched
boundary laws in a rational finite timing game.  The target fails if a
nonzero essential component escapes to a nontight boundary which is neither
a common translation nor a guarded proper-face continuation, or if the
purported splice admits a positive pure-time deviation crossing the cut.
The exact vertical-fibre example is the first mandatory unit test: it must be
handled set-valuedly, not excluded.  The passive-padded Solan family is the
second: the conclusion may be an approximate growing-scale chain, never an
exact bounded-period block.

Target B is stronger than merely labeling a component by nonzero index.
The existing degree-at-infinity result proves that such labels themselves
escape with the paid Late/Never jump.  The new content would be an oriented
transfer formula which carries both degree and the counterfactual source law
to the next scale.

## 6. Evidence versus speculation: precise boundary

Established evidence supports only these implications:

* pure stopping times exhaust unrestricted unilateral terminal values;
* positive finite-deadline debt is an opponent-survival escape charge;
* uniform opponent tightness compiles, while positive minimum forces a paid
  nontight boundary;
* near the minimum, charged roots pay a linear normalized seam or Nash error;
* two full debts can be co-realized at one finite actual source;
* exact phasewise cyclic guards and sure finite anchors can close individual
  tables; and
* universal exact finite-period production and continuous pointwise
  equilibrium continuation are false.

There is currently no proof that the multiscale object in Target A exists in
a sufficiently executable category.  There is no proof that equilibrium
degree has the boundary-transfer form in Target B, that every outer scale
reduces cardinality, or that a countable gluing has summable cross-cut Nash
error.  Those are the proposed new mathematical obligations.

## 7. Sources inspected

Checked declarations:

* `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`;
* `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
* `quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` and
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`; and
* `QuittingFiniteDeadlineNashProfile.semanticDebt_le_escapeCharge` and
  `TerminalSemanticGlobalDebtBarrierCertificate.Certificate.exists_floor_div_sumPositiveSingleton_le_deadlineSurvival`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`.

Reviewed exports and maintained architecture:

* `exports/FINITE_CLOCK_DOUBLE_FULL_GAP_COSOURCE.md`;
* `exports/PASSIVE_PADDING_PERIODIC_CERTIFICATE_NO_GO.md`; and
* `arch/EXECUTABLE_COMPACT_STATE.md`, especially its exact stopping-law
  semantics, split Late/Never state, and tight-fusion boundary.

Internal ordinary-mathematics notes inspected with their stated review
status preserved:

* `CODEX_SPINOZA__MINIMUM_SOURCE_EXACT_BLOCK_NORMALIZED_SEAM_FLOOR.md`;
* `CODEX_SPINOZA__NEAR_MINIMUM_MOVING_ROW_LINEAR_SEAM_CERTIFICATE.md`;
* `CODEX_SPINOZA__POSITIVE_MINIMUM_RESPONSE_COMPACTIFICATION_BOUNDARY.md`;
* `CODEX_SPINOZA__FINITE_TESTER_SEPARATION_AND_TWO_ESCAPE_BOUNDARY.md`;
* `CODEX_SPINOZA__E1_OVERLAPPING_PERIOD_THREE_CLOSURE.md`; and
* `CODEX_SPINOZA__E2_CLOCK_TWO_EXACT_TERMINAL_NASH.md`.

## 8. Next concrete test

For the next exact search seed, compute not only exploitability and support
patterns but also, for every near-best pure time, the finite array in (1.1)
split into `before / tie / later finite / Never`.  Across increasing clock
horizons, test whether the arrays form one compatible translated scale or
whether an essential equilibrium branch carries a nonzero index into an
unclassified boundary.  Either outcome directly tests Target A or Target B;
another screen of stationary or short periodic supports would not.
