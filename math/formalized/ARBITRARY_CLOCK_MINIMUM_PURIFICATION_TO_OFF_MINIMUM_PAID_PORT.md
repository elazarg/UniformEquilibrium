# Arbitrary-clock positive minima purify to an off-minimum paid port

Authors: `PAIRED_HULL_REVIEW`

Independent reviews:

- [adversarial review by SOCIAL_WEIGHT_REVIEW](../feedback/PAIRED_HULL_REVIEW__ARBITRARY_CLOCK_PURIFICATION_TO_OFF_MINIMUM_PORT__BY_SOCIAL_WEIGHT_REVIEW.md);
- [independent falsification review by CODEX_DESCENDANT](../feedback/PAIRED_HULL_REVIEW__ARBITRARY_CLOCK_PURIFICATION_TO_OFF_MINIMUM_PORT__BY_CODEX_DESCENDANT.md).

## Exact statement

Let \(I\) be a nonempty finite player set of cardinality \(m\), and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a finite quitting-game reward table.  All strategies below are ordinary
behavioral strategies: at every live date a player may randomize independently
between Quit and Continue, and a unilateral replacement may change that
player's complete strategy at every date, including arbitrarily late stopping
and Never.

For an actual profile \(\sigma\), write

\[
 U_i(\sigma)=\text{its terminal payoff},\qquad
 B_i(\sigma)=\sup_{\tau_i}U_i(\tau_i,\sigma_{-i}),
\]

where the supremum is over all behavioral strategies of player \(i\).  Put

\[
 d_i(\sigma)=B_i(\sigma)-U_i(\sigma),\qquad
 D(\sigma)=\sum_{i\in I}d_i(\sigma).
\]

Let \(K_r\) be the closed terminal-semantic carrier, let

\[
 D_*:=\min_{z\in K_r}D(z)>0,
\]

and let \(z_*\in K_r\) attain this minimum.  Suppose \((\sigma_n)\) is any
retained sequence of actual behavioral profiles such that

\[
 \operatorname{Sem}(\sigma_n)\longrightarrow z_*.
\tag{1}
\]

Let \(M\) bound the absolute value of every terminal reward coordinate.  Then
there are:

1. an index \(n\);
2. an actual profile \(\tau\) connected to \(\sigma_n\) by a finite list of
   literal unilateral complete-strategy replacements;
3. a player \(h\in I\); and
4. a source-attached paid first-disagreement row against the actual opponents
   \(\tau_{-h}\),

such that

\[
 D(\tau)>D_*,
 \qquad
 d_h(\tau)\ge \Delta:=\frac{D_*}{m},
\tag{2}
\]

and the row has payoff gain at least

\[
 g:=\frac{\Delta}{4}=\frac{D_*}{4m}.
\tag{3}
\]

More precisely, its source pure clock belongs to the positive support of
player \(h\)'s stopping law in \(\tau\).  If \(a\) is the row's first
disagreement date, \(S_h(a)\) is \(h\)'s prescribed survival through \(a\),
\(L_{-h}(a)\) is the opponents' live mass there, and \(J(a)\) is the actual
joint reach probability, then

\[
 \Delta\le 4M S_h(a),
 \qquad
 \Delta\le 8M L_{-h}(a),
 \qquad
 \Delta^2\le 32M^2J(a).
\tag{4}
\]

Thus every output carries fixed positive debt, gain, and actual-reach floors
depending only on \(D_*\), \(m\), and \(M\), irrespective of which branch of
the proof produced it.  For four players the debt floor is \(D_*/4\) and the
paid-row gain floor is \(D_*/16\).

The strict excess \(D(\tau)-D_*>0\) need not have a source-independent lower
bound.  The fixed quantitative datum is the outgoing debt/paid-row passport,
not a uniform off-minimum distance.

## Conjecture-facing change

This result eliminates arbitrary mixed and infinite-support clocks as a
separate positive-minimum entrance.  Every actual sequence realizing a
positive global minimum contracts, through literal descendants of one of its
members, to the already isolated off-minimum paid-cap waist.

It strictly narrows
[the actual paid-cap descent or inert-stall obligation](../questions/FIN4_ACTUAL_PAID_CAP_DESCENT_OR_INERT_STALL.md):
the remaining problem may start from an actual off-minimum profile with a
fixed-gain, fixed-reach first-disagreement passport.  No extra arbitrary-clock
minimum chamber remains.

The off-minimum paid port is not consumed here.

## Definitions, probability, and agency

A pure clock is \(\operatorname{QuitAt}(q)\), with
\(q\in\overline{\mathbb N}:=\mathbb N\cup\{\infty\}\); \(q=\infty\) means
Never.  Before absorption a quitting game has only one public live history at
each date.  Consequently every complete behavioral strategy of one player
induces a probability mass function on \(\overline{\mathbb N}\).

A finite replacement ancestry from \(\sigma\) to \(\tau\) is a finite list

\[
 \sigma=\rho^0,\rho^1,\ldots,\rho^N=\tau
\]

such that consecutive profiles differ in the complete behavioral strategy of
only one player.  The list is literal provenance, not a Nash--Bellman
chronology: the replacements need not be best responses and their gains need
not be positive.

A paid first-disagreement row consists of two pure clocks for one player,
against the same actual opponents, whose payoff difference is at least the
declared gain.  Their histories agree up to their first differing action.  The
row therefore retains the actual continuation and is a genuine unilateral
behavioral deviation witness.  The support clause and (4) ensure that the row
is not merely an off-path comparison.

## Proof

### 1. Stopping-law disintegration and one-clock purification

Fix an actual profile \(\sigma\) and a player \(h\).  Let \(\pi_h\) be the
stopping-time law induced by \(h\)'s prescribed behavioral strategy, and put

\[
 V_h(q)=U_h(\operatorname{QuitAt}(q),\sigma_{-h}).
\]

The terminal payoff disintegrates exactly over the stopping law:

\[
 U_h(\sigma)=
 \sum_{q\in\overline{\mathbb N}}\pi_h(q)V_h(q).
\tag{5}
\]

There is a point \(q_h\) of positive \(\pi_h\)-mass satisfying

\[
 V_h(q_h)\ge U_h(\sigma).
\tag{6}
\]

Indeed, if every positive-mass value were strictly below the average, choose
one positive-mass point.  Its weighted deficit from the average is strictly
positive, every other weighted deficit is nonnegative, and the sum of all
deficits is zero by (5), a contradiction.

Replace only player \(h\)'s complete strategy by
\(\operatorname{QuitAt}(q_h)\).  This replacement weakly raises \(h\)'s
prescribed payoff and makes its strategy a pure clock.  Its unrestricted cap
is exactly unchanged, because its opponents have not changed:

\[
 B_h(\operatorname{QuitAt}(q_h),\sigma_{-h})=B_h(\sigma).
\tag{7}
\]

No assertion is made about the other players' caps, payoffs, or debts.  They
may change by an order-one amount.

### 2. Quantitative actual-reach lemma

We use the following stopping-law lemma.

**Lemma.**  Suppose at an actual profile \(\rho\), player \(h\) has
\(d_h(\rho)\ge\Delta>0\).  Then there are a source pure clock in the positive
support of \(h\)'s prescribed stopping law and a receiving pure clock whose
payoff difference is at least \(\Delta/4\).  Their first-disagreement row
satisfies (4).

**Proof.**  Let \(C=B_h(\rho)=\sup_qV_h(q)\) and
\(U=\mathbb E_{\pi_h}V_h\).  All \(V_h(q)\) and \(C\) lie in
\([-M,M]\).  Call \(q\) bad when

\[
 C-V_h(q)\ge\frac{\Delta}{2}.
\]

If \(p\) is the prescribed probability of the bad set, then

\[
 \Delta\le C-U
 \le \frac{\Delta}{2}+2Mp,
\]

so \(p\ge\Delta/(4M)\).  Choose the earliest finite bad atom if one exists;
if none exists, the bad mass lies at Never.  At every date no later than this
source clock, prescribed own survival is at least \(p\), which proves the
first inequality in (4).

By the definition of the supremum, choose a pure receiving clock with value
strictly above \(C-\Delta/4\).  Its payoff advantage over the bad source is
at least \(\Delta/4\).  Before their first disagreement the two pure clocks
coincide.  Conditional payoff differences after that date are bounded by
\(2M\), so the global advantage is at most \(2M L_{-h}(a)\).  This gives the
second inequality in (4).  Actual joint reach factors as

\[
 J(a)=S_h(a)L_{-h}(a).
\]

Multiplying the two one-sided bounds gives the third inequality.  The chosen
source is a positive-mass atom by construction, including the Never case.
This proves the lemma. \(\square\)

Because \(D_*>0\), necessarily \(M>0\); the division-free form (4) also
avoids any separate positivity convention for \(M\).

### 3. Sequential purification and the strict branch

By continuity of total debt, (1) implies

\[
 D(\sigma_n)\longrightarrow D_*.
\tag{8}
\]

Fix an ordering of the players.  Suppose that on the current subsequence the
first \(k\) players already use pure clocks and total debt tends to \(D_*\).
Apply the replacement from Section 1 to player \(k+1\) at every index.  Total
debt is bounded, so pass to a subsequence on which the new target debts
converge to some \(L_{k+1}\).  Every target is actual, hence global minimality
gives

\[
 L_{k+1}\ge D_*.
\tag{9}
\]

If \(L_{k+1}>D_*\), put

\[
 \varepsilon=\frac{L_{k+1}-D_*}{2}>0.
\]

After discarding finitely many indices, every target \(\rho_n\) satisfies

\[
 D(\rho_n)\ge D_*+\varepsilon.
\tag{10}
\]

For each such target choose a maximum-debt player and stabilize its label on
a further subsequence.  More importantly, the source-independent estimate

\[
 d_h(\rho_n)\ge\frac{D(\rho_n)}m\ge\frac{D_*}{m}=\Delta
\tag{11}
\]

holds throughout.  Apply the actual-reach lemma with this fixed \(\Delta\).
Choose any retained index and set \(\tau=\rho_n\).  It satisfies (2)--(4),
and its purification ancestry begins at the corresponding original
\(\sigma_n\).

If \(L_{k+1}=D_*\), retain that equality subsequence and continue.  Later
replacements never edit a player already purified.  Their debts may reactivate
through cap leakage; the induction records only literal purity of the earlier
strategies and convergence of total debt.  After at most \(m\) equality
steps, every player uses a pure clock and we have actual profiles \(\xi_n\)
with

\[
 D(\xi_n)\longrightarrow D_*.
\tag{12}
\]

### 4. Finite calendar quotient for pure clocks

For a pure-clock profile \(t=(t_i)_{i\in I}\), define its calendar type by:

1. the ordered partition of the finite-clock players into equal-deadline tie
   blocks;
2. the labelled set of Never players; and
3. a total first-date tag: `none` if all players use Never, `zero` if the
   first finite deadline is zero, and `positive` if it is strictly positive.

There are finitely many types for fixed finite \(I\).

**Calendar lemma.**  Two pure-clock profiles of the same calendar type have
exactly the same prescribed payoff, unrestricted behavioral cap vector,
terminal law, debt vector, and total debt.

**Proof.**  The prescribed terminal outcome is the first finite tie block, or
Never if the finite partition is empty, so its law and payoff are fixed by
the type.

Fix player \(i\).  If no opponent has a finite deadline, every finite pure
response terminates alone and Never gives zero.  Hence

\[
 B_i=\max\{r_i(\{i\}),0\}.
\tag{13}
\]

Otherwise let \(m_i\) be the earliest opponent deadline and \(A_i\) its tie
coalition.  A pure response at time \(q\) has exactly one of the values

\[
 \begin{array}{c|c}
 q<m_i&r_i(\{i\}),\\
 q=m_i&r_i(A_i\cup\{i\}),\\
 q>m_i\text{ or }q=\infty&r_i(A_i).
 \end{array}
\tag{14}
\]

The first option exists exactly when \(m_i>0\).  The ordered labelled
partition and the total first-date tag determine \(A_i\) and this fact.  This
also covers the delicate case in which \(i\) is the sole date-zero player:
after deleting \(i\), the next opponent block, if any, is at a positive date.

Every behavioral response induces a stopping law, and its payoff is the
average of the pure values in (13) or (14).  Therefore its unrestricted cap
is exactly the displayed finite maximum.  The cap vector, and hence the debt
vector, is fixed by the calendar type. \(\square\)

### 5. Equality branch: exact attainment and pure-time descent

Apply finite pigeonhole to (12) and retain one calendar type.  The calendar
lemma says that the complete semantic pairs on this subsequence are literally
one fixed pair \(z^{\mathrm{pure}}\), rather than merely convergent.  Therefore

\[
 D(z^{\mathrm{pure}})=D_*.
\tag{15}
\]

Choose one retained profile \(\xi\), and let
\(t:I\to\overline{\mathbb N}\) be its literal vector of pure stopping times,
so that \(\xi\) is definitionally the behavioral realization of \(t\).  This
is an actual pure-time/Never global minimum and retains at most \(m\) literal
purification replacements from its corresponding \(\sigma_n\).  No limit of
strategies \(\operatorname{QuitAt}(t_n)\) is taken.

Apply the checked theorem `pureTimeMinimum_exists_offMinimumPaidPort` directly
to this exact vector \(t\), the global lower bound \(D_*\), and (15).  Its
source is \(t\) itself: it supplies a finite pure-time replacement ancestry
starting literally at \(\xi\) and ending at an actual pure-clock profile
\(\tau\) with

\[
 D(\tau)>D_*.
\tag{16}
\]

That theorem also supplies a complete pure-time/Never best response with gain
strictly greater than \(D_*/m\).  To place both proof branches in the same
actual-reach interface, choose a maximum-debt player at \(\tau\).  Since

\[
 \max_i d_i(\tau)\ge D(\tau)/m>D_*/m,
\]

the lemma of Section 2 with \(\Delta=D_*/m\) supplies (2)--(4).  Composing the
two finite replacement lists gives ancestry from one original \(\sigma_n\).

Sections 3 and 5 exhaust all cases, proving the theorem.

## Source correspondence and novelty

The existing checked source layer provides the arbitrary-game entrance:

- `exists_minimum_quittingTerminalSemanticDebtSum` and
  `exists_profile_sequence_tendsto_minimumTerminalSemanticDebt` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`
  give a global minimum carrier point and a realizing sequence of actual
  profiles;
- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean` is the exact
  disintegration (5);
- `quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` and
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` ensure
  that pure clocks and Never cover the unrestricted behavioral cap; and
- `pureTimeMinimum_exists_offMinimumPaidPort` in
  `UniformEquilibrium/Diagnostics/Quitting/PureTimeMinimumPaidPort.lean`
  is the checked source-exact pure-time capstone used in Section 5.

The quantitative actual-reach lemma is kernel checked in the scratch lane as
`positiveDebt_exists_actualReach_paidFirstDisagreementRow` in
`math/fable/lean/FableDebtActualReach.lean`; its support-strengthened form is
`positiveDebt_exists_actualReach_paidRow_withSupport` in
`math/fable/lean/FableActualReachSupport.lean`.  These scratch declarations
are not production integration evidence.  Section 2 gives their ordinary
mathematical proof so the packet does not assume the desired result as an
interface field.

The checked capstone begins with an already canonical pure-clock minimum.  The
new step is the arbitrary-support purification: it selects only a non-worse
supported pure component, permits uncontrolled nonmover cap leakage, and uses
the strict/equality debt split plus the finite calendar quotient.  A narrow
source and conference search found no existing theorem carrying this
arbitrary-support composition to the off-minimum paid port.

No paper theorem is invoked.

## Boundary tests

1. **All Never.**  The calendar tag is `none`.  For every player the complete
   cap is \(\max\{r_i(\{i\}),0\}\), so the type remains semantically complete.
2. **Date zero.**  If the earliest opponent deadline is zero, the singleton
   response is unavailable.  Formula (14) correctly omits its first line.
3. **Sole date-zero owner.**  If player \(i\) alone forms the date-zero block,
   deleting \(i\) exposes either no finite opponent or a strictly positive
   opponent block.  The labelled partition plus the first-date tag determines
   the correct case.
4. **The first-date tag is necessary.**  Keep the same ordered labelled tie
   blocks but translate every finite deadline from date zero to date one.  If
   \(r_i(\{i\})\) is larger than both collision endpoints, player \(i\)'s cap
   rises in the translated profile because the early singleton response
   becomes available.  Relative order alone is insufficient.
5. **Unbounded deadline escape.**  A constant calendar-type subsequence has
   literally constant semantics even if its absolute deadlines tend to
   infinity.  The proof selects one actual member; it never passes from
   `QuitAt` to Never by continuity.
6. **Nonmover cap leakage.**  A purification controls only the mover's own cap.
   The induction allows earlier debt coordinates to reactivate and branches
   only on total debt after each replacement.  No zero-set monotonicity is
   used.
7. **Global minimality is essential.**  Give every player own singleton reward
   \(-1\) and every other reward coordinate zero.  A profile with one player
   quitting at date zero can have positive local debt and an executable
   refusal, but all Never is an exact zero-debt equilibrium.  The local profile
   is not a positive global minimum and does not contradict the theorem.

## Adapter and consumer

The actual-data adapter is direct.  Given any finite quitting game with
\(D_*>0\),
`exists_profile_sequence_tendsto_minimumTerminalSemanticDebt` supplies (1).
Apply this theorem to obtain one actual off-minimum profile, a literal finite
replacement ancestry from one member of that exact sequence, and the uniform
paid/reach passport (2)--(4).  For a retained minimum-atom source chronology,
use its own realizing sequence instead; no new minimum point, law, or unrelated
profile is selected.

The output is the entrance required by
`FIN4_ACTUAL_PAID_CAP_DESCENT_OR_INERT_STALL`: an actual off-minimum source and
an outgoing complete behavioral paid first-disagreement row.  Existing
cap-lifted port machinery can dispatch such a row further, but its quantitative
descent and inert-stall outputs are still the named open consumer.  This packet
does not claim that dispatch as a theorem consequence.

The retained provenance is exactly:

\[
 \text{one original realizing profile}
 \longrightarrow
 \text{a finite literal replacement ancestry}
 \longrightarrow
 \text{the actual off-minimum target}
 \longrightarrow
 \text{its source-supported paid row}.
\]

It is not an extension-compatible source chronology, does not retain the
original terminal law or post-mark tail, and does not reconstruct a new
minimum-atom producer.

## Lean handoff

Suggested declarations, in dependency order, are:

```text
exists_support_pureTime_payoff_ge_prescribed
QuittingPureClockCalendarType
pureClock_semantics_eq_of_calendarType_eq
minimumRealizingSequence_purify_or_offMinimum
minimumRealizingSequence_exists_offMinimumActualReachPaidPort
```

The first theorem should be proved from
`quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime`, retaining
positive support and not claiming cap attainment.  The calendar type must use
labelled tie blocks and the total `none | zero | positive` first-date tag.

For the induction, a convenient internal state records a subsequence map, the
current literal profiles, purity of an initial player segment, finite
replacement ancestry, and convergence of total debt to \(D_*\).  It must not
record preservation of previously zero debts or of nonmover caps.

At a strict exit and after the checked pure-time capstone, apply the same
actual-reach theorem with \(\Delta=D_*/m\).  This yields one common output
structure containing the off-minimum proof, observer debt floor, paid row,
source-support clause, both one-sided reach bounds, joint reach bound, and
finite ancestry.

Useful finite tests for the calendar lemma are: all Never; one date-zero
player; a multi-player date-zero tie; deletion of the sole first-block player;
and two profiles with the same tie order but zero versus positive first date.

## Scope and nonclaims

1. The theorem covers unrestricted unilateral behavioral deviations, not only
   stationary, finite-horizon, bounded-clock, or pure-time deviations.
2. Purification replacements are literal ancestry, not profitable edges and
   not a Nash--Bellman chronology.
3. Nonmover caps and debts need not be preserved.  Previously zero coordinates
   may reactivate.
4. The output need not retain the input law, marked atom, selected tail, or
   minimum-source wrapper.
5. The off-minimum excess is positive but not uniformly bounded below by the
   game-level constants.
6. The construction is a one-way contraction, not a renewable finite atlas
   rank.
7. No terminal approximate equilibrium, uniform-equilibrium payoff, or
   positive-gap counterexample is produced.
8. The off-minimum paid-cap descent/inert-stall waist remains open.

## Lean formalization record

Pre-formalization packet SHA-256:
`685ac2b80a233e1d4b44876e08e37afa4ad070c483f4a61477f4b0e2c6a3037c`.

The checked arbitrary-clock purification and actual-reach paid-port reduction
is integrated in commit
`60abce1b894a1575358e071c57384417377308e6`. Its production owners are
`UniformEquilibrium/Quitting/Paths/StoppingLawBadMassSelection.lean`,
`UniformEquilibrium/Quitting/Paths/BehaviorSupportedPureTimeReplacement.lean`,
`UniformEquilibrium/Diagnostics/Quitting/PureTimeSemanticFiniteRange.lean`,
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/ArbitraryClockMinimumPurification.lean`,
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualReachPaidFirstDisagreement.lean`,
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ArbitraryClockMinimumActualReachPaidPort.lean`,
and
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourArbitraryClockMinimumActualReachPaidPort.lean`.

The main declarations are
`quittingStoppingLaw_badMass_lowerBound`,
`quittingStoppingLaw_exists_leastBad_survival_lowerBound`,
`quittingStoppingLaw_badMass_le_survival_of_noFiniteBad`,
`exists_support_pureTime_payoff_ge_prescribed`,
`exists_support_pureTimeReplacement_ownDebt_le`,
`finite_range_quittingTerminalSemanticPair_pureTimeProfileBehavior`,
`minimumRealizingSequence_purify_or_offMinimum`,
`positiveDebt_exists_actualReach_paidRow_withSupport`,
`positiveDebt_exists_actualJointReach_paidRow_mem_support`,
`minimumRealizingSequence_exists_offMinimumActualReachPaidPort`,
`exists_minimumRealizingSequence_offMinimumActualReachPaidPort_of_debtSumInf_pos`,
and
`exists_finFourMinimumRealizingSequence_offMinimumActualReachPaidPort_of_debtSumInf_pos`.
The implementation uses `QuittingPureClockSemanticCode`, an exact finite code
for pure-clock terminal semantic pairs, in place of the packet's proposed
calendar-type presentation. This is a stronger finite semantic invariant: it
records exactly the prescribed payoff and unrestricted behavioral cap needed
by the purification argument without taking a limit of strategies.

Evidence seals are `M` and `L`, together with `A`: from the actual compact
terminal-semantic carrier, the positive global debt infimum supplies a
minimum, an actual realizing sequence, literal unilateral-replacement
ancestry, and the source-supported paid first-disagreement passport. There is
no downstream `C`; the resulting off-minimum paid port is not consumed.

The formalized result does not preserve nonmover caps or debts, the original
terminal law, a marked atom, or an extension-compatible chronology. Its
replacement ancestry is not a profitable path or a Nash--Bellman spine. The
strict off-minimum excess has no asserted uniform lower bound. No renewable
rank, paid-cap descent or inert-stall consumer, terminal approximate
equilibrium, uniform-equilibrium payoff, or positive-gap counterexample is
constructed.
