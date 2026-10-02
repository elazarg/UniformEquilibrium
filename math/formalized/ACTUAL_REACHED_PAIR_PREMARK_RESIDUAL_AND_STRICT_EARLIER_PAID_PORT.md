# Actual reached-pair residual and strict-earlier paid port

Author: `CODEX_DESCENDANT`

Independent reviews:
[Paired Hull review](../feedback/CODEX_DESCENDANT__ACTUAL_REACHED_PAIR_PREMARK_RESIDUAL_AND_DELETED_REACH__BY_PAIRED_HULL_REVIEW.md),
[Social Weight review](../feedback/CODEX_DESCENDANT__ACTUAL_REACHED_PAIR_PREMARK_RESIDUAL_AND_DELETED_REACH__BY_SOCIAL_WEIGHT_REVIEW.md)

Both reviews' bounded correction is incorporated: the selected row is
declared at scale \(\rho/4\), while its realized gain is stated only to be at
least \(\rho/4\).

## Exact statement

Let \(I\) be a four-element player set and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a terminal reward table satisfying \(|r_i(S)|\le M\).  Let \(\sigma\) be
an arbitrary behavioral profile.  Suppose its prescribed product root at the
live history at date \(t\in\mathbb N\) is the pure pair \(K=\{a,b\}\).
All roots before \(t\), all earlier absorption, and the complete post-\(t\)
tail are arbitrary.  Put

\[
 L=\Pr_\sigma(\text{reach }t).
\]

Fix \(i\in I\).  Let \(\sigma^{i,t}\) change only \(i\)'s prescribed action
at date \(t\) to the opposite pure endpoint.  Define

\[
 \Delta_i=
 \begin{cases}
 r_i(K\setminus\{i\})-r_i(K),&i\in K,\\
 r_i(K\cup\{i\})-r_i(K),&i\notin K.
 \end{cases}
\]

Write \(U_i(\tau)\) for terminal payoff, \(B_i(\tau)\) for the supremum over
all unilateral behavioral replacements by \(i\), and
\(d_i(\tau)=B_i(\tau)-U_i(\tau)\).  Then:

1. If \(K'\) is the opposite endpoint coalition, the literal update satisfies

   \[
   U_i(\sigma^{i,t})-U_i(\sigma)=L\Delta_i,
   \tag{1.1}
   \]

   \[
   \operatorname{Law}(\sigma^{i,t})
   =\operatorname{Law}(\sigma)+L(\delta_{K'}-\delta_K).
   \tag{1.2}
   \]

   The Never coordinate is unchanged.

2. Among all unilateral replacements whose actions agree with \(\sigma_i\)
   at the quitting live history at every date strictly before \(t\), the
   exact payoff envelope is

   \[
   E_i^t(\sigma)=U_i(\sigma)+[L\Delta_i]_+.
   \tag{1.3}
   \]

   Thus the nonnegative pre-mark cap residual

   \[
   R_i^t(\sigma)=B_i(\sigma)-E_i^t(\sigma)
   \tag{1.4}
   \]

   gives

   \[
   d_i(\sigma)=[L\Delta_i]_++R_i^t(\sigma).
   \tag{1.5}
   \]

3. Assume \(\Delta_i\ge0\) and put
   \(\widehat\sigma=\sigma^{i,t}\).  Own-strategy invariance of the complete
   cap gives

   \[
   d_i(\widehat\sigma)=R_i^t(\sigma).
   \tag{1.6}
   \]

   Hence either \(R_i^t(\sigma)=0\), so the marked update kills the mover's
   whole debt, or, with \(\rho=R_i^t(\sigma)>0\), there is an actual paid
   first-disagreement row \(e\), against the literal opponents of
   \(\widehat\sigma\), such that

   \[
   \operatorname{start}(e)<t,
   \tag{1.7}
   \]

   \[
   \frac{\rho}{4}
   \le
   U_i(\text{receiving pure time},\widehat\sigma_{-i})
   -U_i(\text{source pure time},\widehat\sigma_{-i}),
   \tag{1.8}
   \]

   \[
   \rho\le4M\,\operatorname{OwnSurvival}(e),\qquad
   \rho\le8M\,\operatorname{OppReach}(e),
   \tag{1.9}
   \]

   \[
   \rho^2\le32M^2\,\operatorname{JointReach}(e).
   \tag{1.10}
   \]

   The source pure time belongs to the support of the actual stopping-time law
   of \(\widehat\sigma_i\).  Finite times, Never, and mixed prescribed clocks
   are included.

4. If \(q\) is the toggled player and \(j\ne q\), let

   \[
   H_j(t)=\Pr(\text{every player other than }j
                    \text{ survives strictly before }t).
   \]

   Then

   \[
   |B_j(\sigma^{q,t})-B_j(\sigma)|\le2M H_j(t).
   \tag{1.11}
   \]

   If \(S_j(t)\) is \(j\)'s prescribed survival before \(t\), independence
   gives

   \[
   L=S_j(t)H_j(t).
   \tag{1.12}
   \]

   Therefore no estimate \(H_j(t)=O(L)\) follows without a positive lower
   bound on \(S_j(t)\).

## Conjecture-facing change

This gives a strict reduction to the maintained quantitative paid-port question.
If an insider-leave gap satisfies \(\Delta_i\ge\delta>0\) and the actual
marked reach satisfies \(L\ge\lambda>0\), (1.1) is a literal source-attached
unilateral behavioral replacement with gain at least \(\lambda\delta\).
It preserves the prefix, earlier absorption, literal tail, unconditional law,
and incoming ancestry.

The theorem also gives the strict reduction

\[
\boxed{
\text{whole mover debt killed}
\quad\lor\quad
\text{a source-supported paid row strictly before the mark}.}
\tag{1.13}
\]

Given a separately supplied positive global-minimum terminal-semantic pair,
the second arm feeds the checked paid-cap port trichotomy.  The paid profile
itself is not asserted to be minimum.  The trichotomy's charged-near-return
output has the existing uniform-payoff consumer.  The quantitative-debt-
descent and inert outputs remain open.  The paid response may destroy the
screened pair, so (1.7) is not a renewable calendar rank.

## Definitions and probability audit

A behavioral profile assigns a Quit/Continue distribution to every player at
each live history.  A unilateral behavioral replacement may change one
player's entire strategy and is unrestricted by stationarity, horizon, or
support.  Against fixed opponents its induced stopping law is a probability
measure on \(\overline{\mathbb N}=\mathbb N\cup\{\infty\}\), where
\(\infty\) means Never.  Pure stopping times suffice for the cap supremum.

All masses above are unconditional.  The calculation conditions only on the
literal reach event and then multiplies by its probability \(L\).  It never
replaces the marked source by a mass-one date-zero profile.  A row in
(1.7)--(1.10) is a counterfactual pure-time comparison against the same actual
opponents; it is not thereby an exact cap--Nash root or Nash--Bellman edge.

## Proof

### Marked payoff, law, and residual

Couple play under \(\sigma\) and \(\sigma^{i,t}\).  Outcomes before \(t\) are
identical.  On reach, another pair member Quits surely after either endpoint
action by \(i\), so the game terminates at \(t\) in \(K\) or \(K'\).
The conditional payoff difference is \(\Delta_i\).  This proves (1.1), and
moving precisely the unconditional mass \(L\) from \(K\) to \(K'\) proves
(1.2).

If a response agrees with \(\sigma_i\) on the quitting live history before
\(t\), its pre-mark outcomes coincide with those of \(\sigma\).  At \(t\) it
can only mix the two endpoints; later actions are screened by the other sure
quitter.  Its exact best payoff is therefore (1.3).  Subtracting this envelope
from the unrestricted cap proves (1.4)--(1.5).  The cap depends only on the
opponents, so the one-date own update leaves \(B_i\) unchanged.  Under
\(\Delta_i\ge0\), (1.1) and (1.5) give (1.6).

In particular, if \(R_i^t(\sigma)>0\), every response within error strictly
smaller than \(R_i^t(\sigma)\) of the cap must change \(i\)'s strategy before
\(t\).  Otherwise (1.3) would bound its payoff below that level.

### Strict-earlier localization

Let \(\rho=R_i^t(\sigma)>0\).  Apply
`positiveDebt_exists_actualJointReach_paidRow_mem_support` to the literal
target \(\widehat\sigma\), observer \(i\), and debt floor \(\rho\).  It
supplies a row declared at scale \(\rho/4\), a source pure time \(q_0\) in the
actual stopping-law support, a receiving time \(q_1\), the realized-gain lower
bound (1.8), and (1.9)--(1.10).

Let \(V(q)\) be the payoff of pure stopping time \(q\) against
\(\widehat\sigma_{-i}\).  All pure times at or after \(t\) have the same
pre-mark contribution.  Conditional on opponent survival to \(t\), only the
Quit-at-\(t\) and Continue-at-\(t\) values remain.  The other pair member
screens every later finite time and Never, so all have the Continue value.
The target uses the better of these two values.

If \(q_0\ge t\), then in the Quit-endpoint case its support at or after \(t\)
is concentrated at \(t\); in the Continue-endpoint case every supported later
time, including Never, has the same screened Continue value.  Hence any
\(q_1\) first disagreeing with \(q_0\) at or after \(t\) satisfies
\(V(q_1)\le V(q_0)\), contradicting (1.8).  Thus
\(\operatorname{start}(e)<t\).

### Deleted-reach cap modulus

Fix \(j\ne q\) and any complete response \(\tau_j\).  Couple its outcomes
against \(\sigma_{-j}\) and \((\sigma^{q,t})_{-j}\).  They can differ only if
every opponent of \(j\) survives before \(t\), an event of probability
\(H_j(t)\).  The difference between two rewards in \([-M,M]\) is at most
\(2M\), so

\[
|U_j(\tau_j,\sigma_{-j})
-U_j(\tau_j,(\sigma^{q,t})_{-j})|
\le2M H_j(t).
\]

The bound is uniform in the unrestricted response \(\tau_j\); taking suprema
proves (1.11).  Independence proves (1.12).

## Boundary tests

### Exact-prefix positive boundary

If every pre-mark root is exact cap--Nash against its literal successor pair,
checked cap-prefix debt scaling gives

\[
d_i(\sigma)=L[\Delta_i]_+,\qquad R_i^t(\sigma)=0.
\]

Thus the normalized killed-mover formula is correct with exact-prefix data.
Literal prefix provenance alone is insufficient.

### Exact deleted-reach regression

Take players \(0,1,2,3\), \(t=1\), \(K=\{0,1\}\), toggled outsider \(q=2\),
and \(0<\varepsilon<1\).  At date zero, players \(0,1,2\) Continue surely and
player \(3\) Quits with probability \(1-\varepsilon\).  Conditional on
survival, at date one players \(0,1\) Quit and players \(2,3\) Continue.
Attach any literal tail.  Call this \(X_\varepsilon\).  Let \(Y_\varepsilon\)
make only player \(2\) Quit at date one, and let \(Z_\varepsilon\) instead make
only player \(3\) Quit there.

Set

\[
\begin{array}{c|rrrr}
S&r_0(S)&r_1(S)&r_2(S)&r_3(S)\\ \hline
\{3\}&0&0&0&0\\
\{0,1\}&0&0&0&0\\
\{0,1,2\}&0&0&1&1\\
\{0,1,3\}&0&0&0&-1\\
\{2\}&0&0&1&0\\
\{2,3\}&0&0&1&0.
\end{array}
\tag{1.14}
\]

Set every coordinate at every unlisted nonempty coalition to \(-1\).  Then

\[
B_2(X_\varepsilon)=B_2(Y_\varepsilon)=1,
\]

because player \(2\) can Quit at date zero and obtain one whether player \(3\)
also Quits or not.  The marked join gains only \(\varepsilon\), hence

\[
d_2(X_\varepsilon)=1,\qquad
d_2(Y_\varepsilon)=R_2^1(X_\varepsilon)=1-\varepsilon.
\tag{1.15}
\]

For player \(3\),

\[
B_3(X_\varepsilon)=0,\qquad
B_3(Y_\varepsilon)=1,\qquad
d_3(Y_\varepsilon)=1-\varepsilon.
\tag{1.16}
\]

Indeed, by continuing surely at date zero against \(Y_\varepsilon\), player
\(3\) reaches \(\{0,1,2\}\) surely and obtains one.  Here
\(L=\varepsilon\) but \(H_3(1)=1\), so the nonmover cap moves by one for
arbitrarily small marked reach.

The incoming sibling \(Z_\varepsilon\) pays player \(3\) minus one on the
marked triple, while continuing to \(X_\varepsilon\)'s pair pays zero.  Thus
the actual incoming triple-to-pair gain is \(\varepsilon\).  The example
retains earlier absorption, arbitrary literal tail, positive pair mass,
incoming strict ancestry, and complete caps.

This is not a positive-gap table.  The profile in which player \(2\) Quits
immediately and all others Continue has payoff and cap \((0,0,1,0)\), hence
zero total debt.  The example exactly refutes residual-zero and \(O(L)\)
nonmover-cap conclusions from the pair passport alone.

## Source correspondence

The literal one-date adapter is checked in
`Research/Quitting/PositiveStageAtomConcentratedPacket.lean`:

- `targetProfile_ownerCap_eq` proves own-cap invariance;
- `target_liveMass_eq_source` preserves marked reach;
- `targetProfile_postDate_liveRoot_eq` preserves the post-date roots;
- `sourceToTargetGain_eq_liveMass_mul_defect` proves (1.1); and
- `targetOwnerDebt_eq_sourceOwnerDebt_sub_gain` proves exact debt subtraction.

The primitive profile theorem is
`quittingLiteralSameStage_bestEndpoint_gain_and_debt` in
`Research/Quitting/SameStageEndpointMonodromy.lean`.

The source-supported row and reach bounds are checked by
`positiveDebt_exists_actualJointReach_paidRow_mem_support` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualReachPaidFirstDisagreement.lean`.
Its row field `gain_le_paid` is why (1.8) is an inequality, not equality.
Pure-time pairs are decoded by
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`.

Given a separately supplied positive global-minimum terminal-semantic pair,
the downstream adapter is
`paidFirstDisagreement_capPortTrichotomy` in
`Research/Quitting/PaidRowCapPortDispatch.lean`.  It returns a charged near
return, quantitative debt descent, or inert stall.  Only the first arm
currently carries a uniform-equilibrium payoff.

The new ordinary mathematics is (1.2)--(1.7) and (1.11)--(1.12).  No paper
result is invoked.

## Adapter and consumer

The actual-data adapter takes the literal profile, mark, and pure pair supplied
by the screened-pair source and performs at most one action update at the
existing mark.  Every pre-mark root, earlier absorption event, post-mark root,
and incoming endpoint witness remains attached.

For a profitable insider leave, (1.1) is the accepted behavioral response in
alternative 1 of the named question.  More generally, (1.6)--(1.10) return
either mover-debt annihilation or an actual earlier paid port.  With that
separate positive minimum data, the row feeds the checked paid-cap trichotomy
and its charged-near-return consumer when that arm occurs.  No minimum claim
is made about the row's literal profile.

## Lean handoff

The narrow new interface can be split into:

1. `quittingPurePair_restrictedResponseCap_eq`, proving (1.3);
2. `quittingPurePair_debt_eq_endpointGain_add_premarkResidual`, proving
   (1.5)--(1.6);
3. `quittingLiteralOneDateProfile_terminalLaw_eq_add_dirac_sub_dirac`,
   proving (1.2), including Never;
4. `positivePurePairResidual_exists_strictEarlierPaidRow`, proving
   (1.7)--(1.10) from the checked support-bearing selector; and
5. `quittingLiteralOneDateProfile_nonmoverCap_sub_le_deletedReach`, proving
   (1.11)--(1.12).

The regression should instantiate every unlisted reward coordinate as \(-1\).
Its first finite test should verify the exact caps in (1.15)--(1.16).

## Scope and nonclaims

This result does not:

- make the paid row an exact Nash--Bellman temporal edge;
- consume quantitative debt descent or inert stall;
- transport nonmover caps at the actual marked-reach scale;
- turn a killed mover into renewable minimum-fibre support descent;
- make the one-use calendar decrease renewable;
- produce a uniform-equilibrium payoff in every arm; or
- produce a four-player positive-gap counterexample.

## Lean formalization record

The packet prefix above is preserved at SHA-256
`1e7a62169ed263afe1ad63b78621fd1ee27368995daca9d69b8fcfaaef04ccab`.
Its checked implementation landed in production commit
`8fd6a10c8f573641e0f475e8dedc1fef7632c465`.

The low literal-profile interface is
`UniformEquilibrium/Diagnostics/Quitting/LiteralOneDateProfile.lean`.
It owns the unchanged declarations `quittingLiteralOneDateOverride`,
`quittingLiteralOneDateProfile`,
`quittingLiteralOneDateOverride_idem`,
`quittingLiteralOneDateOverride_self`,
`quittingLiteralOneDateOverride_of_ne`,
`quittingProfileLiveRoot_literalOneDateProfile`,
`quittingBehaviorLiveHazard_literalOneDateOverride`,
`quittingProfileLiveRoot_literalOneDateProfile_eq_rootSequenceUpdate`,
`quittingProfileLiveRoot_literalOneDateProfile_eq_canonical`,
`quittingTerminalPayoff_literalOneDateProfile_eq_canonical`,
`quittingContinuationBestResponseValue_literalOneDateProfile_self_eq`,
`quittingTerminalSemanticDebt_literalOneDateProfile_eq_sub_gain`, and
`quittingTerminalPayoff_literalOneDateProfile_gain_eq_liveMass_mul_defect`.

The packet-facing owner is
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualReachedPairPremarkResidual.lean`.
`QuittingActualReachedScreenedEndpointMark` stores the supplied literal mark.
Its declarations include the exact reached-gain and mover-debt splits,
`abs_target_nonmoverCap_sub_source_le_deletedReach`,
`source_liveMass_eq_ownSurvival_mul_deletedReach`,
`premarkResidual_eq_zero_or_nonempty_strictEarlierPaidRow`,
`target_mover_debt_eq_zero_or_strictEarlierPaidRow_capPortTrichotomy`,
`target_terminalOutcomeMass_eq_add_dirac_sub_dirac`, and the restricted
premark response envelope.  The cap-port theorem stores the separately
supplied minimum's carrier membership and constructs
`QuittingPaidCapLiftedSource` directly from production interfaces.

The exact four-player boundary is checked in
`UniformEquilibrium/Diagnostics/Quitting/Regression/FinFourPremarkDeletedReach.lean`.
`FinFourPremarkDeletedReachRegression.deletedReach_regression` gives the
displayed caps, debts, residual, marked reach, deleted reach, pair-law mass,
and zero-debt witness;
`exists_arbitrarilySmallMarkedReach_with_unitObserverCapChange` gives the
arbitrarily-small-reach/unit-cap-change family.

- **M:** complete for the supplied marked-profile mathematics and regression.
- **L:** complete under the production umbrellas and generated axiom audit.
- **A:** absent; no theorem constructs the screened actual mark or a positive
  global minimum from a bare minimum producer.
- **C:** branch-local only.  After a separate attained positive minimum is
  supplied, the positive-residual row enters the checked paid-cap
  trichotomy; its non-return arms remain open.

No theorem here makes the marked target a minimum, turns the response into a
temporal Nash edge, supplies chronology or renewal, constructs a positive-gap
table, or proves a uniform-equilibrium payoff.
