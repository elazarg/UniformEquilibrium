# Fin4 deletion near-cap collision producer

Authors: original derivation in
[FACE_ENLARGE_FOLLOWUP.md](../FACE_ENLARGE_FOLLOWUP.md) (unattributed
conference intake); strengthened export assembly by Codex Root

Independent reviews:
[Codex Archimedes](../feedback/FACE_ENLARGE_FOLLOWUP_ACTUAL__BY_CODEX_ARCHIMEDES.md),
[Codex Leibniz, explicit falsification attempt](../feedback/FACE_ENLARGE_FOLLOWUP_ACTUAL__BY_CODEX_LEIBNIZ_FALSIFICATION.md)

## Exact statement

Let \(I:=\operatorname{Fin}4\) and let \(r\) be a quitting reward table on
\(I\), with payoff zero after infinite all-Continue play. Strategies are
arbitrary behavioral quitting strategies on the unique live history. For a
behavioral profile \(\sigma\), write

\[
 B_i(\sigma)
 :=\sup_{\tau_i}U_i\bigl(\sigma[i\leftarrow\tau_i]\bigr),
 \qquad
 d_i(\sigma):=B_i(\sigma)-U_i(\sigma),
\]

where the supremum is over all behavioral deviations. Assume the repository's
actual-deviation terminal-gap predicate

\[
\begin{aligned}
&\gamma>0,\quad\text{and}\\
&\forall\sigma,\ \exists i\in I,\ \exists\tau_i,\qquad
U_i\bigl(\sigma[i\leftarrow\tau_i]\bigr)-U_i(\sigma)\ge\gamma .
\end{aligned}
\tag{G}
\]

In particular, \(\max_i d_i(\sigma)\ge\gamma\) for every \(\sigma\).

Let \(D_*\) be the minimum total debt on the compact terminal-semantic
carrier. Then \(D_*\ge\gamma>0\).

Fix any \(j\in I\), put \(C=I\setminus\{j\}\), and define

\[
 f_j:=\min\!\left(0,
     \min_{\varnothing\ne S\subseteq C}r_j(S)\right),
\]

\[
 \Pi_j:=\max\bigl(0,r_j(\{j\})-f_j\bigr),
\]

and

\[
 c_j:=\max\!\left(0,
     \max_{\varnothing\ne S\subseteq C}
       \bigl(r_j(S\cup\{j\})-r_j(S)\bigr)\right).
\]

Assume

\[
 \Pi_j<\gamma.
 \tag{P}
\]

For every

\[
 0<\varepsilon<\gamma,
 \qquad
 0<\delta<\gamma-\Pi_j,
\]

there exist literal data in the same reward table:

- a behavioral profile \(\rho\) of the deletion game on \(C\);
- its ambient quiet lift \(\sigma\), with \(j\) playing Never;
- a finite date \(t\in\mathbb N\);
- the profile update \(\tau:=\sigma[j\leftarrow Q_t^j]\);
- a survivor \(i\in C\); and
- a nonempty coalition \(S\subseteq C\);

such that

\[
 d_k(\sigma)\le\varepsilon\quad(k\in C),
 \qquad
 d_j(\sigma)\ge\gamma,
 \tag{1}
\]

\[
 U_j(\tau)-U_j(\sigma)\ge\gamma-\delta,
 \qquad
 d_j(\tau)\le\delta,
 \qquad
 d_i(\tau)\ge\gamma.
 \tag{2}
\]

Let \(L_t\) be the probability under \(\sigma\) that every survivor Continues
before date \(t\), let \(\mu_t(S)\) be the date-\(t\) product-root probability
that exactly \(S\subseteq C\) Quits, and put \(m_t(S):=L_t\mu_t(S)\).
Then \(m_t(S)\) is exactly the unconditional date-\(t\) mass under \(\tau\)
of the nonsingleton terminal coalition \(R=S\cup\{j\}\), and

\[
 m_t(S)\bigl(r_j(S\cup\{j\})-r_j(S)\bigr)
 \ge {\gamma-\Pi_j-\delta\over7}>0.
 \tag{3}
\]

In particular \(c_j>0\) and

\[
 m_t(S)\ge {\gamma-\Pi_j-\delta\over7c_j}.
 \tag{4}
\]

The checked Fin4 live-weighted collision consumer applies to these same
literal data. Consequently one of the following holds.

1. If \(z_{t+1}\) is the terminal-semantic pair of the literal suffix of
   \(\tau\) after date \(t\), then

   \[
   L_t\bigl(D(z_{t+1})-D_*\bigr)
   \ge {m_t(S)D_*\over2},
   \tag{5}
   \]

   and therefore

   \[
   D(z_{t+1})-D_*
   \ge {(\gamma-\Pi_j-\delta)D_*\over14c_j}.
   \tag{6}
   \]

2. There are a player \(q\in C\), a same-stage pure-endpoint update
   \(\tau'\) of \(\tau\), and a gain

   \[
   G_q:=U_q(\tau')-U_q(\tau)
   \ge {(\gamma-\Pi_j-\delta)D_*\over56c_j}>0
   \tag{7}
   \]

   such that

   \[
   d_q(\tau')=d_q(\tau)-G_q.
   \tag{8}
   \]

   The routed date-\(t\) coalition remains nonempty and has unconditional
   mass at least \(m_t(S)\).

The objects \(\sigma,\tau,\tau'\) are a source-matched chain of
counterfactual profile updates. They are not successive states of one play
and are not asserted to be edges of a Nash--Bellman chronology.

## Conjecture-facing change

Previously, deletion supplied static solo-versus-entry screens, while the
live-weighted collision theorem consumed a profile, date, and nonsingleton
stage atom only when those data were supplied.

This theorem is an arbitrary-table producer for that consumer in the
small-solo-premium arm. From a Fin4 terminal gap and the finite inequality
\(\Pi_j<\gamma\), it constructs one deletion source, one finite near-cap
update, a co-realized full-gap survivor debt, and a quantitatively paid
nonsingleton stage atom. The checked consumer then forces either a fixed
terminal-debt tail excursion or an exact unrestricted-debt decrease at a
distinct survivor while retaining an actual atom.

Thus, for every chosen \(j\), the table space is narrowed to

\[
 \Pi_j\ge\gamma
 \quad\text{or the explicit collision/profile-update packet above.}
\]

This is a producer for the finite-collision branch of the Fin4 producer
atlas. It does not consume the large-solo-premium arm or solve the remaining
chronological-composition problem.

## Definitions and assumptions

- The terminal coalition is the first nonempty set of simultaneous Quitters.
- Infinite all-Continue play pays zero.
- Behavioral strategies may randomize at every live date and may have
  infinite support or Never mass.
- All debts and caps in the statement quantify over unrestricted behavioral
  deviations.
- \(Q_t^j\) means Quit surely at finite date \(t\) and Continue before it.
- The quiet lift retains the survivors' literal live-history strategies and
  prescribes \(j\) to Never.
- The mass \(m_t(S)\) is unconditional stage mass, not conditional root mass
  or a limiting terminal-law atom.
- The value \(D_*\) is a carrier minimum, whereas every profile and suffix
  produced above is literal.

No stationarity, finite-support assumption, punishment-floor hypothesis,
blocker face, or projective-\(\bar Q\) hypothesis is used.

## Source correspondence

The proof uses these checked ingredients:

- quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three in
  UniformEquilibrium/Quitting/Classification/PlayerReindex.lean, together
  with terminal-profile selection in
  UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean;
- quittingTerminalPayoff_liftDeletedProfile and
  quittingBestReplyValue_liftDeletedProfile in
  UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean;
- sSup_range_quittingTerminalPayoff_update_eq_pureTime and
  exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub in
  UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean;
- quittingBestReplyValue_congr_of_opponents in
  UniformEquilibrium/Quitting/Punishment/SharedPunishment.lean;
- quittingRootSequencePureTimeTerminalValue_some_sub_none_eq and
  quittingRootEndpointDifference_eq_outsiderNever in
  UniformEquilibrium/Quitting/Paths/OutsiderNeverGluing.lean;
- quittingFinFourLiveWeightedCollisionTransfer_tailEscape_or_endpointGain,
  quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain, and
  quittingStageCoalitionMass_le_stagePureEndpointRouted in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean;
- terminalExploitabilityGap_le_terminalSemanticDebtSum_of_mem_carrier in
  UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawExploitabilityFloor.lean.

Quiet-lift localization and a finite full-gap outsider witness were
anticipated in
notes/CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION.md. Static deletion
passports bound solo and join terms but do not produce a date or a
probability-weighted atom. The new content is the one near-cap update which
simultaneously makes the outsider debt small, transfers the ambient gap to a
survivor, and finances that update by a literal collision atom before passing
it to the checked consumer.

## Proof

### 1. Quiet deletion lift

The deletion game on \(C\) has three players. Three-player uniform-payoff
existence supplies a terminal \(\varepsilon\)-Nash behavioral profile
\(\rho\). Let \(\sigma\) be its canonical ambient quiet lift.

Exact deletion naturality preserves, for every survivor, both its prescribed
terminal payoff and its supremum over all ambient behavioral deviations.
Hence \(d_k(\sigma)\le\varepsilon\) for \(k\in C\).

Apply (G) to \(\sigma\). Since \(\varepsilon<\gamma\), no survivor carries
the gap, and therefore \(d_j(\sigma)\ge\gamma\).

### 2. One finite near-cap update

Pure-time extremality identifies \(B_j(\sigma)\) with the supremum of payoffs
obtained by deterministic times in \(\mathbb N\cup\{\infty\}\). Choose a pure
time within \(\delta\) of this supremum. It cannot be Never: Never is already
prescribed by \(\sigma\), so its gain is zero, while the chosen gain is at
least

\[
 d_j(\sigma)-\delta\ge\gamma-\delta>0.
\]

The time is therefore finite; call it \(t\), and put
\(\tau=\sigma[j\leftarrow Q_t^j]\). Since \(j\)'s opponents did not change,
\(B_j(\tau)=B_j(\sigma)\). This gives the first two conclusions in (2).

Apply (G) to the literal profile \(\tau\). Because \(\delta<\gamma\), player
\(j\) cannot carry the new gap. Some \(i\in C\) therefore has
\(d_i(\tau)\ge\gamma\).

### 3. The gain contains a paid collision

At date \(t\), expand the exact payoff difference between \(Q_t^j\) and
Never. If \(V_{t+1}\) is \(j\)'s payoff from continuing as Never in the next
suffix, then

\[
\begin{aligned}
U_j(\tau)-U_j(\sigma)
={}&L_t\mu_t(\varnothing)
  \bigl(r_j(\{j\})-V_{t+1}\bigr)\\
&+\sum_{\varnothing\ne S\subseteq C}
  m_t(S)\bigl(r_j(S\cup\{j\})-r_j(S)\bigr).
\end{aligned}
\tag{9}
\]

Every outcome contributing to \(V_{t+1}\) pays either zero or \(r_j(S)\) for
some nonempty \(S\subseteq C\). Thus \(V_{t+1}\ge f_j\). The first term in
(9) is at most \(\Pi_j\): if the raw solo premium is negative, the term is
nonpositive; otherwise its probability is at most one.

Using (2), the collision sum is at least
\(\gamma-\Pi_j-\delta>0\). There are seven nonempty subsets of the
three-element set \(C\). At least one signed summand is at least one seventh
of their positive sum, proving (3). Its reward increment is positive and at
most \(c_j\), which proves (4).

### 4. Apply the collision consumer

Apply the checked Fin4 live-weighted collision theorem to the same profile
\(\tau\), date \(t\), and nonsingleton coalition \(R=S\cup\{j\}\). Its first
arm is (5). The right side is positive, so \(L_t>0\); since \(L_t\le1\), (4)
and (5) imply (6).

In the endpoint arm, the general bound \(m_t(S)D_*/(2|I|)\) is
\(m_t(S)D_*/8\). Combining this with (4) proves (7). The checked debt identity
gives (8), and the routing theorem preserves stage mass while keeping the
routed coalition nonempty.

Finally, the endpoint mover is not \(j\). The global pure-time gain of \(j\)
is positive. Exact transport writes it as \(L_t\) times \(j\)'s
Quit-minus-Continue endpoint difference, so both factors are positive.
Profile \(\tau\) prescribes \(j\) to Quit surely at this row, so its
played-action root Nash defect is zero. The endpoint branch selects a player
with strictly positive root defect and hence selects \(q\ne j\).

## Boundary tests

### The strict premium inequality is necessary

Let every survivor Continue at the selected date, let later survivor
absorption pay \(j\) zero, let \(r_j(\{j\})=\gamma\), and make every collision
increment zero. Quitting at that date gains exactly \(\gamma\), entirely
through the solo term. Here \(\Pi_j=\gamma\), but there is no paid collision.
Thus \(\Pi_j<\gamma\) cannot be weakened without another hypothesis.

### Near-cap selection is necessary

An arbitrary profitable pure time need not make \(j\)'s remaining debt small.
For example, if one pure time is worth \(\gamma\) above the current payoff
and another is worth \(2\gamma\), updating to the former leaves debt
\(\gamma\). The second use of (G) may then select \(j\) again. Near-cap
selection is what forces the gap to a survivor.

### The compactified-clock endpoint causes no loss

The only nonfinite pure time is Never. It is already \(j\)'s prescribed
strategy and has zero gain, whereas the near-cap time gains at least
\(\gamma-\delta>0\). Thus the selected time is genuinely finite; no cap
attainment or tightness hypothesis is hidden.

### The selected atom is literal and nonsingleton

The empty survivor set is exactly the solo term removed before pigeonholing.
The selected \(S\) is nonempty, so \(S\cup\{j\}\) is a nonsingleton terminal
coalition at the actual date \(t\) of the same profile \(\tau\).

## Adapter and consumer

The adapter starts from arbitrary data satisfying (G), (P), and a chosen
player \(j\). It deletes \(j\), invokes unconditional three-player existence,
quietly lifts the resulting terminal approximant, and uses the ambient gap
twice around one finite near-cap update. No profile, atom, or date is supplied.

The downstream consumer is the checked theorem
quittingFinFourLiveWeightedCollisionTransfer_tailEscape_or_endpointGain. The
adapter produces all of its actual source data, including a nonsingleton
terminal, positive unconditional stage mass, and the literal profile and
date. Its exact-debt and no-loss-routing corollaries are also checked.

The composition ends at a quantitative tail excursion or a distinct
survivor's exact debt drop with retained stage mass. It does not claim that
either output has already been converted into a uniform-equilibrium payoff.

## Lean handoff

A narrow implementation should first package the handoff and paid collision,
then compose it with the existing consumer.

Suggested declarations:

- exists_finFour_deletionNearCapPaidCollision: packages the deletion profile,
  quiet lift, finite date, near-cap update, full-gap survivor, coalition,
  paid-mass inequality, and unconditional mass bound;
- finFour_deletionNearCap_collisionDispatch: composes that packet with the
  checked live-weighted tail/endpoint theorem.

The main local proof obligations are:

1. expose self-update cap invariance through
   quittingBestReplyValue_congr_of_opponents;
2. expand the pure-time endpoint difference over seven survivor coalitions;
3. package the finite signed pigeonhole argument;
4. prove \(q\ne j\) from the positive endpoint difference and pure-Quit root
   defect formula; and
5. retain the live weight in the primary statement of the first consumer arm.

The packet structure must carry literal profiles and equalities. It must not
contain an admissible edge or chronology field.

## Scope and nonclaims

This packet does not prove:

- a uniform-equilibrium payoff or terminal approximants for the four-player
  game;
- a prescribed-payoff, punishment-floor, Nash--Bellman, or other executable
  chronology;
- total-debt descent, no-new-support, support-rank descent, recurrence, or
  regeneration;
- an aggregate transfer of the mover's lost debt to another recipient
  coordinate, or a positive recipient-debt increase.  The checked routed
  recipient theorem requires the source profile \(\tau\) to be quantitatively
  near the fixed minimum, and the deletion/near-cap construction does not
  provide that premise;
- any conclusion in the complementary arm \(\Pi_j\ge\gamma\);
- a passive-player deletion theorem inside the hard residual;
- an enlargement of projective \(\bar Q\); or
- a result for more than four players without replacing both three-player
  existence and the Fin4 collision constants.

This is ordinary mathematics assembled from checked ingredients. The valid
core of the composition is now checked in Lean as recorded below.

## Checked Lean realization

The game-independent seven-term extraction is proved in
`MathUE/FinitePaidCollision.lean`.  Its product-retaining declarations are
`Math.FinitePaidCollision.exists_paid_collision_of_card_seven_with_product`
and
`Math.FinitePaidCollision.exists_paid_collision_of_gain_ge_sub_with_product`;
the tail and endpoint rescalings are
`Math.FinitePaidCollision.tail_scale_of_paid_collision` and
`Math.FinitePaidCollision.endpoint_scale_of_paid_collision`.

The literal deletion/near-cap handoff is proved in
`Research/Quitting/FinFourDeletionNearCap.lean` by
`exists_finFour_deletionNearCapData`.  Its returned
`FinFourDeletionNearCapData` stores the quiet lift, the finite pure-time
update, every survivor's source debt bound, the omitted player's full source
debt, the near-cap gain, preservation of that player's unrestricted cap, its
post-update debt bound, and a survivor carrying the post-update gap.

The root-to-stage adapter and composed consumer are proved in
`Research/Quitting/FinFourDeletionCollisionExpansion.lean`.  In particular:

- `quittingFinFourDeletion_gain_eq_stageMass_expansion` gives the exact
  solo-plus-seven-collision decomposition on the literal source/update pair;
- `exists_finFour_deletionNearCapPaidCollision` returns one
  `QuittingFinFourPaidCollisionAtom` with both
  `(gamma - Pi - delta) / 7 <= atom.mass * atom.increment` and the
  corresponding mass lower bound;
- `quittingFinFourPaidCollisionAtom_stageMass_eq_mass`,
  `quittingFinFourDeletionExpansion_nonempty_term_eq_reward_difference`, and
  `finFourDeletionNearCapPaidCollisionAtom_mass_eq_source_survival_mul_opponent`
  identify that same atom respectively with its unconditional terminal stage
  mass, its exact same-coalition reward increment, and the source live weight
  times the same opponent product-root mass; and
- `finFourDeletionNearCap_collisionDispatch_distinct_with_bounds` retains the
  very same existential `data` and `atom` while returning the `1/14` tail
  excess bound or a distinct endpoint mover with the `1/56` gain bound, exact
  semantic and literal unrestricted-debt subtraction, and a nonempty routed
  coalition with no stage-mass loss.

Thus formula (3) is not merely an existence-equivalent estimate: its paid
product is a field-level statement about the exact atom passed to the checked
consumer.  The source-profile survival/product identity and the target-profile
stage-mass identity are both exposed by named declarations.

The result has `M` and checked Lean evidence `L`.  It has an actual-data
adapter `A` from the terminal-gap and small-solo-premium hypotheses to the
literal deletion profile, date, update, and collision atom.  It has `C` only
into the live-weighted tail/endpoint dispatch recorded above.  The generic
finite extraction belongs to `MathUE`; the game-semantic construction remains
Research-only and is reachable through `Research.lean`, not through a
production `UniformEquilibrium` umbrella.

The mathematical provenance is the unattributed conference intake
`FACE_ENLARGE_FOLLOWUP.md`, with strengthened export assembly by Codex Root
and the independent Archimedes and Leibniz reviews linked at the head of this
packet.  The Lean realization uses only the checked repository ingredients
listed in Source correspondence; no external theorem is imported.

The formalization deliberately stops short of any positive debt increase at
another recipient.  Such a conclusion requires the routed-transfer source
profile to be quantitatively near the fixed minimum, while the deletion
construction provides no such premise for `tau`.  Accordingly the checked
capstone exposes exact mover-debt decrease and no-loss routing, but no
recipient-debt-increase field or theorem.

The narrow checks of all three files, the full build, trust scan, import-graph
check, Research/production duplicate check, derivable-telescope check, and
documentation check all passed at promotion.
