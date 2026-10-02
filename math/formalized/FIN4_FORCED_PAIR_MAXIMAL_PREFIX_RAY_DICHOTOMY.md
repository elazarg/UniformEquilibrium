# Forced-pair maximal prefixes form one scalar ray

Authors: `FORCED_PAIR_REVIEW`; strengthened boundary example by
`ATLAS_GATEKEEPER`

Independent review:
[`FORCED_PAIR_REVIEW__MAXIMAL_PREFIX_RAY_DICHOTOMY__BY_ATLAS_GATEKEEPER.md`](../feedback/FORCED_PAIR_REVIEW__MAXIMAL_PREFIX_RAY_DICHOTOMY__BY_ATLAS_GATEKEEPER.md)

Source producer:
[`FIN4_WEAK_SINGLETON_TO_MINIMUM_TAIL_FORCED_PAIR.md`](FIN4_WEAK_SINGLETON_TO_MINIMUM_TAIL_FORCED_PAIR.md)

## Exact statement

### Quitting-game semantics

Let (I) be a nonempty finite player set.  A behavioral strategy may use
private randomization and the complete observed history.  The game stops at
the first date at which a nonempty coalition Quits; infinite continuation
pays zero.  Let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be the terminal reward table.  For an actual behavioral profile (sigma),
write

\[
U_i(\sigma)
\]

for its prescribed terminal payoff and

\[
B_i(\sigma)
=\sup_{\tau_i}U_i(\sigma[i\leftarrow\tau_i])
\]

for the cap over all unilateral behavioral deviations.  Put

\[
d_i(\sigma):=B_i(\sigma)-U_i(\sigma),
\qquad
D(\sigma):=\sum_i d_i(\sigma).
\]

Equivalently, write (operatorname{Sem}(sigma)=(U(sigma),B(sigma)))
and evaluate (d_i,D) on that terminal-semantic pair.

Assume a terminal-semantic global minimum (z_*) is fixed:

\[
D_*:=D(z_*)>0,
\qquad
D_*\le D(z)
\quad
\text{for every }z\text{ in the terminal-semantic carrier.}
\tag{1}
\]

### A pure-coalition base

Fix a coalition (C\subseteq I) with

\[
|C|\ge2.
\tag{2}
\]

For an arbitrary behavioral tail (sigma), let (X_C(\sigma)) be the actual
profile which prescribes exactly the members of (C) to Quit surely at date
zero and uses (sigma) after the counterfactual all-Continue outcome.

All such profiles have one common terminal-semantic pair (Z_C=(U^C,B^C)),
where

\[
U_i^C=r_i(C)
\tag{3}
\]

and

\[
B_i^C=
\begin{cases}
\max\{r_i(C),r_i(C\setminus\{i\})\},&i\in C,\\[1mm]
\max\{r_i(C),r_i(C\cup\{i\})\},&i\notin C.
\end{cases}
\tag{4}
\]

Put

\[
D_0:=D(Z_C).
\tag{5}
\]

By (1), (D_0\ge D_*>0).

### The canonical maximal-prefix ray

At every actual profile (P), select canonically an exact cap--Nash product
root with maximal absorption probability.  This is the selector

```text
quittingMaximalCapPrefixRoot reward P
```

from the checked maximal-cap-prefix development.  Starting from any
(X_C(\sigma)), define recursively

\[
P^0(\sigma):=X_C(\sigma),
\qquad
P^{k+1}(\sigma):=q_k\triangleright P^k(\sigma),
\tag{6}
\]

where (q_k) is the canonical maximal root at (P^k(sigma)), and
(q\triangleright P) means the literal one-stage root (q) followed by (P)
after all Continue.

The roots (q_k) and the semantic pairs

\[
Z_k:=\operatorname{Sem}(P^k(\sigma))
\tag{7}
\]

are independent of the tail (sigma).  Define

\[
c_k:=\Pr_{q_k}(\text{all Continue}),
\qquad
a_k:=1-c_k,
\qquad
\alpha_k:=\prod_{h<k}c_h.
\tag{8}
\]

Then, for every player (i) and every (k),

\[
\boxed{d_i(Z_k)=\alpha_kd_i(Z_C)},
\tag{9}
\]

and hence

\[
\boxed{D_k:=D(Z_k)=\alpha_kD_0}.
\tag{10}
\]

Moreover,

\[
\alpha_k\ge\frac{D_*}{D_0}>0,
\tag{11}
\]

so

\[
\operatorname{supp}^+d(Z_k)=\operatorname{supp}^+d(Z_C)
\tag{12}
\]

and

\[
\frac{d_i(Z_k)}{D_k}=\frac{d_i(Z_C)}{D_0}.
\tag{13}
\]

The original pure coalition is reached at date (k) with exact unconditional
stage mass

\[
\boxed{m_k=\alpha_k}.
\tag{14}
\]

More generally, every fixed suffix stage atom is shifted by (k) dates and
multiplied by (alpha_k).

If a fixed unilateral endpoint change at the pure (C)-row has conditional
payoff difference (delta), then the behavioral deviation which copies all
outer roots and makes that endpoint change at date (k) has exact whole-
profile payoff difference

\[
\boxed{g_k=\alpha_k\delta=\frac{D_k}{D_0}\delta}.
\tag{15}
\]

No best-response-attainment claim is needed: this is one literal behavioral
deviation.

### Scalar limit dichotomy

The sequence (D_k) is decreasing and bounded below by (D_*).  Let

\[
L:=\lim_{k\to\infty}D_k\ge D_*.
\tag{16}
\]

Exactly one of the following occurs.

#### Minimum-return arm: (L=D_*)

Suppose in addition that actual tails (sigma_n) satisfy

\[
D(\operatorname{Sem}(\sigma_n))\longrightarrow D_*.
\tag{17}
\]

For each (n), attach (sigma_n) behind the pure (C)-row and prefix the
first (n) common maximal roots.  Denote the resulting actual profile by

\[
R_n:=P^n(\sigma_n).
\tag{18}
\]

Then

\[
D(\operatorname{Sem}(R_n))=D_n\longrightarrow D_*,
\tag{19}
\]

the pair row occurs at date (n) with mass

\[
\Pr_{R_n}(C\text{ at date }n)=\alpha_n
\longrightarrow\frac{D_*}{D_0}>0,
\tag{20}
\]

and the literal post-row spine is (sigma_n).

If a fixed marked owner (o) has coordinate root defect zero at the pure
(C)-row, then the family (R_n) defines an actual
`QuittingReprojectionConcentratedPacket` by taking

```text
profiles n := R_n
subseq      := id
mark n      := n
cutoff n    := n + 1
scale n     := 1 / (n + 1 : ℝ)
resolution := D_* / D_0.
```

Its normalized owner defect is identically zero, its marked stage mass is at
least its resolution, its semantic-prefix field is the literal date-(n)
decomposition, and its whole source debts converge to (D_*).

If (C) is nonsingleton, the checked concentrated-collision compiler applies.
Its fixed positive tail-escape alternative is eventually impossible by
(17).  Consequently the packet is eventually in the checked executable
three-role-transfer arm and supplies the existing fixed-role/limit-chord
output.

Any fixed positive pure-row endpoint defect (delta\ge\delta_0>0) also
retains the actual mover-gain floor

\[
g_n\ge\frac{D_*}{D_0}\delta_0.
\tag{21}
\]

The player carrying this gain is a mover; the collision compiler separately
selects a distinct debt recipient.

#### Canonical ray-stall arm: (L>D_*)

Every profile on this canonical orbit stays uniformly off the minimum fiber.
Equations (12)--(13) show that neither positive-debt support nor normalized
debt changes at any finite stage.

The exact one-step account is

\[
D_ka_k=D_k-D_{k+1}.
\tag{22}
\]

Therefore

\[
\sum_{k=0}^{\infty}D_ka_k=D_0-L
\tag{23}
\]

and

\[
\sum_{k=0}^{\infty}a_k
\le\frac{D_0-L}{D_*}<\infty.
\tag{24}
\]

In particular,

\[
a_k\longrightarrow0,
\qquad
\sup_{H\ge N}\sum_{k=N}^{H}a_k\longrightarrow0.
\tag{25}
\]

Every finite outward segment of this canonical ray is an exact accepted
punishment-floor forward-prefix certificate, with charge equal to the
corresponding sum of (a_k).  Thus restarting this same canonical
maximal-prefix construction arbitrarily deep cannot regenerate a fixed
positive amount of charge.

At the same time,

\[
m_k\longrightarrow\frac{L}{D_0}>0,
\tag{26}
\]

and every fixed (delta>0) at the pure row satisfies

\[
g_k\longrightarrow\frac{L}{D_0}\delta>0.
\tag{27}
\]

For the prescribed joint semantic/law points, the marked date-(k) event
contributes exactly (alpha_k) to terminal coalition (C).  Outer roots may
also absorb at (C), so the full terminal-law (C)-coordinate is at least,
not necessarily equal to, (alpha_k).  Every joint cluster point therefore
retains (C)-mass at least

\[
\frac{L}{D_0}>0.
\tag{28}
\]

Since (a_k\to0), every individual Quit probability in (q_k) tends to
zero.  Hence (q_k) tends coordinatewise to all Continue.  Closedness of the
root-Nash inequalities makes all Continue exact Nash against the limiting
cap.  The checked changed-state theorem then gives the exhaustive limit
alternative:

* all Continue is the unique exact root Nash action at the limit; or
* a positive-absorption exact root appears by support entry.

Maximality itself is not asserted to pass to the limit.

## Fin4 source-facing corollary

Assume the reviewed source object

```text
FinFourOwnerCompressedMinimumReturnForcedPairPacket
```

from
[`FIN4_WEAK_SINGLETON_TO_MINIMUM_TAIL_FORCED_PAIR.md`](FIN4_WEAK_SINGLETON_TO_MINIMUM_TAIL_FORCED_PAIR.md).
It supplies:

* a positive global terminal-semantic minimum (D_*>0);
* fixed distinct labels (j,o) and the pure pair (C=\{j,o\});
* actual post-row tails (sigma_n) with debt tending to (D_*);
* zero marked coordinate defect for owner (o); and
* after a finite-label subsequence, a fixed player (p\ne o) with pure-pair
  root defect
  \[
  \delta_p\ge\delta_0:=\lambda D_*/6>0.
  \tag{29}
  \]

Apply the generic ray theorem to this literal pair and these tails.

* If (L=D_*), the diagonal family is the formerly missing whole-source-
  return packet.  The checked collision compiler yields its eventual
  three-role transfer and corresponding limit-chord output; the positive
  tail-escape arm cannot recur.
* If (L>D_*), the only conclusion is the canonical quantitative ray stall:
  invariant support and normalized debt, vanishing future canonical charge,
  retained fixed pair mass and mover gain, and the all-Continue/support-entry
  joint-limit alternative.

Thus the maintained whole-source-return question is strictly narrowed to the
second case.  The theorem does not consume that case.

## Conjecture-facing change

The live obligation in
[`questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md`](../questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md)
was to convert a fixed-resolution, source-attached pure pair with a literal
minimum-return tail into whole-source return or an equivalent semantic
consumer.  Tail replacement alone cannot work because two sure quitters make
the pair source's semantic pair tail-blind.

This theorem completely analyzes the canonical maximal-absorption cap-prefix
repair:

\[
\boxed{
\begin{array}{c}
\text{minimum-tail forced pair}\\
\Longrightarrow\\
\text{checked three-role packet output}\
\quad\lor\quad
\text{canonical off-minimum scalar-ray stall }(L>D_*).
\end{array}}
\]

The first branch is a genuine construction of the missing whole-source field.
The second is a strict, quantitative remaining condition and a no-go for
continuing to prefix the unchanged source by the same canonical maximal-root
architecture.  It is not a new equilibrium or descent theorem.

## Proof

### 1. Tail independence against all behavioral deviations

Under prescribed play, the date-zero pure (C)-row absorbs surely.  Fix a
player (i) and allow an arbitrary unilateral behavioral replacement.  Since
(|C|\ge2), at least one member of (C\setminus\{i\}) remains a sure quitter.
Thus absorption still occurs at date zero, even if (i) uses Never, a late
stopping time, private randomization, or an arbitrary history-dependent
strategy.

Conditional on (i)'s date-zero action, the only possible terminal coalitions
are (C) and (C\triangle\{i\}).  Randomizing gives a convex combination of
their two rewards, so the unrestricted supremum is their maximum.  This proves
(3)--(4) and full semantic-pair independence from (sigma).  Prescribed
terminal law is the point mass at (C), also independently of the tail.

### 2. The maximal selectors are common

The canonical selector is defined by choosing a maximal-absorption element of
the exact root-Nash correspondence against the current semantic cap.  Equal
semantic caps therefore give equal selected roots.  The base semantic pairs
are equal by Step 1.  If the semantic pairs at depth (k) are equal, they are
prefixed by the same root, so their depth-(k+1) semantic pairs are equal.
Induction proves that (q_k,Z_k) are independent of (sigma).

### 3. Debt, atoms, and gains have one multiplier

Each (q_k) is exact Nash against the cap of (Z_k).  Exact playerwise
cap-prefix transport gives

\[
d_i(Z_{k+1})=c_kd_i(Z_k).
\]

Induction proves (9), and summation proves (10).  Since each (Z_k) is the
semantic pair of an actual profile, (1) gives (D_k\ge D_*), which implies
(11).  Because (alpha_k>0), equations (12)--(13) follow.

The literal stage-mass transport identity multiplies every shifted suffix
atom by (c_k) at one prefix.  Induction gives the factor (alpha_k); the
pure (C)-root has conditional coalition mass one, proving (14).

For the endpoint gain, couple prescribed play with the deviation that copies
the entire outer word and differs only at the shifted pure row.  Outcomes
absorbed in the outer word are identical.  Conditional on reaching the row,
the payoff difference is (delta).  The reach probability is (alpha_k),
which proves (15).

### 4. The scalar limit and the return packet

Each (c_k\in[0,1]), so (10) makes (D_k) decreasing.  It is bounded below
by (D_*), proving existence of (L).

If (L=D_*), the diagonal profile (R_n) has semantic debt (D_n\to D_*)
because the semantic orbit is common.  Its marked pair mass and literal tail
are given by (14) and the construction.  The marked owner defect remains zero
because outer prefixing does not change the pure marked root or its post-row
tail.  The displayed packet fields therefore satisfy the exact
`QuittingReprojectionConcentratedPacket` definition.  Equation (17) makes the
compiler's fixed positive tail escape eventually false, so its checked
three-role output follows.

### 5. The strict stall and its capacity account

If (L>D_*), equations (12)--(13) already exclude source return or support
descent inside this orbit.  Since (D_{k+1}=c_kD_k), rearranging gives (22).
Finite telescoping gives

\[
\sum_{k<N}D_ka_k=D_0-D_N.
\]

Letting (N\to\infty) gives (23).  Since (D_k\ge D_*>0), (24) follows.
Every summable nonnegative sequence tends to zero and has vanishing tail
sums, proving (25).  Equations (26)--(27) follow from
(alpha_k=D_k/D_0\to L/D_0).

The checked punishment-floor certificate uses the outward Bellman order
(Z_k\mapsto Z_{k+1}), and its charge is (sum a_k).  This is an accepted
forward-prefix certificate.  The roots occur in reverse outer-to-inner order
inside the literal profile (P^k); no chronological-order identification is
used.

### 6. The compact limit

The marked date-(k) event contributes (alpha_k) to the full terminal-law
(C)-coordinate, proving (28).  Also, each player's Quit probability at
(q_k) is at most the root's total absorption probability (a_k\to0).
Therefore (q_k\to\mathbf C), the all-Continue root.  Compactness of the
joint semantic/law carrier and closedness of exact endpoint Nash inequalities
give the claimed limit.  The checked maximal-prefix limit theorem supplies
the unique-all-Continue/support-entry alternative without asserting that
maximality passes to the limit.

## Boundary tests

### Necessity of two sure quitters

If (|C|=1), its only sure quitter may deviate to Continue and expose the
arbitrary tail.  Equations (3)--(4) need not be tail-independent.  The
cardinality hypothesis is therefore essential.

### Zero marked-owner defect does not eliminate the local stall

Let (I=\{0,1,2,3\}) and (C=\{0,1\}).  For (i\in\{0,2,3\}), set

\[
r_i(S)=
\begin{cases}
2,&i\notin S,\\
1,&S=\{i\},\\
0,&i\in S\text{ and }|S|\ge2.
\end{cases}
\]

For player (1), set

\[
r_1(S)=
\begin{cases}
1,&S=\{1\},\\
2,&\{0,1\}\subseteq S,\\
0,&\text{otherwise}.
\end{cases}
\]

At the pure pair,

\[
U=(0,2,2,2),\qquad B=(2,2,2,2),\qquad d=(2,0,0,0).
\]

Player (1) is a zero-defect marked owner and player (0) has a positive
leave gain.  All Continue is the unique exact cap root: Continue is strictly
dominant for players (0,2,3), and after player (0) Continues, player (1)
gets (2) from Continue and (1) from Quit.  Hence the canonical ray is
pointwise inert while the paid pair row persists.

The pure singleton ({1}) is a terminal Nash profile, so this table has
global minimum zero.  It is not a counterexample and does not instantiate
(1).  It proves only that the local pair, zero-owner, and paid-row fields do
not eliminate the stall without positive-minimum provenance.

### State change leaves the theorem's scope

Updating the paid mover at the pair preserves the pair's local causal data,
but changes the suffix semantic cap seen by copied outer roots.  Their former
exact cap-Nash certificates need not survive.  Recomputing maximal roots from
that changed profile starts a new ray and is not covered by the stall no-go.

## Adapter and consumer

The actual-data adapter is the reviewed
`FinFourOwnerCompressedMinimumReturnForcedPairPacket`, constructed from the
maintained minimum-singleton source.  It supplies the fixed labels, literal
pure pair, minimum-return tails, zero marked owner defect, fixed pair mass,
and fixed other-player defect.  These are outputs of the source producer, not
hypotheses invented for this theorem.

In the (L=D_*) arm, the new diagonal construction supplies the exact packet
consumed by:

```text
ConcentratedCollisionFourRole.packet_eventually_tailEscape_or_threeRoleTransfer
ConcentratedCollisionFourRole.packet_tailEscapeFrequently_or_threeRoleLimitChord
```

The tail-debt convergence eliminates the positive fixed tail-escape branch.

In the (L>D_*) arm, there is deliberately no semantic consumer.  The result
is an impossibility theorem for one broad natural repair architecture and a
strict replacement of the prior whole-source-return obligation by the
canonical quantitative ray-stall node.

## Source correspondence

The generic checked infrastructure already contains:

```text
quittingTerminalPayoff_pureSetRoot
quittingStationaryUnilateralCap_pureSetRoot
quittingTerminalSemanticDebt_pureSetRoot_eq

exists_maximalAbsorption_isZeroQuittingRootNash
quittingMaximalCapPrefixRoot
quittingMaximalCapPrefixRoot_exactNash
quittingMaximalCapPrefixRoot_maximal
quittingMaximalCapPrefixProfile
quittingMaximalCapPrefixProfile_debt_succ
quittingMaximalCapPrefixProfile_stage_succ
quittingMaximalCapPrefixProfile_debt_mul_stage_eq
minimum_mul_sum_maximalCapPrefix_absorption_le_debtDrop
summable_maximalCapPrefix_absorption
maximalCapPrefix_atomMass_lowerBound
exists_offMinimum_retainedLaw_allContinue_or_supportEntry
quittingMaximalCapPrefixPunishmentFloorPrefix
maximalCapPrefixPunishmentFloorPrefix_charge_le_semanticBudget

quittingTerminalDeviationDebt_rootThenContinuation_eq_continueMass_mul_of_capNash
quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash
quittingTerminalDeviationDebt_capNashRootStack_eq
quittingTerminalDebtSum_capNashRootStack_eq
```

They occur in:

* `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`;
* `Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
  and
* `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`.

The concentrated packet and consumer interfaces occur in:

* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTemporalSplit.lean`;
* `Research/Quitting/PositiveStageAtomConcentratedPacket.lean`; and
* `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`.

The new mathematical content is:

1. the tail-independent pure-coalition family specialization;
2. the proof that the canonical maximal selector generates one common orbit
   over all moving minimum tails;
3. exact common scaling of debt vector, marked mass, and paid gain;
4. the explicit diagonal source-return packet in the equality arm; and
5. the invariant-support/vanishing-future-capacity no-go in the strict arm.

## Lean handoff

Suggested declarations, in dependency order:

```text
quittingPureCoalitionProfile_semanticPair_eq_of_two_le_card
quittingPureCoalitionProfile_terminalLaw_eq_of_nonempty
quittingMaximalCapPrefixRoot_eq_of_semanticCap_eq
quittingMaximalCapPrefixProfile_semantic_eq_of_purePairTails
quittingMaximalCapPrefixProfile_debtVector_eq_survival_mul
quittingMaximalCapPrefixProfile_pairMass_eq_survival
quittingMaximalCapPrefixProfile_shiftedGain_eq_survival_mul
```

The source-facing theorem should construct the equality-arm packet as an
output rather than assume its fields:

```text
FinFourOwnerCompressedMinimumReturnForcedPairPacket
  .maximalPrefixLimit_eq_minimum_or_rayStall
```

Its first arm should return the actual moving
`QuittingReprojectionConcentratedPacket` or immediately the checked three-role
output.  Its second arm should return the exact quantitative fields
(12)--(13), (24)--(28).  The theorem and result type should contain
`maximalPrefix` or `canonical` in their names, preventing accidental reuse as
a universal no-go for arbitrary exact roots.

Formalization must prove selector extensionality from cap equality.  It must
not store equality of the selected roots, the diagonal packet, or the
three-role conclusion as new hypotheses.

## Scope and nonclaims

* The strict arm does not produce a uniform-equilibrium payoff, terminal
  approximation, cumulative near-return, total-debt descent, or support
  descent.
* Vanishing future charge concerns only the unchanged canonical maximal-root
  orbit.
* The marked endpoint gain is not fresh outer-root absorption and is not an
  exact prescribed-payoff Bellman edge.
* The complete terminal-law (C)-coordinate may exceed the retained shifted
  pair mass because outer roots may also absorb at (C).
* Maximality is not passed to the joint limit.
* Recomputing roots after a horizontal endpoint update starts a different
  problem.
* The boundary table has global minimum zero and is not a quitting-game
  counterexample.
* No claim is made beyond finite player sets in the generic ray theorem or
  beyond Fin4 in the source-facing corollary.

## Formalization record

This packet is formalized by a generic cap-indexed semantic-ray layer and an
actual Fin4 adapter from the previously checked cofinal forced-pair source.

1. `Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean` defines the
   cap-indexed canonical selector `quittingMaximalAbsorptionCapRoot` and proves
   its exact-Nash, maximal-absorption, and cap-extensionality declarations.
   The older profile-indexed `quittingMaximalCapPrefixRoot` remains a thin
   wrapper.  The supporting append, exact-prefix, restart, and payoff-scaling
   laws are checked in
   `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`,
   `UniformEquilibrium/Quitting/Root/LiteralExactPrefixStack.lean`, and
   `UniformEquilibrium/Quitting/Root/SemanticExactPrefixOrbit.lean`; the
   previous static-cycle consumer delegates to that shared infrastructure.
2. `UniformEquilibrium/Quitting/Paths/SureExitSet.lean` proves
   `quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`.
   Thus a pure coalition of cardinality at least two has the displayed static
   payoff and unrestricted behavioral cap, independently of its unreachable
   continuation.  It also proves that the complete all-Continue continuation
   after the pure root is the supplied behavioral tail.
3. `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean` defines the
   autonomous semantic orbit, explicit root stack, survival, and actual
   prefix profiles.  The named declarations expose the exact terminal-
   semantic orbit, playerwise and total-debt scaling, positive-debt support,
   normalized debt, shifted stage mass, copied-prefix payoff gain, and
   additive restart identities.  Different actual tails realizing the same
   semantic source use the same selected roots; no behavioral equality of
   those tails is asserted.
4. `Research/Quitting/MaximalCapSemanticPrefixReturn.lean` proves the exact
   scalar account.  In particular,
   `hasSum_quittingMaximalCapSemanticPrefixDebt_mul_absorption` and
   `QuittingMaximalCapSemanticPrefixRayStall.weightedAbsorption_hasSum` give
   the weighted telescope, while
   `QuittingMaximalCapSemanticPrefixRayStall.absorption_tsum_le_exact_debtDrop`,
   `QuittingMaximalCapSemanticPrefixRayStall.absorptionTailSum_tendsto_zero`,
   `QuittingMaximalCapSemanticPrefixRayStall.finiteAbsorptionTail_le_tailSup`,
   and
   `QuittingMaximalCapSemanticPrefixRayStall.absorptionTailSup_tendsto_zero`
   give the unweighted budget and vanishing future canonical charge.

   `quittingMaximalCapSemanticPrefixLawPoint_cluster_facts` is universal over
   every strictly increasing subsequence whose executable joint semantic/law
   points converge.  At that same supplied cluster it proves membership in
   the law carrier, debt exactly equal to the ray limit `L`, the sharp marked-
   atom lower bound `L / D_0` times the base atom, positivity of that atom,
   exact all-Continue Nash, and the unique-all-Continue-or-positive-absorption
   support-entry alternative.  The existential
   `nonempty_quittingMaximalCapSemanticPrefixRetainedLaw` selects a compact
   subsequence and delegates all fields to this universal theorem.
5. `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`
   applies the generic ray to one
   `FinFourOwnerCompressedMinimumReturnForcedPairPacket` without reselecting
   its source chronology, outsider, pair, owner, payer, or reference tails.
   `FinFourOwnerCompressedMinimumReturnForcedPairPacket.rayBaseOutcomeLaw_eq_pure`
   identifies the complete base outcome law with the point mass at the fixed
   pair; `rayBaseProfile_outcomeMass_eq_pointMass`,
   `rayBaseProfile_terminalMass_eq_one`, and
   `rayBaseProfile_neverMass_eq_zero` are delegating real-coordinate
   corollaries.  `rayMarkedMass_and_paidGainDensity_tendsto` gives the joint
   limit of the marked pair mass and actual payer-gain density, while
   `ray_positiveDebtSupport_eq` and `ray_normalizedDebt_eq` expose the exact
   finite-depth invariants.
6. `FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_maximalPrefixRayMinimumReturn_or_stall`
   is the source-facing capstone.  If `L = D_*`,
   `MaximalPrefixRayMinimumReturn` stores the actual diagonal reprojection
   packet's eventual transfer and fixed-role limit-chord consumer.  If
   `L > D_*`, `MaximalPrefixRayStall` stores the quantitative stall and the
   same sharp `QuittingMaximalCapSemanticPrefixRetainedLaw` object; its atom
   floor is literally `L / D_0` because the stored pure-pair base atom has
   mass one.  The module is reachable through
   `Research/Quitting/FinFourExhaustiveProducerAtlas.lean` and the `Research`
   reader umbrella.

Evidence seals:

- **M:** PASS.  The reviewed common-ray construction, pure-pair boundary,
  exact scalar telescope, universal cluster statement, equality packet, and
  strict-stall account are retained with the constants `D_* / D_0` and
  `L / D_0` unchanged.
- **L:** PASS.  The generic and Fin4 declarations are checked Lean.  Direct
  and named module builds, reader, Research, and full builds, axiom-audit
  freshness, trust, import-graph, documentation, duplicate-proof,
  derivable-telescope, unit, and source-format checks passed at promotion.
- **A:** PASS for the Fin4 capstone.  Starting from the actual cofinal
  forced-pair packet, the adapter constructs the pure-pair base family,
  common semantic ray, scalar limit, equality packet or strict stall, and
  retained joint-law object.  The generic theorems remain supplied-source
  interfaces.
- **C:** PASS only in the equality arm, through the existing eventual
  three-role transfer and fixed-role limit-chord consumer.  The strict stall
  has no checked completion consumer.

The strict account applies only to the unchanged canonical maximal-prefix
orbit.  Copying its finite word across the paid horizontal endpoint is an
exact payoff comparison, not a claim that the roots remain cap--Nash there;
recomputing after that update starts a different ray.  The full terminal-law
pair coordinate may exceed the shifted marked-row contribution because outer
roots may also absorb at that pair.  Maximality is not asserted at the joint
limit.  No near-minimality of finite ray profiles, support descent, cumulative
return, source regeneration, recursive closure, strict-stall completion,
terminal approximation, uniform-equilibrium payoff, or counterexample is
proved.

The mathematical provenance is the FORCED_PAIR_REVIEW packet and the
independent ATLAS_GATEKEEPER review linked at its head, followed by the
checked generic and Fin4 source-adapter implementations.  No external paper
theorem is imported.
