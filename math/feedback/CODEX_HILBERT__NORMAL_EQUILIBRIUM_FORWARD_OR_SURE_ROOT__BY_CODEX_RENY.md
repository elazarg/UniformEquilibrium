# Independent review: normal equilibrium sources, forward packets, and sure roots

Reviewer: CODEX_RENY, independent of both mathematical authors. I read all
three complete originals before any review of them. This is a mathematical
and bounded source-correspondence review, not a Lean build or export approval.

## 1. Reviewed originals and verdict

The exact reviewed surfaces are:

- [HILBERT partial converse](../notes/CODEX_HILBERT__NORMAL_EQUILIBRIUM_TO_FORWARD_PACKET_PARTIAL_CONVERSE.md),
  SHA-256 `b9c9096f87bdd676f2cc94190a16ef35e2dcdbec6b6534c0d4f7c8303f573bda`;
- [HILBERT combined equivalence](../notes/CODEX_HILBERT__NORMAL_EQUILIBRIUM_FORWARD_OR_SURE_ROOT.md),
  SHA-256 `2f4675b83684dbc1525b90c86c2de97c6bd0c60b78eb4d3da066ca45884d02ea`;
- [FRECHET S.2 source test](../notes/CODEX_FRECHET_CYCLE__AGKRS_S2_FORWARD_PACKET_SOURCE_TEST.md),
  SHA-256 `b947425076715ab4bf29832b9bd586b60ca2ab4bc0b6767b82d4425a45c100b0`.

**Mathematical verdict: PASS, with no required repair to these statements
or proofs.** The combined theorem is a correct restricted architecture
equivalence. It is not an arbitrary-table producer, does not establish
UE⇒EP alone, and does not assert joint realization of punishment values.
Export eligibility is assessed separately in Section 8.

## 2. Exact theorem reviewed

There are four players. Nonempty-coalition rewards have absolute value at
most M>0; Never pays zero. Behavioral strategies are independent stopping
laws on ℕ∪{Never}. Every unilateral complete law, with arbitrary late dates
and Never, is an admissible deviation. Let U_i be terminal payoff,

    Cap_i(p)=sup_[own replacements] U_i,
    P_i=inf_[independent opponent laws] Cap_i,
    s_i=r_i({i}).

For a product root q, let α_i be the probability all opponents Continue,
Q_i its immediate-Quit payoff, L_i its Continue absorption contribution,
C_i(q,v)=L_i+α_i v_i, and F_i=q_iQ_i+(1−q_i)C_i. Write
a(q)=1−∏_i(1−q_i).

EP means existence of ONE fixed finite B≥M such that, at every δ>0 and
requested charge Q≥0, there is a finite word in [−B,B]^4 with

    v_(t+1)=F(q_t,v_t),
    support-δ Nash at q_t against v_t,
    v_t(i)≥P_i−δ at every endpoint,
    Σ_t a(q_t)≥Q.

The construction index runs outward through prefixes; play order is the
reverse. Annotations need not be actual joint continuation payoffs. WP is
the existing weighted-error equivalent, with Bellman error and ordinary
root regret at most δ a(q_t), and the same endpoint floor requirement.

The finite sure-root certificate C is

    ∃k,q, q_k=1 and max(Q_i(q),C_i(q,P))=F_i(q,P) for all i.

Its root and label are fixed before accuracy; P is the semantic punishment
vector, not finite computable input automatically obtained from reward data.

Under P_i≤s_i for every i and s_j>0 for some j, the reviewed result is

    existence of a uniform-equilibrium payoff  ⇔  EP or C.

The alternatives are inclusive. Both sufficiency directions hold without
normality or a positive singleton. The necessity proof in fact supplies EP
or WP in the explicit box [−M−2,M+2]^4: this follows directly from the
displayed stationary box and the S.3 box, together with the existing
same-box weighted repair and exact-to-weighted translation.

## 3. Stationary source: full caps and absorption-relative errors

The stationary calculation uses the actual payoff U of an absorbing
stationary terminal e-Nash profile, not an arbitrary root annotation.
Bellman gives F(q,U)=U. Full Nash gives Q_i−U_i≤e and U_i≥P_i−e.
When α_i<1, Never against stationary opponents yields L_i/(1−α_i), so

    C_i(q,U)−U_i≤e(1−α_i).

When α_i=1, L_i=0 and C_i(q,U)=U_i exactly. This separate case is
essential; neither division by zero nor a fictitious stationary absorption
of opponents is used.

For y=U+2e·1, the Bellman residual is exactly 2e a(q). Continue's
gain over F(q,y) is at most

    e(1−α_i)+2e(α_i−c)≤3e a(q),

because 1−α_i≤a and α_i−c=q_iα_i≤a. Quit's gain is at most e−2ec.
If this is positive then c<1/2, whence the gain is at most 2e a. Thus
ordinary root regret is at most 3e a. Also y≥P+e and |y_i|≤M+2 for
0<e≤1. Repetition gives arbitrary charge with length depending on e and
the requested charge. No absorption lower bound uniform in e is needed.

Falsification checks: an all-Never stationary law has a=0 and cannot be
used for this construction. A positive singleton excludes it once e<s_j.
For a sole active stationary quitter, α_i=1 is legitimate and the formula
still works. Replacing full terminal Nash with finite-menu or merely local
root Nash would lose the Never comparison and is not covered.

## 4. Approximate bounded-spine floor and S.3 orientation

The approximate floor lemma is correct. For chronological Bellman values
v_t=F(q_t,v_(t+1)) in [−M,M]^4, ordinary root error η, and a deficit
d_t=P_i−v_t(i)>τ with η≤min(τ/2,τ²/(8M)), normality gives

    1−α_t≥(d_t−η)/(2M)>τ/(4M).

Since Q_i<P_i while the full stationary cap is at least P_i, its
Continue-forever leg gives L_i≥(1−α_t)P_i. Continue's row inequality
then gives α_t d_(t+1)≥d_t−η>0. In particular 0<α_t<1, so division
is legal. The deficit grows by more than τ²/(8M) at every later date,
contradicting d_t≤2M. All dates and all players are covered; no summability,
actual payoff realization, or termination premise is hidden in this lemma.

For S.3, the exact production definition requires row perfection at EVERY
date against the sequence's literal restarted terminal payoff, including
dates unreachable from the initial root. The checked positive-restart
null-tail theorem forces s_i≤η for every i if any restart has positive
survival. Consequently a fixed positive s_j and η<s_j give termination
after every restart, not just initial absorption.

Every-restart termination implies divergent additive charge: if Σa_t were
finite, then eventually a_t≤1/2 and −log(1−a_t)≤2a_t would give a
positive-survival late tail. Finitely many sure rows do not evade this
argument. Row perfection gives support error 2η. The floor lemma covers
all endpoints. Reversing a segment of length H as

    v_j=u_(H−j), x_j=q_(H−1−j), v_H=u_0

gives exactly v_(j+1)=F(x_j,v_j), the required forward convention.

The all-zero example with one sure row followed by all Continue correctly
falsifies the inference from initial absorption alone to divergent charge.
It is not a game-level separation from EP, as the authors expressly state.

## 5. S.2: semantic punishment without joint realization

For S.2⇒C, take errors decreasing to zero and extract a fixed sure player
k and convergent product roots q_n→q. The prescribed root absorbs surely,
so U_n=F(q_n,P), independently of the punishment law. For i≠k, every
deviation still meets sure quitter k at the root, hence only the two root
endpoints matter. For k, the exact full Continue cap is

    L_k(q_n)+α_k(q_n)Cap_k(τ_n)≥L_k(q_n)+α_k(q_n)P_k.

Thus q_n is ordinary approximate Nash against P, and continuity gives C.
The inequalities P_i≤Cap_i(q_n::τ_n)≤U_n(i)+e_n also give F(q,P)≥P.
Neither a compact space of punishment laws nor punishment attainment is
needed. The upper punishment clause is indeed unused in this direction.

For C⇒S.2, select one actual independent opponent punishment of k within
e of P_k, and give k any prescribed tail law. This follows from the
infimum defining P_k. The whole profile and its off-path punishment are
selected BEFORE play. There is no deviation detection, public correlation,
or retrospective switching of opponents. The other players' deviations
cannot expose that tail. Player k's full cap is

    max(Q_k,L_k+α_k Cap_k(τ_e))≤F_k(q,P)+e.

The resulting prescribed payoff F(q,P) is fixed across e. This proves all
required behavioral inequalities and the additional floor by taking e→0.
The existing sure-root punishment compiler already supplies this reverse
direction; the new source characterization is the compactness extraction.

I independently checked the complete canonical shortcut table and its
infinite-response bounds. For q=(1,1/4,0,0) then Never, pivot response
values are 3/2 at date zero, 5/4 at every later date, and 1/2 at Never.
The exact S.2 profile has payoff (3/2,0,0,0), with P=(1,0,0,0).
Repeating that same root instead gives root regret 1/8 and full debt 1/2:
finite-date payoff is 2−(1/2)(3/4)^t and Never pays 2. The repeated
root is not a valid source. The alternative pure root (1,1,0,0) gives
exact arbitrary-charge packets, so no S.2-versus-EP separation is proved.

## 6. Exact bounded source correspondence

I used `docs/TOOLKIT.md` and `docs/FRONTIER.md` to identify the following
declarations, then read the relevant definitions and proofs under imports:

- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`,
  `Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `QuittingPayoffTable.stationary_or_instantPunishment_or_sequentiallyPerfectAbsorbing`,
  `Quitting/Classification/Existence/ApproximateEquilibriumForwardTrichotomy.lean`,
  and the literal branch definitions in `ExistenceBranches.lean` and
  `TableExistenceBranches.lean`;
- `supportApproxNash_of_quittingRowεPerfect`,
  `Classification/Existence/WellSupportedAbsorbingSequence.lean`, and
  `quittingSingletonReward_le_error_of_positiveRestartSurvival`,
  `Classification/Existence/SequentiallyPerfectAbsorbingNullTailAlternative.lean`;
- `quittingBestReplyValue_stationary`,
  `quittingStationaryUnilateralCap_eq_max_div`, and
  `quittingPunishmentValue_le_stationaryUnilateralCap`,
  `Quitting/Stationary/MinMax.lean`;
- `quittingContinuationBestResponseValue_rootThenContinuation_eq_max`,
  `Quitting/Root/TerminalDebtPrefix.lean`, and the sure-row screen in
  `Classification/InstantPunishmentEquivalence.lean`;
- `exists_oneStagePunishedProfile_of_rational_support_sureQuitter`,
  `Classification/SimonFiniteOrbit/CompactQuantitativeAlternatives.lean`,
  with `QuittingSimonRationalPayoffAt` in `SuppliedCorrespondence.lean`;
- `QuittingFiniteForwardPacket` and its UE consumer in
  `Quitting/Projective/FiniteForwardProjectiveLasso.lean`, the weighted
  packet definition, and
  `exists_exactFiniteForwardPacketBox_iff_exists_absorptionWeightedBox`
  in `AbsorptionWeightedForwardPacketTranslation.lean`.

Paths are relative to `UniformEquilibrium/`, with `Classification/` relative
to its `Quitting/` subtree. The current exact declarations, not an unbuilt
literature transcription or assumed paper reverse implication, are the
dependencies of the reviewed composition. I did not rebuild Lean here.

For novelty, the existing normal S.3 consumer already proves UE from S.3,
and the sure-root punishment compiler already proves C⇒UE. The new
mathematics is the stationary-to-weighted-packet adapter, the approximate
all-date bounded-spine floor and S.3-to-EP adapter, and the finite C
characterization. The combined equivalence is their valid composition,
not a new proof of the already checked forward trichotomy.

## 7. Additional finite-word consequence, separately preserved

At ROOT's suggestion I checked the finite form of the deficit proof. It
gives a useful stronger source reduction, preserved with a complete proof
in [finite forward punishment-floor burn-in](../notes/CODEX_RENY__FINITE_FORWARD_PUNISHMENT_FLOOR_BURN_IN.md).
This addition was NOT part of the three frozen originals reviewed above and
has not yet received an independent review.

With annotations in [−B,B], both pure endpoints at most the next outward
annotation plus ζ, and ζ≤min(τ/2,τ²/(8M)), all endpoints after L
outward rows have floor P−τ whenever Lτ²/(8M)>M+B. A violation
propagates toward index zero; that orientation is indispensable. Discarding
those L rows loses charge at most L and preserves every remaining edge.

Bellman error b plus ordinary root regret n supplies endpoint error b+n.
In particular floor-free weighted edges of tolerance e supply ζ≤2e.
Hence under normality, both exact-support and weighted all-accuracy,
arbitrary-charge producers can omit every punishment floor, with the same
fixed box. The construction requests Q+L before trimming; it does not
silently reselect a word or discard a charge-dependent proportion.

The nearest finite source theorem,
`quittingPunishmentValue_le_finitePrefixValue` in
`Quitting/Bellman/Finite/PunishmentFloorFinitePrefix.lean`, assumes
`anchor_floor`. The older arbitrary-spine theorem in
`SummableExactNashBellmanPunishmentFloor.lean` assumes exact Nash and
summable absorption. The exact amplification in
`Debt/Dynamic/PunishmentFloorViolation.lean` and the local normal-row
absorption estimate do not already state this free-start approximate
finite-word reduction. This bounded source search found no duplicate.

## 8. Export eligibility is distinct from correctness

The original equivalence closes an honest restricted architecture question:
under normality and a positive singleton, the UNION of EP and the finite
instant branch covers every UE existence case. This is not tautological
from the existing EP consumer and is mathematically useful.

Nevertheless, by itself I would not use it to claim a strict reduction of
the CURRENT [forward-packet producer question](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md).
That question assumes positive global SUM-debt infimum D_* and normality.
Its premises already exclude C by the existing terminal consumer, and
already force some positive singleton because otherwise all Never is exact
Nash. The new necessity direction starts from UE, which is precisely not
available in the contrary case. Thus it neither supplies the requested
packets nor removes a hypothesis from their construction. An independent
export justified only as answering that producer would overstate the result.

The finite burn-in reduction in Section 7 DOES make a strict named change:
the requested producer may omit its semantic punishment-floor field while
keeping its exact/weighted local conditions, fixed box, and charge target.
It fits the export gate's input-reducing equivalence category once its own
proof receives the required review and a final packet has complete scope
and handoff. It does not establish all-accuracy or unbounded-charge
EXISTENCE. No export placement is approved or made by this review.

The strongest appropriate handoff therefore distinguishes (a) the sound
coverage equivalence, (b) the new finite input-removal corollary requiring
its own review, and (c) the still-open actual word producer. A future use as
part of a complete negative-certificate language must independently prove
that language's completeness; no such conclusion is borrowed here.
