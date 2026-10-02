# A partial converse from normal equilibrium sources to forward packets

Identity: CODEX_HILBERT. Ordinary mathematics, not independently reviewed or
Lean-checked. No export claim.

**Status.** Two necessity adapters are proved below: absorbing stationary
terminal approximate equilibria give weighted packets, and normal
row-perfect sources that terminate after every restart give exact forward
packets. With a positive singleton, the checked AKRS forward trichotomy
therefore leaves only its instant-punishment S.2 arm unmatched by THESE
arguments. This note does not claim UE⇒EP in general and gives no normal
table separating them. The all-Never stationary case remains visible when
every own singleton is nonpositive.

## 1. Definitions and the direction being tested

There are four players, nonempty-coalition rewards r_i(S) bounded in absolute
value by M>0, and zero Never payoff. Behavioral randomizations are independent
across players. Every complete unilateral strategy is an admissible response.
Write s_i=r_i({i}) and

    P_i=inf_[opponent laws] sup_[own laws] terminal payoff.

Punishment normality means P_i≤s_i, not the reversed inequality. Always
P_i∈[−M,M]. For a product root q write c=∏_i(1−q_i), a=1−c,
α_i=∏_(j≠i)(1−q_j), and let Q_i and C_i(q,v) be the Quit and Continue
endpoints. With L_i the expected reward from nonempty opponent absorption,

    C_i(q,v)=L_i+α_i v_i,
    F_i(q,v)=q_iQ_i+(1−q_i)C_i(q,v),
    Reg_i(q,v)=max(Q_i,C_i(q,v))−F_i(q,v).

EP means that ONE fixed box [−B,B]⁴ works for every support error δ>0
and every charge Q≥0: there are finite values v_0,…,v_H and roots x_t with

    v_(t+1)=F(x_t,v_t),
    every used action at x_t within δ of the best endpoint against v_t,
    v_t(i)≥P_i−δ at EVERY endpoint,
    Σ_[t<H] a(x_t)≥Q.

WP replaces the exact Bellman and support conditions by Bellman error and
ordinary root regret at most εa(x_t), again at every row. The frozen
`exports/ABSORPTION_WEIGHTED_FORWARD_PACKET_REDUCTION.md` proves EP⇔WP
and EP⇒existence of a uniform-equilibrium payoff. It makes no converse claim.

The checked target-free equivalence says that a uniform-equilibrium payoff
exists exactly when there are actual terminal approximate Nash profiles at
every positive error. Applying the checked AKRS FORWARD theorem to that
premise gives one fixed disjunction:

- S.1: stationary terminal approximate equilibria at every error;
- S.2: first-stage sure-quitter equilibria with a punishment continuation;
- S.3: initially absorbing root sequences, row-perfect at every date against
  their own literal restarted-tail terminal payoffs.

It would be invalid to replace this disjunction by S.3 alone, or to use the
existence of a uniform payoff as though it already supplied a charged packet.

## 2. Absorbing stationary approximate equilibria imply WP

Let the stationary product root q have a>0 and let its actual stationary
profile be terminal e-Nash against ALL complete responses, where 0<e≤1.
Let U be its terminal payoff. Stationarity and absorption give F(q,U)=U.
Full Nash and the punishment definition imply

    Q_i−U_i≤e,             U_i≥P_i−e.                (1)

There is a second comparison which uses the full stationary Never response:

    C_i(q,U)−U_i≤e(1−α_i).                          (2)

If α_i<1, Never gives L_i/(1−α_i), which is at most U_i+e. Multiply
that inequality by 1−α_i to obtain (2). If α_i=1, then L_i=0 and
C_i(q,U)=U_i, so (2) remains exact. No division by zero is used.

Set y=U+2e·1 and keep this SAME annotation at every row. Its exact residual is

    y−F(q,y)=2ea·1.                                 (3)

The Continue action's advantage over F(q,y) is

    C_i(q,y)−F_i(q,y)
      =C_i(q,U)−U_i+2e(α_i−c)
      ≤e(1−α_i)+2e q_iα_i≤3ea.                     (4)

The Quit action's advantage is at most e−2ec by (1). If this is positive,
c<1/2, so a>1/2 and that advantage is at most e≤2ea; otherwise its
positive part is zero. Together with (4),

    Reg_i(q,y)≤3ea.                                 (5)

Also y_i≥P_i+e, and y lies in the ONE box [−M−2,M+2]⁴. Repeating this
root and annotation H times, with H a≥Q, gives a WP packet of tolerance
3e and charge Q. No lower bound on a uniform in e is needed: H may depend
on both e and Q. No compatibility across accuracies is imposed.

Consequently absorbing stationary terminal approximate equilibria at every
error imply WP and EP. This adapter does not require normality.

If s_j>0 for some j, S.1 automatically supplies absorbing roots for every
e<s_j: the zero-absorption stationary profile is all Never and has player-j
debt at least s_j. Thus the positive-singleton S.1 branch implies EP.
Without a positive singleton, S.1 may consist only of all-Never witnesses;
the repetition argument then has zero charge and proves nothing about EP.

This uses a new specialization of the translation calculation, not a claim
of new stationary equilibrium existence. A narrow search of the finite-forward
and projective source subtree and the nearest stationary/forward notes found
no literal stationary-full-regret-to-weighted-packet declaration. Existing
exact stationary/cyclic compilers and the generic upward translation remain
the nearest ingredients.

## 3. Normality supplies ALL-date floors for approximate Bellman spines

**Lemma.** Let v_t∈[−M,M]⁴ for every t≥0 and q_t be product roots.
Assume exact chronological Bellman equations

    v_t=F(q_t,v_(t+1))

and ordinary root regret at most η at every row. If all players are normal,
then for every τ>0 satisfying

    0≤η≤min(τ/2,τ²/(8M)),                           (6)

one has v_t(i)≥P_i−τ for EVERY t and i.

The values may be abstract bounded annotations; they need not be actual
terminal tails. Exact Bellman converts the ordinary-regret hypothesis into
the two pure-action inequalities Q_i,C_i≤v_t(i)+η used below.

Proof. Suppose at some date a fixed coordinate has deficit
d_t=P_i−v_t(i)>τ. Normality and the bound on the Quit endpoint give

    P_i−2M(1−α_t)≤s_i−2M(1−α_t)≤Q_i≤P_i−d_t+η,

so 1−α_t≥(d_t−η)/(2M)>τ/(4M). In particular α_t<1.
The stationary cap against the opponents' current row is
max(Q_i,L_i/(1−α_t)) and is at least P_i. Since
Q_i≤P_i−d_t+η<P_i, its Continue-forever leg must give

    L_i≥(1−α_t)P_i.

Now C_i=L_i+α_t v_(t+1)(i)≤v_t(i)+η implies

    α_t d_(t+1)≥d_t−η>0.                           (7)

Thus α_t>0. Subtracting d_t and using (6),

    d_(t+1)−d_t
      ≥[(1−α_t)d_t−η]/α_t
      >τ²/(4M)−η≥τ²/(8M)>0.                       (8)

The same violating coordinate therefore persists and increases by a fixed
positive amount at every later date. This contradicts d_t≤P_i+M≤2M.
The claimed all-date floor follows. This argument does not assume summable
charge, complete absorption, a fixed target payoff, or a positive global gap.

The exact η=0 amplification step already occurs in
`quittingPunishmentValue_sub_le_continueMass_mul_of_nashBellmanEdge` in
`UniformEquilibrium/Quitting/Debt/Dynamic/PunishmentFloorViolation.lean`.
The current rowwise opponent-absorption estimate is also present in
`opponentAbsorptionMass_gt_of_normal_of_rowPerfect_of_not_individualRational`
in `NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`.
The lemma is the explicit approximate, bounded-spine combination of these
arguments; the summability hypothesis of the older
`punishmentValue_le_of_all_normal_and_summable` is not used here.

## 4. The every-restart S.3 arm implies EP

Suppose at every sufficiently small η>0 there is a root sequence whose
rows are η-perfect against their literal restarted-tail terminal payoffs
u_t, and which terminates after EVERY finite restart. These literal values
are bounded by M and satisfy exact Bellman equations. Row perfection gives
ordinary root regret at most η and support error at most 2η.

Fix the desired EP error δ>0 and charge Q. Choose τ≤δ positive and then
choose η>0 small enough for (6) and 2η≤δ. Section 3 gives

    u_t(i)≥P_i−τ≥P_i−δ             for every t,i.

Every-restart termination implies Σ_t a(q_t)=∞. Indeed, if that sum were
finite, its tail terms would be at most 1/2; the bound
−log(1−a_t)≤2a_t would give positive survival from a sufficiently late
restart, a contradiction. This includes sequences with sure absorption rows:
finitely many such rows cannot hide the later nonterminating tail.

Select H with Σ_[t<H]a(q_t)≥Q. Reverse this finite chronological segment:

    v_j=u_(H−j),       x_j=q_(H−1−j)       (0≤j<H),
    v_H=u_0.

It is precisely an EP packet, in the fixed box [−M,M]⁴, with the required
support error and EVERY-endpoint floor. No actual-tail identification is
lost: the u_t used before reversing are the source's literal tail payoffs.

If s_i>0 for some player, ordinary S.3 supplies every-restart termination
once η<s_i. The checked null-tail theorem proves that a positive-survival
restarted tail would instead force every s_j≤η. Therefore under normality
and a positive singleton, S.3 implies EP.

Initial absorption alone is not enough for this argument. On the all-zero
table, the sequence consisting of one sure row followed by all Continue is
exactly row-perfect and initially absorbing, but its total charge is only
one. This is NOT a separation from EP: that same normal table has arbitrary
EP charge by repeating a sure row. It only shows why the supplied S.3
sequence cannot be silently assumed to have unbounded additive charge.

## 5. Exact remaining scope

Combining the checked forward trichotomy with Sections 2 and 4 proves the
following partial necessity statement:

    normality + some s_i>0 + existence of a UE payoff
      ⇒ EP OR the literal instant-punishment branch S.2.

This is an inclusive disjunction. It does not say EP fails on S.2 tables.
The S.2 branch permits a punishment continuation selected to control one
sure quitter's full cap; it does not impose Nash behavior or simultaneous
punishment floors on that continuation. Its source has not been turned into
an arbitrary-charge packet here. Independent S.2 analysis is separate.

Without a positive singleton, the all-Never stationary arm and S.3's
null-tail possibility are additionally unmatched by these adapters. Missing
adapters, missing declarations, and a defective supplied witness are NOT
counterexamples to UE⇒EP. No solved normal table failing EP has been found
in this bounded test.

The exact checked source statements read for this distinction were:

- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `QuittingPayoffTable.stationary_or_instantPunishment_or_sequentiallyPerfectAbsorbing`
  in `UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumForwardTrichotomy.lean`;
- the literal S.1/S.2/S.3 definitions in `Classification/ExistenceBranches.lean`
  and `Classification/TableExistenceBranches.lean`;
- `supportApproxNash_of_quittingRowεPerfect` in
  `Classification/Existence/WellSupportedAbsorbingSequence.lean`;
- `quittingSingletonReward_le_error_of_positiveRestartSurvival` and
  `QuittingPayoffTable.allContinueExactNash_or_everyRestartWitnesses` in
  `Classification/Existence/SequentiallyPerfectAbsorbingNullTailAlternative.lean`;
- `quittingBestReplyValue_stationary`,
  `quittingStationaryUnilateralCap_eq_max_div`, and
  `quittingPunishmentValue_le_stationaryUnilateralCap` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`;
- `QuittingFiniteForwardPacket` and its sufficient UE consumer in
  `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`.

The concrete remaining question is whether normal S.2 itself supplies EP,
or whether some such table separates them. This note does not substitute the
already checked normal S.3→UE compiler for that missing necessity direction.
