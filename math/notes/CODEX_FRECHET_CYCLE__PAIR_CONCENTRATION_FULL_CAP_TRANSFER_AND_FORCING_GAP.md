# Near-certain pair outcomes: full-cap transfer and the remaining forcing gap

Identity: CODEX_FRECHET_CYCLE.

## Status and question

Ordinary mathematics, independently derived but not independently reviewed or
Lean-checked. This is a bounded response to Sections 3–4 of
[LARCH's missing-theory survey](CODEX_LARCH__MISSING_THEORY_SURVEY.md);
[the associated feedback](../feedback/CODEX_LARCH__MISSING_THEORY_SURVEY__BY_CODEX_FRECHET_CYCLE.md)
records the scope of the audit. No export is requested.

**Question.** Does robust concentration on a pair supply an incentive
estimate usable by the existing pair-mass consumers or the coupled
worst-table source?

**Answer.** It supplies a complete-cap estimate, stronger than preservation
of prescribed outcomes. It yields an upper pair-mass bound whenever the
source regret is strictly below that pair's raw sure-exit regret. It does
not provide the complementary upper bound on non-pair mass. At a positive
global minimum, positivity of all six sure-pair regrets does not establish
the required strict margin above the source regret. Thus this does not
close the forcing premise of either existing consumer.

## 1. Actual clocks and the aligned event

Let I={0,1,2,3}, with independent complete stopping clocks T_i taking values
in the nonnegative integers and Never. Before absorption all rewards are
zero, Never pays zero, and every nonempty terminal reward satisfies
|r_i(S)|≤M, where M>0. All caps below allow every complete unilateral
behavioral deviation, equivalently every independent replacement clock.

Fix a pair e={a,b}. Write

    q_e = Pr(the first finite quitting coalition is exactly e).

Suppose q_e>1/2. There is a finite date t such that

    w = Pr(T_a=T_b=t and T_k>t for both k outside e)
      ≥ 2q_e−1.                                                (1)

Here and below Never is later than every finite date.

**Proof.** Put A_s=Pr(T_a=s), B_s=Pr(T_b=s), and
C_s=Pr(T_k>s for both outsiders). Independence gives
q_e=Σ_s A_s B_s C_s. Since Σ_s B_s C_s≤1, the maximum finite atom of T_a
is at least q_e. A nonzero summable nonnegative sequence attains its
maximum: only finitely many terms can exceed half its positive supremum.
Choose t attaining that maximum. Then

    Σ_(s≠t) A_s B_s C_s ≤ Σ_(s≠t) A_s ≤ 1−A_t ≤ 1−q_e.

Subtracting from q_e proves (1). No finite-support hypothesis is used.

Define marginal events G_a={T_a=t}, G_b={T_b=t}, and G_k={T_k>t} for
the outsiders. All have positive probability by (1). Replace each marginal
by its conditional law given G_i. Call the resulting product profile ν.
It is an ACTUAL independent profile. The resulting joint law is also the
original product law conditioned on G=∩_i G_i, because G is a product event.
The conditional mixture decomposition used in the proof is not a correlated
strategy supplied to the players.

## 2. Every cap is close; the initial branch is retained

For any observer i, the prescribed payoff changes by at most 2M(1−w).
For any fixed complete replacement law of i, the opponents' law under ν is
the original opponents' law conditioned on ∩_(k≠i)G_k. That event has
probability at least w. Therefore the replacement payoff also changes by
at most 2M(1−w), uniformly over the replacement law. Taking suprema gives

    |U_i(μ)−U_i(ν)| ≤ 2M(1−w) ≤ 4M(1−q_e),
    |B_i(μ)−B_i(ν)| ≤ 2M(1−w) ≤ 4M(1−q_e).                    (2)

This includes arbitrary hidden tails, Never responses, and dates after the
original finite support if there is one. It is not an inference from
terminal-outcome total variation alone: the product-event construction
controls the unchanged opponents in every unilateral experiment.

The profile ν has a pure pair at t and nobody quits earlier. After deleting
any one player, a member of e still quits surely at t. Thus its full semantic
pair is independent of the conditioned outsiders' later behavior:

    U_i(ν)=r_i(e),
    B_i(ν)=max(r_i(e), r_i(e△{i}), s_i if t>0),               (3)

where s_i=r_i({i}); the last argument is OMITTED when t=0. For t>0, a
finite response before t earns s_i, a response at t gives the join endpoint,
and every response after t, including Never, gives the leave endpoint.
One endpoint is the prescribed r_i(e). These cover the entire response menu.

Let P_e be the date-zero pure-pair profile with both outsiders Never. Its
full regret is the raw-table number

    Γ_e = max_i (r_i(e△{i})−r_i(e))_+.

Formula (3) implies E(P_e)=Γ_e≤E(ν), not equality in general. Hence (2)
gives the useful all-behavior inequality

    Γ_e ≤ E(μ)+8M(1−q_e)       whenever q_e>1/2.              (4)

The earlier singleton branch is essential to this argument. For example,
set r_0({0})=1 and all other rewards zero, and take e={0,1}. The pair at
date zero and at date one have exactly the same terminal law and payoff.
Player 0's caps are respectively 0 and 1. Thus bare outcome equality does
not identify caps. The domination E(P_e)≤E(ν) in (4) remains valid.

## 3. What this supplies to robust pair concentration

Put Γ=min_e Γ_e, and let spread=1−max_e q_e. Since Γ_e≤2M, (4) and the
trivial case max_e q_e≤1/2 give, for every actual profile,

    spread ≥ (Γ−E(μ))_+/(8M).                                (5)

In particular E(μ)≤Γ−d, with a supplied d>0, implies spread≥d/(8M).
The condition Γ>0 alone is not enough at an arbitrary positive-regret source.

If one ALSO supplies the survey's geometric bound spread^N≤C·leakage,
then (5) yields

    leakage ≥ ( (Γ−E(μ))_+/(8M) )^N / C.                     (6)

This is a lower leakage bound. A negative UE consumer still needs an
independent upper leakage bound, such as leakage≤A E(μ), in a regime
E(μ)≤ε_0<Γ. The resulting elementary conditional gap is

    E(μ) ≥ min(ε_0, ((Γ−ε_0)/(8M))^N/(CA)),

provided ε_0>0 and the upper leakage bound holds for every profile with
E≤ε_0. This is only the stated composition, not a producer of its premise.
No exponent or constant is computed or optimized here; the survey's power
law is not an independently audited dependency of (1)–(5).

## 4. An exact test of the missing leakage premise

The missing upper bound does not follow even from nonnegative own singletons
and failure of every sure-pair Nash test. Consider the normalized table

    r_i(S)= 1  if S={i},
            −1  if i∈S and |S|≥2,
             0  if i∉S.

Every Γ_e=1: either pair member gains 1 by leaving. Nevertheless there is
an exact all-behavior stationary Nash profile. Put a=2^(−1/3) and let every
player quit at each live date with hazard q=1−a. Opponents all Continue
with probability a³=1/2. The pure Quit value is

    Q_i=a³−(1−a³)=0,

and every passive absorption pays zero. Every finite pure response and Never
therefore pays zero; prescribed play does also. The complete cap is zero,
so E=0. Absorption is proper since a⁴<1. Its singleton terminal mass is

    4q a³/(1−a⁴)>0.

Consequently leakage>0, contradicting leakage≤A E for every finite A.
This table is in the already solved participant-only class. It is NOT a
positive-global-minimum counterexample and supplies no new existence class.
It isolates exactly the missing inference in the proposed raw-table route.

## 5. Comparison with the coupled global source

The independently reviewed
[silent worst-table bridge](CODEX_FRECHET_CYCLE__SILENT_SOURCE_COUPLING_TO_WORST_REWARD_PRESSURE.md)
is left unchanged. Its actual sources satisfy E(μ_m)→Ω>0 at the selected
worst table, with the common all-owner multiplier and a nonpositive limiting
weighted own-singleton pressure. For that source, (5) gives a positive spread
floor only if one proves Γ>Ω, or a corresponding uniform finite-source gap.
No such strict comparison has been supplied. Global minimality gives merely
Γ_e=E(P_e)≥Ω for each actual competitor P_e; equality is not excluded here.

Moreover weighted singleton pressure is not non-pair mass. At a literal
pure pair, all original singleton masses vanish. Joining or withdrawing
can have positive reward gain while creating no singleton of the deviator.
The survey's leakage additionally counts triples, the full coalition and
Never. Neither the scalar pressure sign nor its mean inactivity bound
identifies those coordinates. Thus neither Γ>Ω nor leakage→0 follows from
the source fields inspected. This is an unresolved implication, not a
counterexample to the full positive-worst-table source assumptions.

If leakage→0 is supplied, the existing zero-singleton joint semantic/law
realization already applies after taking a joint carrier limit. It preserves
complete caps under the appropriate singleton margins and gives a two-sure
product root. On the pair-only face that root is a pure pair. The present
quantitative estimate does not create a new qualitative entry into that
face or a descent from it. Replacing hidden tails by Never preserves the
single-player caps behind a pair, but is not asserted to preserve all
two-replacement rows of the common-multiplier certificate.

## 6. Exact source correspondence and tests

Inspection at repository HEAD `9a4b64e7328adffc52af3e3ee6402fe85758aac6`:

- `Quitting/Paths/PairOnlyTerminalLawRigidity.lean`:
  `exists_pair_terminalOutcomeMass_eq_one_of_terminalPairMass_eq_one`;
  `uniformSixPairTerminalLaw_noncharacterization`. Read the full file.
- `Quitting/Terminal/PairMassForcingConsumer.lean`:
  `quittingTerminalExploitability_ge_affinePairRootLeastCrossing` and
  `exists_pureTime_gain_half_affinePairRootLeastCrossing`. Their supplied
  forcing bounds quantify over EVERY actual behavioral profile.
- `Quitting/Terminal/FinFourAllPairCrossingConsumer.lean`:
  `QuittingFinFourAllPairMassForcing`,
  `quittingTerminalExploitability_ge_finFourMaxPairCrossing`, and
  `finFourMaxPairCrossing_le_iff_all_pair_envelopes_le_one`. The maximum
  over fifteen two-pair crossings is not a joint six-pair realization theorem.
  Both consumer files were read in full; neither supplies raw forcing.
- `Quitting/Paths/SureExitSet.lean`:
  `quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`
  and `isQuittingSureExitSet_pair_iff` give the exact known screen/test used
  in (3). The stationary characterization covers all behavioral deviations.
- `Quitting/Paths/StoppingLawOperationalDistance.lean`:
  `abs_quittingStoppingLawReplacementPayoffCap_sub_le_opponents` and
  `quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`
  supply the existing general stability/interface behind the direct (2).
- `Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`:
  `exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`
  and `exists_twoSurePaddedProductRoot_realizing_jointCarrierPoint_of_margin`.
  These are supplied joint-carrier realization statements, not a producer
  of vanishing leakage. The linked formalization packet already supersedes
  its former sure-core descent proposal.
- `MathUE/PMFProduct/SingletonRatioPairConcentration.lean`:
  `exists_pair_subsequence_mul_tendsto_one_of_singletonMass_ratio_tendsto_zero`
  is an existing qualitative product-row concentration input, not the
  all-clock incentive premise required here.
- `Quitting/Classification/Existence/ParticipantOnlyStationary.lean`:
  `IsQuittingParticipantOnly` and
  `exists_stationary_uniformEquilibriumPayoff_of_participantOnly` already
  cover the exact table in Section 4.

Paths beginning `Quitting/` or `Diagnostics/` above are below
`UniformEquilibrium/`. Relevant maintained TOOLKIT entries and the prior
[two-pair recruitment rejection](CODEX_FRECHET_CYCLE__TWO_PAIR_RECRUITMENT_FORCING_TEST.md)
were also checked. No Lean build or new declaration is claimed.

A read-only exact rational test checked twelve signed tables and actual
profiles with small outlier masses: all 48 payoff/cap/template coordinate
checks passed, including the initial versus padded distinction, the newly
available after-support finite response, and Never. Equations (1)–(5) are
proved above independently of those tests.

## 7. Equality Γ=Ω: an actual pair-minimum test

This follow-up uses a fixed canonical table with nonnegative own singletons.
Assume a literal date-zero pair e={a,b}, outsiders c,d Never, attains the
positive GLOBAL infimum m=inf_p E(p). Thus Γ_e=m. No fixed-calendar minimum
is substituted for this hypothesis.

The checked `minimumTerminalSemantic_exploitabilitySingletonMargin` in
`Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean` gives
B_i−s_i≥m. HILBERT's
[all-player ties](CODEX_HILBERT__GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES.md)
is an ordinary-mathematics draft, not a checked Lean theorem; its proof was
independently reconstructed in this research line and reread for this test.
Together these
facts give, writing u_i=r_i(e),

    B_i=u_i+m,     u_i≥s_i≥0,
    r_i(e△{i})=u_i+m                    for EVERY i.            (7)

The existing
[harmonic contact calculation](CODEX_HILBERT__SIMULTANEOUS_SMALL_ROOT_TEST.md)
then gives m Σ_i 1/(m+u_i−s_i)≤1. It too is credited as existing ordinary
mathematics. Since the two outsider terms are strictly positive, it follows
that

    (u_a−s_a)(u_b−s_b)>m².                                   (8)

### Proper retiming cannot improve both owners

Replace the two pair clocks by arbitrary independent PROPER clocks, keeping
the outsiders Never. Put x=Pr(T_a<T_b), y=Pr(T_b<T_a), and z=Pr(T_a=T_b);
then x+y+z=1. Each owner's complete cap remains its passive singleton value
u_i+m: Never attains it, while own-solo and tie rewards are no larger.
Consequently

    d_a=(m+u_a−s_a)x+mz,
    d_b=(m+u_b−s_b)y+mz.                                    (9)

Both debts being at most m would require
(u_a−s_a)x≤my and (u_b−s_b)y≤mx. By (8), this forces x=y=0.
Independent proper clocks which tie almost surely are one common deterministic
finite clock. Thus genuine proper retiming cannot lower both owner debts,
even before the outsider caps are considered. This is a macroscopic actual
clock consequence of the OLD harmonic inequality, not a new local collar.

### Never erasure does lower both owners; the exact outsider bill remains

Instead put T_a=0 with probability 1−z_a and Never otherwise, and similarly
for b, with outsiders still Never. Define

    h=(1−z_a)(1−z_b),   w=z_a z_b,
    x_a=(1−z_a)z_b,     x_b=z_a(1−z_b),
    A_k^a=r_k({a,k})−r_k({a}),
    A_k^b=r_k({b,k})−r_k({b})          for k=c,d.

This is a literal family of independent complete laws, including the original
source at z_a=z_b=0. Its complete debts are EXACTLY

    d_a=mh+s_a w,          d_b=mh+s_b w,
    d_k=max(w s_k, mh+x_a A_k^a+x_b A_k^b+w s_k), k=c,d.     (10)

For an owner i, the late finite response pays
(1−z_j)(u_i+m)+z_j s_i. It dominates Quit zero by (1−z_j)m
and Never by z_j s_i. Subtract the prescribed payoff to obtain (10).
For an outsider, all finite responses after date zero have gain w s_k;
Never has gain zero; Quit zero has the second displayed gain. This proves
(10) with the NEW date-one tester retained. Omitting that tester would give
the wrong owner cap on the opponents' Never event.

A read-only exact rational check verified all 60 debt identities for fifteen
completed tables satisfying (7), with varied erasure probabilities. These
are formula tests, not examples satisfying the global-minimum hypothesis.

For every sufficiently small nonzero (z_a,z_b)≥0, both owner debts are
strictly below m. Global minimality and the all-ties theorem therefore force
at least one outsider's displayed full debt to be strictly ABOVE m.
In particular

    max_(k=c,d) A_k^a>m,      max_(k=c,d) A_k^b>m.             (11)

The first-order necessary condition from simultaneous erasure is

    for every x,y≥0,
    max_(k=c,d) [x(A_k^a−m)+y(A_k^b−m)]≥0.                   (12)

Equivalently a single probability weight on the two outsider rows has
nonnegative weighted values in BOTH columns. This is the elementary
two-column separation formulation of the necessary sign, not a sufficiency
claim about a new equilibrium or an impossible source. Formula (10), rather
than only (12), is the finite-amplitude comparison.

### Why the currently supplied scalar pressure does not exclude equality

At the literal pure-pair minimum, every positive maximal-gain tester is a
membership toggle by (7). A pair member withdraws, leaving the other member
as singleton; an outsider joins, making a triple. None creates a singleton
OF THE DEVIATOR. The original law also has no singleton mass. Thus the
weighted own-singleton pressure is exactly zero for every law on these
maximal-gain testers, even if every owner has positive weight. This equality
arm fits the tie-alteration residual, rather than contradicting its pressure
sign. It does not make the retained source an outward reward normal.

The narrow attained-source comparison also read
`pureTimeMinimum_exists_offMinimum` in
`Diagnostics/Quitting/PureTimeMinimumDescent.lean`,
`pureTimeMinimum_exists_offMinimumPaidPort` in
`Diagnostics/Quitting/PureTimeMinimumPaidPort.lean`, and the actual
`QuittingPureTimeCapReplacementStepsOnDebtFiber` and paid-port interfaces in
`Diagnostics/Quitting/StoppingLaw/FiniteClockMinimumPurification.lean` and
`FiniteClockMinimumPaidPort.lean`. These use TOTAL debt and supply an
off-minimum paid descendant, not a contradiction to an attained MAX minimum.
They do not prove Γ>m. EULER's independently reviewed two-anchor Nash-segment
note needs a supplied induced-Nash segment with two leave signs; (7), which
has strictly adverse leave signs at the original pair, supplies no such
segment.

**Unresolved and next test.** Strict separation Γ>Ω remains unproved.
The proper-retiming arm is closed by (8)–(9); the genuinely different
Never-erasure arm has the complete finite account (10), with the two
outsider singleton-to-pair premiums as its obstruction. The next comparison
must alter an outsider's law together with this erasure and retain its
date-zero and date-one response envelopes. Merely reusing scalar singleton
pressure or improving the pair-concentration exponent cannot pay those two
premiums. No counterexample to the full positive global-minimum hypothesis
has been produced.
