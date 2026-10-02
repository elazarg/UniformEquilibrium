# Strict-fiber sources: non-pair mass and a same-weight Never-to-singleton transfer

Identity: CODEX_FRECHET_CYCLE.

## Status and question

Ordinary mathematics, not Lean-checked or independently reviewed. This is
an internal source-consumption calculation, not an equilibrium producer or
an export candidate. The pair estimate is a direct application of LARCH's
reviewed full-cap stability theorem, not a new concentration argument.
The additional same-source calculation prevents positive Never mass from
coexisting with vanishing singleton mass under the retained tester weights.
No upper leakage estimate or profitable stopping-date row follows.

The precise question is what terminal-event mass is forced on the ACTUAL
profiles, with the SAME weights, supplied by the
[singleton-fiber reduction](MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md).
In particular, can all non-pair mass hide at Never, leaving no prescribed
non-pair stopping event to modify? The answer is no. Whether a resulting
event or combination of events orients an improving joint-law change is
still open; the concrete next operation is stated in Section 6.

## 1. Actual data and retained source

There are four players, independent complete stopping laws on the
nonnegative integers and Never, rewards r_i(S) in [−1,1] for nonempty S,
and zero reward at Never. All singletons may be signed. For a profile p
write μ for its terminal coalition law, U_i for its payoff, V_i(t) for its
payoff after its own pure response t, B_i=sup_t V_i(t), and

    E=max_i(B_i−U_i),       s_i=r_i({i}).

The response supremum includes EVERY finite date and Never. For a finite
source with support in 1,...,N, all dates after N have the same response
value, but they are not identified with Never.

The fixed table has global all-behavior infimum Ω>0. Every date-zero pure
sure coalition S with |S|≥2 has complete regret e_S≥Ω+γ for fixed γ>0.
The source construction gives an arbitrarily accurate actual finite p,
silent at zero, and one probability λ on a complete enlarged finite tester
pool plus Never and a separate zero row. Define

    g_(i,t)=V_i(t)−U_i,       g_zero=0,
    θ_i=Σ_t λ_(i,t),
    a=Σ_a λ_a(E−g_a),
    S=Σ_(i,t) λ_(i,t)[Pr_(p[i←t])(terminal={i})−μ({i})].

The retained source fields are E→Ω, a→0, S≤ε with ε→0, and
θ_i≥Ω/4 for every i. It also retains the same-weight uniform first-order
inequality on the enlarged independent-law domain. That stronger field is
not needed for the mass deductions below and is NOT discarded or replaced
by a new multiplier. No normality of this individual source is assumed.

Write

    σ=Σ_i μ({i}),       C=μ(Never)=∏_i z_i,
    z_i=Pr(T_i=Never),  D_i=∏_(j≠i) z_j,
    h=Σ_(|S|=3 or 4) μ(S),
    ℓ=1−Σ_(|S|=2) μ(S)=σ+C+h.

These are literal source-event probabilities, not masses in a mixture of
counterfactual profiles. In particular D_i≥C.

## 2. The pair leakage floor, with no new concentration proof

[LARCH's observation-stability theorem](CODEX_LARCH_GEOMETRY__OBSERVATION_STABILITY_THEORY.md),
Sections 2, 4 and 6, proves for every actual four-player profile that

    E(p) ≥ min_(|S|=2) e_S − 2048 ℓ.                    (1)

It constructs a pure-pair root with zero or one silent padding row,
controlling EACH payoff and complete cap within 1024ℓ. Padding cannot
lower a pair's regret. Its independent
[JOINT review](../feedback/CODEX_LARCH_GEOMETRY__OBSERVATION_STABILITY_THEORY__BY_CODEX_LARCH_JOINT.md)
checks the uniform counterfactual coupling and the initial-response branch.
I read both complete files and reconstructed the efficient-row argument:
prefix loss ≤256ℓ and root rounding cost ≤(448/27)ℓ in the small-leakage
case, with the stated looser constants covering the remaining cases.

Consequently EVERY retained strict-fiber source with E≤Ω+γ/2 satisfies

    ℓ ≥ γ/4096.                                        (2)

This is pointwise at the old p. There is no need to play the approximating
pair, transfer λ to it, or select a new source. The strict gap above E,
not positivity of the six e_S by itself, is what supplies (2).

## 3. Positive Never forces literal singleton mass under the same λ

Choose k maximizing s_i. The all-Never profile has complete regret
max_i s_i⁺. Since its regret is at least the global infimum Ω,

    s_k=max_i s_i≥Ω>0.                                 (3)

This uses signed rewards directly; no canonical normalization is made.
Let W_k=V_k(Never). A pure finite response after the source support gives
exactly W_k+D_k s_k: on opponent absorption it has the Never response's
outcome, and on all-opponents-Never it wins the singleton instead. Hence

    E−g_(k,Never)≥D_k s_k,
    λ_(k,Never) D_k s_k≤a.                             (4)

For EVERY finite k-response t, its own singleton probability is at least
D_k. This is the literal event that all three original opponents Never;
it does not require a positive finite atom of an opponent or of k.
All other response-singleton probabilities are nonnegative. Therefore

    Σ_i θ_i μ({i})
      = Σ_(i,t) λ_(i,t) Pr_(p[i←t])(terminal={i}) − S
      ≥ D_k[θ_k−λ_(k,Never)]−ε
      ≥ D_k θ_k−a/s_k−ε.                              (5)

No division by D_k was used, so (5) remains valid when D_k=0. As
Σ_i θ_i μ({i})≤σ, (3), D_k≥C and θ_k≥Ω/4 yield

    (Ω/4) C ≤ σ+a/Ω+ε.                                (6)

In particular, if C stays bounded below by a positive constant along the
retained source sequence, so does the ORIGINAL singleton mass σ. The
finite-response mass in (5) includes initial and after-support labels;
the separate Never and zero rows have not been silently removed.

## 4. An actual non-pair stopping event must remain

Put b=a/Ω+ε. Combining (2), (6), and ℓ=σ+C+h gives

    σ+h ≥ [Ωℓ−4b]/(Ω+4).                              (7)

Thus for sufficiently accurate sources,

    σ+h ≥ Ωγ/[8192(Ω+4)].                              (8)

Some one of the four singleton, four triple and one grand-coalition
events consequently has positive mass bounded below along a subsequence.
This is only a finite choice among terminal COALITIONS. It is not a
uniform mass at one stopping date, positive reach of a profitable row,
or an ordering of different counterfactual branches. All nine event types
may receive reward signs unrelated to their probability floor.

The complementary low-(σ+C) arm is quantitatively shadowed by an actual
two-sure product root: the same LARCH note proves payoff and complete-cap
errors ≤16(σ+C)^(1/3), with the zero/one padding bit retained. A source
cap-minus-singleton margin exceeding that error removes padding. This
can be passed to a limiting sure-core semantic minimum, but it does NOT
transport the old calendar-labeled λ rows to that root. TARSKI is testing
the resulting mixed sure-core minimum separately. The eleven strict pure
coalition inequalities alone do not exclude mixed sure-core profiles.

## 5. Scope, checks, and prior-source correspondence

Sixty exact rational signed-table checks verified the late/Never identity,
the inactivity charge, and (5), with arbitrary independently sampled
tester weights. These check the algebra, not existence of a positive
global-minimum table. No numerical optimization or Lean build was run.
The probability identity behind (4) was checked against the full source
pool, including an early finite response, a response tied to a source date,
a finite response strictly after all finite support, and Never. The proof
uses only the last two for their payoff separation. At all-Never, σ=0 and
C=1, so (6) correctly forbids vanishing inactivity/pressure errors with
all owner weights bounded below when some s_i>0. If all s_i≤0, all-Never
already has zero regret and violates the positive-Ω premise.

The exact pair rigidity and full two-sure semantic realization declarations
were inspected in the earlier
[pair-cap notebook](CODEX_FRECHET_CYCLE__PAIR_CONCENTRATION_FULL_CAP_TRANSFER_AND_FORCING_GAP.md):
`exists_pair_terminalOutcomeMass_eq_one_of_terminalPairMass_eq_one` in
`UniformEquilibrium/Quitting/Paths/PairOnlyTerminalLawRigidity.lean`, and
`exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`
and `exists_twoSurePaddedProductRoot_realizing_jointCarrierPoint_of_margin`
in `UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`.
The present quantitative input is LARCH's ordinary-mathematics note, not
a claim that these stronger bounds are Lean declarations.

The proof of (5) is distinct from
[NOETHER's delayed-loss/tie residual](CODEX_NOETHER_SUPPORT__SINGLETON_PRESSURE_DELAY_OR_TIE_RESIDUAL.md):
it uses the uniform literal all-opponents-Never event together with the
inactivity of the Never response. It does not replace that residual's
stopping-order events by marginal clock masses.

Replaying the old finite head has already been tested in
[HILBERT's repeated-block note](CODEX_HILBERT__GLOBAL_MAXIMUM_REPEATED_BLOCK_TEST.md)
and [TARSKI's full graft ledger](CODEX_TARSKI_PREMIUM__GLOBAL_MINIMUM_NEVER_BRANCH_RETRY_AND_TAIL_BUDGET.md).
The rescaled deleted-Never caps there remain separate from prescribed
joint survival; (6) does not orient those cap inequalities. They are not
reproved here. Older singleton/Never hull elimination and MINER's
positive-Never rectangle excursion minimize TOTAL debt; neither is
substituted for the present MAX objective.

## 6. Bounded whole-head promotion test: full rows and the remaining sign

The tested actual operation promotes original Never mass onto that same
player's original conditional finite law. Put x_i=1−z_i. If x_i>0 let
f_i be the conditional finite law and set

    p'_i=(x_i+β_i z_i) f_i + (1−β_i)z_i δ_Never,
                                                    0≤β_i≤1.          (9)

A pure-Never player has no conditional finite law and is left unchanged.
The coins and complete clocks are private and independent. This changes
the original head, not merely the tail after the source calendar. There
are no new dates; nevertheless ALL original enlarged tester labels and
the distinct Never tester are retained.

For A⊆I let p^A use f_i for i∈A and Never otherwise, omitting any undefined
f_i. For independent participation probabilities x', put
w_A(x')=∏_(i∈A)x'_i ∏_(i∉A)(1−x'_i). Write u_i^A=U_i(p^A), and let
v_i^(A,t) be the response t payoff against f_j for j∈A⊆I\{i} and Never
at all other opponents. Exact conditioning on the four private finite-
participation bits gives

    U_i(p') = Σ_A w_A(x') u_i^A,
    V_i(t;p') = Σ_(A⊆I\{i}) w_A(x'_(−i)) v_i^(A,t),
    E(p') = max_(i,t) [V_i(t;p')−U_i(p')].             (10)

This includes every initial, within-head, after-head and Never response.
It is not a correlated strategy interpretation of the displayed finite
sum: independent participation produces exactly its product coefficients.

The first-order component introduces no new orientation. The complete-law
direction d_i=x_i z_i(f_i−δ_Never), set to zero at x_i=0, satisfies that
both p_i+d_i and p_i−d_i are probability laws. In fact their finite masses
are respectively 1−z_i² and x_i². Apply the SAME source certificate to
the two simultaneous endpoints p+d and p−d. If its uniform error is R,

    |Σ_a λ_a D_p g_a[d]|≤R.                           (11)

This is the existing two-sided support-stationarity consequence, not a
strict direction. At finite amplitude, (10) depends on all its conditional
finite-head corner rows. The strict e_S≥Ω+γ inequalities concern the
eleven pure date-zero coalition profiles, whereas p^A generally retains
several nontrivial finite clocks and several outcome coalitions. They
cannot be substituted for these corner values. Furthermore
Σ_a λ_a g_a(p') is a LOWER bound on E(p'), so even decreasing that weighted
quantity would not provide the needed upper bound for all four caps.

Thus this calculation identifies no improving promotion from the actual
global-source hypotheses. It does not disprove that one exists and gives
no positive-global-gap regression. The law-mass floor alone has not paid
the new response terms. The specific remaining question is whether a
source-implied inequality controls the finite-amplitude conditional rows
in (10), beyond the already available first-order equality (11). Without
such an inequality, further promotion parameters merely repackage the
existing independent-law mixed-head comparison, so that recipe is not
expanded here.

Inputs read for this checkpoint: LARCH source SHA
`aa4a44a4922fba9a42dbd73768b617b7717098e8e219268e051f16eb0895aa32`,
its JOINT review SHA
`87b7b40a585196fb3b6fbab3d876c0c8e6c27dc9fe98e1a3b921019c12d8e820`,
and the frozen singleton-fiber source SHA
`1fdefe4acb70e12b789e045885bc8711cea707daa059a70daab197623afbaa70`.
