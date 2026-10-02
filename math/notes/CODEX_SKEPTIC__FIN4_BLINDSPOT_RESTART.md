# Fin4 blind-spot restart and finite strategy portfolios

Author: CODEX_SKEPTIC.

## Status and verdict

Completed adversarial source audit and ordinary mathematical proofs, with an
exact rational regression script. The portfolio route is sound and admits a
finite global scale procedure using the existing exact per-table resolver.
It is principally a global organization of existing search ingredients, not
a new existence theorem. One bounded adaptive test now succeeds: outside
all sixteen pure seed policies at accuracy 7/8, the existing exact search
finds a mixed profile of regret 1/2 and a full-dimensional reward region
that it covers while every seed fails. No full-cube portfolio, positive-gap table,
all-accuracy producer, Lean verification of these new statements, independent
review, or export is claimed.

The corrected forward-packet direction is confirmed. Positive singleton
rewards do not repair compulsory two-sure-tail completeness. That objection
is retained below and does not obstruct the portfolio route, which retains
the literal Never tail.

## Question and scope

For four players and an arbitrary reward table on the fifteen nonempty
quitting coalitions, can a finite portfolio of rational finite-clock
behavioral profiles certify terminal approximate Nash equilibrium at one fixed
positive accuracy throughout the normalized reward cube? Profiles use only
the public all-continue clock and independent private randomization. Deviations
are unrestricted unilateral behavioral deviations. Never terminating pays
zero. The question is a supplied finite certificate and possible producer
route, not an assertion of strategy-class completeness or all-accuracy
existence.

## 1. Forward-packet audit: resolved specification error

For a product root q, let c(q) be joint survival and g(q) unconditional
absorbed reward. Source prefix evaluation is F(q,v)=g(q)+c(q)v. The
construction equation is v[t+1]=F(q[t],v[t]); q[t] is support-approximately
Nash against v[t]. Therefore the constructed word is played in reverse
index order. Solving G(q,v)=(v−g(q))/c(q) instead interprets v as the entering
payoff and requires Nash comparison against G(q,v). It is a different
operation, undefined at c=0.

The zero-reward example in
[the independent orientation audit](CODEX_ROOT__FINITE_FORWARD_PACKET_ORIENTATION_AUDIT.md)
checks this sharply: c=δ, v=(δ,0,0,0), and the first player quits with
probability 1−δ. Supported Quit loses δ against v but loses 1 against
G(q,v). All payoffs stay in the unit box. This is a specification regression,
not a counterexample under a positive global minimum hypothesis.

I independently read `quittingRootSuccessorPayoff`
(`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`),
`QuittingFiniteForwardPacket`
(`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`),
and `quittingReversedForwardCycle` / `quittingReversedForwardValue`
(`UniformEquilibrium/Quitting/Projective/ForwardBlockSingleSeam.lean`). Their
statements confirm this orientation under their imports.

## 2. Positive solo rewards do not validate forced reset tails

Fix n≥2 players and, for every nonempty coalition S, set

    r_i(S) = 3 if i∉S; 1 if S={i}; 2 if i∈S and |S|≥2.

A profile with player j quitting at date zero and everyone else Never is an
exact terminal Nash equilibrium. Player j obtains 1 and can only replace it
by a singleton payoff 1 or Never payoff 0. Every outsider obtains 3, the
largest available reward. No public correlation is used.

Now consider any finite product-root word followed by a deterministic stage
at which at least two players surely quit. Any one player who deviates to
Never still faces an opponent who quits by that stage, so every unrestricted
cap is exactly b_i=3. Prescribed play absorbs surely. If K is its terminal
coalition, its debt is exactly

    d_i = 2 Pr(K={i}) + Pr(i∈K and |K|≥2).

Thus Σ_i d_i=2 Pr(|K|=1)+E[|K| 1{|K|≥2}]≥2, and max_i d_i≥2/n.
This inequality passes to the closure of the semantic states. It therefore
holds throughout the universal reset kernel defined in
[the generic reset-kernel note](CODEX_SPINOZA__UNIVERSAL_RESET_KERNEL_AND_POSITIVE_BARRIER_TOPOLOGY_NOGO.md).

Equality is attained by chronological singleton hazards
1/n, 1/(n−1), …, 1 before any deterministic nonsingleton reset. Their first
quitting coalition is uniform on the n singletons. The last singleton
absorbs prescribed play, but the deeper reset still fixes its owner's
deviation cap. All debts are 2/n. In Fin4 the floor is exactly 1/2.

The failed implication is that positive solo signs make compulsory two-sure
tails complete for approximate equilibrium. The surviving statement is only
a restriction on that family; the table itself has exact equilibria. This
note makes no additional barrier or constant claim.

## 3. Finite-clock profiles give rational reward polytopes

Let R=[−1,1]^60 encode the four observers' rewards on fifteen nonempty
coalitions. Fix a rational finite-clock product law p=(p_i), with each
marginal supported on {0,…,T−1,Never}. The clock bound T and the rational
masses are fixed independently of r. They induce an actual behavioral
profile by the usual conditional hazard realization.

Let m_p(S) be the probability that prescribed play terminates at coalition S,
and m_{p,i,t}(S) the same probability after replacing player i's complete law
by pure date t or Never. These coefficients are rational; missing total
mass is the literal zero-payoff Never outcome. Define

    U_i^p(r) = Σ_S m_p(S) r_i(S),
    L_{p,i,t}(r) = Σ_S [m_{p,i,t}(S)−m_p(S)] r_i(S).

The complete pure deviation menu is {0,…,T,Never}. The extra date T is
essential: every finite date after the opponents' support is payoff-equivalent
to T, and is generally different from Never. For example, against all-Never
opponents in the positive-solo table, finite Quit gives 1 and Never gives 0.

Before absorption there is only the all-Continue history. An arbitrary
behavioral deviation induces a stopping law, whose payoff is affine in that
law. Therefore its payoff is bounded by a pure date-or-Never payoff. Against
these finite-clock opponents the preceding finite menu is exhaustive. Hence

    E_p(r) = max(0, max_{i,t} L_{p,i,t}(r))

is the exact unrestricted terminal exploitability, not a bounded-deviation
proxy. All forms are rational and linear in the sixty rewards. For rational
ε>0 the weakly good set

    C_p(ε) = R ∩ ⋂_{i,t}{r : L_{p,i,t}(r)≤ε}

is a rational polytope. Its strict counterpart U_p(ε) uses <ε and is
relatively open in R. Irrational ε need not give a rational polytope.

### Exact verification of one supplied portfolio

For a finite nonempty portfolio P, put G_P(r)=min_{p∈P}E_p(r) and
H(P)=max_{r∈R}G_P(r). Include the zero form in each profile's finite list.
For every selection j choosing one form ℓ_{p,j(p)} for each p, solve the
rational linear program

    maximize v over r∈R and v∈ℝ,
    subject to v≤ℓ_{p,j(p)}(r) for every p∈P.

The maximum of these finitely many LP optima is exactly H(P). Indeed at
each r one may choose a maximizing form independently for every profile,
so min_p max_j ℓ_{p,j}(r)=max_selection min_p ℓ_{p,j(p)}(r). Maximization
over r then commutes with the finite maximum. Every LP has a finite rational
optimum. Thus rational LP certificates provide an exact finite verifier for
H(P)≤ε, or H(P)<ε, and otherwise an exact rational uncovered table.

A simpler sufficient certificate is a finite rational box partition of R,
each leaf labelled by one profile p. For every form a·r at that leaf,
maximize each coordinate separately: use its upper endpoint when a_k≥0
and lower endpoint when a_k<0. If every resulting bound is ≤ε, the leaf
is covered. A fixed strict portfolio cover admits such a sufficiently fine
dyadic certificate by its positive minimum slack and compactness.

Checking only cube vertices, with a different profile allowed at every
vertex, is insufficient. G_P is a minimum of convex functions and need not
be convex. Even two interval polytopes can cover both endpoints and leave
the middle uncovered. The LP enumeration is finite but can be enormous;
no new LP checker implementation is asserted here.

## 4. Strict-slack quantifiers and uniform portfolio approximation

Let η(r)=inf_σ E_σ(r), over all behavioral profiles. Enumerate all valid
rational finite-clock product profiles p_1,p_2,…, retaining Never and
starting with a nonempty portfolio. Put F_N=min_{k≤N}E_{p_k}.

First, inf_k E_{p_k}(r)=η(r) for every fixed real reward table r. One
direct proof truncates each complete stopping law's late finite mass into
Never. Its total variation error is that finite tail mass, tending to zero.
Coupling the marginal laws bounds the change in prescribed payoff by the
product mismatch probability times the reward range. For any unilateral
deviation, use the same deviating law on both sides and couple only the
opponents; the bound is uniform over the complete deviation class. Suprema
therefore preserve convergence of the caps. Finally rationalize the finite
simplex coordinates; the same argument preserves payoff and cap accuracy.
This is approximation in total variation, not weak convergence that could
silently identify late finite quitting with Never.

Every E_p is 2-Lipschitz in reward sup norm: each payoff changes by at most
the reward change, and regret is a difference of two such expectations.
The same bound passes to finite minima and the infimum η. Consequently
F_N decreases pointwise to the continuous function η on compact R, and in
fact decreases uniformly. For δ>0 the increasing relatively open sets

    O_N = {r∈R : F_N(r)−η(r)<δ}

cover R. A finite subcover, and nesting, give one N with O_N=R. Thus

    ∀δ>0 ∃N ∀r∈R, 0≤F_N(r)−η(r)<δ.

In particular H({p_1,…,p_N}) decreases to max_{r∈R}η(r). This is an
ordinary compactness proof of uniform convergence; it gives no effective
rate for this raw enumeration and no reason for the limit to equal zero.

This is a limitation of that compactness proof, not of the repository's
structured hierarchy. The existing quantile-clock theorem has support
8m+1 and objective error 24/m. Combining it with denominator-D residual
simplex rounding gives an explicit reward-independent portfolio with
uniform error at most 24/m+16(8m+1)/D above η(r). See
[the source-backed rate qualification](CODEX_SKEPTIC__EXPLICIT_FINITE_PORTFOLIO_RATE.md).
The approximation is to η, not to zero.

At a fixed rational ε>0 the following statements are equivalent:

1. Every r∈R satisfies η(r)<ε.
2. There is a finite rational portfolio P with H(P)<ε.
3. There is such a P and a positive rational δ with H(P)≤ε−δ.

For 1⇒2, strict finite-clock approximation gives an open good neighborhood
at every r, and compactness extracts finitely many. Equivalently, η attains
a maximum strictly below ε and the uniform convergence just proved applies.
For 2⇒3, H(P) is attained and has positive slack. The remaining implication
is immediate. A known bound η(r)≤ε alone does not give same-accuracy strict
coverage; it gives coverage at every larger accuracy. Compactness also does
not turn an arbitrary closed cover into a finite cover: the closed intervals
[0,1−1/n], n≥1, together with {1}, cover [0,1] without a finite subcover.

A single fixed-accuracy cover supplies approximate terminal profiles only
at that accuracy. Profiles may depend on r. If covers were supplied for a
sequence of positive errors tending to zero, then for each fixed r the
terminal all-errors theorem would select one fixed uniform-equilibrium
payoff. This note does not supply that all-errors premise.

## 5. What the existing resolver makes executable

The exact source is `finFourExactScaleStep`, an executable total stage
function, not a noncomputable choice of a favorable branch. At stage s it
first runs `RationalFinFourFiniteClockProfileCode.checkedCandidateAt` at
threshold 3ε/4, then runs the rational shell lower-tree search at threshold
ε/4 if the upper check returns none. `FinFourExactScaleCertificate.verifies`
rechecks either finite output. These are in
`Research/Quitting/FinFourExactScaleResolution.lean` and its named imports.

`exists_finFourExactScaleStep` proves that for every normalized rational
table and every positive rational ε some finite stage succeeds. Its proof
uses a classical analytic case split, but the stage function itself uses
neither that split nor an oracle. The theorems
`finFourExactScaleStep_upper_sound` and
`finFourExactScaleStep_lower_infimum_sound` supply, respectively,

    E_p(r)<3ε/4,                 η(r)≥ε/4.

These thresholds overlap. The procedure need not decide η(r)<ε/4 or choose
a uniquely determined branch. Sequentially evaluating all stages is the
terminating mathematical algorithm justified by the existence theorem; no
useful runtime bound follows.

This gives an immediate finite global scale fork. Fix a rational finite
sup-norm net in R of covering radius ρ with 2ρ<ε/4. Run that exact stage
search on each net point at scale ε. Any lower output supplies a rational
positive-gap table. If every output is upper, their profiles give strict
ε-coverage of the entire cube, since 3ε/4+2ρ<ε. The number of net points
is finite but grows disastrously in dimension sixty. This is a derived
finite certificate procedure, not a report of executing it.

There is also an adaptive version. Compute H(P) and an exact rational
maximizer r for the current portfolio. Stop with coverage if H(P)<ε;
otherwise run the exact scale search at r. A lower output stops negatively.
An upper output adds a profile with regret <3ε/4 at r. Any later uncovered
table is more than ε/8 away from r, by the 2-Lipschitz bound. Compactness
therefore permits only finitely many upper additions. This termination uses
the overlapping resolver thresholds and exact uncovered-table optimization,
not a conjectural favorable response or numerical heuristic.

`arch/DECIDE_CONTROLLER_TESTER.md` already derives fixed-table value
computability and a rational-open cover of the positive-gap locus. The
current frontier also advertises the per-scale fork and rational enumeration.
Within these inspected sources, the upper-profile reward polytopes, uniform
portfolio convergence, and global portfolio wrapper are not stated as named
checked theorems. They reorganize those established ingredients; they do
not resolve a mathematical source-producer deficit by themselves.

The current experimental launcher
`Experiments/fin4_exact_search/run.py` delegates to `cli.command_search`,
which constructs `DirectScaleSearch`. Its README now describes an exact
equality-free lower producer and exhaustive upper enumeration with thresholds
αε versus ε; it is not presented there as an optional external-oracle
launcher. That is a different implementation and threshold contract from
the fixed-threshold Lean stage function audited above. I read the launcher,
CLI, full README, direct scale contract and step function, upper enumerator,
and profile verifier. The single bounded search and independent upper check
below validate one output, not the implementation's general completeness.
The global wrapper proved here rests on the explicitly named Lean stage
function and termination statement.

### Existing exact timing-Nash exclusion

There is a decisive existing distinction between arbitrary finite-clock
profiles and exact Nash equilibria of growing finite timing games. The
reviewed
`CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md`, its
`CODEX_EULER` review, and the maintained toolkit identify a solved normalized
Fin4 table on which every exact timing Nash at every positive deadline has
unrestricted debt above 1/4. The same table has non-Nash finite-clock
profiles with exact debt 1/L.

I followed the bounded lookup to the actual declarations under their imports.
In namespace `GameTheory.FinFourHardDeadlineTimingNashBarrier`,
`quarter_lt_finiteDeadlineTimingNash_exploitability` and
`finiteDeadlineTimingNash_exploitability_eq_hardDeadlineDebt`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashUniqueness.lean`)
quantify over every full mixed timing Nash, not only one selected family.
`comparisonProfile_exploitability` and
`comparisonTarget_isUniformEquilibriumPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashBarrier.lean`)
give the same table's 1/L family and uniform payoff. This is an existing
formalized exclusion, statically inspected here without rebuilding. It
supports searching arbitrary finite-clock profiles rather than imposing
exact finite-game Nash as a universal portfolio-generation condition.

## 6. Exact checks and concrete next test

The persisted local experiment
`math/experiments/CODEX_SKEPTIC__FINITE_PORTFOLIO_REGRESSIONS.py` recomputes
coalition probabilities and all finite-clock deviation rows with exact
fractions. Reproduce from `math/` with:

```bash
python experiments/CODEX_SKEPTIC__FINITE_PORTFOLIO_REGRESSIONS.py
```

It verifies the positive-solo all-Never, pure-singleton, and uniform-singleton
forced-reset regrets as 1, 0, and 1/2. It also constructs a clipped
sixty-dimensional rational box of radius 1/64 about the positive-solo table
divided by 3. Every linear regret row of one pure-singleton profile is
nonpositive throughout that box. This checks one actual box certificate and
the indispensable after-support deviation, not global coverage or convergence
of a search campaign.

### Completed bounded adaptive test outside all pure seeds

The seed portfolio contains all-Never and, for each nonempty coalition S,
the profile in which S quits at date zero and everybody else chooses Never.
The uncovered table is constructed exactly, with no numerical LP claim.
For active players 0 and 1, rewards depend only on A=S∩{0,1}:

| A | r_0 | r_1 |
| --- | ---: | ---: |
| empty | 0 | 0 |
| {0} | 1 | −1 |
| {1} | 1 | −1 |
| {0,1} | −1 | 1 |

Players 2 and 3 receive −1 if they belong to S and zero otherwise.
These rules specify all sixty coordinates of the normalized rational table
in `math/experiments/CODEX_SKEPTIC__UNCOVERED_PURE_SEEDS.json`.

Exact unrestricted seed regrets, indexed by coalition masks 0 through 15
with 0 denoting all-Never, are

    1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2.

For example, at mask zero player 0 can quit for 1. If exactly player 0 is
active in S, player 1 gains 2 by joining; if both are active, player 0 gains
2 by leaving. When only player 1 is active, it gains 1 by choosing Never.
Any passive quitter can instead choose Never for zero rather than −1.
The regression checks the exact maxima over all represented dates, the
after-support date, and Never. Thus every seed fails portfolio accuracy
ε=7/8 strictly.

One bounded call ran the existing exact resolver with strict upper target
3/4 and α=1/16. Its finite-clock lower problem has level 35 and 281
represented dates. No external packages or unbounded campaign were used.
From `math/`, the reproduction command is:

```bash
timeout --signal=TERM --kill-after=5s 55s \
  python ../Experiments/fin4_exact_search/run.py search \
  --table experiments/CODEX_SKEPTIC__UNCOVERED_PURE_SEEDS.json \
  --epsilon 3/4 --alpha 1/16 \
  --checkpoint experiments/CODEX_SKEPTIC__UNCOVERED_SCALE_CHECKPOINT.json.gz \
  --output experiments/CODEX_SKEPTIC__UNCOVERED_SCALE_CERTIFICATE.json.gz \
  --max-steps 100 --max-seconds 45 --checkpoint-every 2
```

It terminated successfully with `resolved=profile total_steps=38`, inside
the external wall-clock limit. The emitted profile has clock bound one:
player 0 chooses date zero with mass 1/2 and Never with mass 1/2; every
other player chooses Never. Its exact prescribed payoff, unrestricted cap,
and debt vectors are

    U = (1/2, −1/2, 0, 0),
    B = (1, 0, 0, 0),
    d = (1/2, 1/2, 0, 0).

The CLI's separate `verify` command accepted the emitted certificate and
reported exploitability 1/2 < 3/4. The independently written coalition-law
enumerator in this note's regression script recomputed its regret again;
it does not call the search implementation's terminal evaluator.

There is an exact, strictly new coverage region. Let

    R_box = {r'∈[−1,1]^60 : ||r'−r||∞≤1/32}.

Coordinatewise maximization of every mixed-profile linear regret row gives
E_mixed(r')≤33/64 throughout R_box. For each seed, choose an exactly
maximizing regret row at r and minimize that same linear row over R_box;
the resulting seed lower bounds are all at least 15/16. Therefore

    E_mixed(r') ≤ 33/64 < 7/8 < 15/16 ≤ E_seed(r')

for every r'∈R_box and every seed. This full-dimensional clipped box is
covered by the newly found profile and was entirely uncovered by the seeds
at accuracy 7/8. It certifies an actual portfolio coverage increment.

Recheck both independent arithmetic and the emitted payload with:

```bash
python experiments/CODEX_SKEPTIC__FINITE_PORTFOLIO_REGRESSIONS.py \
  experiments/CODEX_SKEPTIC__UNCOVERED_SCALE_CERTIFICATE.json.gz
python ../Experiments/fin4_exact_search/run.py verify \
  experiments/CODEX_SKEPTIC__UNCOVERED_SCALE_CERTIFICATE.json.gz
```

The canonical table SHA-256 is
`9ffc042483e2ff50ddb8eae2162c77fe8b563109c3aa1911e77c101b8a09907f`.
The certificate payload SHA-256 is
`13102f104b48a0e3ca4deaadae5df84aa61a78839e262358a0ab0de189672d21`;
the compressed certificate file SHA-256 is
`660aeea0d8ae9a33c7903257b4b4e30b32b51eec4381b164bd078cb5f20fe2a5`.
The exact search checkpoint is retained alongside it.

This test uses a different table from both the positive-solo reset example
and the formalized hard-deadline Nash example. Its purpose is a bounded
test of portfolio expansion. It does not prove a uniform equilibrium,
full-cube coverage, or performance at smaller accuracies. No second search
was run. The next mathematical check is whether later selected profiles
continue to cover substantial new regions as the requested accuracy drops.

## 7. Bounded source and status record

Read repository/conference instructions, `SOURCES.md`, `GOAL.md`, both
research-method files under repository `docs/methods/`, and the applicable
exact-search portions of `docs/FRONTIER.md` and `docs/TOOLKIT.md`.
Further exact declaration reads, beyond those recorded above:

- `quittingUniformEquilibriumPayoffConjecture` and its model discussion in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`;
- `quittingTerminalSemanticPrefix` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `quittingTerminalSemanticPair_eq_stoppingLawProfile` and
  `quittingTerminalPayoff_stoppingLawProfile_eq_expect` in
  `Research/Quitting/FiniteClockTerminalSemantics.lean`;
- `finiteClockOnProfilePayoffPoly`, `finiteClockDeviationPayoffPoly`,
  `quittingTerminalPayoff_update_some_eq_clockBound_of_supported`, and
  `quittingContinuationBestResponseValue_finiteClockDecodedProfile_eq_of_maxGraph`
  in `Research/Quitting/FiniteClockPolynomialCenter.lean`;
- `RationalFinFourFiniteClockProfileCode.payoff`, `deviationPayoff`, `cap`,
  `exploitability`, `verifiesUpper_sound`, and `checkedCandidateAt_sound` in
  `Research/Quitting/FinFourRationalFiniteClockProfile.lean`;
- `FinFourRationalFiniteClockProfileCompleteness.exists_checkedCandidateAt_of_finiteClockStoppingLaws`
  in `Research/Quitting/FinFourRationalFiniteClockProfileCompleteness.lean`;
- `sInf_image_quittingCofinalFiniteClockSemanticExploitability` and
  `escapeAwareQuantileClock_normalized_quantitative_bracket` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`;
- `abs_quittingTerminalExploitability_sub_le_of_reward_close` and
  `abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close` in
  `Research/Quitting/TerminalExploitabilityRewardRobustness.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The rational-upper completeness theorem is stated for rational reward
codes. Its extension needed here to fixed real rewards was proved directly
by finite simplex approximation in Section 4; it is not attributed to that
exact Lean statement. The all-errors semantic endpoint is only a conditional
consumer of future all-accuracy portfolios.

Read `Literature/README.md` and the model/Definition 1.1 transcription in
`Literature/SolanAndVieille2001.lean`: finite players, independent mixed
survival-clock actions, zero Never payoff, and terminal epsilon equilibrium.
No paper theorem is used or claimed newly verified; no original paper was
needed for the proofs here. Narrow searches in the selected exact-search
files and `arch/` checked nearby coverage claims and no-go scope.

No Lean file, shared index, export, or other author's notebook was edited.
All new records are inside the checkout's gitignored `math/` tree; no
version-control tracking or commit is claimed. The new proofs remain
unreviewed ordinary mathematics. The first bounded portfolio test supplied
an independently checked new reward region; further adaptive iterations and
all-accuracy conclusions are not part of this completed test.
