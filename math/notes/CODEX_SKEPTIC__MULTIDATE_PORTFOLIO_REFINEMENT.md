# Sure-owner duplicate boundary and one multi-date refinement

Author: CODEX_SKEPTIC.

Current status: COMPLETE bounded exact refinement. The sure-owner mechanism
is already covered by the named singleton-base compiler; no new table-class
theorem is claimed. On one rational four-active table, all 142 old policies
have unrestricted terminal regret above 1/5000, and EVERY stationary policy
has regret at least 1/600. An actual rational 15-date policy has regret
70000000000/3419801026597191 < 1/10000. A positive reward box is newly
covered at accuracy 1/5000. The central table also has the explicit exact
infinite cycle proved below; this is an instance of familiar cyclic
mathematics, not a new UE class. No more search is planned in this tranche.

Status distinctions: ordinary mathematical proof plus exact Python/Fraction
verification, not a newly Lean-checked result. All new records are local
gitignored `math/` records. No Lean, external search source, exports, shared
index, or commit was edited. The math-unicode skill affects notation only.

## Source boundary established before the experiment

Read `quittingRootFreeMixedPoint_mem_singletonBaseNashSet_of_sure_exactNash`
in `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SureRootSingletonHandoff.lean`.
Read the literal `QuittingSingletonBaseCertificate` and its methods
`exists_terminalNash_fixedTarget` and `isUniformEquilibriumPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`.
The certificate asks for exact induced free-player endpoint Nash and the
owner balance A+D P_owner≤Q. It already constructs all-accuracy full-response
profiles at the fixed date-zero target. A one-date/Never owner-safe root has
A+D max(s_owner,0)≤Q, which implies that existing balance because
`quittingPunishmentValue_le_max_solo` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean` gives P_owner≤max(s_owner,0).
The mechanism found in the previous 141-policy experiment is therefore a
special case of a strictly stronger existing compiler, not a new class.

## Bounded fallback test

Use the normalized all-positive-singleton cyclic Fin4 table from
`CODEX_HILBERT__BOUNDED_TIMING_INCENTIVE_TEST.md`, then lower just player 0's
passive predecessor reward from 1 to 1199/1200. The reward sup distance is
1/1200. The exact all-stationary floor 1/300 proved in Section 15 of
`CODEX_HILBERT__EXTREMAL_REWARD_TABLE_VARIATIONAL_TEST.md` therefore leaves
a stationary floor 1/600 at the perturbed table by fixed-profile
2-Lipschitz reward robustness. This is a stationary-class lower bound,
not a full behavioral gap.

The new actual profiles use unequal three-phase hazards
(1398/2797,699/1399,2796/5593), only one cyclic player active at a date,
and player 3 Never. These fractions solve the exact owner Bellman
indifference equations after the stated perturbation. Test only this one
table, the old 141-policy portfolio plus its previous sure-owner addition,
and at most five finite truncations (4 through 8 complete cycles), using
the existing exact full-response evaluator and independent coalition-law
checker. The test stopped after the second truncation, at five cycles.

## 1. Exact table, agency, and target

Players are 0,1,2,3. Before absorption they independently choose Continue or
Quit at each date. The first nonempty quitting coalition S fixes terminal
reward r(S); infinite joint Continue has reward zero. For any actual
independent stopping-law profile σ, let E_r(σ) be the maximum, over players,
of the best unrestricted unilateral behavioral payoff minus the prescribed
terminal payoff, with a nonnegative floor. All deviation statements here
include Never, arbitrarily late quitting, and adaptive behavioral deviations.

For i∈{0,1,2}, let pred(i)=i−1 modulo 3 and put

    (b₀,b₁,b₂) = (1199/400,3,3).

For every nonempty S⊆{0,1,2,3}, define the normalized table r* by

    r*ᵢ(S) = (1 + 1_{pred(i)∈S})/3       if i∈S,
    r*ᵢ(S) = (bᵢ/3) 1_{pred(i)∈S}       if i∉S,
    r*₃(S) = 1/3 if 3∈S, and 2/3 otherwise.

Thus all sixty coordinates lie in [0,1] and every own singleton is 1/3.
Every player is strategically active in the explicit background-reversal
sense: for i<3, joining background {3} raises its payoff from zero to 1/3,
while leaving {i,pred(i)} raises it from 2/3 to bᵢ/3>2/3. Player 3 can quit
alone for 1/3 rather than joint Never's zero, but leaving a coalition with
an active player raises its payoff from 1/3 to 2/3. Player 3's prescribed
Never law is not a dummy-player assumption.

Let r⁰ be the same table with b₀=3. Precisely four reward coordinates change:
player 0's rows whose coalition contains 2 but not 0 (masks 4,6,12,14).
Their decrease is 1/1200, so ‖r*−r⁰‖∞=1/1200. The table's canonical engine
SHA-256 is

    6b98a0f67ff5299ec0b8ae1aa69ff358eba06abf4482e2d57b1370244d0b1427.

The fixed portfolio target is ε=1/5000. The new-profile acceptance threshold
is the strictly smaller 1/10000.

## 2. Literal exact periodic construction at the central table

Put

    (q₀,q₁,q₂) = (1398/2797,699/1399,2796/5593).

At phase i only player i may quit, with probability qᵢ; all other players
Continue. Repeat phases 0,1,2 forever, with independent private coins.
In particular this is not a public lottery between complete profiles.

Theorem (this explicit table). This periodic profile is exact terminal Nash
against unrestricted behavioral deviations and has fixed uniform-equilibrium
payoff

    v = (1/3,5593/8391,1/3,2/3).

Proof. All qᵢ lie strictly between zero and one. With cyclic subscripts they
satisfy the three exact identities

    q_{i+1}/(1−q_{i+1}) = (bᵢ−1)q_{i−1}.                 (1)

These are identities of the displayed rational numbers, not roots chosen
by an oracle. Define the phase payoff for active i by

    Vᵢ(i) = Vᵢ(i+1) = 1/3,
    Vᵢ(i−1) = [1+(bᵢ−1)q_{i−1}]/3,

and V₃(k)=2/3 at every phase. The three vectors are explicitly

    V(0) = (1/3,5593/8391,1/3,2/3),
    V(1) = (1/3,1/3,2797/4197,2/3),
    V(2) = (1399/2100,1/3,1/3,2/3).

At i's own phase its Quit payoff and next-phase Continue value are both
1/3. At phase i−1, Continue has value
q_{i−1}bᵢ/3+(1−q_{i−1})/3, exactly Vᵢ(i−1).
At phase i+1, Continue has value (1−q_{i+1})Vᵢ(i−1)=1/3 by (1), because
the opponent's singleton gives i zero. These verify prescribed Bellman
recursion at all phases. Player 3 receives 2/3 whenever absorption occurs,
and absorption occurs almost surely.

Now check both response endpoints at every phase j. Player j is indifferent
between Quit and Continue at 1/3. The successor j+1 has immediate Quit
value (1+qⱼ)/3 and Continue value [1+(b_{j+1}−1)qⱼ]/3; Continue is better
because b_{j+1}>2. Player j−1 has both endpoints 1/3. Player 3 has Quit
value 1/3 and Continue value 2/3. Consequently every pure endpoint is
bounded by V at that phase, and the prescribed row attains V.

These are full-response inequalities, not merely on-path Nash equations.
After deleting any one player's clock, at least two positive active hazards
remain (three when deleting player 3). Their survival over one period is
strictly below one, uniformly over the deviator's actions. Iterating the
endpoint upper bound for any behavioral deviation leaves a bounded residual
times this geometrically vanishing opponent survival. Thus every adaptive
deviation, including Never and every late response, is bounded by the
displayed initial value. The same recursion with equality identifies the
prescribed terminal payoff. This proves terminal Nash.

For completeness, the same opponent absorption bound gives uniformly
bounded expected absorption time under every unilateral deviation. Since
all stage rewards are bounded, expected long-horizon average payoffs differ
from the corresponding terminal payoffs by a quantity tending to zero,
uniformly in the deviation. Hence this very profile attains the fixed target
v in the uniform-equilibrium payoff sense. Equivalently, the displayed data
directly satisfy `IsQuittingBlockCertificate` and its existing consumer
`isUniformEquilibriumPayoff_of_isQuittingBlockCertificate` in
`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`: the box,
closure, Bellman recursion, exact endpoint complementarity, absorption,
and deleted-opponent absorption fields were all constructed above. No new
general cyclic compiler or new table-class result is being claimed. ∎

The script's `phase_check` independently performs all three vector Bellman
equalities and all twelve player/phase endpoint comparisons with Fractions.
The production `IsQuittingBlockResponseSolution` and
`quittingCyclicResponseCap_le_of_isQuittingBlockResponseSolution` in the same
source express exactly this response system. Their declarations and imports
were read; no Lean instance was created or built here.

## 3. All stationary profiles are quantitatively excluded

This section records a genuinely all-stationary lower bound, separate from
the finite portfolio enumeration. The unperturbed result is HILBERT's
Section 15, independently checked here; its proof is ordinary mathematics,
not a newly formalized table instance.

For a stationary hazard vector p, write
α=1−∏ᵢ(1−pᵢ), βᵢ=1−∏[j≠i](1−pⱼ), Qᵢ for immediate Quit, Cᵢ for the
absorbing contribution conditional on own Continue, and Fᵢ=βᵢQᵢ−Cᵢ.
On βᵢ>0 the exact full terminal debt is

    max((1−pᵢ)Fᵢ/α, −pᵢFᵢ/(αβᵢ)).                    (2)

The zero-denominator cases must be separated: if α=0 the profile is
all-Never; if βᵢ=0<α, player i is the only possible quitter and its debt is
max(0,−rᵢ({i})). This is the complete cap supplied by
`quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap`
and `quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never`
in `UniformEquilibrium/Quitting/Stationary/CompleteBehavioralCap.lean`.

Here is the short exact base-table bound, before normalization by three.
Let h=max(p₀,p₁,p₂) and z=p₃. If h=0 an active player has regret one.
Otherwise relabel cyclically so p₀=h. The outsider's Never debt is z/α;
if z>h/16 then z/α≥z/(3h+z)>1/49. Suppose z≤h/16. Then α≤4h,
every active βᵢ≤3h, and

    Fᵢ=(1−p_{i−1}²)p_{i+1}−p_{i−1}(2−p_{i−1})
       +z(1−p_{i−1})(1−p_{i+1})(1+p_{i−1}).

The final summand lies in [0,2z]. If p₁≥h/4, then
F₁≤−h(1−h+h²)+2z≤−5h/8, and (2) gives debt at least 5/384.
If p₁<h/4, then F₂≥7h/16. When p₂≤1/2 its Quit debt is at least
7/128. Otherwise p₂>1/2, p₀≥p₂ and p₁<p₂; thus
F₀≤−p₂(1−p₂+p₂²)+2z<−1/4, and its Never debt exceeds 1/8.
All denominators actually used are positive because the named player has
a positive opponent hazard. Each case exceeds 1/100. Therefore every
stationary profile at normalized r⁰ has E≥1/300.

Every fixed actual profile's exploitability is 2-Lipschitz in reward sup
distance: every prescribed or deviating payoff changes by at most the
distance, so each payoff difference changes by at most twice it; taking
suprema and maxima preserves the bound. The literal source declaration is
`abs_quittingTerminalExploitability_sub_le_of_reward_close` in
`Research/Quitting/TerminalExploitabilityRewardRobustness.lean`, read under
its imports. Hence at r*, for EVERY stationary profile,

    E ≥ 1/300 − 2/1200 = 1/600.                         (3)

This excludes stationary policies at the tested accuracy. It does NOT give
a positive gap over all behavioral profiles: Section 2 proves the opposite
at the central table. Nor does it exclude all imaginable off-path-tail
sure-owner constructions.

## 4. Precisely enumerated old portfolio and actual new finite policy

The old portfolio has 142 explicitly saved independent profiles:

- 81 one-date roots with each hazard in {0,1/2,1}, followed by Never;
  these include all sixteen pure coalition roots and all-Never.
- 48 half-hazard cyclic truncations: every ordered three-player subset
  (24 choices) and every four-player order (24 choices), each repeated four
  complete rounds, then Never.
- 12 comparison profiles: a named player quits surely at date 0, one other
  player is uniform on dates 1,2,3,4, and the remaining players Never.
- The previous refinement's one-date sure-owner-thirds root
  (1,1/3,1/3,1/3), then Never.

Every law, payoff, complete cap, and debt is in the saved manifest. Exact
evaluation gives

    min[σ in old portfolio] E_{r*}(σ) = 197/983040 > 1/5000,

uniquely attained by `HALF_CYCLE_012`. This is only an enumerated-portfolio
minimum. It is not treated as the unrestricted game value.

For k complete rounds of the unequal hazards from Section 2, define active
player i's finite stopping law by

    Pr(Tᵢ=i+3a)=qᵢ(1−qᵢ)^a,  a=0,...,k−1,
    Pr(Tᵢ=Never)=(1−qᵢ)^k,

and let player 3 Never surely. Laws are independent. The two candidates
actually evaluated were

    k=4, clock 12: E=700000000/4280101410009;
    k=5, clock 15: E=70000000000/3419801026597191 < 1/10000.

The latter is the accepted new policy. Every law has positive Never mass;
every finite atom is below one. There are three nontrivial stopping clocks,
not a sure-owner root and not a stationary policy. Its exact cap vector is

    (1/3,5593/8391,1/3,651264227207998/976911340811997).

Its player debts are

    (10000000000/976911340811997,
     70000000000/3419801026597191,
     10000000000/976911340811997,
     10000000000/976911340811997).

Unequal hazards are mathematically relevant at the stricter upper threshold,
not only a re-labeling of the old truncation: in the infinite equal-half
cycle 012, player 0's prescribed payoff is (4+b₀)/21=1/3−1/8400.
Immediate Quit gains 1/8400>1/10000. Any finite complete-round truncation
of this equal-half cycle has still smaller prescribed payoff and the same
Quit payoff, so cannot meet that stricter threshold. This observation does
not rule out every different cyclic word or claim an optimal clock length.

The `terminal_semantics` evaluator in the read-only exact-search engine
checks all represented dates 0,...,14, one after-support date 15, and Never.
Every later pure date has the same payoff as date 15. A unilateral
behavioral strategy induces a stopping law on the unique unabsorbed history;
with independent opponents its payoff is linear in this law. Therefore
the finite maximum really bounds unrestricted behavioral deviations, not
just deviations whose support stays within the prescribed clock. The
separate coalition-law evaluator `regret_rows`/`evaluate` reconstructed the
new maximum independently and agreed exactly.

## 5. Explicit positive-radius uncovered-cell reduction

Set

    δ = 49/491520000 > 0,
    B = { r∈[−1,1]⁶⁰ : ‖r−r*‖∞≤δ }.

The report saves all sixty lower and upper coordinate endpoints of B.
Its radius is one quarter of the smallest strict center margin needed;
it is not an optimized radius. For EVERY r∈B, fixed-profile reward
2-Lipschitzness gives

    min[σ in old portfolio] E_r(σ)
      ≥ 197/983040 − 2δ = 49201/245760000 > 1/5000,

    E_r(new policy)
      ≤ 70000000000/3419801026597191 + 2δ < 1/5000,

    inf[σ stationary] E_r(σ)
      ≥ 1/600 − 2δ = 136517/81920000 > 1/5000.

Thus adjoining this actual rational policy strictly reduces the old
portfolio's uncovered set: the entire explicit nonempty reward box B was
uncovered and is now covered. These are fixed-accuracy statements on B.
The exact periodic proof at its center does not prove UE for every table
in B, and fixed-policy robustness does not supply an all-accuracy producer.

One rejected intermediate choice is retained for honesty: a proposed
radius 1/100000 failed the strict old-portfolio margin assertion. The
script stopped before saving any completion certificate or robustness
report. The table and old manifest were valid. Replacing only that radius
by one quarter of the exact strict margins produced the displayed δ; no
new table or profile search was launched.

## 6. Reproduction, files, and final verdict

The external exact-search README and relevant engine definitions were read.
Only the existing evaluator and certificate checker were reused, read-only;
this was not an invocation of its exhaustive `UpperSearch` or an exact
global lower resolver. The new-profile search was exactly the bounded
structured list described above and stopped at its second member.

From `/home/elazarg/UniformEquilibrium/math`, the exact commands are:

```bash
PYTHONDONTWRITEBYTECODE=1 timeout --signal=TERM --kill-after=5s 55s python experiments/CODEX_SKEPTIC__MULTIDATE_PORTFOLIO_TEST.py run
PYTHONDONTWRITEBYTECODE=1 python experiments/CODEX_SKEPTIC__MULTIDATE_PORTFOLIO_TEST.py verify
PYTHONDONTWRITEBYTECODE=1 python ../Experiments/fin4_exact_search/run.py verify experiments/CODEX_SKEPTIC__MULTIDATE_PROFILE_CERTIFICATE.json.gz
```

All three completed with exit status zero. The final command independently
reconstructed and accepted full exploitability
70000000000/3419801026597191 at threshold 1/10000. No package installation,
floating-point acceptance, or unbounded campaign occurred.

Local artifacts, all under `math/experiments/`:

- `CODEX_SKEPTIC__MULTIDATE_PORTFOLIO_TEST.py`: self-contained instance
  formulas, bounded candidate list, rational checks, and reproduction entry.
  It reuses the explicit old-portfolio constructor and independent row
  evaluator in the earlier owned experiment files.
- `CODEX_SKEPTIC__MULTIDATE_TABLE.json`: all sixty rational rewards.
- `CODEX_SKEPTIC__MULTIDATE_OLD_PORTFOLIO.json.gz`: every old law and its
  exact unrestricted cap and payoff.
- `CODEX_SKEPTIC__MULTIDATE_PROFILE_CERTIFICATE.json.gz`: accepted new
  profile, table, payoffs, caps, and debts.
- `CODEX_SKEPTIC__MULTIDATE_REPORT.json`: both tested profiles, phase
  identities, exact margins, and all reward-box endpoints.

Verdict: no new sure-owner class survives the source audit. The bounded
fallback instead gives one explicit, nonstationary full-response construction
at a four-active table and an exact positive-volume fixed-accuracy portfolio
refinement. It uses familiar cyclic mathematics and is not advertised as a
new UE class, a new universal producer, a counterexample, or an exportable
frontier advance. The useful restriction is literal: stationary policies
cannot supply even the tested accuracy anywhere in B, whereas the supplied
15-date actual policy does. The all-behavior infimum at the central table is
zero by the independently displayed infinite cycle, not inferred from a
finite search.

Next requested check, if this regression is later reused: independently
verify the rational cycle and the stationary-floor transfer against the
explicit table. No continuation of this search tranche is requested.
