# Independent check of the reset-rank family's stationary equilibrium

Reviewer: CODEX_HILBERT.

**Verdict: PASS.** The displayed stationary strategy is exact terminal Nash
against every complete behavioral deviation throughout the stated parameter
range. Its displayed payoff is a uniform-equilibrium payoff. No mathematical
correction is required. This solves the regression family; it is not a new
general stationary consumer or evidence for a positive-gap table.

Reviewed author proof:
`notes/CODEX_FRECHET_CYCLE__RESET_RANK_FAMILY_STATIONARY_EQUILIBRIUM.md`,
SHA-256 b5cdca10ccfc2fb58553af22309e8878d13ed1adce48b699f40614219911f80a.
The table was independently read and calculated first from
`notes/CODEX_FRECHET_CYCLE__QUADRATIC_FULL_BOX_BARRIER_RESET_RANK_TEST.md`,
SHA-256 668368fc2ee6aa3f4a6a41342ef626bc81302e9942e9d04c1acbd403c4e35b40.
Only after completing the independent cap calculation did I read the entire
230-line strategy proof. No Lean build was run.

## 1. Exact rewards, root, and payoff

For β>0 and a>max(1,β), the own singletons are (1,0,0,0); the exceptional
outsider singleton reward is r_1({0})=a; all other outsider singleton
rewards are −a. On coalitions of size at least two,

    r_i(S)=β ε_i(2·1_(i∈S)−1)(2·1_((i+1)∈S)−1),
    ε=(1,1,1,−1),

with cyclic indices and Never payoff zero. This agrees with the full family
definition, not only a selected coalition subtable.

Write

    p=(a−β)/(a+β),       t=(a+β)/(a+3β),
    q=(1,p,t,0),
    ρ=(1−p)(1−t)=4β²/((a+β)(a+3β)),
    g=β(a−β)/(a+3β).

Both p,t are strictly between zero and one, and 0<ρ<1. Every off-path live
row remains q; players 1 and 2 use independent private randomizations.
Actual prescribed absorption is certain at date zero. The payoff is

    U=(g+(1−β)ρ, g, −β, g).                            (1)

Equivalently,
U_0=β(a²−5β²+4β)/((a+β)(a+3β)). Exact symbolic enumeration of the
four players' product endpoint sums reproduced these identities and those
below. The inequalities have the elementary proofs given here; no parameter
grid or floating-point evidence is used.

## 2. Every unrestricted cap

For i=1,2,3, deleting player i leaves player 0's sure initial Quit. Hence
the value of any complete strategy is a mixture of its initial Quit and
Continue values; its later calendar behavior and Never choice cannot add a
third endpoint. Directly from the reward table,

| Player | Quit value | Continue value | Prescribed payoff/full cap |
|---|---|---|---|
| 1 | β(2t−1)=g | a−(a+β)t=g | g |
| 2 | −β | −a+(a+β)p=−β | −β |
| 3 | −β | β−(a+β)ρ=g | g |

Thus players 1 and 2 can mix as prescribed, while player 3 strictly prefers
Continue. These are complete caps, not stationary-only deviation checks.

For player 0, the possible Quit-now coalitions are {0}, {0,1}, {0,2},
{0,1,2}, with respective rewards 1, β, −β, β. All have positive
probability, so

    Q_0=U_0>−β.                                         (2)

If player 0 never Quits, stationary opponents 1 and 2 absorb almost surely.
Their first coalition is {1}, {2}, or {1,2}, giving player 0 respectively
−a, −a, or −β. Therefore its exact Never payoff N_0 satisfies

    N_0<−β<Q_0.                                         (3)

Algebraically the Continue absorbing contribution and Never payoff are

    L_0=−β(5a²−β²)/((a+β)(a+3β)),
    N_0=L_0/(1−ρ)=−β(5a²−β²)/(a²+4aβ−β²).

For every finite n≥0, the complete strategy Quit at date n has value

    F_0(n)=N_0(1−ρⁿ)+ρⁿQ_0.                            (4)

It is maximized at n=0 by (3). The limit is N_0 and the literal Never
strategy also gives N_0. Every independent behavioral replacement is a
mixture of complete stopping dates along the unique live public history;
its expected payoff is therefore at most Q_0. This checks arbitrary late
deadlines, arbitrary time-dependent hazards, private mixtures, and Never.

All four caps equal (1), so the exact full-debt vector is (0,0,0,0).
The author's Section 2 full-cap formula and Sections 3–4 calculations agree
with this independent derivation, including the a=2,β=1 table.

A useful signed boundary check is a=3,β=2: U_0=−2/15<0 while
N_0=−82/29<−2. Never need not give player 0 zero against absorbing
opponents. Thus imposing a nonnegative owner payoff would wrongly discard
valid members of the family; the proof does not impose it.

## 3. Uniform payoff and inspected consumers

Joint all-Continue mass is zero; the four opponent all-Continue masses are
(ρ,0,0,0), strictly below one. Equation (1) is the actual stationary
fixed point, and the cap calculation implies exact endpoint Nash at that
same point. Every hypothesis of
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` is thus
literal. The conclusion has the fixed target U and covers all behavioral
deviations. This is exactly the source cited in the author's Section 5.

I inspected that theorem, its endpoint/fixed-point and boundary definitions,
and `isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary` in the
same file. The exact full-cap declarations inspected in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean` were
`quittingBestReplyValue_stationary`,
`quittingStationaryUnilateralCap_eq_max_div`, and
`quittingTerminalPayoff_update_stationary_le_cap`.

Uniformity is not inferred merely from prescribed immediate absorption:
player 0 can cancel that absorption. What controls its arbitrary replacement
is opponents' geometric survival ρⁿ, independently of its own law. Other
players still face sure player 0. The named compiler supplies the complete
finite-horizon payoff contract, not merely convergence for each fixed reply.

## 4. Source scope and the barrier interpretation

This is an explicit parameterized table-to-strategy construction inside the
existing stationary endpoint interface. It introduces no stronger consumer,
new general strategy class, or reduction of the hard arbitrary-table source.
The closed formula is useful durable mathematics, particularly because the
family has no pure absorbing-coalition Nash profile, but its present role is
to finish the regression-fixture check.

One should not overstate source duplication in the other direction. The
coarser `QuittingSingleAnchorInducedDominance` screen in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingleAnchorArbitraryCompletionEscape.lean`
requires the owner's Quit value to dominate every coalition excluding it.
That screen fails at this selected root:

    r_0({2,3})=β,
    Q_0−β=4β²(1−a−2β)/((a+β)(a+3β))<0.

The coalition {2,3} is impossible under the selected opponents because
player 3 always Continues. The valid cap calculation uses their actual
product law, not this unnecessary pointwise dominance assumption. Thus the
new formula is not merely an application of that stronger raw-table screen;
it is nonetheless fully within the already checked general stationary
endpoint/cap compiler.

Finally, the quadratic reset-rank lemma can remain a valid general statement
about globally monotone quadratics. Its displayed family, however, is now
known to have zero global behavioral gap. No sound positive barrier of ANY
degree can exist for it. Therefore the family cannot demonstrate that richer
negative certificates are needed to find a counterexample. This corrects its
research interpretation without invalidating the independent reset-rank
linear-algebra argument. No export or further family expansion is suggested
by this check.
