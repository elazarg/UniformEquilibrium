# Extremal reward tables: active terminal laws and a one-player normal certificate

Owner: `CODEX_HILBERT`.

Status: **ordinary mathematical proof, internal and not independently reviewed**.
The extremal-table separation argument is valid without attainment of the
profile infimum or of any best-response cap. Its proposed 60-vector conclusion
improves to at most 15 limiting law differences belonging to one player.
This is a necessary condition for a positive local maximum of the unrestricted
exploitability value on the normalized reward cube. It neither produces a
positive-gap game nor proves that the value vanishes. No Lean work or export
is claimed.

Follow-up status: Sections 7–15 add the correct MAX-minimum singleton-margin
adapter, an exact failed singleton-competitor test, and a proof that every
positive MAX-minimum has two full-gap debtors. Sections 12–13 co-realize
their responses and give an actual two-player lowering criterion, followed
by a finite exact cross-harm obstruction to a generic local descent.
Section 14 shows that imposing the whole actual replacement-rectangle lower
bound still need not expose a third debtor on its minimum level.
Section 15 gives a GLOBAL stationary-class obstruction: a positive reward
normal certificate can satisfy every stationary and pure-coalition screen
while lacking genuine unrestricted-minimum source provenance.
The SUM-objective common-law argument excludes simultaneous saturation of all four averaged caps, but
remains a proof draft. No result supplies an improving reward perturbation
or a contradiction to a general positive extremum. Sections 1–6 remain frozen.

## 1. Question, finite data, and source audit

There are four players I = {0,1,2,3}, fifteen nonempty quitting coalitions
C = 2ᴵ ∖ {∅}, and one additional terminal outcome ∞ for Never. A reward table
r belongs to R = [−1,1]^(I×C); Never pays zero to everyone. Until absorption,
players see the unique public all-Continue history and use independent
behavioral randomization. A deviation replaces one complete behavioral
strategy. All payoffs below are expected terminal payoffs, including zero on
Never. No public correlation device, bounded controller, or finite-clock
restriction is imposed.

Let Σ be the common space of actual behavioral profiles, independent of r.
For σ ∈ Σ, let μσ be its probability law on C ∪ {∞}. For a player i and a
complete deviation τᵢ, let νσ,i,τ be the terminal law after that deviation.
Define a vector vσ,i,τ ∈ ℝ^(I×C) by

    vσ,i,τ(j,S) = 0                         if j ≠ i,
    vσ,i,τ(i,S) = νσ,i,τ(S) − μσ(S)         if j = i.

Thus v·r is exactly the deviator's expected terminal gain. Write

    Vσ = {vσ,i,τ : i ∈ I, τᵢ any complete behavioral deviation},
    fσ(r) = sup {v·r : v ∈ Vσ},
    η(r) = inf {fσ(r) : σ ∈ Σ}.

The unchanged strategy is allowed, so 0 ∈ Vσ and fσ ≥ 0. The vectors have
ℓ¹ norm at most 2. Every fσ and η is 2-Lipschitz in the uniform norm, and
η(ar) = aη(r) for a ≥ 0. The functions fσ are convex support functions;
convexity of their infimum η is neither assumed nor inferred.

The question is conditional: suppose r* is a local maximum of η relative to
R, with γ = η(r*) > 0. What actual-law restrictions does this impose? A
global positive maximum exists if any positive-gap reward table exists:
positive scaling puts such a table in R, and Lipschitz continuity gives
attainment of the maximum on compact R. This is attainment in reward space,
not in profile space. Also γ ≤ 1 at a global maximum: the all-Never profile
has exploitability maxᵢ max(0,rᵢ({i})) ≤ 1.

Bounded source inspection used the semantic waist and reward-robustness route
in `docs/FRONTIER.md`. Declarations read under their imports were:

- `quittingUniformEquilibriumPayoffConjecture` in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`: the open target.
- `quittingTerminalPayoff` in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Asymptotic.lean`:
  the finite reward-weighted absorption-mass formula, with zero Never payoff.
- `quittingTerminalExploitabilityInf`,
  `hasTerminalExploitabilityGap_of_lt_quittingTerminalExploitabilityInf`, and
  `quittingTerminalExploitabilityInf_pos_of_no_uniformEquilibriumPayoff` in
  `UniformEquilibrium/Quitting/Terminal/TerminalDebtPrefixDescent.lean`.
- `HasTerminalExploitabilityGap` and
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
- `abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close` and
  `quittingTerminalExploitabilityInf_scaleQuittingReward` in
  `Research/Quitting/TerminalExploitabilityRewardRobustness.lean`.

These are source inspections, not a Lean build or axiom audit performed here.
Narrow searches in the terminal and robustness files located the exact
supremum/infimum definitions and existing strict-gap caveat. A narrow search
of `Literature/` for extremal reward and normal-cone claims found no directly
used paper result. `Literature/README.md` was read; no literature theorem is
invoked. The earlier conference note
[`CODEX_ROOT__GENERIC_REWARD_REDUCTION_FOR_FIN4.md`](CODEX_ROOT__GENERIC_REWARD_REDUCTION_FOR_FIN4.md)
records the different dense-class consequence of reward robustness.

## 2. The correct limiting active family

For ε > 0 define Aε to contain exactly the vectors v ∈ Vσ for which some
actual profile σ satisfies

    fσ(r*) ≤ γ + ε,
    v·r* ≥ fσ(r*) − ε.                                      (1)

Both inequalities use the same actual σ. The response in (1) is approximate
and need not attain a cap. Set

    K = ⋂[ε > 0] closure(Aε).                                (2)

All closures are in finite-dimensional reward-coordinate space. The sets
closure(Aε) are nested, nonempty compact subsets of the ℓ¹ ball of radius 2.
Nonemptiness follows by first choosing an ε-near-minimizing actual profile
and then an ε-near-maximizing actual response. Therefore K is nonempty and
compact. Equivalently, v ∈ K precisely when v is the limit of vₙ ∈ Vσₙ with

    fσₙ(r*) → γ,
    fσₙ(r*) − vₙ·r* → 0.                                   (3)

Every v ∈ K has

    v·r* = γ,       ‖v‖₁ ≤ 2,                              (4)

and is supported on one player's fifteen coordinates. The latter property
is closed because it is a finite union of coordinate subspaces. Since γ > 0,
no member of K is zero, so its player is unique. Write Kᵢ for its part
supported on player i.

K does not assert that different vectors use a common profile. A sequence
of profiles need not converge to an actual minimizer. Each vector separately
retains the approximation provenance (3); nothing stronger is built into (2).

## 3. Separation theorem, including all approximation quantifiers

Let N be the outward normal cone of R at r*:

    N = {g : g·(r − r*) ≤ 0 for every r ∈ R}.

Coordinatewise this says gₖ = 0 when |r*ₖ| < 1, gₖ ≥ 0 when r*ₖ = 1, and
gₖ ≤ 0 when r*ₖ = −1. Let T be its polar cone, the feasible infinitesimal
directions into the cube. Every d ∈ T has r* + td ∈ R for all sufficiently
small t ≥ 0, since the cube has finitely many coordinates.

**Theorem 1.** If r* is a positive local maximum as above, then

    conv(K) ∩ N ≠ ∅.                                       (5)

**Proof.** Suppose H = conv(K) is disjoint from N. H is compact and N is a
closed convex cone. Choose a closest pair p ∈ H, n ∈ N and set d = p − n.
The positive distance implies d ≠ 0. The minimizing-pair inequalities give

    d·h ≥ d·p    for h ∈ H,
    d·z ≤ d·n    for z ∈ N.

The cone property, by taking z = 0 and z = 2n, gives d·n = 0; scaling any
z ∈ N then gives d·z ≤ 0. Consequently d ∈ T and

    min[v ∈ K] d·v ≥ ‖d‖₂² > 0.                            (6)

Fix c > 0 smaller than the minimum in (6). There is ε₀ > 0 such that

    d·v ≥ c for every v ∈ Aε₀.                             (7)

Otherwise choose εₙ ↓ 0 and vₙ ∈ Aεₙ violating (7). A convergent subsequence
of the bounded vₙ has limit in K, contradicting (6). This is the uniform
step that prevents the profile family from escaping the separator.

Put L = 2‖d‖∞ > 0. Choose t > 0 so small that r* + td lies in the local
maximum neighborhood inside R, Lt ≤ ε₀/2, and tc/2 ≤ ε₀. Consider an
arbitrary actual profile σ.

If fσ(r*) > γ + ε₀, the Lipschitz bound gives

    fσ(r* + td) > γ + ε₀ − Lt ≥ γ + ε₀/2.                  (8)

If fσ(r*) ≤ γ + ε₀, choose an actual response v ∈ Vσ with

    v·r* ≥ fσ(r*) − tc/2.

Such a response exists from the definition of the supremum. Its error is
at most ε₀, so v ∈ Aε₀ and (7) applies. Hence

    fσ(r* + td) ≥ v·(r* + td)
                 ≥ fσ(r*) − tc/2 + tc
                 ≥ γ + tc/2.                              (9)

Taking the infimum of (8)–(9) over every actual σ gives

    η(r* + td) ≥ γ + min(ε₀/2,tc/2) > γ,

contradicting local maximality. This proves (5). ∎

Notice what the argument does not do: it never picks one response attaining
every cap, never interchanges infimum and supremum, and never takes a convex
combination of profiles as an executable strategy.

**Corollary 2.** There are m ≤ 60, v¹,…,vᵐ ∈ K, and nonnegative weights
αₐ summing to one such that g = Σₐ αₐvᵃ ∈ N. Moreover

    r*·g = ‖g‖₁ = γ > 0.                                  (10)

Indeed, K lies in the affine hyperplane r*·v = γ, of dimension at most 59;
the finite-dimensional convex-hull reduction therefore needs at most 60
points. Equation (10) uses (4) and the explicit cube normal signs. The
hyperplane is proper since γ > 0 forces r* ≠ 0.

## 4. The player blocks sharpen 60 to 15

**Theorem 3.** There is one player i, m ≤ 15, points w¹,…,wᵐ ∈ Kᵢ, and
weights αₐ ≥ 0 summing to one such that h = Σₐ αₐwᵃ lies in N. In particular

    h is supported on player i,
    r*ᵢ·hᵢ = ‖hᵢ‖₁ = γ.                                  (11)

**Proof.** Start with Corollary 2 and group its terms by player. Let λᵢ be
the total weight for player i, and gᵢ the corresponding coordinate block.
At least one λᵢ is positive. Since the cube normal cone is the product of
its coordinate cones, retaining only gᵢ and dividing it by λᵢ stays in N.
That vector is a convex combination of elements of Kᵢ. Each such element
has r*ᵢ·wᵢ = γ, so the combination is nonzero and satisfies (11).

The relevant Kᵢ lies in a proper affine hyperplane in ℝ¹⁵ of dimension at
most 14. Convex-hull reduction inside that block gives at most 15 elements.
For completeness, this reduction repeatedly removes a coefficient: if more
than 15 positively weighted points remain, they have an affine dependence
Σ βₐwᵃ = 0, Σ βₐ = 0; subtract the largest permitted multiple of β from
the coefficients so one becomes zero and none becomes negative. ∎

This is a real improvement over generic sixty-dimensional stationarity.
It localizes the necessary law balance to a single player's reward vector.
It does not say that this player is the unique debtor, nor that one of the
individual wᵃ already belongs to N.

## 5. Full-law interpretation and its precise limitation

For each wᵃ in Theorem 3, pass to a subsequence in its realizing family (3)
so the two full terminal laws also converge in the sixteen-outcome simplex.
Denote the limits by μᵃ and νᵃ. Their nonempty-coalition difference is wᵃᵢ.
They are limits of actual same-source unilateral law pairs for the same i.
They need not be a unilateral pair at one limiting actual profile.

Define averaged probability laws

    μ̄ = Σₐ αₐ μᵃ,       ν̄ = Σₐ αₐ νᵃ.

Then hᵢ(S) = ν̄(S) − μ̄(S). The cube normal identities imply exactly:

- at every coalition with |r*ᵢ(S)| < 1, ν̄(S) = μ̄(S);
- at reward +1 coalitions, ν̄(S) ≥ μ̄(S);
- at reward −1 coalitions, ν̄(S) ≤ μ̄(S).

Put a = Σ[r*ᵢ(S)=1](ν̄(S)−μ̄(S)) and
b = Σ[r*ᵢ(S)=−1](μ̄(S)−ν̄(S)). Then

    a ≥ 0,   b ≥ 0,   a + b = γ,
    ν̄(∞) − μ̄(∞) = b − a,
    TV(ν̄,μ̄) = max(a,b) ∈ [γ/2,γ].                         (12)

The total-variation convention is half the ℓ¹ distance on all sixteen
outcomes. Thus at least one saturated reward coordinate in this one player
block has averaged law change of magnitude at least γ/15. Formula (12)
also exposes why subtracting a constant from all nonempty rewards is not a
valid strategic invariance: the average Never masses can differ.

These are probability-law consequences beyond the bare normal equation.
Their current consumer is a necessary-condition search test: an alleged
positive extremal reward table must admit this one-player, at-most-15-term
balance among its globally near-minimizing actual law pairs. A verified
separation of the *complete* Kᵢ from the corresponding normal cone for every
i would rule out positive local maximality and produce the improving
direction used above. A finite sampled subset cannot certify that separation
for the complete family. Conversely, finding a balanced sample is not a
positive lower bound on η.

## 6. Exact tests and unresolved conclusion

The following toy portfolio refutes only a generic corner inference. On
[−1,1]² put

    F(x,y) = min(|x|, |x+y|/2, |x−y|/2).

Each constituent is a support function of finitely many vectors of ℓ¹ norm
at most 2, and F is nonnegative, Lipschitz, and positively homogeneous.
Since min(|x+y|,|x−y|) = ||x|−|y||, one obtains max F = 1/2, attained at
(±1,0), while F vanishes at all four corners. At (1,0) the active gradients
(1/2,1/2) and (1/2,−1/2) average to the outward normal (1/2,0). Neither
individual active gradient is normal. This tests both the need for convex
combination and the failure of generic corner reduction. It is not an
actual quitting-game η and does not refute a special corner theorem for η.

Actual unilateral law provenance by itself is compatible with a nonzero
normal, even at every gain in the admissible range (0,1]. Fix 0 < c ≤ 1,
let player 1 quit surely at date 1, and let player 0 quit at date 0 with
probability q = 1 − c/2 and otherwise Never; players 2 and 3 Never. Set
r₀({0}) = 1 and r₀({1}) = −1; let every other coordinate be zero.
The baseline law is q e_{0} + (1−q)e_{1}. Player 0's deviation to Quit
surely at date 0 has law e_{0}, giving the literal difference

    (c/2)(e_(0,{0}) − e_(0,{1})).

This is a cube normal of ℓ¹ norm c and an exact cap response with gain c.
All other players' debts are zero, so the actual profile has fσ = c. But
the game has η = 0: player 0 quitting at date 0 with all others Never is
terminal Nash. Thus full probability-law provenance, player locality, exact
cap attainment, the normal signs, and the bound c ≤ 1 do not themselves
forbid the pattern. What fails is specifically global near-minimality: this
profile remains c above the true infimum. The example does not satisfy
(1)–(3) with γ = c and does not falsify any theorem above.

Proved: the approximation-safe separation theorem, the one-player 15-term
certificate, and the averaged-law restrictions (12).

Open: whether actual global near-minimality imposes an additional constraint
on those law pairs that makes the certificate impossible at positive γ.
The current proof supplies no such constraint and no contradiction. In
particular, its averaged laws are not silently treated as one actual profile
or one simultaneously optimal family of responses.

Concrete requested check: independently verify the uniform step (7), the
two profile regimes (8)–(9), and the block reduction in Theorem 3; then try
to use the exact same-source provenance of each law pair, together with
global near-minimality, to restrict the possible interior-coordinate
cancellations in their convex mixture. No export is warranted before that
review, and no closure of the finite-quitting conjecture is claimed.

## 7. Follow-up: what global max-debt minimality really adds

Sections 1–6 are the frozen initial proof. Sections 7–10 are a separate
follow-up test, in ordinary mathematics and not independently reviewed.
The test finds a usable existing MAX-debt singleton margin, an exact limit
to what that margin plus elementary competitors can prove, and a conditional
structural exclusion for the alternative SUM-debt reward maximum.

### 7.1 The objectives must remain distinct

For a fixed table write

    F(σ) = maxᵢ dᵢ(σ),       D(σ) = Σᵢ dᵢ(σ),
    γ = infσ F(σ),           Δ = infσ D(σ).

Nonnegative debts give γ ≤ Δ ≤ 4γ. This compares the values, not their
minimizers. A sequence with F(σₙ) → γ only gives

    Δ ≤ liminf D(σₙ) ≤ limsup D(σₙ) ≤ 4γ.                  (13)

It need not make D(σₙ) tend to Δ. The elementary obstruction to inferring
otherwise is already visible in the compact abstract debt set

    {(3/5,3/5,0,0), (9/10,0,0,0)}.

Its MAX minimizer is the first vector and its SUM minimizer the second.
This is an abstract nonnegative-debt example, not an actual positive-gap
quitting game. It refutes the order-theoretic inference, without pretending
to supply the presently unknown positive-gap game.

The existing source theorem
`quittingTerminalExploitabilityInf_sq_div_two_bound_le_debtSumInf_sub`
in `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticDebtRatioSeparation.lean`
gives the stronger genuine-game value comparison

    Δ − γ ≥ γ²/2                                            (14)

for normalized rewards and γ > 0. I inspected its proof: it mixes one
player's stopping law toward a near best response, using own-debt linearity
and the other players' debt chord bounds. Thus any MAX-minimizing source
limit with selected debt γ has total debt on the other three coordinates
at least γ²/2. This retains genuine simultaneous other-player debt, but does
not turn that source into a SUM minimizer.

The existing lexicographic constructor
`exists_lexicographicallyNearMinimal_terminalProfile` in
`UniformEquilibrium/Quitting/Terminal/TerminalDebtPrefixDescent.lean`
minimizes total debt *inside a MAX-debt sublevel*. Its accompanying
`not_hasLexicographicallyNearMinimalSingletonGap` excludes a prescribed
singleton shortfall on a positive-debt coordinate of such a family. Neither
declaration identifies the unrestricted SUM minimum with that secondary
minimum, or permits restricting the complete K in Section 2 to one chosen
lexicographic subfamily. The separation proof needs every sufficiently
near-MAX-minimizing competitor, unless a new domination argument removes it.

### 7.2 A direct MAX margin avoids that mismatch for one useful claim

The theorem `minimumTerminalSemantic_exploitabilitySingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`
already proves the exact MAX-objective statement:

    at every positive MAX-minimizing semantic pair (U,B),
    Bᵢ − sᵢ ≥ γ for every i,      sᵢ = rᵢ({i}).             (15)

I read its proof under the file's imports. It uses the MAX-debt auxiliary
Nash absorption bound, forces all-Continue below the critical cap-shift
threshold, and then contradicts an insufficient singleton margin by shifting
one cap coordinate. It does not assume SUM minimality.

For every realizing family of a vector in K, pass to a further subsequence
so the complete bounded payoff/cap pairs converge. Their limit is in the
terminal-semantic carrier and has MAX debt γ: the objective is continuous
on this carrier, the actual infimum lower-bounds its closure, and the source
values tend to γ. Therefore (15) applies to these exact K-source limits.
Since each dᵢ ≤ γ,

    Uᵢ ≥ sᵢ + γ − dᵢ ≥ sᵢ for every i.                    (16)

For the active player i of a vector in K, dᵢ = γ. Its response-law limit
attains the limiting cap in payoff, because its gain tends to γ. Consequently
the one-player certificate of Section 5 satisfies

    μ̄·rᵢ ≥ sᵢ,       ν̄·rᵢ ≥ sᵢ + γ.                  (17)

Also (15) and Bᵢ ≤ 1 force sᵢ ≤ 1−γ for every player. Thus no own singleton
reward can be +1 at a positive-gap table. In the certificate's selected
player block, if sᵢ > −1, the singleton reward coordinate is interior and
normality forces

    ν̄({i}) = μ̄({i}).                                    (18)

If sᵢ = −1, only the inequality ν̄({i}) ≤ μ̄({i}) follows. These are real
additional source restrictions, not assumptions imported from SUM minima.

## 8. Exact failure of the singleton-competitor attack

The all-Never profile and the four pure singleton profiles give the necessary
competitor inequalities

    γ ≤ maxᵢ max(0,sᵢ),
    γ ≤ max(0, −sⱼ, max[i ≠ j](rᵢ({i,j})−rᵢ({j})))
       for every singleton owner j.                       (19)

The second formula is exact: the owner can switch to Never, and an outsider
can join at date zero; every other pure date has one of those payoff modes.

Here is a normalized rational Fin4 table showing that (15)–(19), genuine
same-source cap laws, and the one-player normal certificate do not suffice
to exclude a positive proposed level. All unlisted coordinates are zero:

| Player | Nonzero reward coordinates |
| --- | --- |
| 0 | r₀({0})=1/4; r₀({1})=−1; r₀({0,1})=1; r₀({0,2})=r₀({0,3})=1/4 |
| 1 | r₁({0})=2/7 |
| 2 | r₂({0,2})=r₂({1,2})=r₂({0,1,2})=1/4 |
| 3 | r₃({1,3})=r₃({0,1,3})=1/4 |

Let σ have player 1 Quit surely at date zero, player 0 Quit at zero with
probability 7/8 and otherwise Never, and players 2 and 3 Never. Exact values:

    U(σ) = (3/4,0,0,0),
    B(σ) = (1,1/4,1/4,1/4),
    d(σ) = (1/4,1/4,1/4,1/4),
    s    = (1/4,0,0,0).                                   (20)

At the proposed level c = 1/4, every MAX singleton margin Bᵢ−sᵢ ≥ c and
every prescribed margin Uᵢ ≥ sᵢ holds. All other-coordinate debt floors from
(14) also hold numerically. Player 0's exact cap response is Quit surely at
zero, with law difference

    (1/8)(e_(0,{0,1}) − e_(0,{1})).                       (21)

This is a cube normal with gain and ℓ¹ norm c, and it preserves own singleton
mass as required by (18). The all-Never and four pure-singleton competitors
have MAX debts respectively

    1/4,       1/4, 2, 1/4, 1/4,

so every inequality in (19) passes at c. Nevertheless the pure coalition
{0,2} quitting at zero is exact terminal Nash, with payoff (1/4,0,1/4,0).
Each quitter loses 1/4 by withdrawing, and neither outsider gains by joining.
Therefore the true γ and Δ of this table are zero.

This is not a counterexample to a theorem about genuine global minimizers:
σ is c above the true MAX infimum. It is an exact counterexample to the
proposed *test based only on the displayed global-margin consequences and
the five simple competitors*. Those numerical consequences do not retain
the full global-minimizing quantifier.

Verification used Python `Fraction` arithmetic, enumerating all independent
terminal action profiles and the unilateral modes {date zero, date one,
Never}. Against every displayed source the opponents use only zero or Never,
so date one represents all strictly later finite deviations. This finite
enumeration therefore gives unrestricted behavioral caps by pure-time
extremality. The table and all values needed to reproduce the calculation
are displayed above; no floating-point evidence is used.

## 9. A SUM-debt normal certificate retains a common baseline law

This is a change of objective, not a new claim about K. Suppose r† is a
positive local maximum of Δ(r) = infσ Σᵢ dᵢʳ(σ) on the normalized cube;
write Δ = Δ(r†) and γ = η(r†). The comparison Δ ≤ 4γ makes γ positive.

For a fixed actual σ, the sum of debts is a support function of response
tuples: choose one complete deviation τᵢ separately for each i and place
its terminal-law difference from μσ in player i's coordinate block. These
are four unilateral counterfactual profiles with the *same* baseline σ,
not one simultaneous deviation. The support vector has ℓ¹ norm at most 8.
The supremum over tuples is the sum of the four caps minus prescribed payoffs.

Apply the proof of Theorem 1 with these tuples and Lipschitz bound 8, using
actual near-SUM-minimizing sources. There are at most 60 limiting active
tuples in a normal convex combination. After extracting their full laws and
averaging with those same weights, its data are one common baseline law μ
and four response laws νᵢ on the sixteen outcomes. Write

    Uᵢ = μ·r†ᵢ,       Bᵢ = νᵢ·r†ᵢ,
    δᵢ = Bᵢ−Uᵢ ≥ 0,  Σᵢ δᵢ = Δ.                        (22)

Each tuple's four cap errors are nonnegative and their sum tends to zero,
so each response really attains its source's limiting cap in payoff. The
common μ is essential: the four blocks cannot be averaged with unrelated
weights or projected to a single player's certificate.

Normality and its block signs imply

    ‖(νᵢ−μ)|C‖₁ = δᵢ,
    TV(νᵢ,μ) ≤ δᵢ.                                      (23)

The second inequality includes Never. Indeed the sum of nonempty-coordinate
differences determines the Never difference; its magnitude is at most the
nonempty ℓ¹ norm. Thus full ℓ¹ distance is at most 2δᵢ. This does not claim
that any of the averaged laws is a jointly executable strategy profile.

Now SUM minimality is valid for every limiting source. The inspected theorem
`minimumTerminalSemantic_singletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`
therefore gives, before and after averaging,

    Bᵢ ≥ sᵢ + Δ for every i.                              (24)

In particular Δ < 1. If Δ ≥ 1, then Bᵢ ≤ 1 implies sᵢ ≤ 0 for all i,
so all-Never is terminal Nash and Δ = 0, a contradiction. This strict bound
is used only to make the structural conclusion below nonvacuous; no constant
optimization is pursued.

## 10. Structural exclusion: all four averaged caps cannot reach the ceiling

For each nonempty coalition S consider the actual profile that Quits at
date zero precisely on S. Its debt is at least γ, and every unilateral cap
is at most 1. Hence at least one player i satisfies

    r†ᵢ(S) ≤ 1−γ.                                        (25)

At Never the payoff is zero; because γ ≤ 1 the same inequality holds there
for any chosen player. Assign each of the sixteen outcomes to one player
satisfying (25), giving a partition E₀,…,E₃. This is an actual pure-profile
competitor constraint, rather than a property of arbitrary law differences.

Use the common baseline law and (23):

    1 = Σᵢ μ(Eᵢ)
      ≤ Σᵢ νᵢ(Eᵢ) + Σᵢ TV(νᵢ,μ)
      ≤ Σᵢ νᵢ(Eᵢ) + Δ.

Therefore

    Σᵢ νᵢ(Eᵢ) ≥ 1−Δ > 0.                               (26)

Some response law places at least (1−Δ)/4 mass in its assigned set, where
its own reward is at least γ below the ceiling. The selected player need
not have positive δᵢ; it is one of the four responses in the SUM certificate.
Equivalently, since 1−r†ᵢ is nonnegative on all outcomes and at least γ on Eᵢ,

    Σᵢ (1−Bᵢ) ≥ γ(1−Δ) > 0.                             (27)

This excludes the face B₀=B₁=B₂=B₃=1 at every positive SUM-debt reward
maximum. More concretely, a proposed complete normal certificate whose four
response laws all avoid their assigned low-payoff coalition sets is
impossible. The test uses finitely many coalition assignments and the four
supplied law vectors, although their provenance from globally near-minimizing
profiles is still an infinite-profile obligation.

This is the structural consequence of the SUM pivot. It retains common-source
law data and a real global-competitor constraint. It does not exclude every
positive normal certificate: the response laws can pay the strictly positive
mass requirement in (26), and nothing here forbids that alternative. The
calculation is not extended into optimization of a positive upper bound.

Additional source audit for this follow-up: besides the named margin and
debt-ratio declarations above, I inspected
`quittingControllerTesterValue_eq_minimum_rawMaximumDebt` in
`UniformEquilibrium/Quitting/ControllerTester/ControllerValue.lean`, the
MAX-debt auxiliary-Nash proof in
`TerminalSemanticPlateauDynamicCostate.lean`, and the SUM-margin proof in
`TerminalSemanticAuxiliaryNashBudget.lean`. The separate stronger SUM-fiber
isolation statement in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`
was read and deliberately not transferred to MAX minimizers. No Lean build
or export was performed.

Follow-up status: the MAX-margin adapter and exact regression are complete
ordinary calculations; the SUM common-baseline and blocker-set exclusion are
a proof draft awaiting independent review. Neither yields a reward direction
that improves the full unrestricted value at a positive extremum.

Concrete next question: does actual same-source best-response provenance,
together with SUM minimality, restrict the unavoidable masses νᵢ(Eᵢ) in
(26) strongly enough to exclude their coexistence? Without such a restriction,
the extremal-table approach has a valid remaining branch and no contradiction.

## 11. Every positive MAX-minimum has two full-gap debtors

This additional source-facing result is ordinary mathematics proved here,
not a substitution of the separate finite-clock co-source existence theorem.
It concerns every minimizing carrier point, including those not attained by
an actual profile.

**Theorem 4.** Let |rᵢ(S)| ≤ M with M > 0, let γ = infσ maxᵢ dᵢ(σ) > 0,
and let (U,B) be any terminal-semantic carrier point whose maximum debt is
γ. At least two distinct players have debt exactly γ at this point.

**Proof.** Suppose instead that i uniquely attains γ. There is κ > 0 such
that dⱼ ≤ γ−κ for every j ≠ i. Choose actual profiles σₙ whose complete
payoff/cap pairs tend to (U,B). Thus dᵢ(σₙ) → γ and
limsup dⱼ(σₙ) ≤ γ−κ for j ≠ i.

Choose a complete deviation τᵢⁿ whose payoff is within εₙ of player i's cap,
where εₙ ↓ 0, and put Tₙ = (σₙ₋ᵢ,τᵢⁿ). Then dᵢ(Tₙ) ≤ εₙ, because the
player's cap is unchanged by its own replacement. Choose a fixed λ ∈ (0,1)
small enough that

    (1−λ)(γ−κ) + 2Mλ < γ.                                (28)

Such λ exists because the left side tends to γ−κ as λ tends to zero. Let
Qₙ replace only i's full stopping law by its mixture with τᵢⁿ, of weight λ.
This is an actual independently randomized behavioral strategy, as in the
checked stopping-law-mixture construction. It is not a simultaneous profile
mixture or public correlation device.

Own debt is exactly affine and every other debt is bounded by its endpoint
chord. Since every endpoint debt is at most 2M,

    dᵢ(Qₙ) = (1−λ)dᵢ(σₙ) + λdᵢ(Tₙ),
    dⱼ(Qₙ) ≤ (1−λ)dⱼ(σₙ) + 2Mλ    for j ≠ i.            (29)

Therefore limsup dᵢ(Qₙ) ≤ (1−λ)γ < γ, while (28) bounds every other
coordinate's limsup strictly below γ. There are finitely many players, so
maxⱼ dⱼ(Qₙ) < γ for all sufficiently large n. These are actual profiles,
contradicting the definition of γ. ∎

The existing declarations used in (29), inspected under their imports, are
`quittingTerminalSemanticDebt_stoppingLawMixture_eq_self` and
`quittingTerminalSemanticDebt_stoppingLawMixture_le_boundChord` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`.
Its underlying full terminal-law affinity and cap convexity proofs were also
read. A narrow search in that subtree, the MAX-debt costate file, and the
lexicographic source located no existing declaration of Theorem 4. This is
a bounded lookup statement, not an exhaustive novelty claim. The independent
`exists_quittingFiniteClockDoubleFullGapCosource` in
`Research/Quitting/FiniteClockDoubleFullGapCosource.lean` is not used: it
provides a finite-clock source, not this assertion about every minimum point.

For a Section 2 vector w ∈ Kᵢ, retain its actual source sequence and extract
a limiting complete semantic point as in Section 7. Player i has debt γ.
Theorem 4 supplies j ≠ i with limiting debt γ. Choosing near-cap responses
for j on this *same sequence*, and extracting their full laws, gives a
partner z ∈ Kⱼ with z·r* = γ. Both response-law limits share the same
baseline-law limit. In particular every MAX-minimum point has total debt
at least 2γ, a stronger statement on this fiber than the small co-debt floor
deduced from (14).

This is a genuine refinement of the variational witness provenance. It
excludes the one-debtor profile used as the deliberately weak law-only test
in Section 6. It does not exclude the Section 8 regression: that profile
has all four debts equal to 1/4, and hence passes the two-full-debtor test
while remaining above the true global minimum.

Nor does it contradict the one-player normal conclusion of Theorem 3. For
each positively weighted w one can retain a same-source partner z, but the
partner may belong to different players for different terms, and its mean
need not satisfy any cube-normal sign condition. Adding its gradient to an
existing normal mixture is not justified. The genuine remaining question is
whether joint profile perturbations can use those paired source laws to
force compatible reward-direction inequalities. Two tied debtors alone
leave that question open; no extra inert normality condition is asserted.

## 12. Two full debtors: literal co-realization and a lowering criterion

This section concerns MAX-minimizers, not the SUM-minimizing families used
by the existing paratangent extraction source. It is ordinary mathematics.

### Same-source response compatibility is available

Let γ>0 be the global infimum of maximum unrestricted debt for one fixed
finite table, bounded in absolute value by M. Suppose a minimizing carrier
point has EXACTLY two coordinates i,j of debt γ. All other debts are at
most γ−κ for some κ>0. Let σ_n be actual profiles converging in complete
payoff/cap semantics to this point. Choose arbitrary complete responses
τ_i^n and τ_j^n whose gains are within ε_n→0 of their respective caps at
the SAME σ_n.

These responses do co-realize. For every n there are four actual independent
profiles σ_n^{00}, σ_n^{10}, σ_n^{01}, σ_n^{11}, according to whether neither,
only i, only j, or both prescribed laws are replaced. Each replacement is
a complete private stopping law. The double replacement uses the product
of the two new laws, not a public mixture of the one-player endpoints.

Every corner has its complete terminal law and all unrestricted caps.
Finite-dimensional compactness extracts one common subsequence on which
ALL these corner semantics and terminal laws converge. Denote its debt
limits by D_k^{ab}. Then

    D_i^{00}=D_j^{00}=γ,
    D_i^{10}=0,  D_j^{01}=0,
    0≤D_k^{ab}≤2M.

The two one-player active law differences and the joint-replacement law
retain the same baseline at each n. No actual attainment of the minimizing
point or of a cap is needed. Conversely, averaging normal vectors from
different minimizing source families does not merge those source families
into one actual minimizing profile; that separate limitation remains.

### Actual two-player descent when cross-harm is small

Put

    A=D_i^{01},  B=D_j^{10},
    a=A−γ,       b=B−γ.

**Theorem 5.** If a_+ b_+<γ², there are fixed sufficiently small positive
weights x,y such that, for all sufficiently large n, replacing i's law by
(1−x)σ_{n,i}+xτ_i^n and j's by (1−y)σ_{n,j}+yτ_j^n produces an ACTUAL
profile with maximum unrestricted debt strictly below γ. In particular,
at a genuine minimum with exactly two active debtors every retained response
pair necessarily satisfies

    A>γ,  B>γ,  (A−γ)(B−γ)≥γ².                  (30)

**Proof.** Applying the checked one-coordinate debt chord inequality twice
bounds each coordinate of the independently mixed profile by the bilinear
interpolation of its four corner debts. Choose u,v>0 such that

    −γu+av<0,       bu−γv<0.                   (31)

Such u,v exist precisely when a_+b_+<γ²: if a,b>0 choose
b/γ<v/u<γ/a; if either is nonpositive the corresponding inequality imposes
no conflicting positive bound. Set x=tu,y=tv. The limiting chord bounds
for i and j are respectively

    γ+t(−γu+av)+t²uv(D_i^{11}−a),
    γ+t(bu−γv)+t²uv(D_j^{11}−b).

Their linear terms are strictly negative, and their quadratic terms are
bounded. All other limiting chord bounds tend to values at most γ−κ as
t→0. Choose one fixed small t>0 so all these finitely many upper bounds
are strictly below γ and x,y≤1. Convergence of the actual corner debts
then gives the same strict bounds for every sufficiently large n. These
are legal independent profiles, contradicting the definition of γ. The
contrapositive gives (30). ∎

This is an executable sufficient decrease test, not another reward normal
condition. It uses the actual caps at the cross-replacement endpoints and
retains the joint corner. It applies only when exactly two coordinates are
active at the selected minimum; with three or four active coordinates their
first-order inequalities must also be controlled.

### Source boundary

The narrow search inspected the full response fields in
`QuittingFiniteClockDoubleFullGapCosource` and the declaration
`exists_quittingFiniteClockDoubleFullGapCosource` in
`Research/Quitting/FiniteClockDoubleFullGapCosource.lean`. They supply a
literal two-response source but not a MAX-minimizing one. They are not used
as a substitute for the minimum hypothesis above.

The already checked
`quittingTerminalSemanticDebt_stoppingLawMixture_le` and
`quittingTerminalSemanticDebt_stoppingLawMixture_eq_self` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`
give the two chord bounds and exact own-debt removal. The source
`quittingStoppingLawResetProfile_comm`, the actual cube record
`QuittingStoppingLawResetCubeData`, and
`quittingTerminalPayoff_twoStoppingLawMixtures_rectangle` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawResetCube.lean`
already verify that frozen same-source replacements commute and payoffs
have the exact rectangle law. Thus literal co-realization itself is not a
new unresolved mathematical producer.

`exists_commonBase_stoppingLawDebtTangentFamily` in the neighboring
`TerminalSemanticStoppingLawTangentExtraction.lean` was also inspected.
Its near-minimality hypothesis is for SUM debt; its nonnegative total slopes
cannot silently be transferred to this MAX argument. The present fixed-t
four-corner proof avoids moving-source derivative assertions altogether.

## 13. Exact normal-certificate obstruction inside the two-response square

The following normalized rational Fin4 table shows that same-source
co-realization, two active debtors, the MAX-minimum singleton margins, the
all-Never and pure-singleton competitor screens, and a one-player normal
law certificate still do not force local descent in the response square.
It is an ACTUAL zero-global-minimum regression, not a purported positive
global minimum.

Let γ=1/4. Use players 0,1 as the two debtors and players 2,3 as other
participants. Specify every nonempty coalition payoff as follows:

    r_0({0})=−1, r_0({2})=−1,
    r_0({0,2})=1, r_0({0,3})=1/4;
    every other r_0(S)=0.

    r_1({1})=−2/7, r_1({0,2})=1;
    every other r_1(S)=0.

    r_2({2})=0;
    r_2(S)=1/4 for every other nonempty S.

    r_3({3})=1/4;
    r_3(S)=1/2 for every other nonempty S.

Prescribe player 0 to Quit at date 2, player 1 to Quit at date 0 with
probability 7/8 and Never with probability 1/8, player 2 to Quit at date 1,
and player 3 to Never. Its exact original payoff/cap/debt vectors are

    U=(−1/8, −1/4, 7/32, 1/2),
    B=( 1/8,     0,   1/4, 1/2),
    d=( 1/4,   1/4,  1/32,   0).

Player 0's full best response is Quit at date 1. Player 1's full best
response is Never. The singleton vector is (−1,−2/7,0,1/4), so B_i−s_i≥γ
for EVERY player. All-Never has exploitability γ. Pure singleton sources
for players 0,1,2,3 have exploitability at least 1,2/7,2,1/4 respectively.
Thus none of those competitor screens exposes the true smaller minimum.

The baseline law is (7/8)e_{1}+(1/8)e_{2}. Player 0's response law is
(7/8)e_{1}+(1/8)e_{02}; its difference is

    w_0=(1/8)(e_{02}−e_{2}).

Its positive coordinate has reward +1 and its negative coordinate reward
−1. Therefore it lies in the reward cube's normal cone, with
||w_0||_1=w_0·r_0=γ. Player 1's same-source difference is
(7/8)(e_{2}−e_{1}), also with gain γ, but it is not itself normal. The
joint-response law is e_{02}. All three differences thus have actual common
source provenance, not merely individually plausible probability laws.

### The full cap obstruction, not a loose chord estimate

Let x be the independent mixture weight toward player 0's date-1 response,
and y the weight toward player 1's Never response. Put Q=(1+7y)/8, the new
Never probability of player 1. Direct enumeration of pure dates 0,1,2 and
the common later-date value gives the EXACT full debts

    d_0(x,y)=(1−x)(1/4+(7/4)y),
    d_1(x,y)=(1−y)(1/4+(7/8)x),
    d_2(x,y)=d_0(x,y)/8,
    d_3(x,y)=0.                                      (32)

Thus the linear active-debt changes at (0,0) are

    −x/4+(7/4)y,       (7/8)x−y/4.

They have no common strictly negative direction with x,y≥0. This is real
cap behavior, not artificial overestimation by endpoint convexity. In fact
the origin is a strict local minimum on the whole response square: if
0≤x,y≤1/2 and (x,y)≠(0,0), then max_i d_i(x,y)>γ.

To verify the last assertion, if either weight is zero the other debtor's
formula increases strictly. If x,y>0 and both active debts were at most γ,
(32) would imply

    y≤x/[7(1−x)],      x≤2y/[7(1−y)],

hence (1−x)(1−y)≤2/49. But the stated square has product at least 1/4,
a contradiction. The cross endpoints in Theorem 5 are A=2 and B=9/8,
so their excess product is (7/4)(7/8), far on the obstructed side of (30).

At the FULL joint replacement x=y=1 every debt in (32) is zero. Both
players 0 and 2 quit together at date 1, and every player's prescribed
reward is its global reward ceiling. Equivalently pure coalition {0,2}
at date zero is an exact terminal Nash profile. Thus the game's actual
global infimum is zero. A substantial jointly coordinated change in the
two independent marginal laws can succeed even though every small change
toward these same responses fails.

An exact `Fraction` check enumerated 25 response-square profiles, all four
pure-singleton competitors, all-Never, and both displayed exact-Nash corner
realizations. It verified all payoff/cap/debt formulas. This is bounded
evidence accompanying the exact argument, not a global-minimality test.

### Outcome of this bounded attack

The optimal-response laws can be co-realized at the same actual minimizing
approximants; that compatibility is not the missing step. Theorem 5 supplies
a genuine actual decrease whenever their cross-harm product is small.
The finite regression shows that a normal selected response, even after all
the retained two-debtor and singleton checks, does not force that product
small or yield local simultaneous descent.

What would be needed next is a genuinely global argument forcing a favorable
joint replacement or another response menu at a positive MAX-minimum,
rather than only a first-order direction. The regression's zero-debt joint
corner explains why local obstruction is not evidence for a positive global
gap. No general contradiction or actual minimum-source lowering beyond
Theorem 5's explicit hypothesis has been proved here.

## 14. Even the entire actual rectangle need not expose a new minimum debtor

This is an exact finite obstruction to a RECTANGLE-ONLY inference. It is
not a positive-global-minimum example. It answers the stronger test of
requiring every actual point of the response rectangle, its joint corner,
and both nonpayer caps to be retained and screened above the proposed γ.

Keep every reward and strategy in Section 13 except the player-3 reward
column. Replace that entire column by

    r_3({3})=1/4,
    r_3({0,2})=0,
    r_3(S)=1 for every other nonempty S.

The source still has exactly two full debtors 0,1 of debt γ=1/4; player 2
still has debt 1/32, and player 3 now has prescribed payoff and cap both
one. All own singleton rewards are unchanged. Every singleton margin
B_i−s_i≥γ still holds, including player 3's margin 3/4. All-Never and all
four pure-singleton competitor screens remain valid. The same player-0
normal law difference and both same-source full best responses are retained.

On the ACTUAL independent response square, all previous debt formulas for
players 0,1,2 remain exact. Put Q=(1+7y)/8. Player 3's prescribed payoff is
1−xQ because the only zero-reward outcome is {0,2}, of probability xQ.
Its cap is exactly one: Quit at date 1 guarantees reward one, either because
player 1 has already absorbed at date zero or because player 3 joins player
2 at date 1. Hence all four full debts are

    d_0=2Q(1−x),
    d_1=(1−Q)(x+2/7),
    d_2=d_0/8,
    d_3=xQ.                                         (33)

**Exact rectangle statement.** For EVERY (x,y)∈[0,1]², the maximum of (33)
is at least γ, and equality holds ONLY at (x,y)=(0,0).

**Proof.** Suppose all four debts are at most γ. If Q=1, the first bound
requires x≥7/8, making d_3≥7/8>γ. Otherwise Q<1. The first two bounds give

    1−1/(8Q) ≤ x ≤ 1/[4(1−Q)]−2/7.

Their compatibility is equivalent to

    72Q²−65Q+7=(Q−1/8)(72Q−56)≥0.

Since Q≥1/8, either Q=1/8 or Q≥7/9. In the first case y=0 and the second
debt bound forces x=0. In the second case,

    d_3=xQ≥Q−1/8≥47/72>1/4,

a contradiction. Thus the only point with maximum debt at most γ is the
original source. At that source its value is exactly γ. ∎

At the full joint response x=y=1, both original debtors and player 2 have
zero debt, but player 3 has debt one. This is an actual transfer to a new
debtor from the same original source. It takes place above, not on, the
minimum level of the response rectangle. There is no path on that minimum
level leading to a third/fourth active debtor: that level is a singleton.
Thus compactness or continuity of the literal rectangle does not supply
the desired minimum-level connectedness.

The complete game still has global minimum zero. Let players 0,2,3 quit
together at date zero and player 1 Never. Players 0 and 1 get zero and
cannot change the other sure quitters' coalition to improve; player 2 gets
its maximal reward 1/4 and player 3 its maximal reward one. This is an
exact terminal Nash profile. It lies outside the two-response rectangle
because player 3's previously frozen law has changed.

The finite obstruction therefore retains MORE than local stationarity:
every response-square profile, both nonpayer caps, the joint corner, all
singleton-margin and simple-competitor screens, and the normal selected
law witness are genuine and explicitly evaluated. What it cannot retain is
global minimality over profiles outside that square. That is precisely the
missing information, rather than a failure to co-realize the two original
responses.

For a genuine positive global minimum, the same observed joint-corner debt
transfer would motivate adding the new player's response law to the menu.
There is no proof here that iterating such menu enlargement terminates,
preserves a minimum-level carrier component, or yields a uniform full-cap
certificate. The current result rules out deriving those conclusions from
the one actual rectangle alone.

## 15. Global stationary screens and a positive normal certificate are consistent

This is a bounded GLOBAL strategy-class test, not another local replacement
cube. Its conclusion is deliberately about a relaxation: complete stationary
screens plus a reward-normal certificate do not force zero. They still lack
the requirement that their source profiles minimize over ALL actual profiles.
No further sharpening of the displayed constants is intended.

### Existing complete stationary source API

The inspected declarations are
`quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap`
and
`quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never`
in `UniformEquilibrium/Quitting/Stationary/CompleteBehavioralCap.lean`,
the boundary definition and attainment/verifier declarations in
`FullRateStationaryVerifier.lean`, and `quittingFaceNumerator` in
`FaceNumerator.lean`, in the same directory. The selected cap and pure-time
formula in `SnellCap.lean` were also inspected. These already establish the
complete behavioral cap; no fresh cap theorem is claimed here.

For hazards q, write c_i=1−q_i, α=1−∏c_i, β_i=1−∏_{j≠i}c_j. Let Q_i
be the immediate-Quit payoff and C_i the unconditional absorbing contribution
when i Continues. Put F_i=β_iQ_i−C_i, the checked face numerator. For β_i>0,

    U_i=[q_iQ_i+c_iC_i]/α,
    B_i=max(Q_i,C_i/β_i),
    d_i=max(c_iF_i/α, −q_iF_i/(αβ_i)).           (34)

Thus d_i≥γ is the disjunction c_iF_i≥γα or −q_iF_i≥γαβ_i, but ONLY on
the positive-β_i stratum. If β_i=0 and α>0, only i has positive hazard:
its debt is max(0,−s_i), while other players use (34). If α=0, all-Never
has exploitability max(0,max_i s_i). Clearing a zero denominator without
this split would create an invalid automatic witness 0≥0.

These formulas supply all stationary hazard vectors and, as special cases,
all sixteen pure date-zero-or-Never coalition profiles. They are not a
new stationary producer or a strategy-class completeness theorem.

### An exact positive floor over ALL stationary profiles

Use the positive-singleton Fin4 table in
`notes/CODEX_HILBERT__BOUNDED_TIMING_INCENTIVE_TEST.md`, Section 3. Before
normalization its active cyclic rewards are own-Quit 1+predecessor-Quit and
own-Continue 3·predecessor-Quit. Player 3 receives one when quitting and
two at every terminal coalition not containing it. Every singleton reward
is one and all rewards are in [0,3]. Its exact period-three terminal Nash
profile and fixed uniform payoff are proved in that note, Section 6, using
the active completion from RENY Section 14. Thus its unrestricted infimum
is zero.

Nevertheless every stationary profile has full terminal exploitability at
least 1/100. Here is a complete all-hazards proof. Let h=max(q_0,q_1,q_2)
and z=q_3. If h=0, an active player obtains zero under the profile and one
by immediate Quit, so the bound holds. Suppose h>0, and cyclically relabel
so q_0=h.

The outsider's Never cap is two because the active stationary opponents
absorb almost surely. Its exact debt is z/α. If z>h/16, then

    d_3=z/α ≥ z/(3h+z)>1/49>1/100.

Now suppose z≤h/16. For active i the immediate-Quit value remains
1+q_{i−1}, the absorbing Continue contribution remains 3q_{i−1}, and its
face numerator is

    F_i=(1−q_{i−1}²)q_{i+1}−q_{i−1}(2−q_{i−1})
        +z(1−q_{i−1})(1−q_{i+1})(1+q_{i−1}).

The last term lies between zero and 2z. Also α≤4h and every active β_i≤3h.

If q_1≥h/4, then q_2≤h and

    F_1≤−h(1−h+h²)+2z≤−3h/4+h/8=−5h/8.

The Never branch of (34) gives d_1≥5/384>1/100. All denominators are
positive because q_0=h>0 is an opponent hazard for player 1.

If q_1<h/4, then q_1≤1/4 and

    F_2≥(1−q_1²)h−2q_1≥7h/16.

When q_2≤1/2, the Quit branch gives d_2≥7/128>1/100. Otherwise q_2>1/2,
q_0≥q_2, and q_1<q_2. Therefore

    F_0≤−q_2(1−q_2+q_2²)+2z
        ≤−3q_2/4+1/8<−1/4.

Since q_0>1/2 and αβ_0≤1, the Never branch gives d_0>1/8. Again all
used β_i are positive. These cases exhaust the full hazard cube, including
sure-Quit coordinates. Dividing the complete table by three therefore gives
a normalized table r⁰ with

    η(r⁰)=0,       inf_{stationary p} E_{r⁰}(p)≥1/300.   (35)

The nonzero coarse constant serves only to prove a strict class separation.

### Consequence for the global reward-normal test

Define η_Stat(r)=inf_{stationary p} E_r(p), with all deviation caps still
unrestricted. For every fixed stationary profile p, E_r(p) is the support
function of its actual unilateral terminal-law differences, each of ℓ¹ norm
at most two. Consequently η_Stat is 2-Lipschitz in r and attains its maximum
on the normalized reward cube. By (35), this maximum γ_Stat is positive.

Apply the already proved separation argument in Sections 2–5 to this ENTIRE
stationary profile family. No step there needs the index family to contain
every behavioral profile: it uses actual response support functions, their
uniform bound, and near-minimizers in the chosen family. We obtain a
reward table r^Stat with

    E_{r^Stat}(p)≥γ_Stat>0 for EVERY stationary p,

and an actual limiting near-active normal certificate, which can again be
chosen using at most fifteen law differences belonging to one player.
All pure-coalition screens hold because their profiles are stationary.
The sources, responses, law differences, and reward-table extremization
are genuine for the stated stationary relaxation.

Thus the complete stationary and pure-coalition screen, even combined with
the reward normal balance, is CONSISTENT with a positive value. No proof can
deduce γ=0 from only those hypotheses. What is NOT supplied is that the
certificate's source profiles approach η(r^Stat), rather than η_Stat(r^Stat).
The two-full-debtor and all-player singleton-margin assertions about genuine
unrestricted minimum carriers are not silently asserted for these sources.

This is why SKEPTIC's uniform finite nonstationary portfolio approximation
is a materially stronger global input: its error controls the difference
from η, whereas replacing that portfolio by the stationary class leaves
the fixed positive gap in (35). The calculation here does not establish a
global portfolio balance, find a positive-gap game, or close the conjecture.
It is frozen at this exact class boundary.
