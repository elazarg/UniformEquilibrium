# Approximate finite timing Nash and conditional error

Author: `CODEX_RENY`.

## Current status

The exact finite-Nash completeness proposal is false by existing checked
declarations, identified in Section 1. Sections 2–11 give ordinary proofs of
the surviving approximate-source statements: compact boundary identities,
the all-player limiting Never floor, conditional error divided by actual
joint reach, one-sided whole-prefix slack, length-independent support
rounding, and a finite-menu punishment-floor producer under no uniform payoff.
The opposite endpoint's cumulative error bound and the direct mixed-root to
support-wise transfer are refuted by exact regressions in Sections 7 and 9.

Sections 1–11 have passed independent mathematical review by `CODEX_HILBERT`
with no unresolved objection; the review and bounded source-interface audit
are in
[`CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH__BY_CODEX_HILBERT.md`](../feedback/CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH__BY_CODEX_HILBERT.md).
The fixed compact carrier is automatic from actual reward-bounded values,
and the final displayed cut requires ε ≤ e_τρη^m; both review clarifications
are incorporated below. No new result in this notebook is Lean-checked.

Section 12 combines these adapters with the existing finite-forward consumer
to obtain a uniform positive reach into one bounded final window for EVERY
sufficiently accurate finite timing Nash profile, with one fixed positive
error threshold independent of deadline. Its first-crossing proof has passed
an independent derivation and adversarial review by `CODEX_SKEPTIC`, saved in
[`CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH__BY_CODEX_SKEPTIC.md`](../feedback/CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH__BY_CODEX_SKEPTIC.md).
There is no unresolved mathematical objection to Sections 1–12. The bounded
source comparison found no inspected neighboring declaration already
supplying Section 12's conclusion.

Section 13 proves the separate qualitative-completeness statement for every
fixed POSITIVE finite-menu tolerance. Section 14 supplies a solved cyclic
regression: exact finite Nash sources reach their last row surely, but no
fixed finite-window-only repair can drive full terminal debt to zero. Those
two sections are not independently reviewed here. The bounded final window's
omitted-date defect remains unconsumed: none of these results supplies a paid
return, lowers full terminal debt, or proves a uniform-equilibrium payoff
from arbitrary data.

## 1. The exact architecture is already refuted

The proposal was: whenever a finite quitting game has a uniform-equilibrium
payoff, the infimum of unrestricted terminal exploitability over all exact
finite timing Nash profiles, allowing every deadline and every equilibrium
selection, is zero.

The normalized Fin4 table in
`GameTheory.FinFourHardDeadlineTimingNashBarrier.reward` refutes it. There are
two active players k,j with rewards

| First active quitters | {k} | {j} | {k,j} |
|---|---:|---:|---:|
| k | 1/2 | 1 | 0 |
| j | −1 | −1 | 0 |

Dummy-only terminal coalitions give both active players zero. For each of
the two dummies d, its reward is −1 when it belongs to the terminal coalition
and zero otherwise. All-Never pays zero.

At every positive deadline N the full mixed timing Nash law is unique and
its complete terminal exploitability is

    D_N = 2^(N−1)/(2^(N+1) − 1) > 1/4,       D_N → 1/4.

The same game has fixed uniform-equilibrium payoff (1,−1,0,0). An explicit
family realizing that target has j Quit at zero, k Continue at zero and use
a uniform planned time on {1,…,L} after refusal, and both dummies Never.
Its exact full terminal exploitability is 1/L. It is a finite timing
1/L-Nash profile at deadline L+1, with full debt also 1/L.

This is an existing architecture no-go, not a new result in this notebook.
The maintained route is the hard-deadline paragraph of `docs/TOOLKIT.md`.
Exact declarations inspected under their imports, without a new build:

- `FinFourHardDeadlineTimingNashBarrier.existsUnique_finiteDeadlineTimingNash`,
  `FinFourHardDeadlineTimingNashBarrier.finiteDeadlineTimingNash_exploitability_eq_hardDeadlineDebt`,
  and `FinFourHardDeadlineTimingNashBarrier.quarter_lt_finiteDeadlineTimingNash_exploitability`
  in `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashUniqueness.lean`.
- `FinFourHardDeadlineTimingNashBarrier.reward`,
  `FinFourHardDeadlineTimingNashBarrier.comparisonProfile_exploitability`,
  `FinFourHardDeadlineTimingNashBarrier.terminalExploitabilityInf_eq_zero`,
  and `FinFourHardDeadlineTimingNashBarrier.comparisonTarget_isUniformEquilibriumPayoff`
  in `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashBarrier.lean`.

The ordinary source is
[`CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md`](CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md),
with its linked independent Euler review. Its uniqueness proof is not being
repackaged as new mathematics. The no-go invalidates exact finite-Nash
selection as a universal positive class. It does not invalidate a conditional
restriction on hypothetical games with a global terminal gap.

## 2. Precise approximate question

Let I be a nonempty finite player set, |rᵢ(S)| ≤ M with M > 0, and zero
all-Never payoff. All stopping laws are independently privately sampled and
realized by their literal behavioral hazards. Complete unilateral behavioral
deviations correspond to arbitrary unilateral stopping-law replacements.

At deadline N the permitted menu is {0,…,N−1,Never}. A finite timing profile
p is ε-Nash if every permitted unilateral timing-law replacement gains at
most ε, coordinatewise. This is ordinary ex ante finite-game ε-Nash, not a
bound on conditional errors at every reached date.

Consider deadlines Nₙ → ∞, errors εₙ ≥ 0 with εₙ → 0, and such profiles pⁿ.
After a subsequence assume each finite atom converges to pᵢ(t), the prescribed
payoff converges to u, and define the limiting Never masses

    aᵢ = 1 − ∑[t ≥ 0] pᵢ(t),       A = ∏ᵢ aᵢ.

As in the predecessor note, aᵢ may strictly exceed the limiting literal
Never mass zᵢ. Let U(p) be prescribed terminal payoff, Fᵢ(t) the pure finite
date payoff, Vᵢ the Never payoff, Bᵢ the unrestricted cap, and dᵢ = Bᵢ−Uᵢ.
The global-gap hypothesis, when used, is

    maxᵢ dᵢ(q) ≥ Γ > 0 for every behavioral profile q.

The question is exactly which source conclusions of
[`CODEX_RENY__FINITE_TIMING_NASH_BOUNDARY_SECURITY.md`](CODEX_RENY__FINITE_TIMING_NASH_BOUNDARY_SECURITY.md)
survive this approximation, and what additional error/reach data their
finite-prefix consumers need.

## 3. Compact support identities survive vanishing finite Nash error

Let Cᵢⁿ be player i's best-response value within the finite timing menu.
Finite εₙ-Nash gives

    Uᵢ(pⁿ) ≤ Cᵢⁿ ≤ Uᵢ(pⁿ) + εₙ.

For a fixed permitted date t the nonnegative slack Cᵢⁿ−Fᵢⁿ(t), multiplied
by its own atom pᵢⁿ(t), is at most the average slack Cᵢⁿ−Uᵢ(pⁿ) ≤ εₙ.
Hence if pᵢ(t) > 0 this slack tends to zero. Since every fixed date is
eventually permitted and its payoff depends on finitely many opponent atoms,
the limit obeys

    Fᵢ(t) ≤ uᵢ,       pᵢ(t) > 0 ⇒ Fᵢ(t) = uᵢ.

Integrating the limiting own law gives exactly

    Uᵢ(p) = (1−aᵢ)uᵢ + aᵢ Vᵢ.                         (3.1)

The late-date identity is independent of Nash:

    lim[t → ∞] Fᵢ(t) = Vᵢ + sᵢ∏[j ≠ i]aⱼ,

where sᵢ = rᵢ({i}). If all aᵢ > 0, the escaped vector

    bᵢ = (uᵢ−Uᵢ(p))/A = (uᵢ−Vᵢ)/∏[j ≠ i]aⱼ

therefore satisfies bᵢ ≥ sᵢ. Its fixed-cut conditional payoff interpretation
is unchanged, so |bᵢ| ≤ M. The interpretation needs only actual conditional
payoffs, not conditional Nash optimality.

## 4. The all-player limiting Never floor also survives

Assume the global gap. For sufficiently large n, εₙ < Γ. The unrestricted
cap of a finite-support profile is the larger of the finite-menu cap Cᵢⁿ
and the common omitted-date value Vᵢ(p₋ᵢⁿ) + sᵢ Z₋ᵢⁿ. Since finite-menu
debt is less than Γ, the gap must select an omitted-date owner. Pass to a
fixed owner k. Then

    Γ ≤ Vₖ(p₋ₖⁿ) + sₖ Z₋ₖⁿ − Uₖ(pⁿ)
      ≤ sₖ Z₋ₖⁿ + εₙ.                                 (4.1)

In particular sₖ > 0 and every opponent's limiting aⱼ ≥ Γ/M. If aₖ = 0,
one player's proper limiting stopping law makes u = U(p) in every coordinate.
The fixed-date cap identities and the positive singleton sₖ then cap Never
as well, producing exact terminal Nash and contradicting the gap. Thus all
aᵢ are positive.

From (3.1), the cap bound Bᵢ ≤ max(uᵢ,Vᵢ), and |bᵢ| ≤ M,

    dᵢ(p) ≤ max(A bᵢ, −(1−aᵢ)(∏[j ≠ i]aⱼ)bᵢ).

For i ≠ k either product contains aₖ. For i = k, bₖ ≥ sₖ > 0 makes the
first term the maximum. Hence every dᵢ(p) ≤ M aₖ. Applying the global gap
to the actual limiting profile proves

    aᵢ ≥ Γ/M for every player i.                         (4.2)

Thus the exact limiting annotations and summable actual limiting hazards
from Sections 7–8 of the predecessor note extend to arbitrary vanishing
finite-Nash-error families. Nothing here requires Nₙεₙ → 0.

## 5. Conditional error and the uniform initial-root bound

For a finite profile p, let R(t) be its joint probability of survival to date
t. If R(t) > 0, its conditional tail, translated to begin at zero, is a
finite timing ε/R(t)-Nash profile. Indeed a conditional gain g can be spliced
into one complete deviation which copies the prescribed prefix; its exact
ex ante gain is R(t)g. Ex ante ε-Nash therefore gives g ≤ ε/R(t). The
division is by joint reach, not by one player's survival or an opponent-only
product.

Let η = Γ/(2M). There exist H₀ ≥ 1 and ε₀ > 0 such that every ε₀-Nash
finite timing profile at every deadline N ≥ H₀ has initial hazards

    qᵢ(0) ≤ 1−η for every i.                            (5.1)

Otherwise choose Nₙ ≥ n and εₙ ≤ 1/n with a violating initial atom, then
extract a fixed violating player and apply (4.2). That player's limiting
Never mass would be at most η instead of at least 2η. This proves the
two-parameter statement by contradiction.

At a later date, (5.1) is applicable while the remaining deadline is at
least H₀ and ε/R(t) ≤ ε₀. It gives positive next reach, but it does not
itself keep R(t) above ε/ε₀ for all subsequent dates. Exact Bellman recursion
still holds at every reached date; its root Nash error is at most ε/R(t).
The exact-block hazard-capacity theorem cannot simply be applied to this
approximate prefix.

## 6. Regression and current consumer boundary

For the solved table in Section 1, the comparison family has deadline L+1,
finite Nash error 1/L, full terminal debt 1/L, and a sure initial quitter j.
The limiting aⱼ is zero and sⱼ = −1. This is precisely the negative-singleton
exception in the zero-a classification. The global gap does not hold for
this table, so (4.2) and (5.1) do not apply.

The family also shows why requiring a favorable error/deadline rate is a
new selection restriction: (L+1)ε_L → 1, although the family already gives
the actual fixed uniform-equilibrium payoff. A proposed condition Nε → 0
is not satisfied by this witness. This alone does not prove that no other
family in the same game could satisfy such a rate; that stronger assertion
is not made.

For a reached prefix of length K whose reach stays above ρ > 0, the elementary
row-error estimate gives total local Nash error at most Kε/ρ. Converting that
estimate into a bounded-capacity or summable-residual consumer requires a new
selection or stability theorem. The sources inspected here do not supply
one merely from ε → 0.

Additional exact declarations inspected for this boundary:

- `timingMixedPayoff_withTail_sub` and
  `timingLawTail_isNash_of_isNash_of_positiveContinue` in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`.
- `QuittingSummableResidualNashBellmanSpine` in
  `UniformEquilibrium/Quitting/Debt/Dynamic/SummableResidualNashBellmanSpine.lean`.
- `QuittingSummableResidualNashBellmanSpine.isUniformEquilibriumPayoff_soloReward_of_persistent`
  in `UniformEquilibrium/Quitting/Classification/Existence/AllNormalUnboundedExactBlockHazardCapacity.lean`.

The approximate conditional statements are elementary deductions from the
same exact splicing identity. They are not described as existing checked
adapters. No exports, Lean changes, or commits were made.

## 7. One global best response does not collect all local root errors

The candidate improvement was to control the accumulated local Nash residual
by the finite-game ex ante error, perhaps after weighting by prescribed
survival. It is false without further structure.

Use one active player with singleton reward 1 and zero Never payoff. If four
players are desired, add three dummies whose own terminal reward is −1 when
they join the first coalition and zero otherwise, give the active player
reward 1 whenever it joins that coalition and zero on dummy-only exits, and
prescribe all dummies Never. Fix N ≥ 1 and 0 < ε < 1. The active player's
finite timing law is

    p(t) = (1−ε)/N for 0 ≤ t < N,        p(Never) = ε.

Its prescribed payoff is 1−ε and every pure finite quit time pays 1. Hence
its exact finite Nash error and exact full terminal debt are both ε; dummies
have zero debt. Put w = (1−ε)/N. At date t < N, the active player's survival
and actual conditional value are

    S_t = 1 − tw,        v_t = 1 − ε/S_t.

There are no quitting opponents. Quit-now payoff is 1 and Continue-now
payoff is v_{t+1}. The maximal one-step endpoint gain above prescribed v_t is
therefore exactly

    r_t = 1 − v_t = ε/S_t.

Consequently the prescribed-survival-weighted sum on any first K dates is

    ∑[t < K] S_t r_t = Kε.                              (7.1)

For K ≤ N/2, every displayed S_t is at least one half. Taking even N and
ε = 1/√N makes the finite Nash errors tend to zero, keeps the whole first
N/2-date prefix uniformly reached, but gives the weighted accumulated local
error √N/2 → ∞. Taking ε = 1/N instead gives a nonzero limit 1/2. Thus even
vanishing ex ante error plus a positive uniform prefix reach does not imply
vanishing accumulated local residual.

There is no omitted gain hidden in the calculation: all pure finite dates
give the same best payoff 1. Quitting at one such date collects the single
global improvement ε and ends play. The positive local errors at later dates
are alternative opportunities to collect the same gain, not distinct gains
that one behavioral deviation can add. This explains exactly why an
unjustified sum of one-step advantages overcounts.

The example does not satisfy a positive all-profile gap and does not disprove
an error estimate using additional hypothetical-counterexample structure.
It does prove that the splicing identity and the bare ε-Nash condition alone
cannot supply that estimate.

## 8. A one-sided cumulative root-error bound does survive

Fix a finite timing ε-Nash profile, one player i, and its literal finite
behavioral realization. Let Sᵢ(t) and S₋ᵢ(t) be own and opponent survival to
t, R(t) = Sᵢ(t)S₋ᵢ(t), and qᵢ(t) its own current hazard. Let Qᵢ(t) be its
root Quit payoff, and Cᵢ(t) its root Continue payoff followed by its prescribed
continuation. Values and root payoffs here are the actual prescribed ones,
not unrestricted cap annotations. Then

    ∑[t < N] R(t) qᵢ(t) max(Cᵢ(t)−Qᵢ(t),0) ≤ ε.        (8.1)

Proof: write f(t) for the unconditional payoff against the fixed opponents
from pure date t, including f(Never), and let c be the largest permitted
pure-action payoff. The original finite Nash condition is

    ∑[a in the finite menu] pᵢ(a)(c−f(a))
      = c−Uᵢ(p) ≤ ε.                                  (8.2)

If pᵢ(t) > 0, define f_later(t) to be the payoff from always continuing
through t and then using the prescribed conditional own tail. When that tail
has zero original own probability, use the literal realization's fallback
continuation; it is still supported on the finite menu. In every case
f_later(t) ≤ c. Before t the two plans face the same opponent absorption;
conditioning opponents on survival through t gives

    f_later(t)−f(t) = S₋ᵢ(t)(Cᵢ(t)−Qᵢ(t)).

Since R(t)qᵢ(t) = pᵢ(t)S₋ᵢ(t), the summand in (8.1) equals
pᵢ(t) max(f_later(t)−f(t),0), which is at most pᵢ(t)(c−f(t)). Summing and
using (8.2) proves (8.1). Zero own atoms and zero opponent reach contribute
zero and require no division.

The local endpoint residual has the exact decomposition

    max(Qᵢ(t),Cᵢ(t)) − vᵢ(t)
      = qᵢ(t) max(Cᵢ(t)−Qᵢ(t),0)
        + (1−qᵢ(t)) max(Qᵢ(t)−Cᵢ(t),0).                (8.3)

Thus (8.1) controls the first orientation without a deadline factor. On a
prefix with R(t) ≥ ρ > 0, its unweighted total is at most ε/ρ. The second
orientation is uncontrolled by this argument: Section 7 has only that
orientation and gives exactly Kε after reach weighting.

This suggests a precise new family-selection obligation. In addition to
vanishing ex ante finite Nash error and the necessary reach estimates, one
must control the cumulative terms

    ∑[t in the consumed prefix] (1−qᵢ(t))
      max(Qᵢ(t)−Cᵢ(t),0)

in the probability mode of the intended residual consumer, or prove a
consumer that avoids summing these mutually exclusive Quit opportunities.
The ordinary finite Nash condition already controls the other orientation;
it need not be charged again by Kε/ρ. No existence theorem selecting this
additional one-sided control has been established here.

## 9. Mixed-root error is not support-wise endpoint error

The finite-forward consumer uses `IsQuittingRootSupportApproxNash` in
`UniformEquilibrium/Quitting/Boundary/Repair/SupportEnlargementAlternative.lean`.
For the endpoint difference g = Q−C, its requirements are

    q > 0 ⇒ g ≥ −δ,       1−q > 0 ⇒ g ≤ δ.

In contrast, `IsεQuittingRootEndpointNash` in
`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean` requires only
(1−q)g ≤ ε and −qg ≤ ε. Both exact definitions and their surrounding
own-marginal identities were read. The support field of
`QuittingFiniteForwardPacket` in
`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`
uses the former, unweighted condition; that record also requires exact
forward Bellman equations, a fixed compact carrier, punishment floors, and
a requested absorption charge. Ordinary mixed-root regret does not fill its
support field directly.

A one-player singleton reward −1 gives the minimal transfer failure.
At any positive deadline prescribe Quit at zero with probability ε and
Never with probability 1−ε. The exact full and finite timing debt is ε,
initial reach is one, and the root endpoint difference is −1. Because Quit
has positive probability, every support-error bound must be at least one.
Thus vanishing ex ante error and full initial reach do not make supported
endpoints nearly optimal. The bad supported action has vanishing mass.

More generally, at a reached root with conditional finite error ε/R,
the only direct bounds are

    q > 0 ⇒ (C−Q)_+ ≤ ε/(Rq),
    1−q > 0 ⇒ (Q−C)_+ ≤ ε/(R(1−q)).

The second is uniformly useful on the long-deadline branch of (5.1), where
1−q ≥ η. The first can fail as q tends to zero, but Section 8 controls the
total mass of its bad Quit actions. This asymmetry leads to an actual
rounding construction, rather than adding an unsupported small-error field.

## 10. Literal support rounding without a deadline factor

### Statement

Let p be a finite timing ε-Nash profile at deadline N, with m = |I| players
and reward bound M. Choose a prefix 0,…,K−1, K ≤ N, on which actual joint
reach satisfies R(t) ≥ ρ > 0 and every player's Continue probability satisfies
1−qᵢ(t) ≥ η > 0. Let δ > 0. Define a new literal hazard profile by

    q'ᵢ(t) = 0       if t < K and Qᵢ(t)−Cᵢ(t) < −δ,
    q'ᵢ(t) = qᵢ(t)   otherwise.                         (10.1)

The endpoint differences on the right are evaluated once on the original
profile's actual conditional continuation values. All roots from K onward
are retained literally. Let

    μ = ∑[t < K] ∑ᵢ (qᵢ(t)−q'ᵢ(t)).

Then

    0 ≤ μ ≤ mε/(ρδ).                                  (10.2)

The new profile's actual conditional values satisfy exact Bellman recursion,
and every new root before K is support-approximate Nash with error

    Δ = max(δ, ε/(ρη)) + 4Mμ.                          (10.3)

Joint reach increases. Total marginal hazard decreases by exactly μ and
total root absorption charge decreases by at most μ. Every conditional
prescribed payoff changes by at most 2Mμ, and the full terminal exploitability
changes by at most 4Mμ. The suffix from K is unchanged as a behavioral root
sequence, not merely in payoff.

For fixed positive ρ,η and ε → 0, choose δ = √ε when ε > 0. Equations
(10.2)–(10.3) give μ → 0 and Δ → 0 with no dependence on K or N. At ε = 0
use the original exact roots. This is an actual finite-prefix construction
from the stated approximate source, not a supplied support-error verifier.

### Proof of the deleted hazard bound

For each removed hazard the original Continue endpoint exceeds Quit by more
than δ. Section 8 therefore gives

    ρδ ∑[t < K] qᵢ(t) 1{Qᵢ(t)−Cᵢ(t)<−δ} ≤ ε.

Sum over players to obtain (10.2). This step is why deleting separately at
every date does not incur a deadline factor. It uses the complete own-law
slack budget, rather than summing the ex ante ε bound once per date.

### Coupling the modified roots and suffix values

Use the same independent private uniforms for old and new Bernoulli hazards.
At one player-date pair the actions disagree with probability
|qᵢ(t)−q'ᵢ(t)|. From any start date, the probability of any disagreement at
or after that date is at most μ by a union bound. Until a first disagreement
the terminal histories and payoffs coincide. Hence every actual prescribed
suffix payoff changes by at most 2Mμ. The same argument applies with one
player forced to Quit now, or forced to Continue now and then follow the
respective prescribed suffix. Therefore each pure endpoint changes by at
most 2Mμ and each endpoint difference changes by at most 4Mμ.

The uniforms are a proof coupling, not a public randomization used by the
new strategy. The new profile is still the independent product of its
displayed private hazards. Recomputing its actual conditional values gives
exact Bellman equations automatically.

If q'ᵢ(t) > 0, its original endpoint difference was at least −δ, so its new
difference is at least −δ−4Mμ. Continue has positive probability both before
and after the change. The original mixed-root Nash bound and R(t) ≥ ρ give

    (1−qᵢ(t))(Qᵢ(t)−Cᵢ(t)) ≤ ε/R(t),

so its original difference is at most ε/(ρη). Its new difference is at most
ε/(ρη)+4Mμ. These are exactly the two support inequalities in (10.3).

At each date, root absorption 1−∏ᵢ(1−qᵢ) is monotone in the hazards, and
its change is at most the sum of removed marginal hazards at that date.
Summing gives the charge-loss bound. Coupling against any fixed unilateral
deviation also changes its payoff by at most 2Mμ, because only opponent
hazards matter to this comparison. Supremum over all complete behavioral
deviations therefore changes each cap by at most 2Mμ. Combining cap and
prescribed-payoff stability gives the stated 4Mμ exploitability bound.

### Scope of the producer

This construction repairs the specific support-field mismatch of Section 9.
It produces no punishment-floor estimate and no unbounded charge. Its reach
and Continue floors must refer to the actual source prefix, before rounding.
Under the global-gap two-parameter theorem, the Continue floor is available
up to any cut at which remaining deadline is at least H₀ and ε ≤ ε₀R(t).
The new profile's larger reach does not retroactively establish that source
inequality at previously uncontrolled dates.

Reversing the finite displayed values and roots gives the forward Bellman
orientation used by `QuittingFiniteForwardPacket`. The fixed compact carrier
is automatic here: all recomputed actual values lie in the same reward cube.
The punishment-rationality and requested-charge fields remain separate.
This incorporates the independent reviewer's carrier clarification. No
finite-forward packet producer or uniform-equilibrium conclusion is claimed.

## 11. Long approximate finite Nash payoffs approach the punishment floor

This section specializes to Fin4 and assumes no uniform-equilibrium payoff.
Let χᵢ = quittingPunishmentValue r i. Then, for every τ > 0, there exist
H_τ ≥ 1 and e_τ > 0 such that every finite timing e_τ-Nash profile at every
deadline N ≥ H_τ satisfies

    Uᵢ(p) ≥ χᵢ − τ for every i.                         (11.1)

This is a finite-menu statement. It is not obtained by applying an
unrestricted terminal-Nash punishment-floor lemma to a finite-menu profile.

### Proof

Suppose (11.1) fails for some τ > 0. Choose deadlines Nₙ ≥ n, finite timing
εₙ-Nash profiles with εₙ ≤ 1/n, and, after a subsequence, a fixed player whose
payoff is below χᵢ−τ. Extract finite atoms and payoff limit u.

The no-uniform-payoff hypothesis supplies a fixed global terminal gap Γ and
all-player punishment normality. The latter is the explicit field
`FinFourQuantitativeFullSupportHardResidual.all_punishmentNormal`, obtained by
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
The definitions of punishment value and normality were read in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean` and
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`.

Section 4 gives every limiting aᵢ ≥ Γ/M. At each fixed finite date, actual
joint reach therefore has a positive limit; dividing εₙ by that reach still
gives a vanishing conditional error. Passing conditional Bellman equations
and root inequalities to the limit gives the exact annotated spine of the
predecessor note, with v₀ = u. Its actual limiting hazards are summable since
their product survivals have positive limits. The annotations lie in the
canonical reward cube because they are limits of actual conditional payoffs.

The inspected theorem
`IsCanonicalExactQuittingNashBellmanSpine.punishmentValue_le_of_all_normal_and_summable`
in `UniformEquilibrium/Quitting/Bellman/Finite/SummableExactNashBellmanPunishmentFloor.lean`
therefore applies and gives χᵢ ≤ v₀,ᵢ = uᵢ. But the violating sequence has
uᵢ ≤ χᵢ−τ, a contradiction.

The proof does not realize the escaped terminal annotation as a behavioral
payoff. The inspected theorem is specifically a floor theorem for a bounded
exact annotated spine with summable absorption and normal players; those are
the data produced above.

### Consequence for support rounding

At every source prefix date t, including its final displayed value, (11.1)
applies if remaining deadline N−t ≥ H_τ and original error divided by actual
joint reach satisfies ε/R(t) ≤ e_τ. Thus its actual values are at least χ−τ.
The support rounding of Section 10 changes each conditional value by at most
2Mμ, so the new values satisfy

    v'ᵢ(t) ≥ χᵢ − (τ + 2Mμ).                           (11.2)

This supplies the previously missing rationality field on the displayed
long-deadline prefix once the same explicit source reach/error condition
holds. Combined support error is the maximum of (10.3) and τ+2Mμ. The fixed
compact reward cube is automatic. Requested absorption charge remains a
distinct input; (11.1) does not by itself produce it.

## 12. Uniform final-window reach for small finite Nash error

### Statement

For a fixed Fin4 quitting game with no uniform-equilibrium payoff, there
exist H ≥ 1, e_* > 0, and ρ > 0 such that every finite timing ε-Nash
profile with 0 ≤ ε ≤ e_* reaches its final min(N,H) dates with joint
probability at least ρ. For N ≥ H, this says

    R(N−H) ≥ ρ.                                       (12.1)

The constants depend on the table; there is no assumption Nε → 0. This is
a conditional restriction on actual approximate finite-game sources, not an
existence theorem within exact finite-Nash profiles. It uses the existing
finite-forward consumer contrapositively, after the actual support rounding
and punishment-floor constructions above.

### A forbidden finite-forward packet

Use the fixed canonical payoff cube as carrier. The inspected declaration
`quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets` in
`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`
states that packets at every positive support tolerance and every requested
absorption charge give a uniform payoff. Under no uniform payoff, its
contrapositive therefore supplies numbers λ > 0 and T ≥ 0 for which there
is no packet with support tolerance λ and charge at least T in this cube.
The packet's rationality floor is χ−λ at every displayed value.

Let η = Γ/(2M) and let H_q,e_q be the uniform initial-root thresholds from
Section 5. Put τ = δ = λ/4. Let H_τ,e_τ be the punishment-floor thresholds
from Section 11, and choose H ≥ max(H_q,H_τ). Set m = 4 and choose

    ρ = exp(−m(T+2)/η).

Choose e_* > 0 sufficiently small that

    e_* ≤ ρe_q,
    e_* ≤ ρη^m e_τ,
    e_* /(ρη) ≤ λ/4,
    me_* /(ρδ) ≤ min(1, λ/(16M)).                       (12.2)

All the right-hand quantities are positive. This is a fixed error threshold
chosen after the forbidden packet, and not a deadline-dependent selection.

### The first survival crossing would produce the forbidden packet

Take a finite timing ε-Nash profile with ε ≤ e_* and N ≥ H. Suppose that
R(N−H) < ρ. Let K be the first date at which R(K) < ρ. Then
1 ≤ K ≤ N−H and R(t) ≥ ρ for every t < K.

At each t < K the actual conditional finite Nash error is at most
ε/R(t) ≤ e_q and the remaining deadline is at least H_q. The initial-root
theorem therefore gives 1−qᵢ(t) ≥ η. In particular the crossing step still
has positive survival and

    R(K) ≥ ρη^m.

All displayed conditional values, including the value at K, have remaining
deadline at least H_τ and conditional finite Nash error at most e_τ by
(12.2). They therefore satisfy the actual payoff floor χ−τ.

Write α_t = 1−∏ᵢ(1−qᵢ(t)) for root absorption. Since qᵢ(t) ≤ α_t and
−log(1−qᵢ(t)) ≤ qᵢ(t)/η,

    −log R(K) ≤ (m/η) ∑[t < K] α_t.

The strict crossing R(K) < ρ gives total prefix absorption charge greater
than T+2. Apply the literal rounding construction of Section 10 at threshold
δ. Its deleted hazard satisfies μ ≤ me_* /(ρδ) ≤ 1. Its support error is
at most λ/4 + 4Mμ ≤ λ/2, and its actual value floor is at least
χ−(λ/4+2Mμ) ≥ χ−λ. Its retained absorption charge exceeds T+1, hence T.

The rounded roots retain the literal suffix at K; their recomputed actual
values lie in the fixed canonical payoff cube and satisfy exact Bellman
recursion. Reverse the K roots and K+1 displayed values. This is exactly a
`QuittingFiniteForwardPacket` with tolerance λ, all required rationality
floors, and charge exceeding T, contrary to the forbidden packet selection.
The contradiction proves (12.1). If N < H, the whole profile is the final
window and its entry reach is one.

### Remaining boundary

This proves the positive reach condition for all sufficiently accurate
finite-game Nash profiles in the hypothetical counterexample branch. It
does not force their final-window unrestricted debt to be small. That
remaining debt is still allowed to come from the omitted date. The solved
hard-deadline table in Section 1 rules out treating exact finite Nash as a
complete positive class, while its approximate comparison profiles are
outside the no-uniform-payoff hypothesis of this theorem.

The theorem does not produce a reusable paid return or control other players'
debt after changing the bounded final window. Its concrete progress is the
extension from exact finite sources to a fixed positive neighborhood of
finite-game Nash error, with literal reach and legal independent behavioral
realizations retained throughout.

## 13. Positive finite-menu slack restores qualitative completeness

For ε ≥ 0 define E_r(ε) as the infimum of unrestricted terminal
exploitability over every finite deadline and every finite timing ε-Nash
profile at that deadline. Then, for every fixed ε > 0,

    E_r(ε) = 0  ⇔  r has a uniform-equilibrium payoff.   (13.1)

This is an exact zero-set statement. It does not identify E_r(ε) with the
global terminal-exploitability infimum at positive values.

The semantic endpoint used in both directions is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`,
inspected under its imports. The target-retaining forward source is also
available there as
`exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff`.
No claim of new semantic uniformization is intended.

The reverse implication is the checked terminal approximate-Nash endpoint:
if the restricted infimum is zero, its actual behavioral profiles are terminal
approximate Nash at every positive error. For the forward implication, begin
with terminal δ-Nash profiles with δ tending to zero. Truncate each player's
finite stopping-time tail after a sufficiently large deadline by moving that
finite mass to Never. The sum θ of moved marginal masses can be made
arbitrarily small for each fixed profile. Couple the old and new complete
stopping laws independently; any terminal payoff differs by at most 2Mθ,
and the same bound applies against any fixed unilateral law after discarding
the mover's irrelevant marginal from the coupling. Thus every unrestricted
deviation debt changes by at most 4Mθ, uniformly over complete deviations.

Choose θ so that δ+4Mθ tends to zero and is eventually below the fixed ε.
The truncated profile then belongs to the finite ε-Nash class and has full
terminal exploitability tending to zero. This proves (13.1). The stopping-law
truncation is a private independent construction; it introduces no public
correlation or extra information.

On the hard-deadline table of Section 1, the discontinuity is exact:

    E_r(0) = 1/4,       E_r(ε) = 0 for every ε > 0.       (13.2)

The first equality is the unique exact finite-Nash barrier. The second is
already witnessed by the same-table comparison family with L arbitrarily
large and 1/L ≤ ε. Consequently the small but fixed positive ε-neighborhood
in Section 12 is a substantive enlargement of the exact source class: it
retains the correct qualitative completeness property for deciding whether
the terminal-debt infimum is zero.

What remains unconsumed is still literal. Under the uniform reach theorem,
any sequence εₙ → 0 of source profiles can be cut at its bounded final window.
The conditional finite Nash errors tend to zero because entry reach is at
least ρ. Compactness of that fixed finite timing simplex yields an exact
finite-H Nash tail in the limit. The omitted-date payoff is continuous on
this finite simplex, so a positive omitted-date defect can survive the entire
reduction. The theorem has not made that tail an unrestricted terminal Nash
profile, attached a return to it, or lowered its full defect.

## 14. Reached bounded windows do not justify bounded-window-only repair

Status: ordinary proof draft, not independently reviewed or Lean-checked.
This is a strategy-architecture counterexample, not a counterexample to
Section 12, whose no-uniform-payoff hypothesis it deliberately does not meet.

### A solved cyclic table with a different collision completion

Take three active players indexed modulo three. Write pred(i) = i−1 modulo
three. For each nonempty terminal coalition S, put

    rᵢ(S) = 1 + 1_{pred(i)∈S}   if i∈S,
    rᵢ(S) = 3·1_{pred(i)∈S}     if i∉S.

Every reward lies in [0,3], every own singleton reward is one, and all-Never
pays zero. The complete table is

| S | {0} | {1} | {2} | {0,1} | {0,2} | {1,2} | {0,1,2} |
|---|---|---|---|---|---|---|---|
| r(S) | (1,3,0) | (0,1,3) | (3,0,1) | (1,2,3) | (2,3,1) | (3,1,2) | (2,2,2) |

Its singleton rows are the canonical three-player cyclic rows, but its pair
and triple rows are NOT the canonical FTV completion. No paper claim about
the canonical completion is being transferred to this different table.

The maintained balanced-singleton route names
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`.
Its structure and consumer were inspected under their imports. The
certificate owner word 0,1,2, hazards (1/2,1/2,1/2), and coarse values

    (1,2,1) → (1,1,2) → (2,1,1) → (1,2,1)

satisfy its exact arc equations, owner equality, all-player solo floors,
and deleted-opponent divergence. That consumer explicitly allows arbitrary
nonsingleton rewards, and therefore supplies a uniform payoff here once this
finite certificate is instantiated; this note does not claim that the new
table's instantiation has been written in Lean. The same singleton data and
the DIFFERENT canonical collision rows were checked in
`CyclicThreePlayerQuitting.AdmissibleCycle.reward` in
`UniformEquilibrium/Quitting/Examples/Cyclic/ThreePlayer/AdmissibleCycle.lean`,
and `CyclicThreePlayerQuitting.Minimality.soloReward` and
`ExactCyclicPacket.standardPacket` in the neighboring `Minimality.lean`.

In fact the literal period-three roots already form an exact terminal Nash
profile for this completion. At phase i, only i quits, with probability 1/2.
The active owner has Quit and Continue values one. Player i+1 has Continue
value two and Quit value 3/2; player i−1 has both endpoint values one.
These are exact conditional best responses at every phase. Under any
unilateral deviation, the two opponents retain one positive hazard each per
cycle, so opponent absorption occurs almost surely; the bounded Bellman
upper bound passes to the terminal payoff without an escaped remainder.
Thus all complete deviations are capped by the displayed values.

The active punishment values are exactly χᵢ=1. Immediate Quit guarantees at
least one against every opponent profile, while the all-Never opponent
profile caps every own deviation by one. In particular this is an all-normal
table and the delayed finite-Nash payoff below is strictly above every
active punishment value. Normality and a strict initial punishment floor do
not remove the bounded-window-only obstruction.

### An exact finite-Nash family with final-window reach one

For every deadline N≥1 let each player Continue until date N−1, then Quit
with probability 1/2, and Never otherwise. At the final row,

    Quit payoff = 1 + 1/2 = 3/2,
    Never payoff = 3·(1/2) = 3/2.

An earlier pure Quit date pays one. Hence this is an exact finite timing
Nash profile at every N. Its payoff is (3/2,3/2,3/2); every fixed final
window of length H≤N is reached with probability one. Its omitted-date
payoff is 3/2 + (1/2)² = 7/4, so its full terminal exploitability is exactly
1/4. This family supplies stronger entry reach than Section 12 requests.

### No finite-clock terminal Nash profile exists for this table

Suppose all stopping laws are supported on one finite timing menu plus
Never and form a terminal Nash profile. Let zᵢ be their literal Never masses.
If every zᵢ>0, replace only player i's Never atom by Quit at the first omitted
date. The gain is zᵢ∏[j≠i]zⱼ = ∏ⱼzⱼ>0, since all earlier terminal events
are unchanged and own singleton reward is one. Thus some zᵢ=0.

There is consequently a first reached date t with a sure-Quit root
coordinate. Its entry joint reach is positive. Relabel that coordinate as
q₀(t)=1. All subsequent actual payoffs are nonnegative. At this root player
1's Quit value is two, whereas Continue yields three because player 0 quits
surely. Conditional Nash therefore forces q₁(t)=0. Player 2 then has Quit
value one and Continue value zero: player 0 already absorbs and player 1
does not quit at this row. Hence q₂(t)=1. But with player 2 quitting surely,
player 0's Quit value is two and its Continue value is three, contradicting
q₀(t)=1. All deviations used here are legal copied-prefix deviations at a
strictly positive joint reach. This contradiction excludes every finite-clock
exact terminal Nash profile, not merely the selected finite-Nash family.

### The exact failed repair implication

For every fixed H, the space of independent stopping laws on H finite dates
plus Never is compact. Its full terminal cap is the maximum of the H finite
pure-date payoffs, Never, and the first omitted-date payoff; all are finite
multilinear functions. Full terminal exploitability is therefore continuous.
The preceding nonexistence proof gives

    c_H := min{ full terminal exploitability of an H-date timing law } > 0.

Now retain the all-Continue prefix of the displayed deadline-N source and
replace ONLY its last H dates by arbitrary independent finite timing laws,
still followed by Never. The resulting full exploitability is at least c_H:
all tail deviations remain available after copying the unchanged prefix.
No such fixed-window repair can make the full defect tend to zero, despite
exact finite source Nash, entry reach one, and a solved exact periodic target.

This does not exclude a repair that installs an infinite periodic tail,
lets its finite repair window grow with accuracy, or changes the earlier
word. It also does not exclude a no-uniform-payoff-specific consumer using
additional source restrictions. It does rule out a generic closure principle
whose only substantive inputs are a reached bounded final window and small
finite-menu Nash error. A bounded calendar window is not the same resource
as a finite controller with an indefinitely repeatable cycle.

### Literal Fin4 embedding

Add player 3. Its reward is −1 when it belongs to the terminal coalition and
zero otherwise. On a coalition containing active players, their payoffs are
the displayed table evaluated at the active subset, whether or not player 3
also quits. On the dummy-only coalition all three active payoffs are zero.
Prescribe Never for player 3 in both the delayed finite family and the exact
period-three profile. Their active calculations remain unchanged and player
3's prescribed payoff and complete cap are both zero.

The no-finite-terminal-Nash argument also survives this embedding; it is not
enough merely to call the fourth player irrelevant. In any terminal Nash
profile, player 3's payoff must be zero because Never guarantees zero and
every own terminal participation pays −1. Thus its prescribed probability
of participating in the absorbing coalition is zero. At EVERY reached date
its Quit hazard must consequently be zero: conditional on joint entry, own
Quit always makes it a member of that date's absorbing coalition. Hence a
first reached sure-Quit row, if present, belongs to an active player and the
three-player contradiction above applies unchanged. If no such row exists
in a finite-clock profile, all own Never masses are positive, and an active
player's omitted-date replacement again gains the strictly positive product
of all four Never masses. No finite-clock terminal Nash profile exists.

For each fixed H the same compactness argument therefore gives a positive
full-debt minimum on the ENTIRE Fin4 H-date timing simplex, allowing all
four players to participate in a proposed repair. The bounded-window-only
obstruction is genuinely Fin4 and does not rely on imposing silence on the
fourth player in the repair class.

### Stronger all-normal Fin4 completion

`CODEX_HILBERT` independently suggested a positive-singleton fourth-player
completion while testing perturbed finite Nash selectors, now recorded in
[`CODEX_HILBERT__BOUNDED_TIMING_INCENTIVE_TEST.md`](CODEX_HILBERT__BOUNDED_TIMING_INCENTIVE_TEST.md).
Keep the active
payoffs above, but now set player 3's reward to one when it belongs to S and
two when it does not. This replaces the strict inactive player of the
preceding embedding; the two completions must not be conflated. This
strengthening has the same ordinary-proof-draft status as Section 14.

Every player now has punishment value and own singleton reward exactly one.
For an active player, immediate Quit guarantees at least one; for player 3,
it guarantees exactly one. Against all-Never opponents every player's cap is
one. Thus all four players are punishment-normal. Prescribing Never for
player 3 in the exact active period-three cycle gives it payoff two and
complete cap two, so that cycle remains an exact terminal Nash profile.

The delayed finite family, with active final hazards 1/2 and player 3 Never,
is still exact finite timing Nash. The active payoffs remain 3/2. Player 3's
Never payoff is 2·(1−(1/2)³)=7/4, whereas every finite pure Quit action pays
one. Its first omitted-date payoff is 7/4+1/8=15/8. The maximum full debt is
still 1/4, and every prescribed payoff is strictly above its punishment
value. Entry into every fixed final window remains sure.

No finite-clock terminal Nash profile exists for this completion either.
Positive joint literal Never mass again permits an active player's strict
omitted-date gain. Otherwise consider the first reached sure-Quit row.

If an active coordinate is sure, player 3 obtains two by Continue and one
by Quit, so its root hazard is zero. The three-active-player contradiction
already proved then applies. If player 3 is sure, the active root endpoint
gap is exactly 1−2q_pred, with no continuation term because player 3 absorbs
at the row. Its only mixed Nash root on the three active coordinates is
q₀=q₁=q₂=1/2. Indeed, any coordinate below 1/2 forces the next to one and
then the next to zero, which forces the original coordinate to one; a
coordinate above 1/2 similarly forces zero, then one, then zero at the
original coordinate. Both strict alternatives contradict the starting
inequality. But against the three half hazards player 3's Continue payoff
is at least 2·(7/8)=7/4, strictly above its Quit payoff one. This contradicts
its being sure to Quit and exhausts all possible sure rows.

Consequently, for this ALL-NORMAL Fin4 table too, the minimum full debt over
each fixed H-date timing simplex is strictly positive. The obstruction to
fixed-window-only repair therefore survives exact finite Nash, joint entry
reach one, and strict coordinatewise source payoff above every punishment
value. It still leaves an infinite periodic tail as a legal successful
repair, and does not meet the no-uniform-payoff hypothesis of Section 12.

## 15. Duplicate check and the next actual-source question

The proposed mesoscopic owner-punishment graft is not being promoted as a
new supplied-object consumer. The exact existing declaration
`isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits` in
`UniformEquilibrium/Quitting/Cycles/ConditionedDeletedClockSoloCompletion.lean`
already accepts an ARBITRARY family of positive-owner roots, vanishing
opponent-root hazards, values converging to the owner singleton vector,
asymptotically safe outsider pure-Quit endpoints, and owner punishment
normality. It does not require one fixed exact infinite spine.

The newer
`IsCanonicalExactQuittingNashBellmanSpine.isUniformEquilibriumPayoff_soloReward_of_persistent`
in
`UniformEquilibrium/Quitting/Classification/Existence/NormalUniquePersistentNashBellmanSpine.lean`
produces those inputs from a supplied bounded exact spine with one persistent
owner and a summable opponent clock. Its
`abs_value_sub_soloReward_le_of_bounded_bellman` is the concentration adapter.
The summable-all-player alternative instead supplies punishment floors through
`IsCanonicalExactQuittingNashBellmanSpine.punishmentValue_le_of_all_normal_and_summable`
in
`UniformEquilibrium/Quitting/Bellman/Finite/SummableExactNashBellmanPunishmentFloor.lean`.
These statements and their relevant imports were read. They distinguish a
source producer from a concentration consumer; none turns the compact
summable spine of Section 11 into a persistent one.

For comparison, the existing endogenous cyclic source route was also checked:
`InteriorCyclicOwnerConcentrationSubsequence` in
`UniformEquilibrium/Quitting/Cycles/InteriorCyclicDebtEscape.lean` retains
positive per-period owner absorption, vanishing opponent absorption, actual
singleton-law concentration, and vanishing full outsider debts.
`abs_quittingCyclicTerminalValue_sub_ownerSingleton_le` in
`UniformEquilibrium/Quitting/Cycles/OwnerSingletonCyclicConcentration.lean`
controls EVERY cyclic phase by 2M times opponent absorption divided by owner
absorption. Consequently selecting owner-active phases feeds the existing
deleted-Quit consumer once owner normality and vanishing local root error
are supplied. This is a straightforward source-interface composition, not a
new punishment-grafting theorem, and it is not being developed further here.
In particular the robust finite-menu theorem has not been shown to produce
such an owner-concentration family.

`CODEX_SKEPTIC` independently proved the reverse finite-menu characterization
in
[`CODEX_SKEPTIC__ROBUST_FINAL_WINDOW_EQUIVALENCE.md`](CODEX_SKEPTIC__ROBUST_FINAL_WINDOW_EQUIVALENCE.md).
For Fin4 with some positive own singleton, robust final-window reach is
equivalent to no uniform payoff. The reverse proof, not repeated here, uses
the playerwise bound d_j≥s_j·Pr(all Never), full-regret-preserving finite-clock
approximation, and only then deadline enlargement. It is ordinary mathematics,
not newly Lean-checked; its forward direction is the reviewed Section 12.

Thus the next finite-game positive source target has literal quantifiers:

    for every e>0, H≥1, and ρ>0,
    produce N≥H and an independent deadline-N finite-menu e-Nash law p
    with R_p(N−H)<ρ.

The object is an actual finite near-equilibrium on its FINAL menu. One must
not first find a Nash law on a smaller menu and then enlarge that menu as if
its omitted-date deviation were still excluded. Nor does the existence of a
bounded forward-packet consumer or of a sparse finite-clock approximation
produce this source. The new research obligation is to construct such early
absorption while preserving its finite-menu Nash inequalities.

## Next concrete test

Attack the Section 15 finite-menu early-absorption source directly, allowing
an unbounded calendar or infinite executable punishment tail in intermediate
constructions. Sections 1–12 have independent passes; the Section 14 cyclic
regression remains an ordinary proof draft. Do not re-prove the existing
normal unique-persistent or deleted-Quit consumers, and do not confuse
accuracy-dependent finite-clock compression with a zero-debt producer.
