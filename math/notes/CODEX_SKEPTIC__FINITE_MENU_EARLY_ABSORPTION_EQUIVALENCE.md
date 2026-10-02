# A direct finite-menu early-absorption characterization of UE

Author of this synthesis and necessity proof: CODEX_SKEPTIC.
Completion input: `gpt/COMPLETION.md`.

## Status and qualification verdict

The equivalence below is proved in ordinary mathematics for **every finite
nonempty player set**, provided at least one own singleton reward is
strictly positive. Sufficiency does not need that sign assumption. It is
not a proof that the finite-game source exists for arbitrary games.

The completion input passed my original-first independent adversarial review
in `feedback/COMPLETION__BY_CODEX_SKEPTIC.md`; I did not read RENY's review.
This newly assembled equivalence has not itself received two independent
full reviews. Nothing is exported and no new Lean theorem is claimed.

Mathematical relevance and export readiness are separate. The complete
package supplies a genuine direct reduction to a weaker finite-source
condition, with an actual full-cap consumer, rather than just the former
unconsumed final-window restriction. It therefore meets the *mathematical
type* of the export gate's “proved equivalence or reduction that strictly
narrows an open obligation.” It is not a completed answer to the named
finite-game producer question, and this note alone is not export-ready.
Section 7 gives the exact comparison and remaining gate requirements.

## 1. Definitions and exact quantifiers

Let I be a finite nonempty set. For every nonempty coalition S⊆I and i∈I
fix a real reward rᵢ(S). The payoff of infinite all-Continue is zero. Let
M>0 bound all |rᵢ(S)|, and put sᵢ=rᵢ({i}).

Each player uses independently privately randomized behavioral actions.
Before absorption the unique live history is all-Continue. Thus the
profile is equivalent to independent complete stopping laws on
ℕ∪{Never}; the first finite date determines the quitting coalition. One
unilateral deviation may replace a player's entire behavioral strategy,
equivalently its entire stopping law. No external correlation is allowed.

Write Uᵢ(p) for terminal payoff, Bᵢ(p) for the supremum over all unilateral
behavioral deviations, dᵢ(p)=Bᵢ(p)−Uᵢ(p)≥0, and E(p)=maxᵢdᵢ(p).

For N≥1, the deadline-N menu is F_N={0,…,N−1,Never}. A finite-menu e-Nash
law is a product p on F_Nⁱ such that, for every player, replacing its law
by any law on this *same menu* gains at most e. This is not a bound on
unrestricted deviations. For integers t≥0 define

    Rₚ(t)=Prₚ(every finite planned date is at least t),
    A(p)=Prₚ(all players Never).

Never is included in the survival event. Define the early-absorption source
property EA(r) by

    ∀ e>0, ∀ integer H≥1, ∀ ρ>0, ∀ integer N₀≥0,
      ∃ integer N≥max(H,N₀), ∃ actual deadline-N product law p,
        p is finite-menu e-Nash and Rₚ(N−H)<ρ.       (EA)

All probabilities, dates, menus, and cap comparisons refer to that literal
source. There is no source-law consistency requirement between different
requests. In particular N, p, and the selected continuation may depend on
the requested parameters.

**Theorem.**

1. For every finite nonempty quitting game, EA(r) implies existence of a
   uniform-equilibrium payoff.
2. If sⱼ>0 for some j, existence of a uniform-equilibrium payoff implies EA(r).

Consequently, under the positive-singleton assumption,

    UE(r) ⇔ EA(r).                                 (E)

UE means the repository's fixed-payoff, all-sufficiently-long-horizons
notion, with unrestricted unilateral behavioral deviations. This is not
merely existence of a terminal equilibrium payoff depending on accuracy.

## 2. Quantitative completion input, with its proof

Let Pᵢ be the infimum over independent opponent behavioral plans of Bᵢ.
Let mᵢ(H) be the minimum response cap when both the opponent plans and
the responder are restricted to F_H, and set

    ω(H)=maxᵢ(Pᵢ−mᵢ(H))₊.

The completion theorem states that ω(H)→0 and, for any source in (EA),
every η>0 admits a behavioral p̂ agreeing with p before t=N−H such that

    E(p̂)≤e+2Mρ+max(2M√ρ,ω(H)+η).                  (C)

For completeness, the full mechanism is recorded here. Put aⱼ=Prₚ(Tⱼ≥t
or Never) and Dᵢ=∏ⱼ≠ᵢaⱼ. For distinct i,j, DᵢDⱼ≤Rₚ(t)<ρ. There is at
most one exceptional player with Dᵢ>√ρ. When there is one, replace the
continuation from t with an actual punishment plan whose full cap for that
player is below Pᵢ+η, filling the target's own strategy there by Never.
Otherwise use all-Never. The target is selected before play, not detected
after a deviation. Prescribed payoff changes by at most 2MRₚ(t).

Let Lᵢ be the payoff ledger from opponents quitting before t while i
continues. A later new response pays at most Lᵢ+MDᵢ. The old finite menu
contains Never with payoff at least Lᵢ−MDᵢ. Thus every nonexceptional full
cap increases from its old finite cap by at most 2MDᵢ≤2M√ρ. Earlier quit
dates are unchanged.

For the exceptional player Dᵢ>0, conditioning all opponents on survival
to t gives a legitimate product law on F_H. Its finite best response
has conditional value at least mᵢ(H), so the old finite cap is at least
Lᵢ+Dᵢmᵢ(H). The new tail permits at most Lᵢ+Dᵢ(Pᵢ+η). Including the
unchanged earlier replies, the new full cap is at most the old finite cap
plus Dᵢ(Pᵢ+η−mᵢ(H))₊≤ω(H)+η. The original finite Nash inequalities and
prescribed payoff drift now give (C). General behavioral deviations are
covered because their stopping payoffs are mixtures of pure date/Never
payoffs along the single live history.

Here is the needed convergence proof, including signs. For one player i
and a product opponent root y, let Q(y) be immediate-Quit payoff, A(y)
the one-stage opponent-absorption reward sum, and c(y) the probability
all opponents Continue. Define

    Φ(x)=min_y max(Q(y),A(y)+c(y)x).

The minimum exists by compactness. Root/suffix factorization of independent
laws gives m(0)=0 and m(H+1)=Φ(m(H)). The operator is monotone,
1-Lipschitz, and preserves [-M,M]. Its iterates from zero are monotone
in the direction chosen by the sign of Φ(0), hence converge to a fixed
point ℓ.

For any fixed infinite opponent profile, censor its finite dates ≥H to
Never. Its finite-menu cap b_H converges to its unrestricted cap B:
represented finite quit payoffs are unchanged; the censored Never payoff
differs from the original Never payoff by at most 2M times the vanishing
sum of censored opponent masses. This yields limsup b_H≤B. Every fixed
original pure reply eventually belongs to the menu, and Never converges,
so liminf b_H≥B. Since m(H)≤b_H, ℓ≤P.

For x>ℓ, nonexpansiveness gives Φ(x)≤x. Choose a minimizing y, so Q(y)≤x
and A(y)+c(y)x≤x. If c(y)<1, stationary repetition has full cap
max(Q(y),A(y)/(1−c(y)))≤x. If c(y)=1, then A=0 and Q=sᵢ. For x≥0 the
all-Never opponent plan has cap max(sᵢ,0)≤x. For x<0 such a minimizing
root would force Φ(x)=x, whence m(H)=Φᴴ(0)≥Φᴴ(x)=x for every H, contrary
to ℓ<x. Thus P≤x for every x>ℓ, proving P=ℓ. Finite I gives ω(H)→0.

## 3. Sufficiency: EA constructs full terminal approximants

Fix any terminal accuracy ε>0. Choose

    e=ε/4,     η=ε/8.

Choose H≥1 with ω(H)<ε/8. Next choose ρ>0 so small that

    2Mρ<ε/4,     2M√ρ<ε/4.

Apply EA at these e,H,ρ and, for example, N₀=1. Its output has a literal
H-date remaining menu at the low-reach cut. Complete this actual source
using (C). The maximum term in (C) is below ε/4; hence E(p̂)<3ε/4<ε.

Doing this separately for every ε>0 constructs terminal approximate Nash
profiles at all positive errors. The existing theorem
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
then supplies one fixed uniform-equilibrium payoff. The target is selected
by that theorem after the all-error family is obtained; a changing target
has not been substituted for UE.

No sign condition, no normalization, no Fin4 assumption, no exact finite
Nash selection, and no public correlation entered this implication.

## 4. Necessity under a positive singleton

Suppose sⱼ>0 and UE holds. Two elementary law estimates supply the source.

First, every actual profile satisfies

    dⱼ(p)≥sⱼA(p),        so A(p)≤E(p)/sⱼ.          (N)

To prove this, replace only player j's Never atom by a quit at a large
finite date k, keeping every originally finite j-atom unchanged. On the
all-Never event this deviation gains exactly sⱼ. It does not change any
outcome where an opponent quits before k. Its remaining possible effects
are bounded by 2M times the probability that j was Never and an opponent's
first finite quit is at least k. This probability tends to zero. Thus the
deviation gains tend to sⱼA(p), proving (N) by the definition of the full
cap. No best response needs to attain that limiting gain.

Second, censor every player's finite atoms at dates ≥L to Never, retaining
its original Never atom; call the result pᴸ. If θ_L is the sum of moved
marginal masses, then θ_L→0. The independent coupling differs somewhere
with probability at most θ_L, so prescribed payoff changes by at most
2Mθ_L. Against any fixed unilateral replacement only the opponent coupling
is needed; the same bound is uniform over that complete replacement.
Taking suprema and subtracting payoffs gives

    |E(pᴸ)−E(p)|≤4Mθ_L.                            (T)

This is pointwise discrete tightness of a fixed law, not uniform tightness
of an approximate-equilibrium family, and not a bound by the joint reach.

Now fix e>0,H≥1,ρ>0,N₀. Put b=min(e,sⱼρ)/2>0. The terminal semantic
endpoint applied to UE supplies an actual profile with E<b/2. Choose its
cutoff L≥1 so 4Mθ_L<b/2. Then (T) gives E(pᴸ)<b<e, and (N), applied to
the truncated actual profile itself, gives A(pᴸ)<ρ.

Finally choose N≥max(L+H,N₀). The laws pᴸ belong to F_N. They are e-Nash
on that enlarged finite menu because their *full* error is below e. Since
N−H≥L and all finite atoms are before L,

    Rₚᴸ(N−H)=A(pᴸ)<ρ.

This proves EA with exactly its quantifier order and arbitrary lower
deadline bound. Enlargement is used only after obtaining small unrestricted
error. Enlarging an arbitrary finite-menu Nash law is not legitimate.

## 5. Exact boundary tests and a proper weakening of input

**Positivity is necessary for necessity.** With one player and singleton
reward -1, Never is an exact uniform equilibrium. Any finite-menu e-Nash
law has total finite quitting probability at most e: Never gives zero and
its prescribed payoff is minus that probability. Consequently every reach
is at least 1−e. With e=1/4 and ρ=1/2, EA fails for every H,N₀. Thus
UE⇒EA is false without the positive-singleton assumption. The same
phenomenon extends to any fixed number of negative-membership players.

**Positive singleton and trivial source.** For one player with reward 1,
Quit surely at date zero is exact terminal Nash. Given H,N₀, take
N≥max(H+1,N₀). Then R(N−H)=0. Both sides of (E) hold.

**The finite input is strictly weaker than small full error.** Use two
players with r({1})=(1,0), r({2})=(2,0), r({1,2})=(0,0). For every H≥1,
take N≥H+1. Player 1 quits at zero; player 2 chooses N−1 and Never with
probability 1/2 each. This is exact Nash on F_N and has R(N−H)=0. Yet
the full gain from player 1 quitting at N is 1/2: its original payoff is
1 and the late deviation pays 3/2. These sources work for every finite
e>0 and every required H,ρ,N₀ after choosing N large enough, but their
own full regrets never decrease. Completion changes their continuation
and removes that omitted-date obstruction. This is not a four-active
candidate, and no such claim is needed for a logical boundary test.

**Negative punishment floors are allowed.** A player receiving -1 at
every nonempty coalition can be punished at -1 by an opponent's immediate
sure quit. Its m(0)=0 but m(H)=P=-1 for H≥1. The convergence proof allows
decreasing iterates and does not rely on nonnegative punishment values.

The displayed calculations are direct exact arithmetic, not new experiments.

## 6. Relation to the robust final-window statement

The completion gives, by contraposition and for any finite nonempty game
with no UE, fixed H,e_*,ρ>0 such that every actual deadline-N e_*-Nash
law, N≥H, satisfies R(N−H)≥ρ. Indeed a positive terminal gap exists by
the established semantic endpoint; choose the parameters in (C) so its
right side is below that gap. Any violating source would complete to a
contradiction. No Fin4 forward-packet or support-rounding theorem is used.

Together with Section 4, this also extends the previously proved Fin4
robust-window equivalence to arbitrary finite nonempty player sets with
some positive singleton reward. This is a consequence of the direct
completion, not an additional assumption and not a construction violating
the robust window.

The redundant lower-bound quantifier N₀ in EA is retained because it is in
the named target. It is supplied explicitly by necessity. Sufficiency
already follows using N₀=1, so no passage to a cofinal source family is
hidden in the consumer.

## 7. Strict qualification comparison, not a gate waiver

I reread `CODEX_SKEPTIC__APPROXIMATE_FINAL_WINDOW_EXPORT_QUALIFICATION.md`.
Its negative verdict remains correct for the result it assessed:

- that theorem constructed a uniformly *positive* entry-reach floor under
  no UE, plus finite-source rounding/floor information;
- its output did not lower any complete deviation debt, control the omitted
  date, create a full-vector return, or supply renewable charge;
- even the attached two-cut alternative remained unconsumed.

The new result does not magically consume those positive-reach sources.
It is a distinct direct route using *small* reach and an actual completion
with all unilateral caps bounded. Its exact new mathematical output is (C)
from the weaker finite-menu source, with m(H)→P constructed internally.
That replaces the formerly supplied target-tail/punishment compatibility
needed in the nearest existing switching compilers.

The named live target is the “Alternative finite-game producer” in
`questions/FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md`. The
finite-game property requested there is exactly EA on Fin4 tables with a
positive singleton. Sections 2–4 prove a direct dimension-free adapter and
the converse, rather than requesting an additional full-regret field in its
source. For the arbitrary-finite conjecture, the remaining games with all
sᵢ≤0 are already solved by all-Never, so (E) reduces the full finite-quitting
existence question to this finite-game producer on positive-singleton tables.

This is strict narrowing of the data required by the producer-to-terminal
interface: the source need only pass ordinary finite Nash comparisons and
a finite reach test; its own unrestricted regret may stay uniformly
positive, as the explicit example in Section 5 proves. No asymptotic tail,
target match, unrestricted cap bound, support perfection, normality, or
N-dependent accumulation budget is requested from that source. The missing
continuation is now mathematically constructed and consumed.

This is why the *complete reduction package* is of an export-eligible type,
whereas the earlier reach restriction and fixed-positive-slack zero-set
equivalence were not. The latter zero-set equivalence still optimized full
regret over the finite Nash class; (E) instead replaces that full objective
by early reach and supplies the missing full-response completion. The
claim is not based merely on a shorter proof or on renaming an open problem.

Important limits of that assessment:

1. This is **not an answer producing EA** for arbitrary Fin4 tables, and
   therefore not a completed accepted answer to that producer question.
   Qualification is as a direct reduction/strictly weaker source interface,
   not as closure of the question, capacity branch, or conjecture.
2. The older Fin4 RF equivalence already implies the qualitative Fin4 EA
   equivalence by contraposition. Do not claim the Fin4 logical equivalence
   alone is new. The independently identified additions are the explicit
   same-prefix full-cap construction and the any-finite-player direct route.
3. Full publication/export readiness still requires two independent reviews
   of the complete unrestricted-strategy reduction, a consolidated source
   audit and honest literature correspondence, and a complete Lean handoff.
   This review and the existing partial-source reviews cannot simply be
   counted twice for every assertion in this new package.
4. The narrower source obligation is still conjecture-level. No refinement
   operation or proof of its arbitrary-game existence is obtained here.

## 8. Sources and narrow Lean handoff

The exact source audit for completion is in the independent feedback file.
In particular, existing `DiagonalTargetTail.lean` requires exact prefix
Nash/Bellman and a diagonal target-closed endpoint; existing
`NormalSequentiallyPerfectAbsorbingUniformPayoff.lean` requires a normal
support/ledger source. Neither named interface is the finite-menu source
of (C). The exceptional deleted-clock inequality and stationary punishment
characterization themselves are already checked and should be reused.

For necessity and the final consumer I inspected:

- `quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton`
  in `UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`;
- `singletonReward_le_nashError_div_never` in
  `UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumVanishingNeverAlternative.lean`;
- `stoppingLawLateFiniteMass_eq_one_sub_none_sub_finiteHead` in
  `UniformEquilibrium/Quitting/Paths/StoppingLawFiniteTail.lean`;
- `exists_finset_pmfFiniteComplementMass_lt` in
  `MathUE/ProbabilityMassFunction/DiscreteTightness.lean`;
- `pmfTV_quittingCounterfactualOutcomeLaw_update_le` in
  `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

No rebuild or new Lean claim is made. A narrow handoff should introduce
the finite-menu punishment value, prove its scalar recursion and convergence,
prove the finite-cap-to-full-cap switching bound at a literal deadline cut,
and then express EA using actual finite product laws and reach. Its main
theorem should return an actual behavioral approximate Nash profile from
one source, with (C) as the quantitative output. It must not store small
unrestricted regret or punishment compatibility as source fields. The
all-accuracy theorem should invoke the named terminal-to-uniform endpoint;
the converse should reuse discrete-law truncation and the Never estimate.

For rational table data, each strict finite-menu Nash/reach witness can be
checked by finitely many rational comparisons; strict margins can be
obtained in necessity and rationalized at its fixed finite menu. That does
not make the all-parameter EA assertion one finite certificate or give a
terminating search without a source-existence theorem. Real reward inputs
also require a representation before an executable checker can be claimed.

The concrete remaining mathematical output is an actual arbitrary-game
producer of EA: for each e,H,ρ,N₀, find one finite-menu source passing the
finite reach test. No additional completion lemma is required by this
direct route; the producer itself is not proved here.
