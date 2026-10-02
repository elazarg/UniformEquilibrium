# Finite timing Nash at the stopping-law boundary

Author: `CODEX_RENY`.

## Current status

Ordinary mathematics, not Lean-checked. Sections 7–10 and their dependencies
in Sections 1–3 passed an
[independent adversarial review by CODEX_HILBERT](../feedback/CODEX_RENY__FINITE_TIMING_NASH_BOUNDARY_SECURITY__BY_CODEX_HILBERT.md),
with no unresolved mathematical objection. The full finite-game support
equations imply the boundary identities in Sections
2–3. The normalized two-active-player example in Section 4 exactly refutes
completion that must preserve the selected escaped payoff; it also refutes
better-reply security of the compact stopping-law game. The game has an exact
terminal equilibrium at a different payoff. Thus this example does not
obstruct arbitrary-payoff uniform-equilibrium existence.

The useful remaining question is whether the full equations, under a global
positive terminal exploitability gap, force an alternative actual equilibrium
or approximation. A payoff vector extracted from escaping conditional tails
is not being treated as an executable equilibrium continuation.

Section 7 completes the zero-limiting-Never classification and proves that,
under a global terminal gap Γ > 0, every limiting Never mass in a fixed-owner
finite-Nash sequence is at least Γ/M. The bound concerns the compact limiting
laws; only the owner's opponents are yet bounded at the literal finite laws.
This has an ordinary mathematical review, but no Lean adapter.

Sections 8–9 give the resulting exact annotated spine and a stronger
finite-source reduction. In a hypothetical Fin4 counterexample, every finite
timing Nash profile reaches a uniformly bounded final window with a common
positive probability. Its prefix is exact Nash--Bellman. The escaped payoff
need not be executable, and the delayed example already satisfies the
structural final-window conclusion, so this is a source refinement without a
uniform-equilibrium consumer.

## 1. Question, probability, and agency

Let I be a finite player set. A reward table assigns r(S) ∈ ℝ^I to every
nonempty S ⊆ I, with |rᵢ(S)| ≤ M. Infinite all-Continue play pays zero. Player
i independently draws Tᵢ from a probability law pᵢ on ℕ ∪ {∞}. The first
finite date determines the terminal coalition S = {i : Tᵢ = minⱼ Tⱼ}; all
Tᵢ = ∞ means Never and payoff zero.

These are independent private randomizations. Before absorption the only
public history is the elapsed sequence of unanimous Continue actions. The
usual conditional-hazard realization gives a literal behavioral profile.
Every complete unilateral behavioral deviation is represented by another
stopping law; its payoff supremum equals the supremum over pure dates and
Never. No public random device, restricted deviation class, or finite-memory
assumption is introduced.

Write Uᵢ(p) for prescribed expected terminal payoff, Fᵢ(t;p₋ᵢ) for the payoff
from finite pure date t, Vᵢ(p₋ᵢ) for the payoff from Never, and Bᵢ(p₋ᵢ) for the
complete unilateral cap. Let sᵢ = rᵢ({i}) and dᵢ(p) = Bᵢ(p₋ᵢ) − Uᵢ(p).

The finite timing game at deadline N permits dates 0,…,N−1 and Never. Let
pⁿ be exact mixed Nash profiles at deadlines Nₙ → ∞. Along a subsequence,
assume every finite atom pᵢⁿ(t) converges to pᵢ(t), and U(pⁿ) → u. Set

    aᵢ = pᵢ(∞) = 1 − ∑[t ∈ ℕ] pᵢ(t),
    A = ∏[i ∈ I] aᵢ,     A₋ᵢ = ∏[j ≠ i] aⱼ.

The limiting Never atom aᵢ need not equal the limit zᵢ of the literal Never
atoms pᵢⁿ(∞). If the latter converges, then 0 ≤ zᵢ ≤ aᵢ; aᵢ − zᵢ is escaped
finite mass. This distinction is retained throughout.

The initial question was whether the full finite Nash equations support
payoff security or an escape completion producing terminal approximate Nash
profiles. Sections 2–4 give what survives and an exact false implication.

## 2. Full support equations survive at finite dates

For every i and fixed finite t,

    Fᵢ(t;p₋ᵢ) ≤ uᵢ.                                      (2.1)

If pᵢ(t) > 0, equality holds. Indeed, Fᵢ(t;·) depends continuously on finitely
many opponent atoms and survival probabilities through t. For large n the
date is permitted, and positive limiting own mass makes it a supported action
of pⁿ. The finite mixed Nash inequalities and support equalities pass to the
limit.

Integrating over the limiting own stopping law gives the exact identity

    Uᵢ(p) = (1 − aᵢ)uᵢ + aᵢVᵢ(p₋ᵢ).                     (2.2)

This also covers zero limiting finite mass and zero limiting Never mass. It
does not assert Uᵢ(p) = uᵢ.

For fixed opponents p₋ᵢ, bounded convergence over their stopping times yields

    lim[t → ∞] Fᵢ(t;p₋ᵢ) = Vᵢ(p₋ᵢ) + sᵢA₋ᵢ.            (2.3)

If some opponent stops at a finite date, sufficiently late own Quit is
preempted and agrees with Never; if every opponent chooses Never, the finite
date yields singleton reward sᵢ instead of zero. Hence (2.1) implies

    Vᵢ(p₋ᵢ) + sᵢA₋ᵢ ≤ uᵢ.                             (2.4)

## 3. The conditional escaped payoff

Assume every aᵢ > 0. Define

    bᵢ = (uᵢ − Uᵢ(p))/A
       = (uᵢ − Vᵢ(p₋ᵢ))/A₋ᵢ.                          (3.1)

The second equality follows from (2.2), so the normalizing probability is
joint survival in the first expression and opponent survival in the second.
Equation (2.4) proves

    bᵢ ≥ sᵢ for every i.                                 (3.2)

The vector b has a concrete approximation interpretation. Let Pᴴ(p) denote
the unconditional payoff contributed by absorption strictly before H and let
Aᴴ(p) = ∏ᵢ P_p(Tᵢ ≥ H). For fixed H, the finite prefix quantities converge
along pⁿ, and the actual conditional tail payoff equals

    (U(pⁿ) − Pᴴ(pⁿ))/Aᴴ(pⁿ).

First pass n → ∞ and then H → ∞. Since Pᴴ(p) → U(p) and Aᴴ(p) → A > 0,
these conditional payoffs approach b. In particular |bᵢ| ≤ M, and b lies in
the closed convex hull of {0} ∪ {r(S) : S nonempty}.

Each positive-reach conditional tail of a finite timing Nash profile is
itself a finite timing Nash profile. A profitable conditional tail change
could be spliced after the public survival history and would give a strictly
positive ex ante gain. Thus b is a limit of payoffs of actual conditional
finite timing Nash tails. This fact does not make it a terminal approximate
Nash payoff: their omitted late actions may remain profitable.

If zᵢ = limₙ pᵢⁿ(∞) exists, the conditional tail Never masses converge, in the
same iterated limit, to zᵢ/aᵢ. Positive zᵢ implies Uᵢ(pⁿ) = Vᵢ(p₋ᵢⁿ) for
large n. When all aᵢ > 0, this says that the escaped prescribed tail payoff
bᵢ equals the corresponding limit of tail payoffs from Never. It does not
identify either one with Vᵢ(p₋ᵢ), and it does not erase zᵢ/aᵢ.

## 4. Exact normalized positive-Never counterexample

There are active players 1,2 and dummies 3,4. For a nonempty coalition S put
Q = S ∩ {1,2}. Define the active coordinates by the complete table

| Q | ∅ | {1} | {2} | {1,2} |
|---|---:|---:|---:|---:|
| r₁(S) | 2/3 | 1/3 | 1 | 2/3 |
| r₂(S) | 2/3 | 1 | 1/3 | 2/3 |

For each dummy d, let r_d(S) = −1 when d ∈ S and 0 otherwise. This specifies
all fifteen terminal rows and keeps every coordinate in [−1,1]. Notice that
r₁(S) + r₂(S) = 4/3 for every nonempty S, including dummy-only coalitions.

At any deadline N ≥ 1, each active player chooses date N−1 with probability
1/2 and Never with probability 1/2. Both dummies choose Never. The prescribed
payoff is

    U(pᴺ) = (1/2, 1/2, 0, 0).                            (4.1)

For an active player, Quit at N−1 yields
(1/2)(1/3) + (1/2)(2/3) = 1/2, Never yields (1/2)·1 = 1/2,
and each earlier date yields the strictly smaller singleton payoff 1/3. A
dummy gets zero from Never and at most zero from every permitted date. These
are all finite pure actions, so pᴺ is an exact mixed Nash profile of the full
finite timing game. Every later finite date gives either active player 2/3;
its unrestricted debt is exactly 1/6.

All finite atoms escape. Thus p is all-Never, every aᵢ = 1, the literal
Never limits are z = (1/2,1/2,1,1), and

    b = u = (1/2, 1/2, 0, 0).

The full support equations hold. Both active boundary inequalities are
strict: bᵢ = 1/2 > 1/3 = sᵢ. Nevertheless b is not in the closure of terminal
approximate Nash payoffs.

To prove this last claim, an inequality valid for every stopping profile q
is useful. Let J(q) = ∏ᵢ qᵢ(∞). For any player with sᵢ > 0,

    dᵢ(q) ≥ J(q)sᵢ.                                     (4.2)

Indeed, the cap is at least Vᵢ(q₋ᵢ) + sᵢ∏ⱼ≠ᵢ qⱼ(∞), by the finite-date
limit (2.3). Express dᵢ(q) as the integral of the nonnegative cap slack over
the player's own stopping law and retain only its Never atom. This gives
(4.2), including the case qᵢ(∞) = 0.

If q has every debt at most ε, (4.2) for an active player gives J(q) ≤ 3ε.
The constant terminal social payoff gives the exact identity

    U₁(q) + U₂(q) = (4/3)(1 − J(q)) ≥ 4/3 − 4ε.

If also |Uᵢ(q) − 1/2| ≤ η for i = 1,2, then

    ε + η/2 ≥ 1/12.                                     (4.3)

Thus ε → 0 and U(q) → b are incompatible. This is an exact falsification of
the implication “full finite Nash support equations plus b ≥ s give an
equilibrium completion at b,” even when the literal Never atoms retain
strictly positive limits.

The same game has an exact unrestricted terminal Nash profile: player 1
Quits at date zero and everyone else chooses Never. Its payoff is
(1/3,1,0,0). Player 1 cannot improve on its singleton reward; player 2 gets
1 from continuing and only 2/3 from joining; a dummy cannot gain by quitting.
This is the required distinction between failure of a selected target and
failure of existence at any target.

## 5. Security interpretation and literature boundary

Use the weak topology on probability laws on ℕ ∪ {∞}, with finite dates
isolated and t → ∞. A player secures c at opponents p₋ᵢ if one fixed own
stopping law yields at least c throughout some neighborhood of p₋ᵢ.

In Section 4, (p,u) belongs to the closure of the payoff graph and p is not
Nash. At p itself every active unilateral payoff is at most 1/3 < uᵢ, and
every dummy unilateral payoff is at most zero = u_d. Consequently nobody
can secure strictly more than its coordinate of u. This is exactly a
better-reply-security failure, witnessed by full finite timing Nash profiles.

Reny, *On the Existence of Pure and Mixed Strategy Nash Equilibria in
Discontinuous Games*, Econometrica 67 (1999), 1029–1056, is the intended
original source for the named security notions. The publisher abstract and
original-paper PDF were located:
[publisher](https://doi.org/10.1111/1468-0262.00069),
[original paper copy](https://kylewoodward.com/blog-data/pdfs/references/reny-econometrica-1999A.pdf).
At this checkpoint the exact numbered definitions and theorem hypotheses
have not yet been extracted from the PDF. No external existence theorem is
invoked. The security failure above uses its explicitly stated elementary
definition and does not depend on a paper theorem.

## 6. Sources inspected and scope

The source audit used the finite timing route selected through
`docs/TOOLKIT.md`, not a survey of the Lean tree. Declarations inspected:

- `quittingUniformEquilibriumPayoffConjecture` in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`: an open proposition.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`:
  the positive semantic endpoint, read under its import of
  `TerminalUniformization`; not rebuilt here.
- `QuittingFiniteDeadlineTimingAction`, `quittingFiniteDeadlineTimingGame`,
  `quittingFiniteDeadlineTimingProfile`,
  `quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU`, and
  `quittingFiniteDeadlineTimingProfile_isFiniteDeadline` in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingGame.lean`.
- `QuittingFiniteDeadlineNashProfile.bestResponseValue_eq_max_boundary` and
  `QuittingFiniteDeadlineNashProfile.semanticDebt_eq_boundaryGain_pospart`
  in `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineAdjacentTotalVariation.lean`.
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.
- The definitions `QuittingOpponentTightLawSequence` and
  `QuittingJointTightLawSequence`, and the statement/proof of
  `all_not_compactStoppingLawIsProper_of_singleton_nonnegative`, in
  `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`.
  The last result assumes a globally minimizing, nonattained semantic point;
  the present finite Nash family has not been asserted to satisfy that premise.

Conference comparisons read:
`CODEX_SPINOZA__OMITTED_CAP_CHILD_NEXT_NASH_SEPARATION_AND_OWNER_HANDOFF.md`,
`CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md`,
`CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING.md`, and
`CODEX_HAHN__FINITE_CLOCK_EXPLOITABILITY_KKT_BOUNDARY_OR_CROSS_AMPLIFICATION.md`.
The present note neither preserves a paid cap child nor tries to make its
next finite Nash profile close in total variation.

`Literature/README.md` was read. A bounded search of the relevant quitting
paper transcriptions did not locate Reny's security theorem. No `Literature`
claim is treated as a checked project theorem.

## 7. Zero limiting Never and a uniform positive boundary floor

Assume M > 0. A global terminal gap Γ means that every unrestricted
behavioral profile q has maxᵢ dᵢ(q) ≥ Γ, with Γ > 0. This is a statement about
all complete unilateral behavioral deviations and all behavioral profiles;
it is stronger than a gap within the finite timing games.

### 7.1 The exact zero-a classification

For any sequence in Section 1, if some aₖ = 0, then u = U(p). To see this,
choose H so that player k's probability of stopping before H is near one.
The same is true for pₖⁿ for all sufficiently large n. Payoff contributions
before H converge because they depend on finitely many atoms. Every remaining
contribution is bounded in absolute value by M times the probability that k
has not stopped before H. First let n tend to infinity, then H tend to
infinity. This proves every coordinate's payoff convergence, even though
other players may retain escaping mass.

If at least two aᵢ vanish, every A₋ᵢ = 0. Equations (2.1) and (2.3) then
bound every pure finite date and Never by Uᵢ(p), so p is an exact terminal
Nash profile.

If exactly one aₖ vanishes, every player other than k still has zero debt.
Player k satisfies

    0 ≤ dₖ(p) ≤ max(0, −sₖ A₋ₖ).                         (7.1)

Indeed all finite deviations are capped by Uₖ(p), and (2.4) gives the
displayed upper bound on the possible Never gain. In particular p is exact
terminal Nash if sₖ ≥ 0. Thus a zero-a limit can fail Nash only through the
unique zero-a player's Never deviation and only when its singleton is
strictly negative. No claim that the upper bound in (7.1) is attained is
needed here.

### 7.2 The fixed omitted-date owner's literal opponent floor

Under the global gap, choose for each finite Nash profile an owner of debt at
least Γ, and pass to a subsequence with fixed owner k. Put

    Zᵢⁿ = pᵢⁿ(∞),          Z₋ₖⁿ = ∏[j ≠ k] Zⱼⁿ.

The first omitted date pays exactly Vₖ(p₋ₖⁿ) + sₖ Z₋ₖⁿ. Every permitted
date and Never is capped by Uₖ(pⁿ). Consequently

    Γ ≤ dₖ(pⁿ) ≤ sₖ Z₋ₖⁿ ≤ M Z₋ₖⁿ.                    (7.2)

In particular sₖ > 0, Z₋ₖⁿ ≥ Γ/M, and each Zⱼⁿ ≥ Γ/M for j ≠ k. These
are literal finite-law inequalities, not assertions about escaped mass.
The same conclusion already occurs in the source proof of
`QuittingFiniteDeadlineBoundaryResponseCollision.of_boundaryParticipation`
and is exposed coordinatewise by
`QuittingFiniteDeadlineBoundaryResponseCollision.opponentNever_ge`, both in
`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineBoundaryResponseCollision.lean`.
Its boundary-participation data are unnecessary for the elementary inference
(7.2); this note claims no new theorem for that existing opponent floor.

Thus aⱼ ≥ Γ/M for j ≠ k. If aₖ were zero, Section 7.1 and sₖ > 0 would
produce an exact terminal Nash profile, contradicting the global gap. Every
aᵢ is therefore positive and Section 3 applies.

### 7.3 The owner's limiting floor, with constant Γ/M

From the full finite-date cap and the Never option,

    Bᵢ(p₋ᵢ) ≤ max(uᵢ, Vᵢ(p₋ᵢ)).

Writing uᵢ − Vᵢ(p₋ᵢ) = A₋ᵢ bᵢ in (2.2) yields

    dᵢ(p) ≤ max(A bᵢ, −(1 − aᵢ) A₋ᵢ bᵢ).              (7.3)

The conditional-payoff interpretation proves |bᵢ| ≤ M. If bᵢ ≥ 0 the
right side is at most M A; if bᵢ < 0 it is at most M A₋ᵢ. For i ≠ k both
products contain aₖ, so dᵢ(p) ≤ M aₖ. For i = k, (3.2) and sₖ > 0 imply
bₖ > 0, giving dₖ(p) ≤ M A ≤ M aₖ as well. Applying the global gap to this
actual limiting behavioral profile p gives

    Γ ≤ maxᵢ dᵢ(p) ≤ M aₖ.

Combining this with Section 7.2 proves the common floor

    aᵢ ≥ Γ/M for every i,       A ≥ (Γ/M)^|I|.             (7.4)

In particular the proposed weaker owner constant Γ/(2M) is valid, and the
argument supplies Γ/M without assuming nonnegative singleton rewards for
the other players. This does not bound Zₖⁿ or its limit zₖ away from zero.
The compact-law source has at least Γ/M probability of Never in every
marginal, while a positive fraction of that mass may have come from finite
dates escaping to infinity.

## 8. The actual limiting roots and their escaped annotations

Retain the global gap and fixed-owner subsequence of Section 7. For a finite
date t set

    Sᵢ(t) = P_p(Tᵢ ≥ t),       A_t = ∏ᵢ Sᵢ(t),
    qᵢ(t) = pᵢ(t)/Sᵢ(t),
    v_t = (u − Pᵗ(p))/A_t.                               (8.1)

Here Pᵗ(p) is the unconditional payoff contributed by absorption strictly
before t. Every denominator is positive because Sᵢ(t) ≥ aᵢ ≥ Γ/M. For each
fixed t, sufficiently large finite profiles reach t with positive joint
probability, their conditional tail is finite timing Nash, and their root
and conditional payoff converge to q(t) and v_t.

Ordinary normal-form Nash at a reached date implies exact root Nash against
its conditional successor payoff: the two root deviations are Quit now and
Continue now followed by one's prescribed conditional tail. Each is an
allowed complete timing-law replacement. Conditional independence preserves
the product opponent root law. The exact Bellman equation and these finite
root inequalities pass to the limit. Thus, with r interpreted as the
one-stage terminal payoff table,

    v_t = F_{q(t)}(v_{t+1}),
    q(t) is exact root Nash against v_{t+1},    |v_{t,i}| ≤ M.   (8.2)

The roots are the literal hazards of p, so this is an actual-profile root
spine with possibly nonrealized annotations. The distinction is exact. Let
p^[t] be the conditional tail law on joint survival to t, translated so that
t becomes zero. Equations (3.1) and (8.1) give

    v_t = U(p^[t]) + (A/A_t)b,      v_t → b.               (8.3)

The second term is an escaped-payoff annotation. It is not the payoff of a
continuation available on the limiting profile's Never event.

Since ∏[t < H](1 − qᵢ(t)) = Sᵢ(H), the elementary inequality
q ≤ −log(1 − q) gives the explicit charge bound

    ∑[t ≥ 0] ∑ᵢ qᵢ(t) ≤ −∑ᵢ log aᵢ ≤ |I| log(M/Γ).     (8.4)

This quantitative bound uses the finite Nash source and the global gap; it
does not require the separate Fin4 bounded-capacity theorem. In particular
q(t) → 0. If bᵢ > sᵢ for every player, then q(t) is identically zero for all
sufficiently large t. Indeed the pure-Quit root payoff converges to sᵢ and
the pure-Continue payoff to bᵢ. Exact root Nash therefore assigns zero mass
to Quit eventually, simultaneously in all finitely many coordinates. The
limit spine is then exactly constant (b, all-Continue) after a finite date.
This conclusion concerns the limit. It does not set the original finite
profiles' later root hazards to zero.

These elementary statements are consistent with the existing phantom-source
boundary in
`CODEX_CEDAR__ZERO_BOUNDARY_PHANTOM_CARRIER.md` and
`CODEX_STRENGTHEN__FIN4_EXACT_SPINES_ARE_BALLISTIC_TO_PHANTOMS.md`.
The latter already explains why compact shifts of an exact summable spine
cannot supply a positive returned charge. No novelty is claimed for the
general summable-spine or phantom conclusion. The specific finite-Nash source
floor and quantitative bound (8.4) retain the extra data from Section 7.

## 9. A reached final window of uniformly bounded length

### 9.1 Long remaining deadlines uniformly exclude near-sure roots

Under the same global gap, put η = Γ/(2M). There exists an integer H₀ ≥ 1,
depending on the fixed table and Γ, such that every exact finite timing Nash
profile at every deadline N ≥ H₀ satisfies

    qᵢ(0) ≤ 1 − η for every player i.                    (9.1)

If not, choose deadlines tending to infinity, violating finite Nash profiles,
and one fixed violating player. Extract a fixed omitted-date debt owner,
finite atoms, and payoff limit as in Section 1. The violating date-zero atom
has limiting mass at least 1 − η. Hence its limiting Never mass is at most
η, contradicting (7.4), which gives at least 2η. This proof provides no
effective numerical value for H₀.

Now take any finite timing Nash profile with N > H₀. Its initial root has
positive Continue probability in every coordinate. Conditional-tail Nash
transfer therefore applies. Repeating it at every date t < N − H₀ proves
that these literal roots are reached, satisfy (9.1), and are exact Nash
against their actual conditional successor payoffs. The value at N − H₀ is
the payoff of an actual finite timing Nash profile with deadline H₀.

This excludes a sure root, or a root tending to sure, at an unbounded
remaining distance from the finite deadline. It permits such roots inside
the final H₀ dates. No condition on literal Never masses in that final window
has been assumed.

### 9.2 Bounded exact-block capacity supplies the reach lower bound

Specialize to I = Fin4 and take M to be a positive bound at least the canonical
reward bound. Under no uniform payoff, the checked declaration
`finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`
gives C ≥ 0 bounding the total marginal hazard of every exact block in the
canonical reward box. All conditional finite-profile values lie in that box,
so the prefix in Section 9.1 is such a block. Consequently

    ∑[t < N − H₀] ∑ᵢ qᵢ(t) ≤ C.                         (9.2)

For 0 ≤ q ≤ 1 − η,

    −log(1 − q) = ∫[0..q] 1/(1 − x) dx ≤ q/η.

The literal joint probability of reaching the final H₀ dates therefore has
the uniform positive lower bound

    ∏[t < N − H₀] ∏ᵢ (1 − qᵢ(t)) ≥ exp(−C/η) =: ρ > 0.  (9.3)

Every marginal prefix survival is also at least ρ, since a product of numbers
in [0,1] is no larger than each factor. For N ≤ H₀ the whole profile is the
final window and its entry reach is one.

The exact output is thus a bounded final timing game, reached with probability
at least ρ through one literal exact prefix. Both constants depend on the
table and gap but not on the deadline or the choice of finite Nash profile.
This is a reduction of finite sources. It supplies neither a replacement
continuation for the final window nor a uniform-equilibrium payoff.

### 9.3 Limits of this reduction

Bounded total hazard by itself cannot imply (9.3): one hazard 1 − 1/n has
bounded charge and vanishing survival. Section 9.1 is the necessary uniform
distance from one, and it is available only outside the final bounded window.

The Section 4 example meets the structural conclusion with a one-date final
window, zero prefix hazard, and entry reach one. Its escaped payoff is still
not completable at that target. The example has a uniform equilibrium
elsewhere, so it refutes only a proposed consumer based on the final-window
structure alone; it does not refute a consumer that also uses the global gap.

Similarly, shifting a finite source to its next nonzero region does not yet
give additive progress. The source may contain just one active final region
behind an arbitrarily long all-Continue prefix. One cannot re-extract that
same region repeatedly and count its charge as distinct activity within one
finite block. A successful restart must specify strictly ordered disjoint
regions of the same original finite profile, or pay for a new seam in an
existing compiler.

### 9.4 Additional bounded source audit

The following declarations and files were read for this continuation:

- `HasTerminalExploitabilityGap` and
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.
- `timingLawTail_isNash_of_isNash_of_positiveContinue`,
  `timingMixedPayoff_bellman`, and the first-date/tail definitions in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`.
- `retainedTimingCurrentRoot_isZeroEndpointNash_of_isNash` and
  `isQuittingLiteralExactRootStack_of_retainedTailMixedNash` in
  `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingRealization.lean`;
  these use a supplied retained tail, with positive literal Never masses for
  the full-stack compiler. The zero-tail/reached-prefix reasoning above is
  given separately and no missing adapter is described as already checked.
- `QuittingFiniteExactNashBellmanBlock`, `hazardCharge`, and
  `HasBoundedFiniteExactNashBellmanHazardCapacity` in
  `UniformEquilibrium/Quitting/Bellman/Finite/UnboundedExactBlockHazardCapacity.lean`.
- `QuittingNashBellmanPoint`, `quittingNashBellmanBox`, and
  `IsQuittingNashBellmanEdge` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`, and
  `IsCanonicalExactQuittingNashBellmanSpine` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean`.

No Lean build was run. Narrow searches in the finite timing, retained-tail,
and finite Nash--Bellman source files found no existing exact statement of
the root floor (9.1) or reached final-window conclusion (9.3). This is a
bounded lookup result, not a claim of exhaustive repository novelty.

## 10. What the final window supplies to actual-source consumers

This section adds ordinary deductions and is included in Section 7 of the
independent review linked above. The review confirms the absorption and atom
bounds, the same-profile paid update, and the exact two-cut interface match.

### 10.1 Uniform final-window absorption and a finite atom

The global gap applied to all-Never gives maxᵢ sᵢ ≥ Γ. Fix one player i
with sᵢ ≥ Γ. In any finite timing Nash profile q of positive deadline, let β
be its total absorption probability. Prescribed payoff is at most Mβ. A
deviation to date zero is preempted only by opponents also quitting at zero.
That event has probability at most β, so its payoff is at least

    sᵢ − (sᵢ + M)β.

Finite Nash optimality implies

    β ≥ sᵢ/(sᵢ + 2M) ≥ Γ/(Γ + 2M) =: β₀ > 0.            (10.1)

This is valid for every positive finite deadline and does not use root
exactness after a zero-probability history. Applied to the final H₀-date
conditional law of Section 9, it gives unconditional absorption probability
at least ρβ₀ inside that final window. There are 15H₀ possible finite atoms
(relative date, nonempty terminal coalition), so at least one atom has

    unconditional mass ≥ ρβ₀/(15H₀).                     (10.2)

Along a deadline sequence tending to infinity, pass to a subsequence fixing
the relative date and coalition. Its absolute date still escapes to infinity,
but it belongs to the same original finite profile and retains the displayed
absolute mass floor. The roots and full terminal law are behavioral and use
independent private stopping randomization; this is not an arbitrary convex
combination of terminal rows.

### 10.2 A paid suffix update retaining the original prefix

Apply the global gap and the omitted-date formula to the final H₀-date
conditional finite Nash law. Some player has gain at least Γ from Quit at
relative date H₀. Copy that player's original behavior strictly before the
window entry and, if still live, use this deterministic suffix deviation.
The exact ex ante gain in the original profile is

    (entry joint reach) × (conditional suffix gain) ≥ ρΓ.  (10.3)

Only that player's complete behavioral strategy is changed. Every prescribed
root, finite stopping atom, and stage coalition law strictly before the entry
cut is preserved. The mover's complete cap is unchanged because its
opponents are unchanged, so its own unrestricted debt falls by exactly the
payoff gain. Nothing controls the other players' debt increases. This is one
actual paid deviation, not a Nash or total-debt improvement.

No minimum hypothesis is needed for (10.3). Its role is to retain the exact
long prefix while paying at the final window; it does not improve the already
known existence of an unrestricted profitable deviation at the parent.

### 10.3 Exact interface match and remaining deficit

The definitions `QuittingPositiveMinimumTwoCutBlock` and
`QuittingUniformlyReachedPostMarkTwoCutBlock`, and the theorem
`QuittingUniformlyReachedPostMarkTwoCutBlock.offMinimum_or_exists_paidSplice`
in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveMinimumTwoCutPaidSplice.lean`
were inspected directly. Their fields require an actual root sequence, two
strictly ordered cuts, a supplied positive global carrier minimum, a positive
hazard floor, a positive absolute entry-reach floor, and an earlier marked
date. They do not require the entry or exit to attain the minimum.

For N > H₀, the present final window supplies actual cuts
entry = N − H₀ and exit = N, reach floor ρ, and marginal-hazard floor β₀,
because total absorption never exceeds total marginal hazard. Date zero is
an earlier marked date whenever entry > 0; no special mark property is
encoded by that particular record. Once the separately supplied positive
global-minimum record is inserted, these data instantiate that two-cut
interface. The consumer then gives its existing disjunction: the all-Never
exit is quantitatively above the minimum, or a paid suffix splice exists.
The direct update (10.3) already supplies one paid splice using the gap.

The missing facts are consequential. The source has no proven proximity to
the global minimum, so an off-minimum final exit need not be progress from
the source. It has no full-vector return target and no law that regenerates
the same source after payment. Its positive charge lies in one final region;
the proof does not produce arbitrarily many disjoint charged regions in one
finite word. Thus this does not supply a chronological producer or close the
existing positive-minimum return problem.

The superficially adjacent record `QuittingActualReachedScreenedEndpointMark`
in `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualReachedPairPremarkResidual.lean`
requires a specified mover at a pure endpoint, a distinct opponent quitting
surely at the mark, and a nonnegative selected endpoint gain. A macroscopic
terminal coalition atom from (10.2) supplies none of those three root facts.
No screened-pair adapter is asserted.

## Next concrete test

Test whether the bounded final timing game in Section 9 can be replaced by an
actual approximate equilibrium at a different target, using the retained exact
prefix and the global gap. Alternatively, determine a precise hypothesis
forcing two disjoint charged active regions of the same finite source. The
delayed one-date example must remain a regression: an escaped annotation and
repeated selection of its single final region are not progress certificates.
