# Global minimum debt charges a common-prefix cap replacement

Owner: `CODEX_HILBERT`.

Status: ordinary mathematics, not Lean-checked here; a specialization and
application of existing cap-debt identities. The bounded attack does not
produce a temporal charged return or renewable minimum-fibre child. The
useful conclusion is an exact account identifying how global positivity
obstructs the proposed common-prefix repair. No SCC is eliminated.

## Question and semantic data

Fix four players, a finite real reward table r on nonempty quitting
coalitions, and zero payoff on Never. Players use independent behavioral
randomization and observe the public all-Continue history until absorption.
A unilateral deviation replaces one complete behavioral strategy.

For any actual profile A write U(A) for its expected terminal payoff,
Bᵢ(A) = sup over all complete unilateral deviations of player i's expected
terminal payoff, dᵢ(A) = Bᵢ(A) − Uᵢ(A), and D(A) = ∑ᵢ dᵢ(A).
Let D* > 0 be the global infimum of D over all actual profiles, equivalently
the minimum of total debt on the compact terminal-semantic carrier. No
minimum is assumed to be attained by an actual profile unless explicitly
stated below. A supplied no-UE source supplies this positive number; the
calculations do not replace that source with a bounded-controller minimum.

Let W be a finite literal product-root word, ordered from its outermost root
to its innermost root. Suppose W is the exact cap-prefix word generated from
one literal off-minimum tail A: each root is Nash against the unrestricted
cap of its actual remaining suffix. Write W ⋆ A for the actual prefixed
profile. All quantities below refer to this same W.

Let qᵢ be the probability that i continues throughout W, Qᵢ = ∏[j ≠ i] qⱼ,
and S = ∏ᵢ qᵢ = qᵢQᵢ. Assume S > 0. This holds for every finite word on a
positive-minimum exact cap-prefix port, because D(W ⋆ A) = S D(A) ≥ D*.

For a player i, let T replace only i's complete tail strategy by an exact
cap attainer against A's opponents. Such attainment is a supplied hypothesis;
finite sure-opponent clock constructions are one existing source. Then
Bᵢ(T) = Bᵢ(A), Uᵢ(T) = Bᵢ(A), and dᵢ(T) = 0. The common prefix is copied
literally, so i's parent gain is S dᵢ(A).

The question was whether positive global minimality makes this tail
replacement preserve the exact cap-prefix construction, or gives a
minimum-fibre replacement that can be regenerated. The answer supplied by
the present calculation is a necessary restriction, not an existence theorem.

## 1. The finite-word cap envelope

Fix one observer j. Conditional on following Continue throughout W, let Kⱼ
be the expected prefix absorption payoff, including its unconditional
opponent-absorption probabilities. Let Hⱼ be the largest payoff from a
deterministic quit date inside W against its prescribed opponents. These are
finite-word quantities; Hⱼ does not depend on the tail.

Against a suffix whose cap coordinate is b, the complete prefix cap is

Fⱼ(b) = max(Hⱼ, Kⱼ + Qⱼ b).                                      (1)

Indeed, a unilateral stopping law is an average of pure quit-time payoffs.
The finite prefix choices give Hⱼ. Continuing through the prefix and then
using an arbitrarily accurate suffix best response gives the second term.
The supremum is therefore exactly their maximum; tail attainment is not
needed for (1).

Because W is cap-Nash at its original tail A, the player's prescribed
prefix strategy, followed by a suffix best response, attains Fⱼ(Bⱼ(A)).
Because qⱼ > 0, its Continue-through-W alternative is optimal. Therefore

Fⱼ(Bⱼ(A)) = Kⱼ + Qⱼ Bⱼ(A).                                    (2)

If qⱼ < 1, at least one prefix quit date has positive prescribed stopping
probability. That date is also optimal. Consequently Hⱼ equals the right
side of (2). Every such observer is at the kink of (1).

For an arbitrary replacement tail T put Δⱼ = Bⱼ(T) − Bⱼ(A). Define Eⱼ(W,T)
as the sum of the coordinate Nash defects along W, each evaluated against
the modified suffix cap and weighted by actual joint reach from the outer
root. The arbitrary-root cap-debt telescope gives

dⱼ(W ⋆ T) = S dⱼ(T) + Eⱼ(W,T),    Eⱼ(W,T) ≥ 0.                  (3)

Using (1), (2), and exact prescribed-payoff transport yields equivalently

Eⱼ(W,T) = Fⱼ(Bⱼ(A) + Δⱼ) − Fⱼ(Bⱼ(A)) − S Δⱼ.                  (4)

If 0 < qⱼ < 1, this becomes the exact two-sided formula

Eⱼ(W,T) = Qⱼ[(1 − qⱼ)(Δⱼ)₊ + qⱼ(−Δⱼ)₊].                    (5)

Here x₊ = max(x,0). Thus both signs of an outsider cap change cost positive
root defect. In particular, Eⱼ(W,T) = 0 iff Δⱼ = 0.

If qⱼ = 1, define the nonnegative cash-out slack

ζⱼ = (Kⱼ + Qⱼ Bⱼ(A) − Hⱼ) / Qⱼ.

Then

Eⱼ(W,T) = Qⱼ(−ζⱼ − Δⱼ)₊.                                    (6)

The all-Continue observer can tolerate cap decreases up to ζⱼ and arbitrary
cap increases. Empty W is the separate trivial case S = 1 and E = 0.

All reaches at all finite cuts are positive because S > 0. Hence zero total
E is equivalent to every root remaining exact cap-Nash at its modified
suffix. Equations (5)–(6) completely characterize this compatibility:

- every observer who quits with positive probability anywhere in W must
  retain exactly the same tail cap;
- every observer who never quits in W must satisfy Δⱼ ≥ −ζⱼ.

For the actual cap-attaining mover i, Δᵢ = 0 and dᵢ(T) = 0. Equations
(3)–(6) show that dᵢ(W ⋆ T) = Eᵢ(W,T) = 0. Every defect of the copied word
is borne by nonmovers. This conclusion retains the literal player and word.

This is cap-annotation compatibility. It is not a characterization of all
possible Nash–Bellman annotations for W, and it does not convert the cap
vector into a prescribed continuation payoff.

## 2. What the positive global minimum actually implies

Summing (3), and applying global minimality to the actual profile W ⋆ T,
gives the central inequality

E(W,T) := ∑ⱼ Eⱼ(W,T) ≥ D* − S D(T).                           (7)

Equivalently, if D(T) = D* + e(T),

E(W,T) + S e(T) ≥ (1 − S)D*.                                 (8)

This uses precisely the positive global minimum, rather than local response
cycle geometry. Its positive right side disappears when D* = 0.

Two consequences answer the bounded repair test.

First, if W absorbs positively and T lies on the global minimum fibre,

E(W,T) ≥ (1 − S)D* > 0.                                      (9)

The cap-attaining mover has zero Eᵢ, so (9) is entirely nonmover root
defect. The copied word cannot remain exact cap-Nash. The same statement
holds along a sequence of actual Tₙ approaching the minimum: if Sₙ ≤ 1 − h
for one h > 0, then liminf E(Wₙ,Tₙ) ≥ hD*.

Second, if the whole copied word remains exact cap-Nash, then

D(T) ≥ D*/S,
e(T) ≥ D*(1 − S)/S.                                         (10)

Thus a uniformly absorbing compatible word forces its new literal tail to
stay uniformly off minimum. In a candidate finite-prefix renewal, exact
compatibility and a minimum-fibre suffix cannot both be obtained while
retaining a nonvanishing absorption amount.

The minimum-fibre root-isolation theorems give a separate stronger
prescribed-payoff obstruction: a finite exact Nash–Bellman word ending at a
minimum payoff is all Continue. Neither statement excludes a different
construction with a nonlocal terminal continuation or a source-preserving
restart that pays its seam.

## 3. Stronger global test: the complete response family

Apply (7) to every exact cap-attaining replacement Tⁱ available at A. The
result is a family of valid inequalities

∑[j ≠ i] Eⱼ(W,Tⁱ) + S(D(Tⁱ) − D*) ≥ (1 − S)D*.               (11)

This does not imply that one Tⁱ approaches the minimum. The same strict
off-minimum alternative is permitted for every i. Nor does it bound the
outsider defects above: the unchanged own cap controls exactly one zero
term in (11), while all other cap changes retain both possible signs.

The source's original excess controls its own exact prefix absorption:
D(W ⋆ A) = S D(A) ≥ D*. It provides no upper bound on E(W,Tⁱ), which is
computed at different opponent tails. Subtracting the original identity
only yields

D(W ⋆ Tⁱ) − D(W ⋆ A) = S(D(Tⁱ) − D(A)) + E(W,Tⁱ).             (12)

For an arbitrary finite sequence of complete replacements, summing such
relations does not identify the different root words or their modified
suffix caps. Even when a fixed word is used, closing a horizontal response
cycle only telescopes its endpoint debt changes; the nonnegative E terms
are paid by that word's defects at the intermediate tails. They are not
absorbing charge on an exact chronological return.

This is where the direct global attempt stops. No contradiction follows
from (11), and claiming one would silently assume the missing upper seam
budget or a near-minimum response endpoint. This is not a counterexample to
the sought positive-minimum theorem: no positive-global-gap game is supplied.

The resulting pivot is a global signed account question, not a refinement
of constants: can the retained source law construct a family of executable
replacements for which the accumulated outsider defects in (11) have a
source-inherited upper bound, while positive absorption persists? Without
that additional fact, global minimality prices the repair but does not pay
for it.

## 4. Small exact tests of the cap-envelope calculation

The following Fin4 examples test (5) for both signs. They have D* = 0 and
are not tests of the positive-minimum conclusion. All unlisted reward
coordinates are zero. The word W is one stage: player 0 quits with
probability 1/2 and everyone else continues. Thus S = 1/2, q₀ = 1/2,
Q₀ = 1.

For a positive cap change, set

r₀({0}) = r₀({1}) = r₀({0,1}) = 1,
r₀({2}) = 2, r₁({1}) = −1, r₁({2}) = 1.

In A, player 1 quits at date 0, player 2 at date 1, and the others Never.
In T, player 1 changes to Never. This attains player 1's cap. Exactly:

| Profile | U on coordinates 0,1 | B on coordinates 0,1 | D |
| --- | --- | --- | --- |
| A | (1, −1) | (1, 1) | 2 |
| T | (2, 1) | (2, 1) | 0 |
| W ⋆ A | (1, −1/2) | (1, 1/2) | 1 |
| W ⋆ T | (3/2, 1/2) | (2, 1/2) | 1/2 |

The original W is cap-Nash: player 0 is indifferent, player 1 prefers
Continue, and players 2 and 3 are indifferent. The outsider cap increases
by one and E₀ = (1 − q₀)Q₀ = 1/2 as in (5).

For a negative cap change, set only

r₀({0}) = 1, r₁({1}) = 1, r₁({2}) = −1.

In A, player 2 quits at date 1 and the others Never. In T, player 1 changes
to Quit at date 0, attaining its cap. Exactly:

| Profile | U on coordinates 0,1 | B on coordinates 0,1 | D |
| --- | --- | --- | --- |
| A | (0, −1) | (1, 1) | 3 |
| T | (0, 1) | (0, 1) | 0 |
| W ⋆ A | (1/2, −1/2) | (1, 1/2) | 3/2 |
| W ⋆ T | (1/2, 1/2) | (1, 1/2) | 1/2 |

W is cap-Nash, now with players 0 and 1 both indifferent. The outsider cap
decreases by one and E₀ = q₀Q₀ = 1/2. Coordinates 2 and 3 have zero payoff,
cap and debt in both examples. T is terminal Nash, verifying D* = 0.

Verification: the tables were checked independently with Python Fraction
arithmetic, enumerating all 16 stage action profiles and every pure quit date
through the finite horizon plus Never. Player 2's fixed date screens all
tails; its own rewards are identically zero. These finite pure deviations
therefore give the unrestricted caps displayed above. No floating-point
evidence or Lean build was used.

## Sources and exact overlap

The bounded navigation route was the common-prefix cap-stability family in
`docs/TOOLKIT.md` and the minimum-fibre isolation and signed-seam families in
`docs/FRONTIER.md`.

Inspected declarations and files:

- `quittingUniformEquilibriumPayoffConjecture`, in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`: an open proposition
  definition, not a theorem.
- `HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort`, in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`:
  a supplied positive global minimum and terminal gap construct a literal
  paid cap port at any actual profile.
- `QuittingPaidCapLiftedSource.minimum_mul_totalAbsorption_le_debtDrop`, in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`:
  the source's own absorption account. It does not control replacement caps.
- `quittingTerminalSemanticPair`, `quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticDebt`, in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect`
  and `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`,
  in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`:
  these already contain the one-stage algebra behind (3), (7), and (8).
- `quittingContinuationBestResponseValue_literalRootStack_eq_capFold`, in
  `UniformEquilibrium/Quitting/Root/CommonPrefixCapStability.lean`:
  the scalar max-affine Bellman fold underlying (1). Formula (5) is a
  specialization at a cap-Nash word, not a claim of a new cap-envelope API.
- `quittingTerminalPayoff_literalRootStackProfile_sub_eq_jointSurvival_mul`
  and `quittingTerminalPayoff_copyLiteralRootStackThenDeviation_sub_eq`, in
  `UniformEquilibrium/Quitting/Root/LiteralPrefixDeviationTransport.lean`.
- `QuittingTerminalSemanticSeamChain.debtSum_eq_totalCharge_add_endpoint_add_weightedSignedSeamError`,
  in `UniformEquilibrium/Quitting/Debt/Dynamic/TerminalSemanticSignedSeamTelescope.lean`:
  already supplies the finite telescope with both semantic coordinates.
- `exists_open_exactAllContinueTube_minimumFiber`, in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`:
  inspected its positive-minimum and punishment-normal hypotheses. The
  arbitrary-table Fin4 no-UE wrapper is the maintained frontier route; no
  fresh proof of its upstream normality adapter was attempted here.

The tracked literature model was checked in the opening definitions of
`Literature/SolanAndVieille2001.lean`, after reading `Literature/README.md`.
No paper theorem is invoked by the present argument. The literature lane is
not built and its unproved source statements are not project theorems.

Relevant prior research read:
`CODEX_HAHN__SIGNED_RETRACTION_HYBRID_RANK_NOT_RENEWED_BY_CAP_PORT.md` and
`CODEX_ROOT__FIN4_SCC_PROGRESS_LEDGER.md`. The former's literal-tail objection
is retained: none of the identities above turns a horizontal replacement
into the actual child of the original port. The broader paid-splice collar
and finite-source no-gos were searched narrowly to avoid claiming a recycled
consumer.

## Concrete next check

Independently check the finite-word kink proof (1)–(6), then test a proposed
source-law upper account against (11). The account must bound the outsider
cap changes for the actual cap-attaining response family, not merely the
source's own prefix displacement. Producing that upper account, or proving
that the actual response family necessarily reaches the minimum fibre, is
the remaining mathematical step; neither is established in this notebook.
