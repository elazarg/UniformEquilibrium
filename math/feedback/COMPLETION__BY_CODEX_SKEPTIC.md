# Independent adversarial review of COMPLETION

Reviewer: CODEX_SKEPTIC.

## Verdict and independence

**PASS for the quantitative completion theorem and finite-menu punishment
convergence**, as ordinary mathematics. No unresolved mathematical objection.
I read `gpt/COMPLETION.md` in full before reading any other completion review;
I have not read `feedback/COMPLETION__BY_CODEX_RENY.md`. The small statement
clarifications and expanded limiting argument below should be explicit in a
self-contained final packet. They do not change the claimed bound.

The theorem is a supplied finite-source completion, not an arbitrary-game
early-absorption producer. It does not itself prove UE. My separate
`notes/CODEX_SKEPTIC__FINITE_MENU_EARLY_ABSORPTION_EQUIVALENCE.md` records the
generic finite-game reduction obtained by combining it with a proved
positive-singleton necessity argument.

## 1. Claim reviewed

Fix a finite nonempty player set, zero payoff on all-Never, and arbitrary
real rewards bounded in absolute value by M. Let Pᵢ be the infimum over
independent opponent behavioral plans of player i's unrestricted terminal
best-response cap. Let mᵢ(H) be the analogous minimum with both opponents
and the responder restricted to {0,…,H−1,Never}. Define

    ω(H)=maxᵢ (Pᵢ−mᵢ(H))₊.

For N≥H, let p be an actual deadline-N finite-menu e-Nash product law, and
suppose its joint survival Rₚ(N−H)<ρ. For every η>0 the claim constructs a
behavioral profile p̂ agreeing with p before t=N−H and satisfying

    E(p̂) ≤ e+2Mρ+max(2M√ρ, ω(H)+η),              (C)
    ω(H)→0.

Make the parameters explicit: N,H are integers, H≥1 suffices for the
application, e≥0, ρ>0, η>0, M≥0. Nonempty players are needed for the displayed
maximum over players. M=0 is harmless and gives the zero game. No reward-sign,
punishment-normality, exact finite Nash, or support-perfection assumption is
required. The original note uses Pᵢ without defining it locally; its intended
unrestricted behavioral minmax definition should be included.

## 2. Same-prefix cap calculation

Let aⱼ be player j's probability of a planned date at least t or Never, and
Dᵢ=∏ⱼ≠ᵢaⱼ. For distinct i,j,

    DᵢDⱼ=Rₚ(t)∏ₖ≠ᵢ,ⱼaₖ≤Rₚ(t)<ρ.

Thus at most one player has Dᵢ>√ρ. This includes a one-player game: its
empty opponent product is 1, and there is at most one player trivially.
If exceptional i exists, Dᵢ>0, so the conditional surviving opponent laws
used in the proof are well-defined and still independent. The exceptional
player's own reach may be zero; the argument never divides by it.

Choose one punishment plan against the exceptional player with full cap
below Pᵢ+η. This exists by the definition of the infimum; it need not attain
Pᵢ. The target is a deterministic function of the supplied source p, fixed
before play. If there is no exceptional player, choose all-Never after t.

Prescribed payoff changes by at most 2MRₚ(t), because the strategies agree
on every pre-t live history and prescribed play reaches the changed part
only with probability Rₚ(t).

For a player with Dᵢ≤√ρ, any deterministic quit date before t has unchanged
payoff. Any later date or Never first yields the same pre-t opponent-exit
ledger Lᵢ, and its new continuation contributes at most MDᵢ. The original
finite menu contains Never, whose payoff is at least Lᵢ−MDᵢ. Therefore

    new full cap ≤ old finite cap+2MDᵢ.

This compares the new unrestricted cap to the old *finite* cap, not to the
old unrestricted cap. No missing deadline response is silently discarded.

For the exceptional player, its old finite menu contains a best response
to the conditional H-date opponent law, shifted by t. Hence its old cap is
at least Lᵢ+Dᵢmᵢ(H). Every new deviation that reaches t has payoff at most
Lᵢ+Dᵢ(Pᵢ+η). Taking the maximum with unchanged earlier quit dates gives

    new full cap ≤ old finite cap+Dᵢ(Pᵢ+η−mᵢ(H))₊
                 ≤ old finite cap+ω(H)+η.

Subtracting the perturbed prescribed payoff proves (C), with no factor N,
t, or H multiplying e. This proof only uses the ex ante finite-menu Nash
inequalities; it does not infer approximate Nash of each reached suffix.

## 3. Punishment convergence: checked details

For a product opponent root y, write Q(y) for immediate Quit value, A(y)
for the one-stage opponent-exit reward sum, and c(y) for all-opponent
Continue probability. Compactness of the finite product of mixed-action
simplexes gives a minimizer in

    Φ(x)=min_y max(Q(y), A(y)+c(y)x).

Backward induction gives m(0)=0 and m(H+1)=Φ(m(H)). To justify the minimum
over independent stopping laws, split each opponent law into its date-zero
hazard and its conditional remaining law. Conversely any product root and
independent suffix laws concatenate legally. The only surviving public
history is all-Continue, so no history-dependent correlation is being added.
Continuations of zero-probability surviving branches can be filled arbitrarily.

Φ is nondecreasing and 1-Lipschitz and maps [-M,M] into itself. Its iterates
from zero are increasing if Φ(0)≥0 and decreasing if Φ(0)≤0. They converge
to ℓ, and continuity gives Φ(ℓ)=ℓ. In particular m(H) is NOT silently claimed
to be increasing for every signed table.

For a fixed infinite opponent profile v, censor all its finite dates ≥H
to Never and let b_H be the resulting finite-menu cap. The assertion
b_H→B(v) is valid. Here is the uniform upper argument, which the original
text compresses:

- Each finite reply k<H has exactly its original payoff.
- The censored Never payoff differs from the original Never payoff by at
  most 2M times the sum of opponents' censored late-finite masses, tending
  to zero. Thus limsup b_H≤B(v).
- Every fixed finite reply eventually belongs to the menu with unchanged
  payoff, and the Never payoff converges. Therefore liminf b_H is at least
  every original pure reply payoff and hence at least B(v).

Since m(H)≤b_H, ℓ≤B(v) for every v, so ℓ≤P.

For the reverse inequality fix x>ℓ. Nonexpansiveness gives Φ(x)≤x. A
minimizing root therefore satisfies Q(y)≤x and A(y)+c(y)x≤x. If c(y)<1,
stationary repetition of y has full cap

    max(Q(y), A(y)/(1−c(y)))≤x.

Indeed the payoff of quitting at date k is a geometric interpolation
between these two values; Never gives A/(1−c). If c(y)=1, then A(y)=0
and Q(y) is the own singleton reward s. For x≥0 all-Never opponents have
cap max(s,0)≤x. For x<0 this minimizing root would imply Φ(x)=x; then
m(H)=Φᴴ(0)≥Φᴴ(x)=x for every H, contradicting ℓ<x. This rules out the
only problematic signed degenerate root. Hence P≤x for every x>ℓ, so P=ℓ.

Finiteness of the player set now gives ω(H)→0. No rate is asserted or needed.
Stationary near-minimizing punishment plans are already available in Lean;
the convergence argument does not claim a new stationarity reduction.

## 4. Adversarial boundary tests

**Negative rewards and decreasing finite values.** With two players, let
the reviewed coordinate receive -1 at every nonempty coalition. An opponent
who quits surely at date zero forces payoff -1 against every response.
Thus m(0)=0, m(H)=-1 for H≥1, and P=-1. The monotone-decreasing branch is
essential; an unqualified assertion m(H)≥0 or m(H) increasing would fail.
The actual proof does not make either assertion.

**One player, either sign.** If its singleton reward is s, then for H≥1
m(H)=P=max(s,0). There are no opponent choices; c=1 identically. For s<0,
Never fixes the cap at zero, and for s>0 finite Quit fixes it at s. The
exceptional-player selection and the completion estimate remain valid.

**Zero prescribed reach, deleted reach one.** The original example has
reward pairs r({1})=(1,0), r({2})=(2,0), r({1,2})=(0,0). Let player 1
quit surely at 0 and player 2 choose N−1/Never equally, N≥2. The displayed
menu cap and payoff of player 1 are both 1, but quitting at N yields 3/2.
At every t∈{1,…,N−1}, R(t)=0 while D₁(t)=1. This is an exact falsifier
of unchanged-tail extension, not of (C). The predetermined punishment
against player 1 may use all-Never opponents: P₁=1. It removes the late
gain without changing prescribed play.

Terminology correction only: in that example player 2's own reward is
identically zero. It affects player 1's payoff but is not “strategically
active” if that phrase excludes indifferent/payoff-dummy coordinates. The
counterexample does not need a four-active claim.

**Finite cap genuinely below punishment.** In the same two-player table,
m₁(1)=min_q max(1−q,2q)=2/3, whereas P₁=1: every positive stationary
opponent hazard permits Never payoff 2, and all-Never opponents give cap 1.
Therefore ω(H) cannot simply be replaced by zero at an arbitrary fixed H.

**Adaptive deviations.** Before absorption, all observed actions were
Continue. Any behavioral unilateral strategy induces an independent
stopping law along this single live history. Its payoff is the corresponding
mixture of deterministic finite quit-date and Never payoffs. No detection
of deviation, simultaneous coordination of punishers after a signal, or
public correlation is used. The punishment profile is not asserted to be a
subgame equilibrium; (C) is a root terminal Nash assertion only.

## 5. Narrow source and duplicate audit

Sources were selected through `docs/TOOLKIT.md`. Read exact declarations
under their imports, without any Lean build:

- `quittingPunishmentValue`, `quittingBestReplyValue`,
  `quittingPunishmentValue_eq_stationaryPunishmentValue`, and
  `quittingStationaryUnilateralCap_eq_max_div` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean` establish the exact
  behavioral punishment semantics and existing stationary characterization.
- `exists_quittingStationaryPunishmentRoot_lt_add` in
  `UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean` already
  constructs an actual near-minimizing punishment row.
- `exists_phaseSwitchProfile_isεAsymptoticNash_of_diagonalJointSurvival`
  and `HasExactQuittingDiagonalTargetTailCertificate` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/DiagonalTargetTail.lean`
  already use small joint survival to select an exceptional target. They
  require an exact Nash–Bellman prefix ending at a supplied family of
  target-closed tails. They do not accept an arbitrary finite-menu e-Nash
  law with a remaining H-date menu.
- `quittingOpponentSurvivalWeight_mul_le_jointSurvivalWeight` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/DiagonalTargetTailSelection.lean`
  already proves the exceptional-clock product inequality itself; that
  selection step is not new content of the completion note.
- `exists_isεAsymptoticNash_of_normalSupportDelayedSwitch` and
  `exists_terminalNash_of_all_normal_of_sequentiallyPerfectAbsorbing` in
  `UniformEquilibrium/Quitting/Classification/Existence/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`
  use a support/ledger/floor switch object or a normal sequentially perfect
  absorbing source. Those source hypotheses are not supplied by the present
  theorem, nor needed in its direct cap proof.
- `QuittingRootSequenceLateSureSoloCompletion` in
  `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletion.lean`
  starts from unrestricted root-sequence approximate Nash and late-finite
  deleted-tail control, unlike this finite-menu input.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  is the downstream fixed-payoff semantic consumer, not a proof of the
  missing finite-menu source.

A narrow search for finite-menu/deadline punishment and small-joint-survival
completion found the adjacent interfaces above, not the specific m(H)→P
and finite-menu completion statement. The finite stopping-law tightness
and late-date interfaces were also rechecked for the separate necessity proof.
The corresponding model and restricted solo-exit theorem in
`Literature/SolanAndVieille2001.lean` were inspected as a correspondence
screen only; no original-paper theorem is invoked as a premise here, and
no literature-priority claim is made.

## 6. Scope of this review

The reviewed proof constructs the formerly missing same-prefix completion
from finite-menu error and early joint reach; it does not construct sources
with that reach. The original finite-game producer, charged forward packet,
and inert-chamber obligations remain open. There is no new Lean declaration,
build, export, implementation, or experiment in this review.
