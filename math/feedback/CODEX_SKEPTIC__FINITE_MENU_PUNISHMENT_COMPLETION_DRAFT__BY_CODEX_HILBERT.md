# Whole-packet adversarial review: finite-menu punishment completion

Reviewer: `CODEX_HILBERT`.

Reviewed draft:
`notes/CODEX_SKEPTIC__FINITE_MENU_PUNISHMENT_COMPLETION_DRAFT.md`.

Reviewed SHA-256:
`2a2ead51daf086932b13c4e972c4aa5055e5dc88f755c57847db4fd1a167ceef`.

## Verdict

**PASS — no unresolved mathematical objection.** The entire frozen packet
was read first, including its definitions, all four proof parts, examples,
source correspondence, handoff, and nonclaims. I did not read the earlier
completion reviews or the other final review before this audit. This is an
independent whole-packet review, not credit carried over from my earlier
reviews of different RENY boundary results.

The punishment convergence and quantitative completion hold for every finite
nonempty player set and arbitrary signed terminal rewards with zero Never
payoff. EA implies a fixed uniform-equilibrium payoff without a singleton
sign assumption. Its converse correctly requires only one strictly positive
own singleton reward. No exact finite-menu Nash producer, arbitrary-game EA
producer, or unrestricted-equilibrium source is assumed in the forward proof.

No Lean build or implementation was performed. The new packet remains
ordinary mathematics; only the named pre-existing declarations were inspected
as source statements under their imports.

## 1. Claim checked and source of the strategic improvement

The packet proves convergence of the finite-menu opponent min-max values
mᵢ(H) to the unrestricted behavioral punishment values Pᵢ. It then takes an
actual finite-menu e-Nash profile at deadline N, with small joint reach at
N−H, and constructs a new same-prefix actual profile with full regret at
most

    e + 2Mρ + max{2M√ρ, ω(H)+η}.

Only one possibly exceptional player is punished, selected from the source
before play. The remaining players are protected by small **deleted** reach.
The exceptional player's comparison with its old finite cap is supplied by
mᵢ(H), not by an assumed safe source continuation.

This is the key genuine source-strength change. The input does not contain
small full regret, exact Bellman/root-Nash matching, diagonal closed tails,
normality, or support-perfect continuation data. The source's existing tail
may be unsafe and is replaced. The all-request EA property then supplies
exactly the sources needed at successive errors, and the existing terminal
all-errors equivalence handles the fixed uniform payoff target.

## 2. Part A: signed scalar recursion and punishment convergence

The recursive minimization is valid for product opponent laws. Conditioning
each opponent on its own first-date Continue event preserves independence.
Conversely, an arbitrary root and arbitrary independent conditional suffix
can be concatenated player by player. The responder's Continue option is
A+cb, with b the H-date suffix cap. All mixtures of responses are covered
by affinity. This proves m(H+1)=Φ(m(H)), including m(0)=0.

The following potentially false shortcuts were specifically excluded:

* finite-menu punishment values are not assumed nonnegative;
* the sequence is not assumed to increase;
* restriction of both players and opponents is not treated as a monotonicity
  theorem by itself;
* a best reply in the infinite game is not assumed attained;
* weak convergence is not used to pass a changing supremum through a limit.

Monotonicity of Φ instead implies that the whole iteration increases when
Φ(0)≥0 and decreases when Φ(0)≤0. Boundedness and the global 1-Lipschitz
property give a limiting fixed point ℓ.

For ℓ≤P, fixing one arbitrary infinite opponent plan is essential. Its late
finite mass tends to zero. Every fixed early finite reply remains exactly
unchanged after censoring, and the censored Never reply converges uniformly
within the stated coupling estimate. Thus the finite caps converge to the
complete cap of that fixed plan. Taking the infimum only afterwards is valid.

For P≤ℓ, the minimizer of Φ(x), x>ℓ, gives Q≤x and A+cx≤x. If c<1,
stationary repetition has full cap max{Q,A/(1−c)}, including Never, and is
therefore a literal punishment below x. If c=1 and x≥0, all-Never opponents
work. If c=1 and x<0, then Φ(x)=x, and iterating monotonicity from 0≥x
forces m(H)≥x for every H, contradicting ℓ<x. This signed degeneracy
argument is necessary and correctly included.

No stationary punishment equality is needed to prove the convergence: the
stationary root in the last step is constructed directly. Its behavior
agrees with the existing stationary-cap semantics.

## 3. Part B: full-response cap comparison at a literal cut

The independent product identity

    DᵢDⱼ = R ∏[k≠i,j]aₖ ≤ R < ρ

proves that at most one deleted reach exceeds √ρ. This is not a claim that
small joint reach makes every deleted reach small.

The prescribed-payoff change is bounded by 2MR because outcomes before the
joint cut are unchanged. For an ordinary player, every new late response is
at most Lᵢ+MDᵢ, while the old permitted Never response is at least
Lᵢ−MDᵢ. Together with unchanged early finite responses this gives (8).
Its benchmark is the old finite cap Bᵢᴺ, not the old unrestricted cap.

For the exceptional player, Dᵢ>0 makes every opponent survival probability
positive. The conditioned opponent suffix lies literally on F_H after the
shift. There is no need for the player's own survival probability to be
positive. The maximizing suffix response is permitted in F_N when shifted
back: every finite relative date is below H, and Never remains Never.
Therefore Bᵢᴺ≥Lᵢ+Dᵢmᵢ(H).

The appended punishment bounds all new responses that Continue to the cut
by Lᵢ+Dᵢ(Pᵢ+η). Earlier replies are unchanged. Taking a positive part
before removing Dᵢ correctly handles signed Pᵢ−mᵢ(H). This proves (10).
Pure-time extremality then controls every complete behavioral deviation;
no horizon, row count, or factor 1/R appears.

The punishment plan is independent and preselected. Other players who serve
as punishers may themselves deviate; their small deleted reaches are exactly
what pays for that possibility. The proof needs initial terminal Nash only,
not equilibrium or credibility of the isolated tail as a subgame. A public
device identifying the deviator is not hidden in the construction.

## 4. Parts C and D: all-parameter quantifiers and the fixed target

Part C chooses the remaining-window length from ω(H) before asking EA for a
source. It chooses positive finite-menu error and punishment accuracy, then
small reach. Its resulting regret bound is strictly below the requested
terminal error. The named terminal all-errors equivalence legitimately
selects one uniform payoff from these possibly unrelated actual profiles.
The proof does not assume a source payoff target or projective consistency.

For necessity, releasing only one player's Never atom at a late finite date
proves dⱼ≥sⱼA. The changed event outside joint Never is a late **finite**
opponent event whose probability vanishes. This justifies the limiting
deviation gain without asserting attainment of the cap. Only sⱼ>0 is used
to infer A≤E/sⱼ; other singleton rewards may have either sign.

The full-regret TV truncation estimate applies uniformly to every deviating
strategy because only its opponents are changed in the cap comparison.
The order of construction is correct:

    full approximate Nash → finite TV truncation → enlarged displayed menu.

Only after full regret is small is the deadline enlarged. Then all new
finite actions are automatically safe, and the reach after the finite
support is exactly the truncated profile's joint Never mass. This establishes
the independent e,H,ρ,N₀ quantifiers in EA. It never upgrades a supplied
finite-menu Nash law merely by renaming its deadline.

Exact e=0 source existence is neither proved nor used. The output completion
allows e=0 if such a source is supplied, while EA and the converse correctly
use every e>0.

## 5. Explicit falsification attempts and boundary checks

**One player.** The opponent cube has one element and the empty deleted
product is one. Φ(x)=max{s,x}, so the iterates from zero equal max{s,0}
after one step. For small ρ the single player is the exceptional target;
the opponent conditioning and punishment construction are vacuous but valid.
No two-player existence assumption is concealed in Part A or Part B.

**Negative rewards.** A coordinate constantly −1 at every nonempty
coalition gives m(0)=0 and m(H)=P=−1 for H≥1 when one opponent is present.
This falsifies an increasing-only proof but not the packet's signed proof.
For one player with s=−1, all-Never is exact UE and finite-menu e-Nash forces
total finite stopping mass at most e. Thus EA fails at e=1/4, ρ=1/2,
verifying that the converse's positive-singleton hypothesis cannot simply
be discarded.

**M=0 and t=0.** No division by M occurs. If t=N−H=0, the antecedent
requires ρ>1 because R(0)=1; the claimed coarse bound remains valid. For
the meaningful small-ρ use, the antecedent itself rules out this case.

**Zero joint reach, positive deleted reach.** I independently recomputed
the packet's two-clock example. With player 1 sure at zero and player 2
mixing equally between N−1 and Never, player 1's old menu cap and payoff
are both 1. Its omitted date-N payoff is 3/2. For every interior cut,
R=0 but D₁=1. Thus the example genuinely refutes unchanged-tail full safety,
including when H becomes arbitrarily large. Replacing the old tail by
all-Never makes player 1's full cap 1 and retains its sure initial Quit.

**The finite-window punishment correction cannot be omitted.** In this same
example m₁(1)=2/3, while P₁=1. The first identity is direct minimization of
max{1−q,2q}. Independently of the stationary equality, the late-quit formula
against any opponent law of Never mass z gives limiting reply payoff 2−z≥1;
all-Never opponents attain cap 1. Thus ω(1) really can be positive.

**Both players have zero deleted reach.** If at least two players have
already quit surely before the cut under their planned clocks, any unilateral
deviation leaves another such opponent. All Dᵢ=0; changing the suffix
affects neither prescribed payoff nor any cap. This validates the nonexceptional
constant-tail branch without needing a punishment target.

**Late and adaptive deviations.** The exceptional new cap uses a complete
punishment cap. The ordinary-player estimate bounds every late date and
Never uniformly. Hence arbitrarily late or randomized stopping does not
escape the proof. No one-shot-deviation principle is substituted for this
whole-law argument.

## 6. Narrow source and novelty audit

The finite timing encoding in
`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingGame.lean`
was read, particularly `QuittingFiniteDeadlineTimingAction`,
`quittingFiniteDeadlineTimingGame`,
`quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU`, and
`quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU`.
Its menu is exactly Option(Fin N), so the old-cap/shift claims match the
actual production semantics, including N=0 in the punishment recursion.

In `UniformEquilibrium/Quitting/Stationary/MinMax.lean`, the definitions
`quittingBestReplyValue` and `quittingPunishmentValue` quantify over complete
behavioral replies and independent behavioral opponent profiles. The
declarations `quittingStationaryUnilateralCap_eq_max_div` and
`quittingPunishmentValue_eq_stationaryPunishmentValue` include the all-Continue
boundary and do not claim attainment. The near-minimizer
`exists_quittingStationaryPunishmentRoot_lt_add` in `Punishment/InstantPunishment.lean`
is a valid existing source for the appended actual punishment.

The following neighboring consumers were checked at their actual statements:

* `quittingOpponentSurvivalWeight_mul_le_jointSurvivalWeight` in
  `Terminal/TargetTail/DiagonalTargetTailSelection.lean` is the existing
  exceptional-clock inequality, not new content;
* `exists_phaseSwitchProfile_isεAsymptoticNash_of_diagonalJointSurvival`
  in `Terminal/TargetTail/DiagonalTargetTail.lean` requires exact prefix
  Bellman/Nash equations and diagonal target-closed tails;
* `exists_isεAsymptoticNash_of_normalSupportDelayedSwitch` and
  `exists_terminalNash_of_all_normal_of_sequentiallyPerfectAbsorbing`
  in `Classification/Existence/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`
  require the stated switch or normal/perfect absorbing data;
* `nonempty_lateSureSoloCompletion_at_cutoff` in
  `AbsorptionPath/RootSequenceAbsorbingCompletion.lean` takes unrestricted
  source root-sequence Nash and explicit deleted-tail control.

These paths are relative to `UniformEquilibrium/Quitting/`. They do not
already accept the finite-menu source in this packet. The packet's reference
to the `QuittingRootSequenceLateSureSoloCompletion` structure is interpreted
through this actual constructor, whose hypotheses confirm its stated scope.

The existing late-quit identity, `singletonReward_le_nashError_div_never`,
the discrete tightness and late-finite-mass declarations, and
`pmfTV_quittingCounterfactualOutcomeLaw_update_le` were also read at the
paths named in the draft. None licenses using full-Nash consequences on
the input finite-menu Nash law. The draft avoids that mismatch.

A narrow punishment/finite-deadline/target-tail phrase search found no
declaration supplying the finite-menu punishment convergence or the new
finite-menu cap comparison. This supports the claimed bounded repository
novelty, not worldwide priority.

The [original Solan–Vieille paper](https://www.math.tau.ac.il/~eilons/quitting19.pdf)
was checked at its model, Theorem 1.2, Propositions 2.4/2.6, and the stated
Section 2.6 context. Its positive-singleton normalization and joint-exit
restriction, and its support-perfect terminating source, differ from this
packet's arbitrary finite-menu input. The packet correctly uses the checked
terminal semantic endpoint instead of treating the paper's uniformity
wording as a new repository theorem. No paper theorem is required for the
elementary Parts A–D beyond that already checked semantic endpoint.

## 7. Gate type and precise nonclaims

I read `exports/README.md` and the live question's “Alternative finite-game
producer” paragraph. The packet does not answer that producer question; it
says so. Its qualifying mathematical type is a **direct weaker-source
reduction with an actual-data adapter and full terminal semantic consumer**,
not an arbitrary-game producer and not a bare supplied-object verifier.

The strict weakening concerns the missing full-response safety at a supplied
finite source and cut: the example retains a full gap of 1/2 while its
finite error and early joint reach are zero. It is not necessary to claim
that small full regret alone, without any reach geometry, implies the
pointwise source antecedent. The draft's example and discussion support the
intended source comparison.

The qualitative Fin4 equivalence was already known in the conference; the
draft explicitly limits its novelty claim. The direct all-sign completion,
its finite-menu punishment comparison, and its any-finite-player reduction
are substantive changes. EA remains an infinite source obligation; finitely
many successful finite games do not verify it. The completed profile need
not be finite-clock, absorbing, or subgame perfect.

This review supplies one of the requested two independent final checks of
the unrestricted-deviation packet. I find no mathematical repair necessary
on the reviewed hash. Final review-count, link/integrity checks, and any
promotion remain with the author/coordinator; I have not modified the draft
or an export.

## Final administrative freeze confirmation

The final draft at the same path has SHA-256
`c8861a4160c0bf77da4fff22e2961b6cf63980e70656e4277b73edf8b15c3ef6`.
I verified that hash, reread the complete pre-proof material against the
reviewed version, and checked the proof-through-EOF digest
`368cb616c5d19f64f2b9eb6438fedda0edc60c6da43f1122ad2a42557bb4b9c0`.

The changes are administrative only: the external-proof provenance now links
to its durable owned note; the pending/partial-review header is replaced by
the two whole-packet PASS links; and the active question hyperlink becomes
its stable identifier in prose. Mathematical statements, hypotheses, proofs,
examples, and nonclaims are unchanged. This PASS therefore applies to the
final hash above without a new mathematical review round.
