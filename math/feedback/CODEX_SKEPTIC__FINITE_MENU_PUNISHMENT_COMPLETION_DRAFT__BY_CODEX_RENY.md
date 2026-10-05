# Whole-packet review: finite-menu punishment completion

Reviewer: `CODEX_RENY`.

Reviewed file:
[`FINITE_MENU_PUNISHMENT_COMPLETION_AND_EARLY_ABSORPTION_CHARACTERIZATION.md`](../formalized/FINITE_MENU_PUNISHMENT_COMPLETION_AND_EARLY_ABSORPTION_CHARACTERIZATION.md).

Reviewed SHA-256:

    2a2ead51daf086932b13c4e972c4aa5055e5dc88f755c57847db4fd1a167ceef

**Verdict: PASS for the entire frozen mathematical package.** I read all
605 lines before consulting any other final-draft review. No mathematical
objection or required repair remains. The claims are ordinary mathematics,
not newly Lean-checked. I did not edit the draft, another author's notes,
source files, or exports. This review is independent of HILBERT's final
review; the assembler's earlier review is not counted as a final reviewer.

## 1. Exact scope checked

For an arbitrary finite nonempty player set, bounded real coalition rewards,
zero Never payoff, independent private randomization, and unrestricted
unilateral behavioral deviations, the packet proves:

- finite-menu punishment minima mᵢ(H) converge to full behavioral punishment
  values Pᵢ, allowing both reward signs and a one-player game;
- from an ACTUAL deadline-N finite-menu e-Nash source with N≥H≥1 and
  R_p(N−H)<ρ, one literal same-prefix completion satisfies

      E(p̂)≤e+2Mρ+max{2M√ρ, ω(H)+η},

  where ω(H)=maxᵢ(Pᵢ−mᵢ(H))₊→0;
- the stated all-request finite-game source EA implies one fixed uniform-
  equilibrium payoff for every finite nonempty game;
- if some own singleton is positive, UE implies EA, including arbitrary
  requested lower deadline N₀. Thus UE⇔EA on that class.

The sign assumption is not silently added to completion or sufficiency.
The finite-menu input does not contain a full-regret bound. No early-
absorption producer, exact finite-Nash selection theorem, effective horizon
bound, subgame perfection, or solution of the general conjecture is claimed.

## 2. Punishment recursion and convergence

The finite opponent strategy space is a product of compact finite simplexes,
and the finite cap is a continuous finite maximum, so mᵢ(H) is attained.
Every finite opponent law decomposes into a product first root y and a
product conditional suffix on the all-opponents-Continue event. Every such
suffix can also be concatenated with any root player by player. Thus the
recursion

    mᵢ(0)=0,
    mᵢ(H+1)=min_y max{Q(y),A(y)+c(y)mᵢ(H)}

is exact. It does not exchange a minimization and maximization without a
proof or introduce a correlated opponent plan. When c=0, the suffix is
irrelevant and may be fixed arbitrarily.

The scalar operator is monotone and 1-Lipschitz, and preserves [−M,M].
Its iterates from zero are monotone in whichever direction the first step
selects, hence converge to a fixed point ℓ. The decreasing negative-reward
case is retained, not replaced by an assumed increasing recursion.

For ℓ≤Pᵢ, the packet correctly controls the CHANGING finite response menu.
Under censoring opponent finite dates at least H to Never, every retained
pure date below H has EXACTLY its original payoff. The Never payoff changes
by at most 2M times the sum of censored opponent masses, tending to zero.
Therefore the finite caps converge to the full cap: the limsup is bounded
uniformly, and every fixed finite response plus Never supplies the liminf.
There is no unsupported implication from mere pointwise convergence of
tests to convergence of their suprema.

For Pᵢ≤ℓ, x>ℓ implies Φ(x)≤x by nonexpansiveness. A minimizing row has
Q≤x and A+cx≤x. If c<1, stationary repetition has exact full cap
max{Q,A/(1−c)}≤x. The displayed pure-time formula proves this for all
signs, with Never included. If c=1 and x≥0, all-Never opponents have cap
max{sᵢ,0}≤x. If c=1 and x<0, MINIMALITY of the selected row gives
Φ(x)=x, whence Φᴴ(0)≥x and ℓ≥x, contradicting x>ℓ. This correctly
excludes the false negative terminal anchor at the noncontracting row.

No attainment of the infinite punishment infimum is assumed. Selecting
an η-optimal behavioral punishment, or the already checked near-optimal
stationary row, is sufficient. The proof covers the empty opponent cube
of a one-player game and M=0.

## 3. Actual completion, probability modes, and agency

For distinct players, DᵢDⱼ=R∏[k≠i,j]a_k≤R. Hence at most one Dᵢ can
exceed √ρ. The exceptional target, if any, is chosen from the source law
BEFORE play, and its punishment begins at the fixed calendar cut if the
game is still alive. This is not detection of who deviated. The laws in
the appended opponent plan remain independently privately randomized.

Pre-cut live hazards are retained, including the source's off-path live
prescriptions. The hazard convention at a zero OWN survival denominator
is harmless: after that player's own sure earlier quit it cannot affect
prescribed play or an opponent's unilateral deviation, while its own
deviation replaces the whole strategy. Irrelevant absorbed-history
behavior can likewise be retained. Joint-zero reach is not used to erase
counterfactual pre-cut behavior.

Prescribed payoff changes are bounded by 2MR, because only JOINT survival
sees the modified tail. Unilateral cap effects instead use Dᵢ. For a
nonexceptional player, any new response continuing to the cut is at most
Lᵢ+MDᵢ, whereas OLD Never is at least Lᵢ−MDᵢ. Early finite dates are
unchanged. This proves the new full cap is at most the OLD finite cap
plus 2MDᵢ, without pretending that old late dates were already tested.

For the exceptional player, Dᵢ>0 makes every required opponent conditioning
legitimate. Its OWN survival may equal zero; it is not conditioned on.
The original conditional opponents form an actual H-date product law.
Their finite best response is at least mᵢ(H), and the maximizing response
can be lifted to an old date t+a<N or Never. Thus

    Bᵢᴺ(p)≥Lᵢ+Dᵢmᵢ(H).

The new punishment cap is at most Lᵢ+Dᵢ(Pᵢ+η). Taking also unchanged
early responses gives the positive-part correction
Dᵢ(Pᵢ+η−mᵢ(H))₊≤ω(H)+η. That positive part is important when mᵢ(H)
approaches Pᵢ from above. Subtracting the prescribed-payoff bound proves
the claimed error estimate for every player, with no horizon multiplier.

All live public histories are all Continue. Consequently any adaptive
unilateral behavioral strategy induces a stopping law, and its payoff is
an average of deterministic finite-date and Never payoffs. The full cap
bound therefore covers the stated strategy class. Punisher optimality
after the cut is unnecessary: the conclusion is terminal Nash at the
initial node, not sequential rationality in every continuation.

## 4. Both directions of the assembled reduction

For sufficiency, e=ε/4, η=ε/8, ω(H)<ε/8, and sufficiently small ρ make
the completed full error strictly below ε. These parameters are chosen
before asking EA for a source. M=0 is explicitly harmless. Repeating for
all ε>0 invokes the checked terminal-to-uniform endpoint, whose conclusion
selects one fixed payoff target. The packet does not substitute a moving
target for uniform-payoff existence.

For necessity, moving only player j's own Never atom to a late finite date
gives limiting gain sⱼA(p), with a residual bounded by late FINITE opponent
mass. Thus dⱼ(p)≥sⱼA(p). The bound does not require cap attainment.
Truncating a fixed full profile at L changes prescribed values by at most
2Mθ_L and every cap by at most 2Mθ_L uniformly over deviations. Hence
|E(pᴸ)−E(p)|≤4Mθ_L. This is fixed-profile discrete tightness, not a
uniform family tightness claim.

Given e,H,ρ,N₀, b=min{e,sⱼρ}/2 is positive. UE supplies E(p)<b/2;
choose L with 4Mθ_L<b/2. Then E(pᴸ)<b<e and A(pᴸ)<ρ. Choosing
N≥max{L+H,N₀} makes R_pᴸ(N−H)=A(pᴸ), and its already-small FULL error
proves finite Nash on the enlarged menu. The order “full approximation,
truncation, enlargement” is literal. Mere padding of a finite-menu Nash
law is never used. The quantified source can depend on all four requested
parameters, as allowed by EA.

If every own singleton is nonpositive, all-Never is exact terminal Nash
and directly a uniform equilibrium. Thus the unrestricted composite
statement is UE iff [(every sᵢ≤0) or EA], and the remaining arbitrary-
game source question is precisely EA on positive-singleton tables.

## 5. Boundary tests and explicit attempts to falsify the statement

Every displayed boundary calculation checks out:

- All coalition rewards −1 in one reviewed coordinate permit an opponent's
  sure exit, yielding m(0)=0 and m(H)=P=−1 for H≥1.
- With one player, m(H)=P=max{s,0} for H≥1. Negative s gives UE but can
  fail EA; positive s gives the zero-reach sure-Quit source. This also
  tests the empty opponent product and c=1 branch.
- The zero table has M=0 and no division-by-zero issue.
- In the two-clock example, the old cap is 1 and prescribed payoff is 1,
  but the newly admitted late date pays 3/2. Thus full regret is exactly
  1/2 while finite regret and post-date-zero prescribed reach are zero.
  Deleted reach for player 1 remains one. No other pure response gives
  more than 3/2, and player 2's payoff is identically zero.
- In that same table, m₁(1)=min_q max{1−q,2q}=2/3. Against a positive
  stationary opponent hazard Never gives 2; against zero hazard the cap
  is 1. Hence P₁=1 by the checked stationary punishment equality. This
  shows why ω(H) cannot be deleted at an arbitrary fixed H.

These tests target the actual vulnerable implications: signs, degenerate
opponent survival, omitted menu dates, joint versus deleted reach, and
finite versus unrestricted punishment. They do not pretend to be a new
unsolved four-active table or a positive full-gap counterexample.

## 6. Source correspondence checked

I checked the packet's named theorem statements under their imports in:

- `UniformEquilibrium/Quitting/Stationary/MinMax.lean` and
  `UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`:
  `quittingPunishmentValue_eq_stationaryPunishmentValue`,
  `quittingStationaryUnilateralCap_eq_max_div`, and
  `exists_quittingStationaryPunishmentRoot_lt_add` have the stated full
  punishment and near-minimizer roles.
- `UniformEquilibrium/Quitting/Terminal/TargetTail/DiagonalTargetTailSelection.lean`
  and `DiagonalTargetTail.lean`:
  `quittingOpponentSurvivalWeight_mul_le_jointSurvivalWeight` and
  `exists_phaseSwitchProfile_isεAsymptoticNash_of_diagonalJointSurvival`
  supply the existing product inequality and the more structured
  diagonal-tail/exact-prefix consumer, respectively.
- `UniformEquilibrium/Quitting/Classification/Existence/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`:
  `exists_isεAsymptoticNash_of_normalSupportDelayedSwitch` and
  `exists_terminalNash_of_all_normal_of_sequentiallyPerfectAbsorbing`
  require their stated support/ledger or normal source inputs.
- `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletion.lean`:
  `QuittingRootSequenceLateSureSoloCompletion` and its source constructors
  retain the unrestricted Nash/deleted-tail inputs described by the packet.
- `UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumVanishingNeverAlternative.lean`
  and `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`:
  `singletonReward_le_nashError_div_never` and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  have the required strategy class and quantifier order.

I also checked the original stage-payoff definition `quittingGame` in
`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Game.lean`:
active state payoff is zero and an absorbing state repeats its coalition
reward, as the packet states. The direct coupling proofs in the packet
justify its finite-law estimates without requiring a new weak-continuity
claim about unrestricted caps.

For the bounded literature correspondence, I inspected the actual journal
PDF at the linked original source, not only a library summary. Section 1
uses zero nontermination payoff and independent time-indexed actions;
Theorem 1.2 imposes its normalized singleton/joint-exit assumptions.
Propositions 2.4/2.6 use terminating support-perfect sequences, and Section
2.6 discusses uniformity. These are not the packet's finite-menu input.
The packet correctly uses the checked semantic endpoint instead of
importing paper-level uniformity as new theorem truth. [Solan–Vieille,
“Quitting Games” (2001)](https://www.math.tau.ac.il/~eilons/quitting19.pdf)

The stationary punishment identity, product inequality, and tail-splice
idea are existing ingredients. The new combination supplies the missing
OLD FINITE-menu comparison through mᵢ(H)→Pᵢ. No exhaustive literature-
priority claim is made, and none is needed for the bounded source audit.

## 7. Weaker-source qualification and handoff

I read the actual export criteria and the named question's “Alternative
finite-game producer.” This packet is NOT a completed answer producing EA
for that question. Its valid qualification is the proved direct reduction
with a strictly weaker actual-source interface and a downstream semantic
consumer. The source's full regret can remain 1/2 for every requested
finite tolerance and remaining-window length, so the completion is not
merely verifying that an already full-near-Nash source is full-near-Nash.
It constructs the missing tail and bounds every unrestricted response.

The packet expressly recognizes that its qualitative Fin4 equivalence was
already implied by the earlier conference RF equivalence. Its claimed
addition is the explicit same-prefix finite-source completion and the
direct dimension-free route. That is the correct novelty boundary. It
does not repair arbitrary positive-reach final windows, force an early-
absorbing source, or remove the conjecture-level difficulty of EA.

The handoff introduces actual finite punishment minima, scalar recursion,
literal cut cap comparisons, and EA with only finite Nash/reach fields.
It does not encode full regret, target closure, or the desired producer as
a hidden structure field. Its positive-error restriction, one-player and
negative tests, unrestricted cap semantics, and final named semantic
consumer are appropriate for a narrow formalization.

With no unresolved mathematical objection, this review supplies one
whole-packet independent mathematical PASS for the recorded hash. The
other independent final review, administrative freeze/link checks, and
any eventual implementation are separate facts; no Lean or integration
seal is asserted here.

## Administrative final-hash confirmation

The final candidate at the same path has SHA-256

    c8861a4160c0bf77da4fff22e2961b6cf63980e70656e4277b73edf8b15c3ef6

I verified the three agreed nonmathematical changes: durable author-source
provenance, completed whole-review links/header, and the unchanged question
identifier in prose instead of an active-question hyperlink. Reversing only
those three changes in a read-only text stream reproduces the ORIGINAL
reviewed SHA-256

    2a2ead51daf086932b13c4e972c4aa5055e5dc88f755c57847db4fd1a167ceef.

The substring from `## Proof` through EOF separately retains SHA-256

    368cb616c5d19f64f2b9eb6438fedda0edc60c6da43f1122ad2a42557bb4b9c0.

Thus all mathematical content is unchanged, and the whole-packet PASS
applies to the final candidate hash as well. No source or export was edited
as part of this confirmation; promotion remains ROOT's separate action.
