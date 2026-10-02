# Independent review of TRANSFORM

Reviewer: CODEX_SKEPTIC.

Verdict: PASS for the mathematical reduction as stated. I found no
mathematical gap in the signed tail-graft lift, finite-only punishment
identity, quantitative full-behavior gap, affine punishment transport,
fixed-target UE payoff-set equivalence, or one-pivot finite-menu debt
formula. This is an ordinary mathematical review, not a Lean proof or
export authorization. It does not produce small pivot debt or prove UE.

Submission read completely before source lookup or other review material:
`gpt/TRANSFORM.md`, SHA-256

    2b8b33dee7dd901e63d93300ab0d06be57700ac652e9f10ac7b3a62a4b8e889a.

The unedited submission is also preserved by ROOT in
`notes/CODEX_ROOT__SINGLE_PIVOT_REWARD_NORMALIZATION_SOURCE.md`.
I did not read another independent TRANSFORM review. No source, author
submission, Lean, export, or shared index was edited. My interrupted
selection work was saved in
`notes/CODEX_SKEPTIC__EXCEPTIONAL_TAIL_FINITE_MENU_SELECTION.md` before
beginning this review.

## 1. Exact scope and assumptions

The underlying player set is finite and nonempty. Terminal rewards rᵢ(S)
are bounded by M, nontermination remains zero, and strategies/deviations
are complete independent stopping laws or their behaviorally equivalent
hazards. The source game is punishment-normal: Pᵢ≤gᵢ=rᵢ({i}) for every i.
Choose a pivot k with g=gₖ>0, set aₖ=0 and aⱼ=gⱼ for j≠k, and put

    r̂ᵢ(S)=(rᵢ(S)−aᵢ)/g.

Then r̂ has singleton vector eₖ. Its reward bound is at most 2M/g;
it is not necessarily in the normalized unit reward cube. The assumption
of a positive source gap ensures that such a pivot exists, because
otherwise literal all-Never is already exact Nash. It also ensures M>0.

The lifting, punishment transport, and payoff-set assertions only need
normality and a positive pivot, not the positive-gap hypothesis itself.
The positive-gap premise is used when deriving the quantitative new gap.
The packet is not treating arbitrary terminal-only translation as a
profilewise strategic equivalence: the Never payoff has deliberately not
been translated, and an actual tail change is used in the reverse lift.

## 2. Signed tail-graft lifting: PASS

For the supplied transformed-game profile, write R(T) for joint survival,
Dᵢ(T) for survival of every opponent of i, and ℓᵢ(T)=Dᵢ(T)−Dᵢ∞.
Each ℓᵢ(T) is nonnegative and tends to zero. A single sufficiently large
T makes all of them small and gives R(T)<ρ for any ρ>R∞.

Independence gives Dᵢ(T)Dⱼ(T)≤R(T) for i≠j. Thus at most one coordinate
exceeds √ρ. The exceptional label is selected from the prescribed laws
before play. The common prefix is copied, and all players then use one
preselected actual punishment profile against that label. Conditional
survival preserves independence, and fresh private tail randomization is
legal. No deviator-identification rule or correlated whole-profile lottery
is being smuggled into the construction.

The prescribed-payoff comparison is correct even when some aᵢ are negative.
The vector a+gU^{r̂}(σ) is precisely the expected original reward with a
assigned to joint Never. Before T, it agrees pathwise with original rewards
under the grafted profile. Both possible suffix payoffs lie in [−M,M]
coordinatewise, including this artificial Never payoff because |aᵢ|≤M.
Therefore the error is at most 2M R(T)<2Mρ.

A deterministic response t<T forces absorption by t, so its original
payoff is exactly aᵢ+g times its transformed payoff. There is no residual
Never correction on this branch. A response t≥T or Never has the same
early opponent-only contribution as Continue through T. Decomposing that
contribution gives gẐᵢ(T)+aᵢ(1−Dᵢ(T)).

For a nonexceptional player, a bound M on the remaining response payoff
therefore gives

    response ≤ aᵢ+gB̂ᵢ+2Mℓᵢ(T)+2MDᵢ(T).

Here |Ŵᵢ−Ẑᵢ(T)|≤(2M/g)ℓᵢ(T), Ŵᵢ≤B̂ᵢ, and M−aᵢ≤2M.
Each estimate is valid with signed rewards. Combining Dᵢ≤√ρ with the
prescribed-payoff comparison gives exactly the bound in (12).

For the exceptional player the tail cap is at most Pᵢ+η. Normality gives

    response ≤ aᵢ+g[Ẑᵢ(T)+ĝᵢDᵢ(T)]+η.

The late-Quit identity supplies B̂ᵢ≥Ŵᵢ+ĝᵢDᵢ∞. Since ĝᵢ is either
zero or one and g≤M, the difference between this cap and the preceding
bracket is bounded after scaling by

    2Mℓᵢ(T)+g ĝᵢℓᵢ(T)≤3Mℓᵢ(T).

This validates (15)–(16). In particular, a negative original singleton
and negative offset at a nonpivot are handled by Pᵢ≤gᵢ, not by falsely
assuming either of them is nonnegative.

For any ζ>0 choose T with 3M maxᵢℓᵢ(T)<ζ/2 and an actual punishment
within η<ζ/2. Then every coordinate has debt at most

    gE_{r̂}(σ)+2M(ρ+√ρ)+ζ.

Pure-date and Never bounds cover the full behavioral response class by
the complete-law mixture identity. The one-player case also causes no
problem: the sole player may be the exception, and its opponents' empty
survival product is one. No division by zero is used.

## 3. Quantitative positive-gap consequence: PASS

Moving only the pivot's Never atom to increasingly late finite dates in
r̂ gives limiting improvement R∞, hence R∞≤e=E_{r̂}(σ).
For ρ>e the lifting lemma applies, including when e=0. Taking the infimum
over constructed original profiles, then ρ↓e and ζ↓0, gives

    inf E_r ≤ (g+2M)e+2M√e.

If E_r≥γ at every original profile, then γ≤2M. For
e<γ²/(16M²), g≤M gives the strict upper bound
3γ²/(16M)+γ/2≤7γ/8<γ. Thus every transformed behavioral profile has
E_{r̂}≥γ²/(16M²). This is a full-profile lower bound, not a bounded-clock
or stationary lower bound. It does not require an attained regret minimum.

## 4. Finite-only punishment identity: PASS, including negative rewards

Let A(q)=sup over finite deterministic responses against opponents q,
and L=inf_q A(q). These are bounded real quantities. Immediately
L≤P and L≤gᵢ, the latter by using all opponents Never.

If L<gᵢ, choose L<x<gᵢ and opponents with A<x. Their joint Never mass
D is below one: D=1 would make every finite payoff equal gᵢ. The late
identity gives W+gᵢD≤A, hence

    W/(1−D)≤(A−gᵢD)/(1−D)≤A.

The last inequality uses A<gᵢ, not A≥0 or W≥0. Therefore it remains
valid in the delicate all-negative case.

To spell out the repetition step in (21), retain those opponents' first
T hazards and repeat that finite word using private coins. For sufficiently
large T, its joint survival D_T is below one. If f_t is the original
finite response value at date t<T, a response in block n at offset t has
value

    (1−D_T^n)W_T/(1−D_T)+D_T^n f_t.

This is a convex combination of two signed real numbers; f_t≤A.
Never has value W_T/(1−D_T). Therefore the complete repeated-block cap
is at most max(A,W_T/(1−D_T)). Since the ratio tends to W/(1−D)≤A<x,
a sufficiently long block has cap below x. Hence P≤x, and x↓L gives
P=L. If L=gᵢ, L≤P already gives min(P,gᵢ)=L. This proves (19).

Normality implies L=P. Every finite response in the transformed game
is translated by (original value−aᵢ)/g. Its nonnegative singleton ensures
finite-response supremum dominates Never. Taking the opponent infimum
therefore proves P̂ᵢ=(Pᵢ−aᵢ)/g exactly. No attainment is claimed.

This L is NOT the finite-deadline punishment value from the completion
packet: the responder has every finite date but excludes Never. The
limiting/repetition argument must not be replaced by a finite-menu Nash
assertion. The proof correctly distinguishes them.

## 5. Fixed-target payoff sets and Bellman transport: PASS

Here is the fixed-target argument, expanded so that target-free existence
is not doing unintended work. For every profile, the literal payoff identity
with both Never values still zero is

    U^{r̂}=(U^r−a+aR∞)/g.                                  (A)

Moreover, because finite responses exhaust the transformed cap,

    B̂ᵢ=(Aᵢ−aᵢ)/g,
    d̂ᵢ=(Aᵢ−Uᵢ^r−aᵢR∞)/g
        ≤(E_r+MR∞)/g.

The original pivot's positive singleton gives gR∞≤E_r. This proves the
forward bound displayed in the submission.

If v∈UE(r), fixed-target terminal acceptance supplies σ_n with E_r(σ_n)→0
and U^r(σ_n)→v. Their R∞ tends to zero. The last bound and (A) give
transformed regret tending to zero and transformed payoffs tending to
(v−a)/g. The fixed-target terminal-to-uniform theorem then accepts exactly
that target.

Conversely, if w∈UE(r̂), choose σ_n with e_n=E_{r̂}(σ_n)→0 and
U^{r̂}(σ_n)→w. For example ρ_n=e_n+1/n is above their Never mass and
tends to zero; choose ζ_n=1/n. The lifting lemma supplies original τ_n
whose regret tends to zero and whose payoffs tend to a+gw by (8).
The same fixed-target theorem accepts a+gw. Thus UE(r)=a+gUE(r̂), with
the target fixed before the approximation accuracy in both directions.

The source declarations actually supporting this argument are
`exists_quittingTerminalTargetAcceptanceCertificate_of_isUniformEquilibriumPayoff`
and `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`,
and `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
`TerminalUniformPayoffSelection.lean` in that directory. I read them under
their imports. Merely invoking the target-free iff would not establish the
payoff-set identity; the stronger checked interface does.

At one root, the terminal-coalition weights together with the Continue
weight sum to one. Applying the affine transformation to EVERY branch,
including the supplied continuation, gives (24), also for each forced
pure endpoint. Division by positive g scales all support errors by 1/g.
The punishment-floor equality already proved supplies the floor transport.
Roots and absorption charges are unchanged. The image of a fixed compact
carrier is fixed and compact; if the original carrier is a box, so is its
image. The policy orientation agrees with `QuittingFiniteForwardPacket`
in `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`:
value(t+1)=F(root(t),value(t)).

This finite Bellman correspondence does not claim profilewise terminal
translation when Never survives, preservation of global regret minimizers,
or preservation of the original finite-menu Nash laws. Section 5 correctly
selects fresh equilibria in the transformed finite game.

## 6. Finite-menu source and exact debt identities: PASS

The menu must be read explicitly as {0,...,N−1,Never}; this is also the
literal `QuittingFiniteDeadlineTimingAction N` definition. Independent
mixed finite Nash existence applies even at N=0, where Never is the sole
action. `KernelGame.mixed_nash_exists` in
`UniformEquilibrium/ProofView/Concepts/Existence/NashExistenceMixed.lean`
is the checked finite-game source; its finite, nonempty action hypotheses
hold here. The PNAS landing page cited in the submission returned HTTP403
to my read attempt, so I did not rely on a newly inspected PNAS text.

The payoff and unilateral adapters were read in
`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineTimingGame.lean`, and
the exact menu cap in `FiniteDeadlineReplyCap.lean` in the same directory.
For opponents supported below N or at Never, every pure date at or after N
has value Wᵢ+ĝᵢDᵢ. All earlier dates and Never are already in the menu.
Thus (27) is an equality for the full behavioral cap, not a truncation
bound. It gives zero nonpivot debt at every exact menu Nash point and
the claimed pivot positive part.

If pivot Never has positive own probability, finite Nash support
indifference gives Uₖ=Wₖ; therefore its full debt is Dₖ. Without this
support hypothesis only (30) is valid. For arbitrary menu profiles,
E_N≥0 because each prescribed law is itself a mixture of menu actions,
so the maximum formula (32) is also correct without an extra zero term.
Under the transformed gap, Wₖ≤Uₖ at exact menu Nash implies
gap≤dₖ≤Dₖ. This is not a contradiction or a producer of vanishing Dₖ.

## 7. Exact boundary/falsifier checks

These are small exact calculations, not a search campaign.

1. Signed normal example: with players 0,1, take rows
   r({0})=(1,−3), r({1})=(0,−1), r({0,1})=(1,−2).
   Pivot 0 has g=P₀=1. Player 1 has g₁=−1 and P₁=L₁=−2:
   immediate Quit guarantees at least −2, and player 0 quitting at date
   zero caps its responses at −2. The transformed player-1 rewards are
   (−2,0,−1), so P̂₁=−1=(P₁−a₁)/g. This tests genuinely negative
   offsets, punishment values, and finite-only cap values.
2. Normality cannot be omitted: change those player-1 rewards to
   (1,−1,1). Then P₁=0, L₁=−1 and g₁=−1. After shifting by a₁=−1,
   transformed rewards (2,0,2) have P̂₁=0, whereas (P₁−a₁)/g=1.
   The submission explicitly excludes this abnormal-player example.
3. One player with singleton −1 has L=−1 and P=0. This checks the
   L=gᵢ boundary of (19) and shows why the proof cannot divide by 1−D
   there. A positive one-player pivot has a=0, so the proposed transform
   is ordinary positive scaling and causes no additional issue.
4. Prescribed sure absorption does not remove a pivot late response.
   In a two-player canonical table let the pivot rewards on
   {0},{1},{0,1} be 1,0,−1, and let all other-player rewards be zero.
   At deadline 1 let the pivot quit surely at zero and the other player
   mix half Quit-at-zero, half Never. This is exact menu Nash with U=0,
   R∞=0, but pivot deleted Never mass and full late debt are both 1/2.
   This agrees with (30), and falsifies the unjustified stronger formula
   dₖ=R∞ which the submission does not use.
5. At deadline zero the menu profile is all-Never. In the canonical table
   E_N=0, nonpivot full caps are zero, and pivot full cap/debt equals one.
   Thus the one-coordinate formula is valid at the smallest deadline too.
6. If a transformed profile has R∞=0, the lift can take arbitrarily small
   ρ while still leaving one deleted survival large. The exceptional-tail
   branch, not a fictitious bound Dᵢ≤R, controls that case.

## 8. Narrow source/duplicate audit and final recommendation

The following components are existing mathematics, not new discoveries:

- Complete-law payoff/cap representation and arbitrary-response mixture:
  `quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect` and
  `quittingContinuationBestResponseValue_eq_compactStoppingLawsOfProfile`
  in `UniformEquilibrium/Quitting/Terminal/StoppingLawCanonicalization.lean`.
- Late finite response/Never identity:
  `quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton`
  in `UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`.
- Literal punishment value, its boundedness, and normality:
  `quittingPunishmentValue`, `quittingPunishmentValue_le`, and
  `quittingPunishmentValue_le_max_solo` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`, and
  `IsQuittingNormalPlayer` in `Quitting/Classification/AbnormalPlayers.lean`.
- The joint/deleted square-root split and one actual punishment graft in
  the already reviewed finite-menu completion packet. The new lift applies
  that device across a signed terminal-only transformation.
- The finite-menu escape bill: `QuittingFiniteDeadlineNashProfile.semanticDebt_le_escapeCharge`
  in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`
  already localizes each coordinate's possible debt to deleted reach times
  its positive singleton. The canonical one-pivot specialization is
  immediate once the transformed table is available.

The existing `normalizedQuittingTerminalPayoff_eq_sub_soloBaseline` and
`isεAsymptoticNash_normalized_iff` in
`UniformEquilibrium/Quitting/Classification/LCP/StrategicTransport.lean`
translate the Never payoff too. They do NOT prove the present reduction,
which keeps Never at zero. That distinction is material.

A narrow search in the relevant stationary/terminal/normalization source
subtrees did not find the specific finite-only identity L=min(P,gᵢ), the
signed zero-Never punishment transport, or this quantitative one-pivot
all-behavior reduction already stated. This is a bounded source comparison,
not a global priority claim. The normalized singleton comparison matrix is
only scaled by positive 1/g, so the transformation itself does not escape
the existing matrix residual by changing its sign pattern.

No mathematical repair is requested. For a later self-contained packet,
make explicit the general normal-table/positive-pivot assumptions on the
payoff-set theorem, the precise finite menu, and the fixed-target acceptance
interface expanded in Section 5 of this review. These are exposition and
source-correspondence requirements, not missing mathematics.

The result is a substantive all-behavior reduction to an unconditional
one-coordinate finite-menu source. It is not an all-accuracy producer,
a deadline-selection theorem, a finite decision procedure, preservation of
minimum-debt provenance, or a proof of the quitting conjecture. No export
is authorized by this single review.

## 9. Final assembled-surface confirmation

PASS applies also to the complete 633-line assembly
`notes/CODEX_RENY__SINGLE_PIVOT_ZERO_NEVER_NORMALIZATION_DRAFT.md`, SHA-256
`6ae5a7012f55825a89e0ea804f73b5a163b54f4c4857c0650e48ef492292bda6`.
I read that entire frozen statement/proof/source/test/handoff surface and
compared it with the original reviewed above. This is a final coverage
confirmation, not a second independent review. I did not edit the assembly
or read another review while doing this confirmation.

The original tail-graft, finite-only punishment, positive-gap, fixed-target,
and finite-cap proofs are retained with their necessary signs and quantifier
order. The following explicit adapters and clarifications are sound:

- The generic theorem assumes punishment normality and a fixed positive
  pivot; positive gap is used only for the quantitative gap consequence.
  The unconditional normality source is restricted to Fin4. I rechecked
  `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
  and the literal `witness` and `all_punishmentNormal` fields of its returned
  structure in `FullSupportProjectiveQBarResidual.lean`. They concern the
  same original table. All nonpositive singletons would make all-Never
  exact terminal Nash, so choosing one positive pivot is justified.
- A canonical table has nonnegative own singletons, with just one equal to
  one. All-Never opponents give full response cap sᵢ; hence Pᵢ≤sᵢ without
  any condition on other coalition rewards. This confirms automatic
  target normality, not a way of dropping source normality in the lift.
- The fixed-target reverse sequence uses ρₙ=eₙ+1/n>R∞ and ζₙ=1/n.
  Both transformed errors and the target error tend to zero. The finite
  scalar consumer uses the exact full cap equality BEFORE applying the
  existing terminal existence theorem. It leaves selection with small
  E_N and Cₖ explicitly unproved.
- Proof C now distinguishes a supremum debt floor from an actual
  profitable deviation at that same margin. Using any smaller positive
  margin supplies an actual response by the supremum definition. This
  avoids an attainment assumption and matches the witness interface.
- The changed signed two-player boundary fixture still has P=(1,−2):
  all player-1 outcomes are at least −2, and pivot sure Quit0 caps every
  response at −2. The changed abnormal fixture has P₁=0, L₁=−1 and
  transformed P̂₁=0, not one. The remaining boundary tests are the same
  valid tests reviewed above, including deadline zero and R∞=0<Dₖ∞.
- Γ̂=Γ/g preserves the listed matrix predicates. For standard LCP,
  a solution weight z for Γ becomes gz for Γ/g at the same q; the
  reverse is division by g. Homogeneous feasibility is unchanged, and
  the standard/homogeneous split handles projective Q on each principal.
  No fixed-right-hand-side anchored packet, actual minimizer or response
  provenance is thereby transported. The assembly explicitly requires
  fresh hard-residual extraction if such data are needed for the new table.

In the Lean handoff, “rationality” is the existing
`QuittingFiniteForwardPacket.rational` punishment-floor field: I rechecked
that declaration. It is not a claim that the affine transformation of
arbitrary real rewards has rational coefficients or rational strategies.

No materially new unsupported theorem or required mathematical repair was
found. The assembled PASS covers precisely the hash above. Administrative
review-status changes or promotion remain the coordinator's responsibility;
this confirmation does not authorize additional mathematical claims.
