# Single-pivot zero-Never normalization and the finite-menu scalar source

Authors: external proof submission preserved by CODEX_ROOT; packet assembly
and source adapters by CODEX_RENY.

Source: [preserved submission](../notes/CODEX_ROOT__SINGLE_PIVOT_REWARD_NORMALIZATION_SOURCE.md).
The original `gpt/TRANSFORM.md` was reviewed at SHA-256
`2b8b33dee7dd901e63d93300ab0d06be57700ac652e9f10ac7b3a62a4b8e889a`.
Independent whole-original reviews:
[CODEX_SKEPTIC](../feedback/TRANSFORM__BY_CODEX_SKEPTIC.md) and
[CODEX_HILBERT](../feedback/TRANSFORM__BY_CODEX_HILBERT.md), both PASS.
Both reviewers confirmed the complete assembled statement/proof surface PASS;
their final confirmations are recorded in the linked reviews. ROOT alone
authorizes promotion.

## Exact statement

Let I be a finite nonempty player set. A quitting table assigns a real payoff
vector r(S) to every nonempty S⊆I; play absorbs when exactly S first choose
Quit together. Infinite all-Continue pays zero. Put sᵢ=rᵢ({i}), and choose
M>0 with |rᵢ(S)|≤M for every i,S. Let Pᵢ be the unrestricted behavioral
punishment value, U^r(σ) the terminal payoff vector, Bᵢ^r(σ) the supremum
over all complete unilateral behavioral responses, dᵢ^r=Bᵢ^r−Uᵢ^r, and
E_r(σ)=maxᵢdᵢ^r(σ). These quantities and the exact strategy model are
defined below.

### General punishment-normal transformation

Assume Pᵢ≤sᵢ for all i, and fix k with g=sₖ>0. Define

    aₖ=0,       aⱼ=sⱼ for j≠k,
    r̂ᵢ(S)=(rᵢ(S)−aᵢ)/g,                           (1)

with infinite all-Continue STILL paying zero. Then the own-singleton vector
of r̂ is eₖ, its rewards satisfy |r̂ᵢ(S)|≤2M/g, and:

1. For every transformed profile σ, every ρ>R∞(σ), and every ζ>0, there
   exist a finite date T and an actual original profile τ agreeing with σ
   before T such that

       E_r(τ)≤gE_r̂(σ)+2M(ρ+√ρ)+ζ,
       ‖U^r(τ)−a−gU^r̂(σ)‖∞≤2Mρ.                  (2)

   The construction uses at most one preselected punishment target, not
   identification of a deviator.
2. Punishment values and uniform-equilibrium payoff SETS obey

       P̂ᵢ=(Pᵢ−aᵢ)/g,
       UE(r)={a+gv : v∈UE(r̂)}.                    (3)

   In particular the transformed game remains punishment-normal.
3. If, in addition, E_r(σ)≥γ>0 for every original behavioral profile σ,
   then every transformed behavioral profile satisfies

       E_r̂(σ)≥γ²/(16M²).                          (4)

4. Every product root q and supplied continuation v satisfy

       F_r̂(q,(v−a)/g)=(F_r(q,v)−a)/g.              (5)

   Pure root-action payoffs transform by the same affine map. Consequently
   a supplied exact forward Bellman packet with support tolerance δ,
   punishment floors P−δ, and one fixed compact carrier K maps to such a
   packet with tolerance δ/g, floors P̂−δ/g, carrier (K−a)/g, identical
   roots, and identical absorption charge.

The positive-gap assumption is used only for (4), not for (2), (3), or (5).
Original nonpivot own-singleton rewards may have either sign.

### Unconditional Fin4 counterexample adapter

For every Fin4 quitting table r with NO uniform-equilibrium payoff, the
already established same-table hard-residual theorem supplies all-player
punishment normality and a positive unrestricted terminal gap. At least one
sₖ is positive. Thus (1) produces, without adding players or changing Never,
a Fin4 table with own-singleton vector eₖ, no uniform-equilibrium payoff,
the positive bound (4), and exactly transported punishment values.

Consequently a Fin4 counterexample exists if and only if one exists with
own-singleton vector eₖ for some fixed player k (equivalently e₀ after a
permutation of labels). The generic transformation above is conditional on
punishment normality; only this Fin4 source adapter obtains normality from
the bare no-UE assumption.

### Actual finite-menu source on the canonical table

For N≥0 let F_N={0,…,N−1,Never}. Every player independently mixes over
F_N, with the actual quitting payoffs. For a product law p let Bᵢ^N(p)
be its displayed-menu response cap, E_N(p)=maxᵢ(Bᵢ^N−Uᵢ), and write

    Wᵢ(p)=Uᵢ(Never,p₋ᵢ),
    Dᵢ(p)=∏[j≠i]pⱼ(Never),
    Cₖ(p)=Wₖ(p)+Dₖ(p)−Uₖ(p).                     (6)

Every table with own-singleton vector eₖ is automatically punishment-normal:
against all-Never opponents a player's full cap is max(sᵢ,0)=sᵢ, so
Pᵢ≤sᵢ. Thus the canonical target class requires NO extra restriction on
punishment or on its other reward entries. Source normality remains an
essential premise of the signed transformation itself.

For EVERY product law on that menu in any canonical table s=eₖ,

    Bⱼ^∞(p)=Bⱼ^N(p)                         (j≠k),
    Bₖ^∞(p)=max(Bₖ^N(p),Wₖ(p)+Dₖ(p)),
    E_∞(p)=max(E_N(p),Cₖ(p)).                       (7)

At EVERY deadline N an exact mixed finite-menu Nash law exists. At EVERY
such equilibrium, not merely one selector,

    dⱼ^∞(p)=0                 (j≠k),
    dₖ^∞(p)=[Cₖ(p)]₊≤Dₖ(p).                      (8)

If pₖ(Never)>0, also Uₖ=Wₖ and dₖ^∞=Dₖ. Without that support condition
only (8) is asserted. Under the transformed gap in (4), every exact finite
Nash law therefore has Cₖ(p)≥γ²/(16M²) and Dₖ(p)≥γ²/(16M²).

## Conjecture-facing change

The live obligation named “FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER”
includes an alternative source theorem: for every e>0, H≥1, ρ>0, and N₀,
construct an actual finite-menu e-Nash law at some N≥max(H,N₀) with
R_p(N−H)<ρ. The completion theorem converts that source to UE, but no
general producer is presently supplied.

This packet strictly narrows the table and deviation dimensions of a
potential counterexample: the SAME four players and zero Never payoff can
be retained while making exactly one own singleton positive, equal to one.
All unrestricted debt of any exact finite-menu equilibrium is then one
explicit scalar in one fixed player. For approximate menu Nash, (7) isolates
the only additional full-response condition beyond the displayed error.
Thus it suffices to select, for every e>0, an actual canonical finite-menu
law with E_N≤e and Cₖ≤e; (7) and the terminal consumer then give UE.

The packet does NOT construct such a small-scalar selector, early absorption,
an arbitrarily charged packet, or a temporal move between actual sources.
The lower bound on every exact finite selector under no UE is a restriction,
not a contradiction. It neither requires nor proves that exact finite-Nash
selection is a complete architecture for all solved games.

## Definitions and assumptions

### Probability, information, and deviations

Before absorption the only public history is a string of all-Continue
outcomes and its length. A behavioral strategy therefore gives a hazard
at each finite date; it is equivalent to a complete stopping law on
ℕ∪{∞}, where ∞ is literal Never. Players use independent private random
coins. Their first finite stopping date determines the terminal coalition;
if all choose ∞, every payoff is zero. Actions after absorption are irrelevant.

A unilateral deviator may replace its ENTIRE behavioral strategy. Against
fixed opponents its reward is an expectation of pure-date/Never rewards,
so its cap is

    Bᵢ=max{sup[t∈ℕ]fᵢ(t), Wᵢ},
    fᵢ(t)=Uᵢ(t,σ₋ᵢ),       Wᵢ=Uᵢ(Never,σ₋ᵢ).    (9)

The supremum need not be attained. Every prescribed law is an available
response, so dᵢ=Bᵢ−Uᵢ≥0. All payoffs and caps lie in [−M,M], and
0≤E_r≤2M. Punishment means the genuine bounded infimum

    Pᵢ=inf[σ₋ᵢ] Bᵢ(σ₋ᵢ),                         (10)

over independent complete opponent plans, not a joint correlated plan.
For every η>0 an actual opponent plan has cap ≤Pᵢ+η. The punished
player's own tail can be filled arbitrarily; the cap overwrites it.

For marginal stopping variables Tᵢ define

    Sᵢ(T)=Pr(Tᵢ≥T),       R(T)=∏ᵢSᵢ(T),
    Dᵢ(T)=∏[j≠i]Sⱼ(T),
    R∞=∏ᵢPr(Tᵢ=∞),       Dᵢ∞=∏[j≠i]Pr(Tⱼ=∞).

Empty products are one. In particular R is joint reach; Dᵢ is the reach
after deleting the deviator's own survival factor. They cannot be interchanged.

### Fixed-target uniform equilibrium

v∈UE(r) means that for every ε>0 there are one behavioral profile σ and
one finite threshold N₀ such that for EVERY horizon n≥N₀, σ delivers
expected n-stage average payoff within ε of v in every coordinate, and
no complete unilateral behavioral replacement gains more than ε at that
horizon. The target v is fixed before ε; σ and N₀ may depend on ε.

The existing fixed-target terminal acceptance theorem is used in both
directions: v∈UE(r) exactly when there are terminal approximate Nash
profiles whose errors tend to zero and whose terminal payoffs tend to v.
This fixed-target statement, not only target-free existence, is needed for
the equality of payoff sets in (3).

## Source correspondence

Paths beginning `UniformEquilibrium/` are relative to the repository root;
shorter `Quitting/` and `Diagnostics/` paths are within that directory. The
declarations were read under their imports; no new result in this packet is
called Lean-checked.

- Complete stopping-law response semantics: the declarations
  `quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect` and
  `quittingContinuationBestResponseValue_eq_compactStoppingLawsOfProfile`
  in `UniformEquilibrium/Quitting/Terminal/StoppingLawCanonicalization.lean`.
- Late-Quit limit:
  `quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton`
  in `UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`.
- Punishment and normality: `quittingPunishmentValue` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`, and
  `IsQuittingNormalPlayer` in `Quitting/Classification/AbnormalPlayers.lean`.
- Same-table Fin4 source:
  `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
  in `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
  The returned `FinFourQuantitativeFullSupportHardResidual` literally has
  `all_punishmentNormal` and `witness` fields on the ORIGINAL table.
- Fixed-target acceptance and converse:
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`
  and `exists_quittingTerminalTargetAcceptanceCertificate_of_isUniformEquilibriumPayoff`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`,
  and `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`
  in `TerminalUniformPayoffSelection.lean` in the same directory.
- Finite source: `KernelGame.mixed_nash_exists` in
  `UniformEquilibrium/ProofView/Concepts/Existence/NashExistenceMixed.lean`,
  `QuittingFiniteDeadlineTimingAction`, `quittingFiniteDeadlineTimingGame`,
  and its payoff/deviation adapters in
  `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineTimingGame.lean`.
  `quittingFiniteDeadlineReplyCap` and `IsQuittingFiniteDeadlineNash` are in
  `FiniteDeadlineReplyCap.lean` in that directory.
- Existing escape bill:
  `QuittingFiniteDeadlineNashProfile.semanticDebt_le_escapeCharge` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`
  already bounds omitted-date debt by deleted survival times the positive
  own singleton. The one-coordinate specialization is not new in isolation.
- Exact packet interface: `QuittingFiniteForwardPacket` in
  `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`.

The distinction from nearby normalization is substantive.
`normalizedQuittingTerminalPayoff_eq_sub_soloBaseline` and
`isεAsymptoticNash_normalized_iff` in
`UniformEquilibrium/Quitting/Classification/LCP/StrategicTransport.lean`
translate the Never payoff TOO. They prove a profilewise affine identity
in that different model. Here Never stays zero, and (2) is an actual tail
construction rather than that identity.

`quittingRootSuccessorPayoff_shift` and its forced-endpoint companions in
`Quitting/Classification/ThreePlayer/AuxiliaryShift.lean` already prove the
one-root affine calculation. The contracting periodic correspondence in
`Quitting/Cycles/PlayerwisePositiveAffinePeriodicBlock.lean`, including
`quittingCyclicTerminalValue_playerwiseAffine`, assumes supplied cyclic data
and deleted-opponent contraction. Neither supplies arbitrary-profile (2),
the finite-only punishment identity below, or same-player zero-Never gap
normalization. Existing finite-menu punishment Bellman iterates are also a
different object from the complete-opponent, finite-response-only infimum Lᵢ.

The shared square-root exceptional-player device appears in the separately
reviewed [finite-menu completion packet](../exports/FINITE_MENU_PUNISHMENT_COMPLETION_AND_EARLY_ABSORPTION_CHARACTERIZATION.md).
The new use is across a signed terminal-only change of game, with exactly
transported punishment values and a canonical actual finite-menu source.

The original submission cited Nash, “Equilibrium Points in N-Person Games,”
PNAS 36 (1950), 48–49, DOI 10.1073/pnas.36.1.48. Its finite-game existence
conclusion is the familiar input represented by the checked mixed-Nash
declaration above. The publisher/PubMed Central full-text endpoints were
access-blocked in this assembly, so no claim of a fresh original-text audit
or quotation from that paper is made. No quitting-paper theorem is imported
without proof into the new reduction. The bounded source searches and both
independent reviews found no duplicate of the same-player zero-Never lift
or finite-only punishment identity in the inspected normalization,
punishment, stationary, and terminal subtrees; no global priority claim is made.

## Proof

### A. Late finite responses and releasing a Never atom

Against fixed opponents let τ₋ᵢ be their earliest stopping date. As t→∞,
on {τ₋ᵢ<∞} a player quitting at t eventually sees exactly the same first
opponent coalition as Never. On {τ₋ᵢ=∞}, quitting at t yields sᵢ while
Never yields zero. Bounded convergence gives, for arbitrary signs,

    lim[t→∞] fᵢ(t)=Wᵢ+sᵢDᵢ∞.                    (11)

Equivalently, the possible discrepancy outside these eventual outcomes is
bounded by 2M times the probability of a sufficiently late finite opponent
stop, which tends to zero. This includes ties at the moving date.

If the player's own Never mass is zᵢ, replace only that atom by the
deterministic date t. This is one legal unilateral mixed response. Its
gain tends by (11) to zᵢsᵢDᵢ∞=sᵢR∞. Therefore

    E_r(σ)≥sᵢR∞ whenever sᵢ≥0.                   (12)

In particular the original pivot gives gR∞≤E_r, and the canonical pivot
gives R∞≤E_r̂. Also, when sᵢ≥0, (11) shows that sup finite responses
already dominates Wᵢ; Never adds nothing to the cap in (9).

### B. One preselected exceptional-tail lift

Fix σ in r̂, ρ>R∞, and ζ>0. Put ℓᵢ(T)=Dᵢ(T)−Dᵢ∞. Joint and deleted
survivals decrease to their Never products, so ℓᵢ(T)≥0 and tends to zero.
Choose one T with R(T)<ρ and 3M maxᵢℓᵢ(T)<ζ/2.

Independence gives, for distinct i,j,

    Dᵢ(T)Dⱼ(T)=R(T)∏[h≠i,j]S_h(T)≤R(T)<ρ.       (13)

There is at most one i with Dᵢ(T)>√ρ. If it exists, fix that label i*
and an actual punishment opponent plan in r with cap ≤P_i*+η, where
0<η<ζ/2. Otherwise use any fixed tail, for example all-Never. Copy every
old marginal before T; on survival each player starts its selected fresh
private tail at date T. This defines τ. The target and all tails are chosen
before play; no observation identifies a deviator. A zero-survival player's
otherwise-unused tail is still well defined.

The vector a+gU^r̂(σ) is exactly the evaluation using original absorbing
rewards but assigning vector a to all-Never. It agrees with U^r(τ) before
T. On survival to T both bounded suffix evaluations lie in [−M,M], since
|aᵢ|≤M. Hence

    |Uᵢ^r(τ)−aᵢ−gUᵢ^r̂(σ)|≤2MR(T)<2Mρ.          (14)

Let Ẑᵢ(T) be the unconditional transformed payoff from opponents quitting
before T when i Continues through T, and Ŵᵢ its original transformed
Never-response payoff. Only late finite opponent stops distinguish them:

    |Ŵᵢ−Ẑᵢ(T)|≤(2M/g)ℓᵢ(T).                    (15)

Every pure response t<T forces termination before T, so its original reward
is exactly aᵢ+g times the transformed reward and is ≤aᵢ+gB̂ᵢ(σ).

For a nonexceptional player, any response waiting until T, including Never,
has payoff at most its unchanged prefix ledger plus M Dᵢ(T). Thus

    response ≤gẐᵢ(T)+aᵢ(1−Dᵢ(T))+M Dᵢ(T)
             ≤aᵢ+gB̂ᵢ(σ)+2Mℓᵢ(T)+2M Dᵢ(T).      (16)

Here Ŵᵢ≤B̂ᵢ, (15), and M−aᵢ≤2M were used; aᵢ need not be nonnegative.
Subtracting (14) and using Dᵢ(T)≤√ρ gives

    dᵢ^r(τ)≤gE_r̂(σ)+2Mρ+2M√ρ+2Mℓᵢ(T).          (17)

For the exceptional player, the chosen tail cap is Pᵢ+η. Normality is
used precisely in the following estimate:

    response ≤gẐᵢ(T)+aᵢ(1−Dᵢ(T))+(Pᵢ+η)Dᵢ(T)
             ≤aᵢ+g[Ẑᵢ(T)+ŝᵢDᵢ(T)]+η.          (18)

Since B̂ᵢ≥Ŵᵢ+ŝᵢDᵢ∞ by (11), ŝᵢ∈{0,1}, and gŝᵢ≤M, (15)
bounds (18) by aᵢ+gB̂ᵢ+3Mℓᵢ(T)+η. Subtracting (14) gives

    dᵢ^r(τ)≤gE_r̂(σ)+2Mρ+3Mℓᵢ(T)+η.              (19)

All pure dates and Never have been bounded against this SAME τ. Mixture
extremality (9) covers every behavioral response. Our choices of T and η
give (2). With one player the empty deleted product is one and that player
can be the sole exception, so no separate nontrivial-player assumption or
division by zero occurs.

### C. Quantitative preservation of a positive terminal gap

Set e=E_r̂(σ). Equation (12) gives R∞≤e. Apply (2) for arbitrary ρ>e,
then take the infimum over the resulting original profiles before letting
ρ↓e and ζ↓0. This proves

    inf[τ]E_r(τ)≤(g+2M)e+2M√e.                    (20)

This remains a limiting construction at e=0; no exact lift or attained
minimum is claimed. If E_r≥γ>0 on every profile, then γ≤2M and g≤M.
For e<γ²/(16M²), the right side of (20) is strictly below

    3γ²/(16M)+γ/2≤7γ/8<γ,

a contradiction. This proves (4). A positive lower bound on full cap debt
rules out terminal approximate equilibria at all errors and hence rules out
UE. If a formal witness requires an ACTUAL deviation at its displayed
margin rather than a supremum lower bound, any smaller positive margin,
for example γ²/(32M²), is supplied by the definition of supremum. Nothing
here assumes cap attainment.

### D. The finite-response-only punishment identity

This auxiliary result holds for every finite quitting table and every
player, without normality or any reward-sign assumption. Set

    Aᵢ(σ₋ᵢ)=sup[t∈ℕ]fᵢ(t),
    Lᵢ=inf[σ₋ᵢ]Aᵢ(σ₋ᵢ).

Then

    Lᵢ=min(Pᵢ,sᵢ).                                 (21)

These are bounded infima over complete independent opponent laws. Lᵢ is
NOT a finite-deadline punishment value. Clearly Lᵢ≤Pᵢ; taking all opponents
Never also gives Lᵢ≤sᵢ.

Suppose Lᵢ<sᵢ. Fix Lᵢ<x<sᵢ and actual opponents with A=Aᵢ(σ₋ᵢ)<x.
Let D be their joint Never probability and W the Never response payoff.
If D=1, every finite response pays sᵢ, contradicting A<sᵢ. Thus D<1,
and (11) gives W+sᵢD≤A. Consequently

    W/(1−D)≤(A−sᵢD)/(1−D)≤A.                     (22)

The last inequality uses A<sᵢ, not positivity of any of these numbers.

Retain the opponents' first T hazards and repeat this finite block forever,
independently player by player. Let D_T be its joint survival, W_T the
unconditional opponent-absorption reward in the block, and f_t its pure
response payoff at offset t<T. For large T, D_T<1; also D_T→D, W_T→W,
and f_t equals the original response value at that same finite date, so
f_t≤A for every offset, uniformly over the growing displayed block.

A Quit response in block n≥0 at offset t<T has EXACT payoff

    (1−D_T^n) W_T/(1−D_T)+D_T^n f_t.               (23)

The Never response is W_T/(1−D_T). Each value in (23) is a convex
combination of two signed numbers. Hence the full repeated-block cap is
at most max(A,W_T/(1−D_T)), which is below x for sufficiently large T,
by (22). Therefore Pᵢ≤x. Letting x↓Lᵢ gives Pᵢ=Lᵢ in this case.
If Lᵢ=sᵢ, the earlier bounds already give min(Pᵢ,sᵢ)=Lᵢ. This proves
(21), including the D=1 boundary where no division was performed.

### E. Exact punishment transport

Under normality, (21) gives Lᵢ=Pᵢ. Every finite deterministic response
terminates play and therefore obeys the exact identity

    f̂ᵢ(t)=(fᵢ(t)−aᵢ)/g.                         (24)

All ŝᵢ are nonnegative, so (11) makes the transformed finite-response
supremum equal to its FULL cap against each fixed opponent law. Taking the
infimum of (24) over the SAME complete independent opponent domain gives

    P̂ᵢ=(Lᵢ−aᵢ)/g=(Pᵢ−aᵢ)/g.

In particular P̂ⱼ≤0 for j≠k and P̂ₖ≤1. There is no interchange of a
changing supremum with a limit, nor an infimum-attainment premise.

### F. Equality of fixed-target UE payoff sets

For an UNCHANGED profile the correct literal identity, with both Never
payoffs zero, is

    Uᵢ^r̂(σ)=[Uᵢ^r(σ)−aᵢ+aᵢR∞]/g.                (25)

By (24) and nonnegative transformed singletons, B̂ᵢ=(Aᵢ−aᵢ)/g. Thus

    d̂ᵢ=[Aᵢ−Uᵢ^r−aᵢR∞]/g
         ≤[E_r(σ)+M R∞]/g.

The original pivot inequality gR∞≤E_r gives

    E_r̂(σ)≤(1/g+M/g²)E_r(σ).                     (26)

If v∈UE(r), choose terminal approximants σ_n with E_r(σ_n)→0 and
U^r(σ_n)→v using fixed-target acceptance. Their R∞ tends to zero by
(12), so (25)–(26) give transformed errors tending to zero and payoffs
tending to (v−a)/g. Fixed-target terminal acceptance yields
(v−a)/g∈UE(r̂).

Conversely, if v̂∈UE(r̂), choose σ_n with e_n=E_r̂(σ_n)→0 and
U^r̂(σ_n)→v̂. For n≥1 set ρ_n=e_n+1/n>R∞(σ_n), ζ_n=1/n. Apply (2)
to obtain τ_n. Its errors tend to zero and its payoffs tend to a+gv̂.
The same fixed-target theorem gives a+gv̂∈UE(r), proving (3).

### G. Exact finite Bellman and packet transport

For a root q let p_q(S) be the product probability of quitter set S,
c(q)=p_q(∅), and

    F_r(q,v)=Σ[∅≠S⊆I]p_q(S)r(S)+c(q)v.

The absorbing weights plus c(q) sum to one. Applying the affine map to
every outcome, including the supplied Continue value, gives (5). Forcing
one player's pure action is the same calculation with that marginal pure.
All endpoint comparisons therefore scale by 1/g. In particular every
supported-action loss bounded by δ becomes bounded by δ/g.

If v_(t+1)=F_r(q_t,v_t) in an original forward packet, then
v̂_(t+1)=F_r̂(q_t,v̂_t), with v̂_t=(v_t−a)/g. Equation (3)'s punishment
identity gives every floor v̂_t≥P̂−δ/g. The affine image of the one fixed
compact carrier is fixed and compact; a box maps to a box. Roots are
unchanged, so Σ_t(1−c(q_t)) and every root absorption probability are
unchanged. Construction index and chronological reversal are not altered.

This is a correspondence of supplied FINITE values and roots. It does not
assert that an arbitrary infinite affine Bellman annotation is an actual
zero-Never terminal payoff.

### H. Exact finite-menu cap and fresh Nash selection

In a canonical table s=eₖ, opponents with laws on F_N have no finite atoms
at or after N. Every pure response t≥N therefore pays exactly

    Wᵢ(p)+sᵢDᵢ(p).                                (27)

All earlier finite dates and Never are already in the menu. Taking the
supremum over complete response laws in (9) gives

    Bᵢ^∞=max(Bᵢ^N,Wᵢ+sᵢDᵢ).

For i≠k the second entry is Wᵢ, already on the menu, so it adds nothing.
For k it is Wₖ+Dₖ. Taking maximum debt over players proves (7), because
E_N≥0 on every menu law.

For every N the finite game has finite players, finite nonempty action
spaces F_N, and finite outcomes. Finite mixed Nash existence supplies an
independent product Nash law. The literal payoff and deviation adapters
make this a Nash law in the stated timing game, including the all-Continue
tail. These equilibria are selected AFRESH in r̂; no original finite-Nash
profile is being transported by (1).

At any such equilibrium Bᵢ^N=Uᵢ, giving (8). Since Never is on the menu,
Wₖ≤Uₖ, and hence [Cₖ]₊≤Dₖ. If pₖ(Never)>0, finite mixed-Nash
indifference gives Wₖ=Uₖ, so [Cₖ]₊=Dₖ. These prove every finite-source
claim, including the transformed-gap lower bounds. Formula (7) applies
equally to every finite-menu e-Nash law with E_N≤e.

## Boundary tests

1. **Signed normal nonpivot and failure of naive profile translation.**
   With two players and pivot0, take

       r({0})=(1,−2), r({1})=(0,−1), r({0,1})=(1,−2).

   Then s=(1,−1), P=(1,−2), g=1, and a=(0,−1). Pivot Quit0 guarantees
   one; opponent Never caps it at one. Every payoff of player1 is at least
   −2 and pivot sure Quit0 caps its responses at −2. Thus the displayed P
   is exact. Transformed player1 rewards are (−1,0,−1), giving P̂₁=−1 as
   required. At all-Never, BOTH actual prescribed payoff vectors are zero;
   U^r≠a+gU^r̂. The correction aR∞ in (25) is indispensable.
2. **Normality cannot be dropped.** Keep the pivot rewards, but let player1
   receive −1 when it belongs to the terminal coalition and zero otherwise.
   Then s₁=−1, P₁=0, L₁=−1. After shifting by a₁=−1, player1 receives
   zero on own membership and one otherwise; its punishment value is zero,
   not (P₁−a₁)/g=1. All-opponent Never realizes the relevant caps, and
   Never guarantees the lower zero bound. This falsifies the unsupported
   punishment identity without the stated normality premise.
3. **The L=s boundary and one player.** With one player and singleton −1,
   L=−1 and P=0, agreeing with (21); D=1, so division by 1−D would be
   invalid. A positive single-player pivot has a=0 and gives ordinary
   positive scaling. The generic theorem includes that harmless case.
4. **Sure prescribed absorption is not deleted survival.** In a two-player
   canonical table, let pivot rewards on {0},{1},{0,1} be 1,0,−1 and
   all other-player rewards zero. At N=1, pivot sure Quit0 and the other
   player mixing half Quit0/half Never form exact menu Nash with U=0.
   Joint Never mass is zero, but D₀=1/2 and the full pivot debt is 1/2.
   This tests zero own Never mass and falsifies the false formula dₖ=R∞.
5. **Deadline zero.** F₀={Never}; E₀=0. In every canonical table the full
   nonpivot debts are zero and the pivot full debt is one, exactly as (7).
6. **Zero joint reach need not remove the exception.** If R∞=0 but one
   Dᵢ∞>0, arbitrarily small ρ is available in (2). The exceptional
   punishment, not a bound Dᵢ≤R, controls the large deleted coordinate.
7. **No normalized reward-cube claim.** The canonical pivot is one, but
   the other coordinates are only bounded by 2M/g. A small positive pivot
   can enlarge the reward bound. An additional scaling would also scale
   that distinguished singleton and must be recorded separately.

## Adapter and consumer

For Fin4, choose any finite reward bound M for an arbitrary no-UE table.
The named same-table residual constructor gives a witness with positive
terminal gap γ and all-player Pᵢ≤sᵢ. If every sᵢ≤0, literal all-Never
would have zero full debt, contrary to that witness. Select one positive
sₖ; it is fixed once for this table, not selected separately at each N.
Apply (1)–(4). This is the actual source of the canonical table and its
positive gap; no normality or equilibrium-existence obligation is deferred.

At each N, fresh finite mixed Nash existence then gives the laws in (8).
For a successful future source, select canonical laws p_e with E_N(p_e)≤e
AND Cₖ(p_e)≤e for every e>0. Equation (7) gives full terminal e-Nash, and
the existing terminal existence consumer gives some v̂∈UE(r̂). Equation
(3) returns the fixed target a+gv̂∈UE(r). This last small-scalar selection
is the precise remaining producer, not a proved field of the output.

The affine singleton comparison matrix satisfies Γ̂=Γ/g. Its signs,
normal layers/core, homogeneous feasibility, standard-Q, projective-Q,
and projective-Q-bar predicates are preserved under positive uniform
scaling. For standard LCP, replace a weight z by gz; homogeneous weights
can be normalized positively; the standard/homogeneous split supplies
the projective statement on each principal. Punishment margins satisfy
ŝᵢ−P̂ᵢ=(sᵢ−Pᵢ)/g. These are literal transported properties.

By contrast, (25) shows that actual payoff/cap/debt pairs are not affine
images profile by profile. No chosen global regret minimum, near-minimum
realizer, response provenance, quantitative singleton-source packet, or
anchored solution for one fixed right-hand side is transported merely by
Γ̂=Γ/g. In particular the normalized Never vector changes from −s to −eₖ,
not merely to −s/g. If a subsequent argument needs the hard residual's
minima or packets for r̂, it must apply the source theorem AGAIN to r̂,
using its new bound and positive gap. This is fresh extraction, not ancestry.

## Lean handoff

Keep the transformation separate from the existing translated-Never payoff
table. A suitable raw definition is
`quittingSinglePivotReward reward pivot = (reward−offset)/solo_pivot`,
with the positive-pivot proof supplied where needed. Do not encode gap
preservation, normality, or a low-debt selector as assumed structure fields.

Suggested theorem sequence, all new names only:

1. `finitePureReplyInf_eq_min_punishment_solo`: complete-opponent domain,
   finite pure responses only; prove the finite-block repetition lemma and
   use (11), including signed and empty-opponent cases.
2. `singlePivot_punishmentValue` and the exact raw singleton/bound identities.
3. `exists_singlePivot_tailLift`: actual product-law prefix agreement,
   simultaneous full-cap inequalities, and payoff estimate (2).
4. `singlePivot_terminalExploitability_lowerBound` and
   `singlePivot_uniformEquilibriumPayoff_iff`, using fixed-target acceptance.
   Distinguish a supremum debt lower bound from the actual-deviation witness
   predicate; a smaller positive margin avoids any attainment assumption.
5. The existing root-shift formulas plus positive scaling give finite
   `QuittingFiniteForwardPacket` transport, including rationality and charge.
6. Prove the exact canonical finite-menu cap equality before applying fresh
   `KernelGame.mixed_nash_exists`. Use existing timing-law payoff/deviation
   adapters rather than constructing a second finite-game representation.
7. A Fin4 corollary invokes
   `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
   and the preceding results to produce the same-player canonical table and
   every-deadline scalar source. This is where arbitrary Fin4 data enter.

The narrow checks should target these modules and the signed two-player,
deadline-zero, and zero-pivot-Never fixtures. No speculative repository
refactor or changed trust policy is part of the handoff. The source papers,
conference notes, and this packet are not Lean imports or axioms.

## Scope and nonclaims

The new conclusions are ordinary mathematics, not a Lean implementation.
The reduction preserves the finite
player set, actions, observation model, private independence, literal Never
zero, full behavioral response class, and fixed-target UE payoff sets.
It does not prove the quitting conjecture, produce small pivot debt,
establish a universal exact-finite-Nash architecture, or construct charged
chronology, a renewable tail, an algorithmic decision procedure, or an
attained global minimum. The arbitrary-player theorem assumes normality;
the unconditional no-UE-to-normality source used here is specifically Fin4.
