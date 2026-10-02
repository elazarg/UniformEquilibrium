# Global finite-calendar minima: Never-branch retry and the complete tail budget

Identity: CODEX_TARSKI_PREMIUM.

## Status and bounded question

Ordinary mathematics, not independently reviewed or Lean-checked. No export.
This tests an actual all-law operation outside an exact-menu-Nash family:
retain a finite source head and release each original Never branch into an
arbitrary independently chosen complete tail. In particular the tail can
independently replay the source, with player-dependent permanent-Never mass.

The full response calculation is exact. It does **not** produce lower
unrestricted regret from a positive global minimum. The zero-joint-Never
arm fixes several near-maximal owner debts, and a head/late double contact
of a zero-singleton owner fixes that owner's entire debt even when joint
Never is positive. These are source-specific operational restrictions,
not counterexamples to existence of uniform equilibrium or to global
selection which also changes the head.

The reusable checkpoint is the complete budget (4), including every tail
tester. Its outer-debt lower bound specializes the established cap-ledger
principle; it is not claimed as a new proof mechanism. The unresolved
positive-joint arm is stated precisely in Section 5. Section 4a consumes
the SAME-multiplier advancing-clamp source to exclude one composite repair:
its charged nonowner cannot be repaired by ANY post-calendar tail.

## 1. Source, actual laws, and exact proposed consumer

There are four players. The reward table has |r_i(S)|≤M, M>0, for every
nonempty first-quitter coalition S, and Never pays zero. Randomization is
independent. Every prescribed or deviating strategy is an actual law on
the nonnegative integers and Never; pure stopping dates and Never compute
the full behavioral response supremum.

Let X_K consist of product laws on {0,…,K−1,Never}, K≥1. Write E for the
maximum of the four COMPLETE debts, including the after-support and Never
testers. Let μ^K be a global X_K minimizer, η_K=E(μ^K), and suppose for
the contemplated contradiction argument that η_K decreases to m>0.
Do not replace this hypothesis with a restricted cap/root minimum.

The input is the same-owner certificate in
[FRECHET's silent-prefix note](CODEX_FRECHET_CYCLE__SILENT_PREFIX_ALL_OWNER_MULTIPLIERS.md).
After its literal silent prefix, the source has the same U and B, and
there is ONE enlarged-calendar multiplier law with all owner masses
uniformly positive. In particular its source debts satisfy

    d_i^K=B_i^K−U_i^K → m, for every i.                 (1)

The source note proves this from the finite near-optimality errors and
positive singleton cap margins, without realizing a limiting strategy.
Only (1), not an unsupported upper bound from the multipliers, is needed
below. A silent prefix does not change any original Never mass.

The attempted consumer was: select actual tails ν^K, allowed to change all
four laws jointly, so that the source-head/tail graft has full regret
bounded below m by a fixed positive amount. Sections 3–5 determine exactly
what this restricted operation can and cannot change. No existence of such
tails is asserted.

## 2. Exact all-law graft ledger

Fix one finite source μ. Put z_i=μ_i(Never), C=∏_i z_i, and
D_i=∏_(j≠i)z_j. These are respectively joint and player-deleted Never
probabilities. Write U_i for the source payoff, W_i for its literal Never
response, and H_i for its largest response at dates 0,…,K−1. Put
s_i⁺=max{r_i({i}),0}. Then

    B_i=max{H_i,W_i+D_i s_i⁺}.

For ANY complete independent tail ν define μ⊙ν by

    (μ⊙ν)_i(t)=μ_i(t)                         (t<K),
    (μ⊙ν)_i(K+t)=z_i ν_i(t)                   (t finite),
    (μ⊙ν)_i(Never)=z_i ν_i(Never).

This is a literal product law, not a public mixture or an inferred renewal
of a prescribed payoff. Let u_i and b_i be the actual payoff and complete
cap of ν. Direct first-quitter conditioning gives

    U_i(μ⊙ν)=U_i+C u_i,
    B_i(μ⊙ν)=max{H_i,W_i+D_i b_i}.             (2)

Proof: before K all original prescribed outcomes are unchanged. Prescribed
tail play is reached exactly when all four original clocks choose Never.
A responding owner can instead Continue through the entire head, so every
response at K+t has value W_i+D_i F_i^ν(t), and Never has the analogous
value. All responses before K retain their old values. Taking the supremum
proves (2), including infinite tails and unattained tail caps. No positive
reach is divided out, so zero C or D_i is allowed.

Define two nonnegative cap slacks

    h_i=B_i−H_i,       ℓ_i=B_i−W_i−D_i s_i⁺.

At least one of h_i,ℓ_i is zero. The exact new debt is

    d_i(μ⊙ν)=d_i + max{
      −h_i−C u_i,
      −ℓ_i+D_i(b_i−s_i⁺)−C u_i}.              (3)

Thus a proposed decrease by δ_i in this owner's debt requires and is
equivalent to BOTH inequalities

    C u_i ≥ δ_i−h_i,
    D_i(b_i−s_i⁺)−C u_i ≤ ℓ_i−δ_i.          (4)

For strict decrease use strict inequalities. The two different survival
factors cannot be replaced by each other.

There is also a tail-independent, nonnegative head budget

    L_i=(1−z_i)H_i+z_i W_i−U_i ≥ 0,
    d_i(μ⊙ν) ≥ L_i+C(b_i−u_i).              (5)

Indeed U_i is the source-weighted average of its pure responses; every
finite one is at most H_i. For the second inequality take the convex
combination, with weights 1−z_i and z_i, of the two entries defining the
new cap in (2), and subtract the new payoff. Since z_iD_i=C, (5) follows.
Equivalently

    L_i=d_i−(1−z_i)h_i−z_iℓ_i−C s_i⁺.

This lower bound is an explicit coarse version of the nonnegative
outer cap-defect ledger. The latter depends on the actual tail and may
be strictly larger; L_i is not asserted to equal that complete ledger.

## 3. Zero-joint and double-contact source arms

If C=0, every tail leaves every prescribed payoff unchanged. If exactly
one z_k is zero, D_i=0 for each i≠k, so all THREE nonowner caps and debts
are also unchanged. If at least two z's are zero, every D_i is zero and
the entire payoff/cap/debt vector is unchanged for EVERY tail. A source
with one proper clock need not have every deleted clock absorbing.

The sequential statement keeps the actual sources: suppose (1) holds and
C_K→0. Pass to a subsequence on which one fixed z_k^K→0. For any fixed
i≠k, D_i^K≤z_k^K→0. Uniformly over ALL possibly moving complete tails,

    |U_i(μ^K⊙ν^K)−U_i^K| ≤ M C_K,
    |B_i(μ^K⊙ν^K)−B_i^K| ≤ 2M D_i^K.

Therefore these three particular owner debts still tend to m. This is
not an additional global lower bound beyond the global minimum; its extra
information is which original owner debts are unaffected by the operation.
It does not prohibit a useful smaller improvement tending to zero or a
later operation that changes clocks before K.

A second exact arm does not require C=0. If s_i⁺=0 and

    H_i=W_i=B_i,

then L_i=d_i, so (5) proves d_i(μ⊙ν)≥d_i for EVERY tail. In particular
this applies to a canonical nonpivot whose head and Never responses both
attain its cap. Approximate double contact has the quantitative retained
floor d_i−(1−z_i)h_i−z_iℓ_i. No sign condition on tail rewards or tail
payoffs is being silently imposed.

## 4. Actual private retries and their full caps

One optional source replay with player-dependent probabilities β_i is the
tail ν_i=(1−β_i)δ_Never+β_i μ_i. Its new finite masses are
z_iβ_i μ_i(t) at K+t, and its permanent Never mass is
z_i[1−β_i(1−z_i)]. Formula (2) computes all its caps exactly. Merely
decreasing these marginal Never masses does not imply increased actual
absorption when C=0, nor any debt decrease when C>0.

Unlimited independent replay of the original head has masses
z_i^a μ_i(t) at aK+t. If z_i<1 its Never mass is zero; if z_i=1 it
remains Never. When C<1 and every D_i<1 its exact semantics are

    U_i^∞=U_i/(1−C),
    B_i^∞=max{H_i,W_i/(1−D_i)}.              (6)

The first equality sums the joint geometric series. A tester in block a
has value W_i(1−D_i^a)/(1−D_i)+D_i^a F_i(t), while the literal Never
response has value W_i/(1−D_i). Their full supremum is the second
formula. If D_i=1, all opponents remain Never under replay, W_i=0, and
the cap is instead s_i⁺; no ratio with denominator zero is taken.
If C=1, every law is Never and replay changes nothing.

For example, in the canonical case s_i=0, a late-active nonpivot with
ℓ_i=0 and U_i≥0 is not improved even by a single FULL source replay:

    d_i(μ⊙μ)−d_i
      ≥ D_i[(1−z_i)U_i+d_i] ≥ 0.            (7)

This is a conditional exact source calculation, not a claimed supplied
example with positive global minimum. At a limiting positive global
minimum, (1) and the checked singleton margin give limiting U_i≥s_i;
one must retain finite approximation errors before using (7) on sources.
Thinning the copied laws can change payoff signs, so (7) does not cover
every β or every tail.

## 4a. Actual global-source composition: advance, then arbitrary tail

This uses the exact advancing arm in
[FRECHET's clamp note](CODEX_FRECHET_CYCLE__CLAMP_CROSS_AMPLIFICATION_AND_SOURCE_INTERVAL_REACH.md),
not an arbitrary supplied corner. Let μ be its silently shifted source,
η=E(μ), and retain the SAME probability λ on the complete finite tester
set, owner masses θ_i>0, and error R, with

    Σ_(i,t) λ_(i,t)[η−g_(i,t)(μ)] ≤ R,
    Σ_(i,t) λ_(i,t)Dg_(i,t)(μ)[q−μ] ≥ −R
                         for every enlarged endpoint q.

Fix owner j and a finite cap-attaining response r. Let μ⁻ replace its law
by min(T_j,r), and let a=U_j(μ⁻)−U_j(μ)≥0. Every j-owned gain has
increment −a. Affineness in this one changed law and the certificate give

    Σ_(i≠j,t) λ_(i,t)[g_(i,t)(μ⁻)−g_(i,t)(μ)] ≥ θ_j a−R.

For τ>0 put b=(θ_j a−R−4MR/τ)/(1−θ_j). The denominator is positive
because every other owner has positive mass. If b>0, discarding source
testers below η−τ loses at most 4MR/τ, so some i≠j and tester t satisfy

    g_(i,t)(μ)≥η−τ,
    g_(i,t)(μ⁻)−g_(i,t)(μ)≥b.

Now retain the WHOLE actual μ⁻ head, ending strictly after r and every
original finite date, and append ANY independent complete tail ν. Its
owner-j head clock is proper. Section 3 gives the exact equality

    d_i(μ⁻⊙ν)=d_i(μ⁻) ≥ η−τ+b, for this same i≠j.    (9)

In fact every nonowner pure response is fixed, not just this tester or its
full cap: j stops before the appended tail both in prescribed play and
when the nonowner deviates. This proves (9) against arbitrary infinite
tails, replays, tail root stacks, and permanent-Never choices simultaneously.

Consequently, on a sequence of genuine source certificates with R→0,
uniformly positive θ_j, and a bounded below by a positive constant, choose
τ→0 with R/τ→0. The advance-then-tail composite retains a uniformly
POSITIVE INCREASE over the original source's maximum regret. This is a
complete comparison for the specified composite, not a claim that every
owner has a macroscopic advancing arm. An owner may instead put its large
gain in the delaying arm, exactly as the clamp note distinguishes.

The remaining repair must change one of these clocks before the retained
head ends; merely adding a powerful terminal/tail consumer cannot erase
the linked observer debt in (9). This does not rule out FRECHET's changes
at or before the paid gate, or an arbitrary joint reselection.

## 5. Exact remaining implication and source comparison

In the remaining arm C>0, all z_i>0. Rewriting (4) gives the coupled
actual-tail requirements

    u_i ≥ (δ_i−h_i)/C,
    b_i−z_i u_i ≤ s_i⁺+(ℓ_i−δ_i)/D_i.      (8)

To beat the source's maximum by ε, substitute
δ_i=d_i−E(μ)+ε, separately for all four owners. This states a testable
necessary-and-sufficient full-response condition; it is not a producer.
No argument here forces an actual tail satisfying (8) from the remaining
global-source hypotheses. In particular, payoff realization alone gives
only u, not the upper bounds on b_i−z_i u_i. The all-owner multipliers
give supporting LOWER derivative inequalities; they cannot be used as
upper bounds on the four new response envelopes.

There is no additional finite-law obstruction AFTER strict tail feasibility
has been obtained. For one fixed complete ν, move each marginal's finite
mass after date N to Never. If these removed masses are ε_i(N), then
Σ_i ε_i(N)→0. Coupling the four clocks gives prescribed-payoff change at
most 2MΣε_i(N), uniformly over every fixed unilateral intervention as
well. Taking full suprema bounds the change of the graft's full maximum
debt by 4MΣε_i(N). Thus any strict improvement by an actual complete tail
is retained by a sufficiently long finite tail. This is sourcewise static
approximation, not compactness or convergence of a sequence of selectors.

Thus the bounded retry test stops before claiming descent. If a source
lands in Section 3's arms, a mechanism aimed at a fixed debt drop must
also change earlier surviving clocks. FRECHET's advancing-clamp operation
does so and retains different source-reach information; this note neither
supplies its missing orientation nor duplicates its clamp calculation.

Narrow source audit:

- `arch/SUFFICIENT_STATE.md`: actual marginal laws suffice for the present
  overwrites. No compactness or zero-survival suffix reconstruction is used.
- `quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
  `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`: the checked
  complete-response max recursion underlying (2).
- `quittingTerminalDeviationDebt_literalRootStack_eq_playerLedger_add`
  and `quittingFiniteWordPlayerCapDefectLedger_append` in
  `UniformEquilibrium/Quitting/Root/FiniteWordWeightedCapDefectLedger.lean`:
  the prior exact ledger identity and nonnegative outer-ledger principle.
- `not_two_positive_deletedClock_limits_of_joint_zero` and
  `terminalExploitability_tendsto_zero_iff_playerLedger_tendsto_zero` in
  `UniformEquilibrium/Quitting/Root/ZeroJointCapLedgerBoundary.lean`:
  the established zero-joint information boundary and conditional consumer.
- `minimumTerminalSemantic_exploitabilitySingletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`,
  together with FRECHET's cited finite-source certificate, supplies the
  positive-minimum margin and all-owner source correspondence used here.
- [RENY's global reach note](CODEX_RENY__GLOBAL_FINITE_NASH_REACH_MINIMIZATION.md),
  Section 9, already calculates repeated-block prescribed and cap series.
  Its exact global-minimum obstruction minimizes REACH under a finite
  Nash-error constraint, not unrestricted maximum debt. Its signed table
  has global full debt zero. Neither that test nor SKEPTIC's independently
  mixed-pair replay regression refutes a positive FULL global minimum.
- The current toolkit records the fixed-calendar whole-payoff realization
  and closure result in `Paths/FiniteCalendarPayoffClosure.lean`, explicitly
  without cap preservation. No stronger use of that new theorem is made.

An independent exact rational calculation checked (2) and (5) on
384 owner instances from 96 signed integer tables and two-date source/tail
laws with third-grid masses. Zero and positive joint Never, every finite
after-support response, and Never were included. These checks corroborate
the all-law proof, not the hypothetical global-source existence.

The next mathematical question is not another retry formula: can a joint
head change, linked to the actual all-owner source certificate, reduce a
positive L_i or break a zero-singleton double contact while controlling
the unmarked complete caps? No answer to that orientation question is
claimed here.
