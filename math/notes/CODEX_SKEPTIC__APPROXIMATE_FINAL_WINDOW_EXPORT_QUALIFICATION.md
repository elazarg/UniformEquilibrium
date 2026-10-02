# Qualification audit: approximate finite-Nash final-window sources

Author: CODEX_SKEPTIC.

## Current verdict

The reviewed theorem is a genuine new conditional source theorem, but the
bounded audit below does not establish the strict conjecture-facing narrowing
required by `exports/README.md`. Keep it in the conference notes. In
particular, do not prepare an export merely by changing the name of the open
problem to “consume the final window.”

What is new is substantial: one positive finite-menu Nash tolerance, one
bounded final-window length, and one positive actual entry-reach floor work
simultaneously for every deadline and every source in that tolerance class
under Fin4 nonexistence. This constructs the previously supplied reach field,
not just a verifier for a source already known to be reached. Length-free
support rounding and the finite-menu punishment-floor producer are necessary
parts of its proof. None is claimed here as newly Lean-checked.

What remains missing is a use of those fields that reduces unrestricted
deviation debt, returns to an accepted source, or produces renewable charge.
The named forward-packet question does not accept an unconsumed source
restriction as a complete answer. The nearby two-cut consumer can be fed the
new source, but its resulting alternative remains unconsumed. This is a
qualification verdict for the presently audited interfaces, not a claim that
the theorem could never become part of an export.

The mathematical proofs and completed reviews remain in:

- [RENY's source notebook](CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH.md),
  Sections 1–12;
- [HILBERT's review](../feedback/CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH__BY_CODEX_HILBERT.md),
  passing Sections 1–11, with a bounded Section 12 source-novelty addendum;
- [SKEPTIC's independent derivation](CODEX_SKEPTIC__ROBUST_APPROXIMATE_FINAL_WINDOW_REACH.md);
- [SKEPTIC's review](../feedback/CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH__BY_CODEX_SKEPTIC.md),
  passing Section 12 after the independent derivation.

These are two completed, complementary reviews. They are not represented as
two separate full reviews of every section. The elementary Section 13
zero-set argument is checked separately in Section 3 below.

## 1. Exact theorem and source contract

There are four players. The reward r_i(S) is specified for every nonempty
quitting coalition S and satisfies |r_i(S)|≤M for one M>0. The all-Never
outcome has payoff zero. A behavioral profile uses private independent randomization;
on the unique live history it is equivalent to independent stopping laws.
A unilateral behavioral deviator may replace its entire stopping law.

A deadline-N timing profile is a product of laws on
{0,…,N−1,Never}. Its finite-menu Nash error is at most ε if no replacement
law on this same finite menu improves any player's payoff by more than ε.
Write q_i(t) for its literal Quit hazards and

    R(t) = ∏_{s<t} ∏_i (1−q_i(s)).

The reviewed conclusion is:

    If r has no uniform-equilibrium payoff, then
    ∃ H≥1, e_*>0, 0<ρ<1,
      ∀ N≥H, ∀ ε∈[0,e_*], ∀ deadline-N finite ε-Nash p,
        R_p(N−H)≥ρ.

H, e_*, and ρ depend only on the fixed table, not N, ε, or the chosen
profile. There is no Nε restriction. The suffix at T=N−H is the actual
conditional suffix of this very source, with finite-menu error ε/R(T).
It is not a replacement source or a compactified terminal annotation.

More generally, at every reached cut t the finite conditional Nash error is
at most ε/R(t): copy the original prefix, then use the conditional finite
deviation. Its ex ante gain is exactly R(t) times its conditional gain.

The proof additionally gives a fixed positive Continue floor on the long
prefix, and an actual payoff floor χ−τ at every relevant displayed cut,
after fixing τ and the corresponding horizon and error thresholds. Here χ
is the behavioral punishment vector. It does not give χ plus a positive
separation from punishment caps.

The source class is nonempty at every positive deadline. This is supplied by
`exists_finiteDeadlineTimingNash_terminalDebt_le` in
`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingNashDebt.lean`,
whose proof constructs an exact mixed finite timing Nash law and its literal
behavioral realization. Exact Nash laws also belong to every nonnegative
finite-menu error class. Thus the source's existence is not an additional
conjecture-level assumption.

## 2. What is constructed, and what remains supplied

The reviewed intermediate statements construct the following information.

1. For every τ>0, sufficiently long sufficiently accurate finite timing
   sources have actual prescribed payoff at least χ−τ. This is a
   finite-menu statement, not an application of an unrestricted approximate
   Nash floor to a source that fails its hypothesis.
2. On a supplied reached prefix with Continue floor η, deleting original
   Quit hazards whose Quit-minus-Continue payoff is below −δ removes total
   hazard at most μ≤4ε/(ρδ). The original tail is retained literally;
   all suffix payoffs and full caps change by at most 2Mμ each. Recomputed
   exact Bellman values have support error at most
   max(δ,ε/(ρη))+4Mμ. No prefix-length factor occurs.
3. The first-crossing argument constructs the uniform reach floor itself.
   It uses the previous two producers and the contrapositive of the checked
   all-tolerances/all-charges finite-forward consumer. At the crossing cut K
   only R(K)≥ρη⁴ is available, so the endpoint floor uses ε/(ρη⁴).
   Reversing the pruned prefix produces the exact forbidden packet if an
   early crossing exists.

The conclusion does not require pruning the actual source. Pruning is used
only in the contradiction. The source's original roots, its absolute cut,
and all opponent-deleted survival products remain available.

There is an important qualification concerning the nearby two-cut record.
The positive minimum itself is NOT an open extra premise under no uniform
payoff: the inspected theorem
`not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt`
in `UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean`
constructs an attained positive global minimum of total semantic debt.
What the source lacks is proximity or convergence to that minimum, not its
existence.

Indeed the bare two-cut record can be filled. Let Γ>0 be a global terminal
gap; applying it to all-Never gives some singleton self-reward s_i≥Γ.
Shrink e_* if necessary so e_*/ρ≤Γ/2. For a final H-date conditional
source with finite error e≤Γ/2 and total absorption probability β,
prescribed payoff is at most Mβ. Quitting at its first date pays at least
s_i−(s_i+M)β. Finite Nash therefore yields

    β ≥ (s_i−e)/(s_i+2M) ≥ Γ/[2(Γ+2M)] > 0.

Conditional total absorption is at most the sum of the same window's
marginal hazards. For N>H, choose entry N−H, exit N, and marked row zero;
insert the already available positive minimum. Together with R(N−H)≥ρ
these are all the fields of `QuittingUniformlyReachedPostMarkTwoCutBlock`.
This elementary attachment deduction is ordinary mathematics here; it is
not being attributed to the Section 12 review as a separately checked result.

The record and its parent `QuittingPositiveMinimumTwoCutBlock` were read in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveMinimumTwoCutPaidSplice.lean`.
Neither record demands entry or exit near the minimum. Its theorem
`QuittingUniformlyReachedPostMarkTwoCutBlock.offMinimum_or_exists_paidSplice`
returns an exit quantitatively above that minimum or an actual paid splice
for one player. It does not bound the other players' new debts, show
decrease from the original source, or produce a renewable child.

Thus a bare two-cut source can be constructed, but its existence is too weak
to identify the missing chronology producer. Existing silent-padding sources
already show the same distinction between supplying that record and making
strategic progress.

## 3. Fixed positive menu slack: the precise completeness statement

Let E(p) denote maximum unrestricted terminal deviation debt. For e≥0 put

    a_r(e) = inf { E(p) : N≥1,
      p is a deadline-N finite timing e-Nash profile }.

For each fixed e>0,

    a_r(e)=0  if and only if r has a uniform-equilibrium payoff.

Here is the argument checked from RENY Section 13. The reverse implication
uses actual profiles of arbitrarily small E and the inspected semantic
endpoint `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
For the forward implication, that endpoint supplies terminal δ-Nash profiles
as δ tends to zero. For each profile independently, move each player's
sufficiently late finite stopping mass to Never. The sum θ of moved masses
tends to zero as the truncation deadline increases. An independent product
coupling changes every prescribed payoff by at most 2Mθ. Against any fixed
complete unilateral deviation the same estimate applies to the unchanged
opponent laws, uniformly over the deviator. Hence the unrestricted regret
changes by at most 4Mθ. Choose truncations so δ+4Mθ tends to zero and is
below e. Their finite laws are e-Nash on their finite menus and have E
tending to zero.

This proves the stated zero-set equivalence, not equality of a_r(e) with
the unrestricted infimum at positive values. It is not a producer that
starts from arbitrary finite e-Nash and improves E. Its forward implication
starts with the very all-accuracy terminal profiles that the positive
conjecture would have to construct.

Consequently the final-window theorem concerns a class with the right
qualitative zero set, unlike the exact finite-Nash class. That repairs an
architecture objection, but does not automatically consume a bounded tail.
Under no uniform payoff, fixed-window compactification of sources with
finite errors tending to zero yields an exact finite-H timing Nash tail.
The omitted date H remains outside its finite menu; its full debt can
remain positive throughout this compactification.

## 4. Named obligations and the export gate

The named question
[FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER](../archive/FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md)
asks for packets at every support tolerance and arbitrary charge, or a
consumer of the bounded-capacity branch yielding a terminal conclusion,
renewable finite rank, or a complete positive-gap table. Its macroscopic
alternative likewise asks for a paid accepted charge, renewable transition,
or contradiction of the hard residual.

The new theorem instead uses the packet compiler by contraposition to
constrain finite-menu sources. It does not produce unbounded packet charge,
consume the surviving final window, exhibit a rank that decreases, or
produce a table. Although this is more than merely restating an approximate
capacity barrier, it is not one of that question's completed accepted
answers.

The principal live chronology interfaces were also read directly:
`VanishingDebtAtomChronologicalConsumer` and
`PaidFirstDisagreementAdmissibleReturnConsumer` in
`UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`.
They require compatible chronological certificates at every accuracy or a
positive exact admissible return. Neither such object follows from one
reached final window. No source identity with the supplied minimum-frontier
family is produced.

The nearby minimum-tail source makes the missing attachment explicit:
`QuittingPositiveMinimumTailProfileSource` in
`UniformEquilibrium/Diagnostics/Quitting/MinimumTailProfileSource.lean`
requires a literal profile sequence whose total semantic debt converges to
the global positive minimum. The final-window theorem gives no such
convergence. `FinFourSilentPaddingTwoCutRealization` in
`UniformEquilibrium/Diagnostics/Quitting/MinimumTailSilentPaddingConsumer.lean`
already records source ancestry and the branch-local two-cut alternative;
it does not promote that alternative to renewal or terminal approximation.

Thus the precise audit result is:

- closed source subcondition: fixed-positive-slack finite Nash sources now
  have uniform actual entry reach, plus the preceding finite-source floor
  and length-independent rounding adapters;
- not closed: near-minimum ancestry, control of nonpayer caps under repair,
  full-vector return, repeatable charge, or the omitted-date deviation cap;
- not established: an implication reducing a named live producer problem
  to a strictly smaller producer already handled by another theorem.

The source theorem is not rejected for assuming no uniform payoff; that is
a legitimate contradiction-side premise. Nor is it rejected merely because
it does not settle the conjecture. It currently fails the named progress
test because the relevant consumer output and its required source relation
remain absent. Gate item 4 is not established for the audited live targets.

## 5. Exact boundary tests

1. **Finite Nash is not unrestricted Nash.** On the normalized hard-deadline
   table, active players k,j have rewards (1/2,−1) at {k}, (1,−1) at {j},
   and (0,0) at {k,j}. Dummy-only exits give both active players zero;
   each dummy receives −1 when it joins the terminal coalition and zero
   otherwise. Every positive-deadline exact timing Nash has full regret
   D_N=2^(N−1)/(2^(N+1)−1)>1/4, tending to 1/4. Yet an actual finite-clock
   comparison family has full regret 1/L and one fixed uniform payoff.
   Therefore a_r(0)=1/4 while a_r(e)=0 for every e>0. The table is solved;
   it is not a counterexample to the no-uniform-payoff source theorem.
2. **No accumulation of alternative gains.** One active player with own
   quitting reward one has uniform finite atom mass (1−ε)/N and Never
   mass ε. Full and finite regret both equal ε. At survival S_t its
   maximal root endpoint advantage above the prescribed value is ε/S_t.
   Summing the survival-weighted advantages across K dates gives Kε,
   not ε. With N=16, ε=1/16 and K=8 this is exactly 1/2, although all
   displayed reaches exceed 1/2. This is why the one-sided pruning budget,
   rather than a sum of local Nash errors, is necessary.
3. **Rare bad support.** Own quitting reward −1, Quit mass ε and Never
   mass 1−ε give full and finite regret ε, reach one, but supported Quit
   has endpoint gap −1. Vanishing mixed regret does not supply the packet's
   unweighted support condition. Removing that bad hazard fixes this
   example; merely relabeling mixed regret does not.
4. **The crossing endpoint denominator is real.** With η=1/2 and ρ=1/8,
   roots with Continue vectors (1/2,1/2,1/2,1) and then
   (1/2,1/2,1/2,1/2) give reaches 1,1/8,1/128. The first strict crossing
   is exactly ρη⁴. This is a probability-only regression, not a Nash
   source. A floor estimate justified only above reach ρ cannot be used at
   this endpoint.

Exact Fraction arithmetic reran the last probability identity and the
N=16 residual example, and checked the hard-deadline formula for N=1,…,9.
The general hard-deadline statement is not inferred from these finitely many
checks. Its inspected declarations are
`FinFourHardDeadlineTimingNashBarrier.finiteDeadlineTimingNash_exploitability_eq_hardDeadlineDebt`
and `FinFourHardDeadlineTimingNashBarrier.quarter_lt_finiteDeadlineTimingNash_exploitability`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashUniqueness.lean`,
together with `FinFourHardDeadlineTimingNashBarrier.comparisonProfile_exploitability`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashBarrier.lean`.
These existing no-go declarations are regression inputs, not new output.

## 6. A concrete missing mathematical output

One sufficient, currently unproved next output would be a literal final-window
repair operation with a source-preserving full-regret contraction. Precisely,
under the same fixed hypothetical no-uniform-payoff table, require a κ>0
and ω(e) tending to zero such that, for every sufficiently small e and every
source in the reached finite-menu e-Nash class above, the operation constructs
another actual finite-menu e-Nash source, at some deadline at least H, with

    E(new source) ≤ (1−κ) E(old source) + ω(e),
    0<κ≤1.

The operation must handle the omitted-date response and every nonpayer's
complete cap. It may not select a publicly correlated lottery of profiles,
assume an external small-debt source, or reinstall an exact finite-deadline
Nash equilibrium. Requiring the output to remain in the actual source class
is substantive: lengthening a deadline can add profitable omitted actions,
so it cannot be justified by silent padding of the menu alone.

This concrete output would have a named consumer. Start with the existing
finite timing Nash producer, iterate the operation, and use E≤2M initially.
After k iterations,

    E_k ≤ (1−κ)^k 2M + ω(e)/κ.

Taking e small and k large gives unrestricted terminal Nash profiles at
every positive accuracy, accepted by
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`.
Equivalently, one accuracy below the fixed terminal gap already contradicts
the no-uniform-payoff premise. This explains exactly what the proposed
operation would add; no such contraction is asserted or implemented here.

A weaker new result could also qualify if it consumed the window into one
of the precise renewable-rank or admissible-return outputs of the named
question. Merely selecting the same last window again would not do so.

## 7. Scope of this qualification session

The audit used `exports/README.md`, the named forward-packet question,
the relevant maintained FRONTIER/TOOLKIT entries, the source and review
files above, and the displayed Lean declarations under their imports.
The earlier independent reach audit records the finite-forward packet,
support-Nash, terminal-gap, and summable exact-spine punishment-floor
dependencies. No new literature-derived theorem or exhaustive novelty claim
is made. The present comparison is bounded to the named producer routes.

No Lean build or edit was made. No export, shared index, question, or other
author's notebook was edited. This gitignored conference note is not a
tracked implementation or an export handoff. The reviewed source theorem is
preserved without closure credit; the concrete next question is the
full-regret repair operation in Section 6, especially its nonpayer-cap and
output-source clauses.
