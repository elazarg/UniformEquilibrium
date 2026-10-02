# Marked rows of strict-inert selections are uniformly cap-inexact

Author: CLAUDE_FABLE. Companion to `PREMARK_ABSORPTION_FLOOR.md` and
`TIGHT_COORDINATE_DICHOTOMY.md`; consumes the same strict-inert
provenance on the cap (`.2`) side of the ledger.

Notation: profiles \(\pi_n\), marks \(m_n\), a fixed terminal coalition
\(T\) with uniform stage-mass floor \(\kappa>0\) at the mark (the
decoration's marked-mass floor), spine tails
\(\tau_n=\operatorname{pair}(\pi_n^{(m_n+1)})\), and the marked live
root \(\rho_n\) (the live root of \(\pi_n\) at date \(m_n\)). The
cap-side row defect is the total one-stage Nash defect of \(\rho_n\)
against the tail cap \(\tau_n.2\) — exactly the summand of the checked
directed-transport ledger
(`debt_zero_eq_sum_reached_defect_add_tail`,
`TerminalSemanticDirectedTransport.lean`).

**Theorem (marked-row cap-defect floor).** Suppose the tail caps
converge, \(\tau_n.2\to c_\infty\), and every exact product root at
\(c_\infty\) is all-Continue. Then there is \(\mathrm{moat}>0\) with,
eventually in \(n\),

\[
\mathrm{moat}\;\le\;
\operatorname{TotalNashDefect}(\tau_n.2,\rho_n).
\]

**Corollary (minimum-tail form).** If instead the tails converge to a
carrier pair with total debt at most the positive global minimum
\(D_*\) (as at every strict-inert/minimum-return selection, where
tail debts tend to \(D_*\)), the uniqueness hypothesis at \(c_\infty\)
is automatic from the table-level radius
(`exists_pos_nearMinimum_capNash_eq_allContinue_radius`), and the same
floor holds.

## Proof

The marked root has uniform absorption: stage mass factors as live
mass times root-coalition mass
(`quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass`), live
mass is at most one, so the root-coalition mass of \(T\) at the marked
row is at least \(\kappa\); coalition mass is at most total absorption
(`quittingRootCoalitionMass_le_absorptionMass_of_nonempty`). The
robust moat at a unique-all-Continue cap
(`exists_eventually_absorptionNashDefect_moat_of_unique_allContinue`)
supplies \(\mathrm{moat}>0\) and a cap neighborhood on which every
root of absorption \(\ge\kappa\) pays total defect \(\ge\mathrm{moat}\);
cap convergence puts \(\tau_n.2\) eventually inside. ∎

## Placement

1. This is the `.2`-side complement of the stored zero: the decoration
   pins the marked **owner's** defect to zero on the prescribed (`.1`)
   side, while this floor makes the marked **row as a whole**
   uniformly inexact on the cap (`.2`) side at all late ranks.
2. Through the checked ledger, the uniform row defect charges the
   whole-minus-tail debt gap at an identified date: the reached-weight
   times \(\mathrm{moat}\) at the mark is a named, non-vanishing
   summand of \(D(\pi_n)-\text{surv}\cdot D(\tau_n)\).
3. Contrast with the exact-minimum-tail negative theorem
   (`not_isZeroQuittingRootNash_profileLiveRoot_of_positive_collisionStageMass_at_minimumTail`):
   that statement needs the exact minimum tail, a collision
   (\(|T|\ge2\)), and the prescribed side; this floor needs only
   near-minimum limits, any nonempty \(T\), and lives on the cap side
   with a quantitative moat.

Status: kernel-checked in the scratch lane
(`lean/FableMarkedRowCapDefectFloor.lean`; independently verified: clean
compile, lexical scan clean, axioms propext/Classical.choice/Quot.sound
only on all three theorems). The ledger corollary
`fable_strictInert_wholeDebt_excess_floor` (the whole-debt excess floor
\(D(\pi_n)\ge\kappa\cdot\mathrm{moat}+\text{surv}\cdot D(\tau_n)\))
is included and verified the same way.
