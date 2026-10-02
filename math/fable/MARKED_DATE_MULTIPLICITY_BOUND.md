# Marked near-minimum dates are finitely multiple in any single play

Author: CLAUDE_FABLE. Companion to `MARKED_ROW_CAP_DEFECT_FLOOR.md`;
same toolkit, one play instead of one selection.

**Theorem (marked-date multiplicity bound).** Fix a cap \(c_\infty\)
whose exact product-root correspondence is uniquely all-Continue, a
terminal coalition \(T\), and \(\kappa>0\). There are
\(\mathrm{moat}>0\) and a neighborhood \(U\) of \(c_\infty\) such that
for EVERY behavioral profile \(\pi\) and every finite set \(F\) of
dates at which

1. the stage-coalition mass of \(T\) is at least \(\kappa\), and
2. the post-date all-Continue-shift tail cap lies in \(U\),

one has

\[
|F|\cdot\kappa\cdot\mathrm{moat}\;\le\;D(\pi).
\]

With bounded rewards \(D(\pi)\le 2M\,|I|\), so at most
\(2M|I|/(\kappa\,\mathrm{moat})\) such dates exist in any play.

**Corollary.** When \(c_\infty\) is the cap of a carrier pair at the
positive global minimum debt, uniqueness is automatic from the
table-level radius, and the same bound holds.

## Proof

The robust absorption moat at \(c_\infty\)
(`exists_eventually_absorptionNashDefect_moat_of_unique_allContinue`)
supplies \(\mathrm{moat}\) and the neighborhood \(U\): every root with
absorption \(\ge\kappa\) pays total Nash defect \(\ge\mathrm{moat}\)
against every cap in \(U\). At each date of \(F\), the live root has
absorption \(\ge\kappa\) (stage mass factors through live mass and
coalition mass; coalition mass bounds absorption), so its cap-side row
defect is \(\ge\mathrm{moat}\), and its reached weight (live mass) is
\(\ge\) the stage mass \(\ge\kappa\). The summed directed-transport
ledger
(`debt_zero_eq_sum_reached_defect_add_tail`, summed over players, at
any cutoff beyond \(\max F\)) expresses \(D(\pi)\) as the
nonnegative-weighted sum of row defects plus a nonnegative tail term;
keeping only the dates of \(F\) gives
\(D(\pi)\ge\sum_{t\in F}\text{live}_t\cdot\Delta_t
\ge|F|\,\kappa\,\mathrm{moat}\). ∎

## Placement

1. This is the absolute-chronology rarity certificate for marks: a
   single play can reach only boundedly many \(\kappa\)-heavy marked
   dates whose continuations sit near the minimum — while every rank
   of a strict-inert selection carries one such date with
   \(\kappa\) = the clock resolution. The selections evade the bound
   only because their profiles and root words are re-selected per rank
   (`FinFourMinimumAtomChronology` retains no cross-rank coherence) —
   the exact content of the open coherent-ray layer and the
   escaping-clock boundary.
2. Contrapositively: any future coherence theorem placing infinitely
   many rank marks inside one play with non-vanishing reached weight
   contradicts the ledger — so coherence, if achievable, must drive
   the reached weights of successive marks summably to zero, with the
   explicit budget \(D(\pi)/\mathrm{moat}\) on
   \(\sum_{t\in F}\text{live}_t\).

Status: kernel-checked in the scratch lane
(`lean/FableMarkedDateMultiplicity.lean`; independently verified: clean
compile, lexical scan clean, axioms propext/Classical.choice/Quot.sound
only on both theorems).
