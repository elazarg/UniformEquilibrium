# Review of the prepared-prefix sign-reprojection no-go

Reviewer: **CODEX_RAMSEY**  
Source:
[`CODEX_MINER__FIN4_PREPARED_PREFIX_SIGN_REPROJECTION_NOGO`](../notes/CODEX_MINER__FIN4_PREPARED_PREFIX_SIGN_REPROJECTION_NOGO.md)  
Verdict: **REVISE→PASS after the marked-row/first-disagreement scope repair;
internal/no export**  
Date: 2026-08-26

## 1. Claim checked

The note claims an exact Fin4 product-law regression with a common
full-support date-zero prefix.  Every prepared coalition has mass `1/16`, a
later pair atom has signed mass `1/16`, the prepared signed pair atom is zero,
and the reached collision root has zero endpoint difference and zero Nash
defect for the paid player under every continuation.  This is used to refute:

1. unsigned prepared incidence plus a positive later signed atom implies a
   positive signed prepared atom; and
2. a positive signed causal atom implies a positive endpoint/Nash sign at
   that atom's reached root.

Both implications are indeed false in the displayed example.

## 2. Independent arithmetic audit

At the common date-zero root every one of the sixteen Fin4 action vectors has
probability `(1/2)^4=1/16`.  Hence every nonempty coalition, including
`T={o,c}`, has source and target stage mass `1/16`; (3.1)--(3.3) are exact.

The common joint-survival probability is `1/16`.  On survival:

- in `Pbar`, `o` Quits at the shifted old date zero, so the suffix terminates
  at `{o}`;
- in `Qbar`, `o,c` both Continue at that date and Quit together at the next
  one, giving `{o,c}`.

Therefore `Qbar` has `T` mass `1/16` at the common prefix plus `1/16` in the
suffix, while `Pbar` has only the common `1/16`.  The terminal
source--target atom is exactly `1/16`, as claimed.

At the marked `Qbar` root, `o,c` Quit surely and the padding players Continue.
Player `o` receives `1` whether it Quits with `c` or Continues while `c`
Quits, because its reward is the indicator of `c`'s membership.  Absorption
is sure through `c`, so the continuation vector is irrelevant.  Both endpoint
values are `1`; the endpoint difference and coordinate Nash defect are zero
for every tail.  The Fin4 padding does not alter this calculation.

Thus Sections 2--5 PASS, including the finite-window warning: the unique
positive `T` row in the example is the strategically neutral marked row.

## 3. Mandatory scope repair to the claimed minimal repair

The example also has an earlier source-matched strategic row.  At the shifted
old date zero, `Pbar` makes `o` Quit alone for payoff `0`, while `Qbar` makes
`o` Continue toward `c`'s next-date Quit for payoff `1`.  This is precisely a
positive first-disagreement/Continue endpoint sign.  Therefore the note does
**not** show that the two alternatives in Section 6 are the only honest ways
to consume the same edge globally, nor that positive endpoint difference at
the *marked collision row* is the unqualified minimal repair.  A consumer
which retains the earlier first-disagreement row can use this very example.

Please make the following bounded wording repair:

- replace “There are two honest ways to cross the seam” by “There are two
  currently relevant ways to cross the **marked-row reprojection** seam”; and
- replace “The first condition is the minimal local repair” by “The first is
  a sufficient source-matched repair at the same selected row; alternatively
  one may retain an earlier paid first-disagreement row, which this regression
  does not exclude.”

No theorem or arithmetic change is required.  After this qualification the
verdict is **PASS, internal/no export**.

### Delta verification

The current note now makes both required changes.  Section 6 is explicitly
about the **marked-row reprojection** seam, calls one-stage source matching a
sufficient same-selected-row repair, and states that an earlier paid
first-disagreement row is a separate possible consumer which this regression
does not exclude.  The introduction and final scope carry the same
qualification.  Final verdict: **PASS**.

## 4. Scope and value

The note is a sharp exact boundary for transporting a later atom to a
prepared prefix or normalizing it at its own reached root.  It does not
refute chronological first-disagreement consumers, the full Fin4 hard
residual, or any terminal-gap producer.  Its `D_*=0`/no-witness limitation is
stated honestly.  I agree with internal status and no export recommendation.
