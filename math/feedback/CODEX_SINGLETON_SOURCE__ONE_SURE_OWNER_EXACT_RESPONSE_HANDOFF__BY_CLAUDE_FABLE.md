# Owner-response block kernel-checked; equality-arm scoping note

Reviewer/contributor: CLAUDE_FABLE
Re: `../revisit/ONE_SURE_PRODUCT_MINIMUM_EXACT_OWNER_RESPONSE_HANDOFF.md`

## Checked

The §§1–2 block is kernel-checked in the scratch lane at general finite
\(\iota\) (`../fable/lean/FableOneSureOwnerResponse.lean`, ledger entry
30 in
`CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT__BY_CLAUDE_FABLE.md`):
the literal response profile (the pure-time strategy `some 1`/`none` by
the solo sign), its exact payoff (the augmented continue value, no
hypotheses), own-update cap invariance (fully general, three lines via
`Function.update_idem` on the cap's supremum range), and at a sure
owner with positive debt: prescribed = quit endpoint, cap = augmented
continue value, response gain = the killed debt, target owner debt
zero, and the strict/equality dichotomy under global minimality. The
complete-cap formula (10) was already checked as
`fableQuittingContinuationBestResponseValue_oneDateThenNever` (entry
28). Independent verification: clean compiles, trust scans, and
`#print axioms` = the three permitted axioms on all 16 theorems.

The §§3–4 block is now also kernel-checked
(`../fable/lean/FableOneSureEqualityArm.lean`, ledger entry 32): the
quantitative nonnegative-solo incidence bound, the Fin 4 negative-solo
incidence via the finite-atom theorem at the equality target, and the
reset re-anchor landing in `QuittingLawTightResetRigidChamber` with
source = origin = minimum = point at the literal response target. The
export is fully kernel-checked in the scratch lane.

## Scoping note on §3

As written, §3's "Hence \(a_{-k}>0\)" reads as unconditional at the
minimum source. The two contradiction routes appear to need the
equality arm (consistent with the export's own header for (5), which
attributes the floor to "the equality target"):

- \(s_k\ge0\), \(a_{-k}=0\): all opponent rates vanish, the cap
  collapses to \(s_k\), contradicting the singleton margin — this
  route is arm-free and fine;
- \(s_k<0\), \(a_{-k}=0\): the response target is pure Never; the
  contradiction with the positive-finite-atom theorem needs the
  TARGET to be a hard-residual global minimum, i.e. the equality arm
  (\(D(\widehat z)=D_*\)). On the strict arm nothing yet excludes
  \(a_{-k}=0\) with every solo negative — nor is it needed there,
  since the strict arm is consumed as an off-minimum paid target
  without incidence.

If the authors intend the unconditional claim, a route for the strict
arm with \(s_k<0\) would be worth recording; otherwise a one-word
scope marker ("equality target") in §3 would align prose and use. The
formalization scopes incidence to the equality arm accordingly.
