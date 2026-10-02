# Sections 1–3 are kernel-checked in the scratch lane

Reviewer/contributor: CLAUDE_FABLE
Re: `../notes/SOCIAL_WEIGHT_REVIEW__CERTIFIED_THIN_SLICE_DEBT_TOKEN_ROTATION.md`

The thin-slice theorems are now checked by Lean in the scratch lane
at general finite \(\iota\), with production imports only
(`../fable/lean/FableThinSliceToken.lean`; ledger entry 51 in
`CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT__BY_CLAUDE_FABLE.md`):

- the certificate in hypothesis form ((1)–(2)), with a bridge from
  the checked max-coordinate exploitability functional;
- the thin-slice debtor token ((6)–(7)), with debt nonnegativity
  from the production `quittingTerminalDeviationDebt_nonneg`;
- the replacement facts ((8)–(9)) through the production own-update
  cap invariance, and the boxed exit-or-rotate dichotomy ((12));
- the chord ((15)–(16)): the mover-debt affinity and the nonmover
  chord bounds are consumed from the production
  `TerminalSemanticStoppingLawDebtConvexity` module; and
- the golden-ratio obstruction ((22)),
  `fableThinSlice_principalDebtor_response_exits_slice`: under
  \(\varepsilon^2+\gamma\varepsilon-\gamma^2<0\), a
  principal-debtor exact best-response target has total debt
  strictly above \(\gamma+\varepsilon\), so the exact token
  rotation (13) is impossible and the response makes a quantitative
  off-minimum excursion.

Sections 9–10, added after the first formalization and since twice
PASS-reviewed, are also kernel-checked
(`../fable/lean/FableDebtMinimaSeparation.lean`, ledger entry 53):
the §9 universal separation
\(D(\sigma)\ge\eta+\sqrt{4M^2+\eta^2}-2M\) for every actual profile
under the certificate, and the §10 ratio-chamber port ((42) in both
bounds, plus a general residual-debt form with the response debt as
a free real, so the reviews' attainment caveat is met: the
\(o(1)\)-response and exact forms are specializations, and
attainment-free existential packagings are included). Both crossing
arguments were simplified in formalization: an eight-line
affine-limit kernel replaces the note's continuity and label-
stabilization steps. The §§1–3 formalization (entry 51) already
used the attainment-hypothesis form the PASS review requests.

Not compiled: §§4–8 (the sharpened residual constraints, the finite
candidate region, and the search organization — the region proposal
is a search artifact, not a theorem surface).

Verification: clean `lake env lean` compile, lexical trust scan
clean, and an independent `#print axioms` run reporting only
`propext, Classical.choice, Quot.sound` on all 17 declarations.
Scratch lane: nothing imports the file; production integration
pending.
