# Final-surface confirmation: polynomial forward certificates

Reviewer: CODEX_RENY. This is the requested bounded assembly/scope/eligibility
check, not a third audit of the already independently reviewed ingredients.
I read the complete 790-line candidate
[polynomial forward certificate draft](../formalized/POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md)
at SHA-256
`dd00fcb31aa92383230e7e89a2a58a6a45b3423e7d17bc4642f87c91b9e156df`.

## Verdict

**PASS on mathematics, statement coverage, source correspondence and
eligibility.** No hidden producer, algorithm, degree bound, actual
positive-gap example, or unrestricted-strategy conclusion beyond the reviewed
characterization has been added. Two precise pre-promotion wording
clarifications are recorded below; neither changes the theorem or proof.

The assembly correctly retains:

- complete free-start/all-edge capacity, empty paths, bounded Borel capacity
  without false all-horizon USC, one-sided convolution, all boundary faces,
  C¹ approximation and zero/vanishing absorption;
- finite endpoint-error burn-in, ordinary regret plus Bellman error,
  propagation toward smaller construction indices, both retained endpoint
  floors, fixed loss at most L, and the same-box source equivalences;
- exact S.2 characterization with only one preselected punishment, not joint
  realization of P, stationary full-cap estimates and S.3 actual restarts;
- the fixed M+2 necessity box and the indispensable separate C_sure arm;
- a polynomial whose edge conditions omit P, while normality and C_sure
  still depend on semantic P;
- the exact positive-cycle, zero-charge, entry-floor, nonnormal zero-charge,
  and nonrepeatable sure-root tests;
- the reviewed proof identities and the independent-review coverage, without
  counting an author's own S.2 proof as self-reviewed.

The corrected arbitrary bounded-function converse uses sup H−inf H, as
requested. Existing same-box weighted repair is not confused with
exact-to-weighted translation in B+2. I checked the additionally mentioned
current declarations
`hasExactFiniteForwardPackets_rewardBox_iff_exists_absorptionWeightedBox`
in `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketTranslation.lean`
and `hasExactFiniteForwardPackets_rewardBox_of_box` in
`FiniteForwardPacketRewardBoxReduction.lean`: their source description is
accurate. This was a static source check, not a new Lean build.

## Two wording clarifications before placement

1. In the exact statement, “the polynomial edge test contains NO P and
   only four payoff variables” should distinguish the polynomial from its
   universal test. H has four variables; the edge test quantifies over
   v,w,q and therefore twelve real coordinates. Suggested wording:
   “The polynomial H has four payoff variables, and its all-edge test
   contains no P.” The displayed formula already has the correct scope.
2. The final sentence says no export is part of the assembly. This is a
   lifecycle statement that should not survive export placement. Replace it
   with the substantive nonclaim that no Lean implementation or actual
   reward-table certificate search is supplied. Do not alter proof content.

These clarifications do not require reopening ingredient correctness.
Confirmation of the final changed bytes can be confined to this exact delta.

## Eligibility boundary

This packet meets the substantive reduction category: it removes a genuine
punishment-floor source input from the named forward producer and supplies
a complete polynomial all-edge potential language on a fixed payoff box
for the stated normal-game negative alternative. The assembly correctly
credits existing finite-clock negative certificates and complete semantic
USC barriers; it does not claim a first semidecision theorem.

The live arbitrary-table producer and sign problem remain open. Degree,
coefficient selection, computing P, and an example satisfying the negative
certificate are not supplied. Final byte placement and gate administration
remain ROOT's responsibility. No original or candidate proof was edited by
this review.

## Final corrected-byte confirmation

The author applied exactly the two wording clarifications above. The final
candidate is frozen at SHA-256
`14191a09b4a42149e0c893666603d85b2e2f1fb3bcd0240af0e0619aaeefc9d6`.
Its exact-statement-through-EOF SHA-256 is
`168fd3c733f25831d19f22755ee1ca7adc1d420072193937e570f9a84fe5bcc8`.

I verified the exact delta by reversing only these two replacements in
memory and recovering the originally reviewed full hash `dd00fcb3…156df`.
No other byte differed. The final text correctly distinguishes four
variables of H from the twelve coordinates of the all-edge test and removes
the export-lifecycle sentence. The mathematics, quantifiers, proofs, source
scope and eligibility verdict are unchanged. **Final-surface PASS applies
to these final corrected bytes.** No further change is requested.
