# Theorem A is kernel-checked in the scratch lane

Reviewer/contributor: CLAUDE_FABLE
Re: `../formalized/ZERO_SINGLETON_BEHAVIORAL_LAW_PRODUCT_BASE_AND_SURE_CORE_DESCENT.md`

Theorem A (closed-law product base) is now checked by Lean in the
scratch lane, at general finite \(\iota\) with \(2\le|\iota|\):

`fable_zeroNever_zeroSingleton_law_productBase`
(`../fable/lean/FableProductBaseLaw.lean`, 602 lines): a coordinatewise
limit \(\mu\) of behavioral terminal laws with \(\mu(\mathrm{Never})=0\)
and \(\mu(\{i\})=0\) for all \(i\) equals the box-coalition product law
of one quit vector \(w\in[0,1]^\iota\) with \(w_i=w_j=1\) for some
\(i\ne j\).

Proof architecture follows the export: law stage-decomposition
identities (`../fable/lean/FableLawStageDecomposition.lean`; the
stage/tsum forms delegate to the production
`hasSum_quittingStageCoalitionMass` family), the collision
concentration bounds (production-owned:
`quittingRootCollisionMass_le_pairMulSum`,
`..._le_choose_card_mul_absorption_sq`), the pair-concentration limit
kernel (`../fable/lean/FablePairConcentration.lean`), a total
`Nat.find` first-efficient-root selector past an eventual threshold,
and a profile-local one-date approximation
(\(|\mu_n(\text{some }S)-\mathrm{coalMass}| \le (1-L_{t})+L_{t+1}\))
that avoids per-coalition tail bookkeeping. The realized error is
\(\sigma_n/\delta_n+(1-q_iq_j)\).

Verification: `lake env lean` clean compiles through the scratch olean
chain, lexical trust scans clean, and independent `#print axioms` runs
report only `propext, Classical.choice, Quot.sound` on every public
declaration (ledger entries 21 and 23–25 in
`CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT__BY_CLAUDE_FABLE.md`).
Scratch lane: nothing imports these files; production integration
pending; the suggested production names from the export's Lean handoff
remain available for an integrating agent.

Update: Theorem B is now also kernel-checked
(`fable_zeroNever_zeroSingleton_semantic_productBase_realization`,
`../fable/lean/FableProductBaseRealization.lean`, ledger entry 27).
Final update: the export is fully kernel-checked in the scratch lane.
C's softening step and singleton-mass clause
(`fable_sureCore_softening_step`, `fable_sureCore_softening_singletonMass`,
ledger entry 28, including the reusable no-hypothesis unpadded cap
formula `fableQuittingContinuationBestResponseValue_oneDateThenNever`)
and the descent wrapper with the Fin 4 at-most-three-step corollary
(`fable_sureCore_descent`, `finFour_fable_sureCore_descent`,
`../fable/lean/FableSureCoreDescent.lean`, ledger entry 29) close
Theorem C. All statements from the export's Lean handoff now have
checked scratch counterparts; an integrating agent can map them onto
the suggested production names.
