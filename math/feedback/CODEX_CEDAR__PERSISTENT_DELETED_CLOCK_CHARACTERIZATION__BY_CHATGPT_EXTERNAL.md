# Independent external confirmation of the two-label characterization

Provenance: this derivation was produced by an external ChatGPT session
(not a conference agent), relayed by the conference owner, and checked
step-by-step by the orchestrator before filing. It was produced without
sight of `CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md` or
the export packet, so it is genuinely independent evidence, filed as
feedback rather than a new notebook because the results coincide.

## Claim checked

CEDAR's exact characterization: for a finite player set under a product
profile with marginals `p(t,j)`, writing `P` for the set of players with
divergent hazard series, the following are equivalent: (1) every
one-player-deleted suffix survival product tends to zero; (2) every
deleted opponent charge series diverges; (3) `|P| >= 2`. Joint suffix
survival vanishes iff `P` is nonempty, so the joint field is redundant
given all deleted fields.

## Confirmation

The external derivation reaches the identical equivalences by the same
two elementary inputs: the exponential upper bound
`prod (1-h) <= exp(-sum h)` for the divergent direction, the
finite-product union bound `prod (1-h) >= 1 - sum h` on a tail with
`sum h < 1/2` for the summable direction (which also disposes of
isolated zero factors), and the pointwise sandwich
`p(t,j) <= h_{-A}(t) <= sum_{k not in A} p(t,k)` for the reduction to
individual marginals. The four-player harmonic instance
(`H(m,N) = (m+1)/(m+N+1)` by telescoping; joint `H^2`; active-deleted
`H`; inactive-deleted `H^2`; both-active-deleted identically `1`) was
re-derived exactly, matching the checked `QuittingHarmonicGreenRegression`
instance. The exactly-one-persistent-carrier obstruction (CEDAR's
boundary case; the reason `frozenRadialRepeatedRoots_opponentSurvival`
assumes strict one-period deleted contraction) was found independently.

## Two small additions beyond the note

1. General deletion-count rule: for any deleted set `A`, all suffix
   survivals with `A` deleted vanish iff `P \ A` is nonempty; hence all
   pair-deleted clocks vanish iff `|P| >= 3`. This makes the note's
   "pair-deleted is out of scope" remark quantitative: two persistent
   carriers are exactly enough for every one-deleted clock and exactly
   insufficient in general for pair-deleted clocks.
2. Exact packet-boundary form: for block boundaries `N_0 < N_1 < ...`
   with per-block deleted absorption
   `A(k,-i) = 1 - prod_{t in B_k} prod_{j != i} (1-p(t,j))`, all deleted
   suffix clocks vanish iff `sum_k A(k,-i)` diverges for every `i`
   (partial first blocks are discarded; no uniform rate in the start
   date is needed). This is a rate-free cousin of the note's
   moving-source adapter; it is weaker than the adapter (no
   nominal-vs-actual error tolerance) but may be the more convenient
   interface when a producer controls per-packet absorption directly.

## Lean correspondence

The external text proposed four target lemmas; all are already realized
by checked declarations in
`UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`:
`summable_quittingOpponentClockCharge_iff`,
`hasTwoPersistentQuittingMarginals_iff_all_opponentClocks`,
`all_opponentClocks_iff_all_suffix_survival_zero`, and
`hasTwoPersistentQuittingMarginals_iff_all_suffix_survival_zero`, with
the joint bound alongside. No new Lean obligation arises from this
confirmation; item 2 above would be a small additional block lemma if
the formalizers want the packet-boundary interface explicitly.

No objection to any claim in the note or the export packet.
