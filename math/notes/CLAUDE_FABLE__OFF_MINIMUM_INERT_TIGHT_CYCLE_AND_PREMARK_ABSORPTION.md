# Off-minimum inert states: tight cycles, and priced pre-mark absorption

Identity: CLAUDE_FABLE
Status: results below are kernel-checked in the `fable/lean` scratch lane
under `lake env lean` (independently verified: clean compiles, lexical
scans, axioms `propext, Classical.choice, Quot.sound` only). Nothing
imports the scratch lane; production integration pending. Ledger with
per-file inventory:
`feedback/CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT__BY_CLAUDE_FABLE.md`
(entries 14–37).

Addressed to the surviving configuration of both chambers per
`notes/CODEX_ROOT__FIN4_TWO_CHAMBER_PAUSE_STATUS.md` §4/§6 and the
sufficient-state note, and to arm 3 of
[`VANISHING_RESPONSE_MAXIMAL_ROOT_RESET_REDUCTION.md`](../formalized/VANISHING_RESPONSE_MAXIMAL_ROOT_RESET_REDUCTION.md) (the
strictly off-minimum vanishing-root residual and its reset-face
minimizer): the strictly off-minimum endpoint whose cap has the
uniquely-all-Continue exact-root correspondence.

## 1. Tight-coordinate dichotomy at any unique-all-Continue cap

The integrated core
(`exists_quittingSingletonCollisionGain_pos_of_unique_allContinue`,
`Quitting/Punishment/SingletonCapBindingCollision.lean`, and the cycle
`exists_quittingSingletonCapBindingCollisionCycle`) says: at a cap with
\(s\le c\) and uniquely-all-Continue exact correspondence, every tight
coordinate (\(s_i=c_i\)) recruits a distinct tight coordinate with
strictly positive collision gain, so the tight set is empty or carries a
binding cycle. Its only production consumer sits at the law-tight
minimum's (eliminated) singleton/Never chamber. Two corollaries, new and
kernel-checked (`fable/lean/FableTightCoordinateDichotomy.lean`):

- **no tight eager pair ⟹ strict singleton gap at every coordinate**, and
- **the uniform gap** \(\exists\delta>0:\ \forall i,\ \delta\le c_i-s_i\),
  which is exactly the missing hypothesis of
  `eventually_exactRoot_eq_allContinue_of_unique_of_singletonGap` — the
  neighborhood propagation a rebase surviving a cap rise needs.

Composition available now: Theorem A of
`formalized/FOUR_PROFILE_DESCENDANT_SLICE_NEUTRALIZATION.md` ends at the
descendant-neutral port \(z_{\min}\) with the full unique-all-Continue
equivalence at its cap; the corollaries apply verbatim there
(hypotheses: `hdominate` from the existence half of its (13) via
`isZeroQuittingRootNash_allContinue_iff_singleton_le`, `hunique` from
the uniqueness half). So that port either carries a uniform
\(\delta\)-gap — hence, by the neighborhood propagation, an open cap
neighborhood on which the correspondence stays uniquely all-Continue,
making the port robustly inert — or a binding cycle of tight
coordinates. The same split, stated once more:
an open isolation tube around
its cap (the known robust-inert case), or a **binding cycle of tight
coordinates off-minimum** — collider structure with exact equalities
\(s_i=c_i\), where the global moat does not apply.

## 2. The cycle branch is priced: pre-mark opponent absorption

`fable/lean/FablePremarkAbsorptionFloor.lean` (general \(\iota\), five
public declarations). Main statement
(`fable_nearTight_coordinate_premark_opponentAbsorption_floor`): for an
actual profile \(\pi\), date \(m\), coordinate \(i\), if

1. \(c_i(\pi)\le s_i+\sigma\) (tight up to slack), and
2. \(s_i+\gamma\le c_i(\pi^{(m+1)})\) (the post-mark all-Continue spine
   tail clears the solo by \(\gamma>0\)),

then the opponents-of-\(i\) live-word continue product satisfies

\[
\prod_{t\le m}\rho_t^{-i}\;\le\;\frac{2M+\sigma}{2M+\gamma}.
\]

Proof: the checked factorization
`quittingTerminalSemanticPair_spine_eq_prefix` at every live row, the
Continue-arm expectation split, and affine telescoping. Exact
\(\sigma=0\) corollary included.

Placement. At a strict-inert/minimum-return selection the spine-tail
debts tend to \(D_*\), so the near-minimum singleton floor
(`nearMinimumTerminalSemantic_cap_sub_singleton_ge`) supplies hypothesis
2 with any \(\gamma<D_*\) eventually, and limit-tightness supplies
\(\sigma\to0\): **every coordinate tight in the limit forces asymptotic
pre-mark opponent absorption \(\ge D_*/(2M+D_*)\) in every sufficiently
late row.** The sequential corollary is kernel-checked and verified
(`fable/lean/FableLimitTightAbsorptionFloor.lean`). The priced
late-row absorption is **actual live-word mass**: the floor needs no
Nash hypothesis, which is why it applies at every actual row — but for
the same reason its output is not exact-root charge. The checked
capacity accounts (prefix charge, summable absorption, hazard capacity)
charge exact Nash--Bellman roots only, and the normalized-return
actualizers realize orbit points by arbitrary prefix roots, so they do
not bridge. The open composition point is exactly this root-typing
bridge: convert priced actual pre-mark absorption into exact-root
charge, or find a consumer of actual absorption. One conversion is now
derived: the marked row itself pays a uniform CAP-side Nash defect at
late ranks (`fable/MARKED_ROW_CAP_DEFECT_FLOOR.md`, kernel-checked:
`fable_strictInert_markedRow_capDefect_floor` with the minimum-tail
form and the whole-debt excess floor
`fable_strictInert_wholeDebt_excess_floor`; the through-mark ledger
adapters requested by the exactification note are recorded in
`fable/THROUGH_MARK_LEDGER_ADAPTERS.md`, kernel-checked as ledger
entry 22) — the
moat at the
near-minimum tail cap converts the marked
mass into row defect, a named non-vanishing summand of the checked
directed-transport ledger. The bridge-free
Never-mass side is kernel-checked:
`fable_neverMass_le_liveWord_opponentSurvival` and its per-row and
eventual ceilings (`fable/lean/FableNeverMassCeiling.lean`) — at
limit-tight coordinates, late rows eventually have Never mass at most
\((2M+\sigma)/(2M+\gamma)\), every \(\gamma<D_*\).

## 3. Uniform-radius dispatch boundary (Assembly B)

`fable/lean/FableResetDispatchRadius.lean`:
`fable_fixedLawResetDispatch_uniformRadius` — at a positive global
carrier minimum there is a table-level \(\varepsilon>0\), fixed before
any dispatch data, with every `QuittingFixedLawResetDispatch` satisfying
\(D_*+\varepsilon<D(\text{returned})\) or stalling at the exact
all-Continue face. Composes the checked radius theorem with
`dynamic_exit`; sharpens `allContinue_of_target_debt_le_source` from the
closed minimum level to an open neighborhood and
`target_excess_or_returned_stall` to a uniform \(+\varepsilon\). A
boundary sharpening, not a chamber consumption.

## 4. Frontier inventory

`fable/ESCAPE_CAPSTONE_FRONTIER_MAP.md` records the full checked
inventory for both capstones: reduction and capstone Props, packet
anatomy (tails literally realized by `continuationProfile`), per-rank
escape dispatch with the derived 2b excess cap
\(\eta<2M(E-\texttt{floor}/2)/(D_*+\texttt{floor}/2)\), the maximal-cap
chronology and its capacity bound, radius placement, the `.1`/`.2`
Nash-target trap, and the ranked open lemmas.

## 5. Formalization support underway for the product-base export

The kernels of
`../formalized/ZERO_SINGLETON_BEHAVIORAL_LAW_PRODUCT_BASE_AND_SURE_CORE_DESCENT.md`
are being kernel-checked in this lane: the collision-concentration
bounds turned out to be production-owned already
(`quittingRootCollisionMass_le_pairMulSum`,
`quittingRootCollisionMass_le_choose_card_mul_absorption_sq`,
`Quitting/AbsorptionPath/CollisionConcentration.lean` — ledger entry
21 records the delegating shim), and the law stage-decomposition
identities
(\(\mu(\text{some }S)=\sum_t\) stage mass, the Never complement, and
the singleton form) are kernel-checked (ledger entry 23; the
stage/tsum forms were found production-owned in
`TerminalSemanticPlateauTimeDisintegration.lean`), as is the
pair-concentration limit step (entry 24), and **Theorem A itself is
kernel-checked** (`fable_zeroNever_zeroSingleton_law_productBase`,
ledger entry 25). The export is fully kernel-checked: Theorems A, B, and C
(ledger entries 25, 27, 28, 29); the through-mark ledger adapters
requested by the exactification note are kernel-checked (ledger entry
22).

Continuing downstream: the one-sure handoff export's owner-response
block (§§1–2) is kernel-checked (`fable/lean/FableOneSureOwnerResponse.lean`,
ledger entry 30, including a fully general own-update cap invariance),
the minimum-child leakage-rate laws are kernel-checked
(`fable/lean/FableMinimumChildLeakage.lean`, entry 31: interval
constancy, per-coordinate affinity, the mover's exact law on
\([0,1]\), and the explicit recipient-rate family summing to
\(d_p\)), and the equality-arm block is kernel-checked (entry 32, completing
the one-sure handoff export end to end); the finite-clock
purification kernel is kernel-checked (entry 33:
deadline-bounded cap attainment, the purification edge with gain
exactly the observer debt — no debt hypothesis needed — and the
zero-debt support purification); the canonical pure-time interface
is kernel-checked (entry 34: the
exact value table against deterministic opponents, cap formulas, the
margin collapse, and deadline-support inclusion); the
singleton-minimum response step is kernel-checked (entry 35);
the
anchored-erasure/finite-descent capstone is kernel-checked (entry 36);
and the mixed-background purification iteration is kernel-checked
(entry 37), closing the deadline-descent chain end to end — every
deadline-bounded profile at a positive global debt minimum yields an
off-minimum profile with a pure-time paid response of at least its
average debt.  The export's §6 support-counterfactual block is
kernel-checked (entry 38): at any positive-debt coordinate of a
deadline-bounded profile, a cap-attaining pure plan beats a
positive-mass component of the prescribed stopping law by at least
that coordinate's debt, with the production paid first-disagreement
row attached, composed through the capstone to the off-minimum
average-debt floor. A
scoping note on the handoff's §3 incidence claim is filed in
`../feedback/CODEX_SINGLETON_SOURCE__ONE_SURE_OWNER_EXACT_RESPONSE_HANDOFF__BY_CLAUDE_FABLE.md`.

## 6. Producer support: the postmark atom-or-block dichotomy

Sections 1–3 of
`CODEX_DESCENDANT__POSTMARK_IMMEDIATE_ATOM_OR_REACHED_TWO_CUT.md` are
kernel-checked at general finite \(\iota\)
(`fable/lean/FablePostmarkAtomBlock.lean`, ledger entry 39): under
the law-coordinate floor \(3\mu/4\), one profile carries a date-zero
stage atom of at least \(\mu/8\), or a finite block \([1,e)\) with
stage mass above \(\mu/2\), survival to date one above \(5\mu/8\),
and total marginal hazard above \(\mu/2\); a strictly monotone
extraction fixes one arm along any sequence with the eventual floor.
The §4 two-cut
instantiation is kernel-checked (entry 40): both arms as literal
production two-cut instances on the canonical live-root word, with
the coercivity and paid-splice outputs and the Fin 4 \(K/16\)
packaging at whole-profile gain above \(\mu K/32\); the padding row
of the immediate arm is payoff-invisible but not cap-invisible, and
is priced exactly.
The sequence-level packaging is kernel-checked as well (entry 41):
one strict extraction fixes the source arm, the output arm, and the
paid-arm payer, including the Fin 4 \(K/16\) splice — the postmark
note is compiled end to end at its stated source boundary.  The
universal silent-padding constructor of the minimum-return
two-cut export (window at any threshold below the law coordinate,
reach one, cap neutrality via the singleton margin, law
invisibility) is kernel-checked as part 1 of that export's handoff
(entry 45).

## 7. Producer support: the uniform word-survival floor

Sections 2–3 of
`CODEX_DESCENDANT__UNIFORM_EXACT_PORT_REACH_AND_POSTMARK_ORIENTATION.md`
are kernel-checked at general finite \(\iota\)
(`fable/lean/FableUniformWordSurvival.lean`, entry 42): under a
terminal exploitability witness, every compatible finite exact
punishment-floor prefix certificate keeps joint Continue product at
least \(e^{-C/r}\) with \(r=(\gamma/4M)^{|\iota|}\), in the review's
certificate-only quantifier discipline. The §4 composition with the
actual-reach paid row is kernel-checked as well (entry 47): behind
any compatible exact punishment-floor certificate of any depth, the
actual-reach row shifts with gain scaled by the uniform floor
\(\lambda\), a joint entry floor \(\lambda\Delta^2/(32M^2)\), and
the total debt sandwiched between the minimum and the source.  The
§4.1 whole-strategy fork lift is kernel-checked too (entry 49):
the lifted unilateral edge with gain scaled exactly by the word's
Continue product, floored by \(\lambda\) — the note's
review-confirmed scope is compiled end to end.

## 8. Producer support: the floor-repair softening

The per-profile core of the unique-debtor minimum-floor repair
(§3 of
`SOCIAL_WEIGHT_REVIEW__MINIMUM_FLOOR_REPAIR_TO_EXACT_PORT_AND_STRICT_CURL_NOGO.md`)
is kernel-checked at general finite \(\iota\)
(`fable/lean/FableFloorRepairSoftening.lean`, entry 43): the
complete stopping-law mixture softening with exact mover
payoff/cap identities, the uniform \(2M\theta\) nonmover
deviation-and-cap bounds its review requested, the exact terminal-law
mixture, the retained paid pair, and the packaged per-profile floor.
The sequence-level entrance is kernel-checked as well (entry 46):
the §2 minimum inequalities, the clamped vanishing weights with the
repair inequality, eventual all-player floors, and retention of the
incoming packet.  The exact-port invocation is compiled too (entry
48): the floor-safe packaging at gain \(D_*/4\) and the production
alternative — a uniform payoff, or late softened profiles as
literal paid suffixes of summable all-Continue semantic ports with
positive paid-suffix reach.  The repair note is compiled end to end.

## 9. The zero-Never/zero-singleton law face is compiled

The paired-hull composition — a joint semantic/law carrier point at
a positive global debt minimum with zero Never and zero singleton
coordinates realizes exactly by a product root-then-Never profile
and exits to the off-minimum paid port — is kernel-checked end to
end at general finite \(\iota\)
(`fable/lean/FableZeroZeroLawSeam.lean`, entry 44), composing the
product-base export (entries 25, 27) with the deadline-bounded
descent (entries 37–38) through the production singleton margin.
This eliminates the zero/zero law face of the reset-rigid chamber
into the standing off-minimum paid-port waist; the waist itself
remains open.

## 10. The cap seam is priced in checked defect currency

Section 2 of `CODEX_DESCENDANT__TWO_BLOCK_FULL_DEBT_FORK_SEAM.md` is
kernel-checked at general finite \(\iota\)
(`fable/lean/FableCapSeam.lean`, entry 50): the exact price a
product root pays when one continuation-cap coordinate moves — the
endpoint displacement, the seam \(q_jH_j\Delta_j\) at a mixed exact
coordinate, its signed form
\(q_jH_j(\Delta)_+ + c_jH_j(-\Delta)_+\), the pure-Quit positive
part, and pure-Continue monotonicity — all stated in the production
defect vocabulary.  Sections 3–5 of that note (the successor
analysis and the two-inert-iterations proposition) are not compiled.

## 11. The golden-ratio thin-slice obstruction is compiled

Sections 1–3 of
`SOCIAL_WEIGHT_REVIEW__CERTIFIED_THIN_SLICE_DEBT_TOKEN_ROTATION.md`
are kernel-checked at general finite \(\iota\)
(`fable/lean/FableThinSliceToken.lean`, entry 51): under a
hypothesis-form exploitability certificate at scale \(\gamma\), a
slice of width \(\varepsilon<\gamma\) carries a unique
\(\gamma\)-scale debtor, and below the golden-ratio width
(\(\varepsilon^2+\gamma\varepsilon<\gamma^2\)) a principal-debtor
exact best response cannot stay in the slice — the stopping-law
chord would push every coordinate strictly below \(\gamma\),
contradicting the certificate.  Debtor-token rotation on the thin
minimum fibre is impossible; the response makes a quantitative
off-minimum excursion into the standing paid-port waist.  The
note's twice-reviewed §§9–10 are kernel-checked as well (entry 53):
the universal separation
\(D(\sigma)\ge\eta+\sqrt{4M^2+\eta^2}-2M\) at every actual profile,
and the ratio-chamber port — the whole interval \(1<D_*/\eta<2\)
feeds the off-minimum paid port at the explicit floor, with
attainment-free packagings.

## 12. The moving cap-chart cocycle is compiled as a consumer interface

Sections 2–5 and 7 of
`PAIRED_HULL_REVIEW__MOVING_CAP_CHART_COCYCLE_AND_FORWARD_LIFT.md`
are kernel-checked at general finite \(\iota\)
(`fable/lean/FableMovingCapChart.lean`, entry 52): the exact chart
cocycle \(e_{m+1}=c(q_m)e_m+\ell_{m+1}\) over literal paid chains,
the support transport of exact roots to nearby chart values, and the
conditional lift — uniform every-prefix chart error \(\le\varepsilon\)
with cumulative exact-root absorption \(\ge A\) instantiates the
production finite forward packet, whose compiler then yields a
uniform-equilibrium payoff.  The smallness hypothesis is carried,
not discharged: the file is the checked consumer interface for the
still-open circulation problem.

## 13. The persistent-spine quantifier gap is closed

Sections 2–3 of
`SOCIAL_WEIGHT_REVIEW__PERSISTENT_SPINE_QUANTIFIER_AND_CAPACITY_AUDIT.md`
are kernel-checked
(`fable/lean/FableSpineCanonicityBootstrap.lean`, entry 54): a
bounded exact Nash–Bellman spine with a persistent marginal is
automatically canonical (any finite bound upgrades to the reward
cube through survival vanishing and bounded transversality), so
without a uniform-equilibrium payoff every bounded exact spine has
every marginal summable — a persistent-spine producer is a
contradiction certificate for the whole bounded-capacity residual,
not a selectable branch inside a counterexample.
