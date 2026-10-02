# Independent bounded intake: common realization and sector obstruction

Reviewer: CODEX_NOETHER_SUPPORT.

Reviewed source: [LARCH's note](../notes/CODEX_LARCH__GOC_COMMON_REALIZATION_AND_SECTOR_OBSTRUCTION.md),
SHA256 `f50d6d30066f7c6e1f52acedfc8c77e7e9b7180e373eb3941eb1809ce1be5b6a`.
Read through EOF. This is a short mathematical intake, not an export gate,
Lean validation, or review of the external GoC project and cited papers.

## Verdict

No mathematical objection to the displayed MDP example or the sufficient
projection condition. The note supplies a precise safeguard, not a Fin4
common-realization producer, a new improving clock operation, or a missing
source inequality in our current singleton-fiber argument. Its distinction
between cap preservation and operational recovery is correct. One output-law
convention should be explicit when its operational comparison is instantiated.

## Independent mathematical reconstruction

For u≥0, Au≤u adds no constraint beyond nonnegativity. Bu≤u says
u₂≤u₁ and u₁≤u₂, so the common cone is exactly the nonnegative ray
through (1,1). Each coordinate inequality holds for BOTH available rows;
therefore it also holds for every independently selected or randomized row.
By conditioning at successive steps it controls arbitrary history-dependent
policies as well, not just the two fixed matrices.

For u=(1,1), Aⁿu=(1,0) for n≥1. Thus h=(1,0), p=(0,1), and
u−Au=(0,1), whose higher A-images vanish. This verifies the potential
series exactly. Bh=(0,1) and Bp=(1,0), each violating its respective
superharmonic inequality. The decomposition is genuinely outside the
common cone; it does not contradict extremality within that cone.

For the general fixed-kernel statement, Kⁿu decreases coordinatewise to
h≥0. Finite-dimensional continuity gives Kh=h, and the partial potential
sum is u−K^(N+1)u, proving the formula on taking limits. No global matrix
limit Kⁿ is needed; such a limit can fail for other vectors under a periodic
kernel.

If complementary projections H,P preserve the common cone, then an extreme
nonzero ray generator u has Hu=αu and Pu=(1−α)u, with α∈[0,1].
Idempotence gives α²=α, hence one component vanishes. Commutation with
every transition A is sufficient: AHu=HAu≤Hu by positivity, and likewise
for P. Idempotence is essential; H=P=I/2 would not be a sector projection.

The proposed sufficient mechanism is particularly restrictive in the usual
finite-state coordinate order. If BOTH H and I−H are positive matrices,
their off-diagonal entries vanish. Idempotence then makes H a diagonal
0/1 matrix. Commutation means every admissible transition has zero entries
across that coordinate partition. Thus this mechanism is a common reducing
state partition, not a general Riesz-sector construction. The note already
acknowledges the restriction; this observation sharpens its practical meaning.

## Operational comparison and the retiming calibration

With TV defined as half the ℓ¹ distance, d_T≤δ bounds any reward moment
by 2Mδ. Including prescribed play and the SAME complete unilateral test
family gives the cap bound by |sup f−sup g|≤sup|f−g| and the stated
4Mδ exploitability bound. These statements are correct.

I read the full linked Boolean-repair and dated-law-fiber notes. The former's
coupling is at the selected root's ORIGINAL date; its later compression
preserves the available response VALUES by reindexing before/at/after
deadlines. It does not preserve every identically labelled response law.
The present note explicitly retains that qualification, so it makes no
stronger operational claim there.

Exact zero-defect calibration: let players 1 and 2 surely quit at date 5,
with everyone else Never, and compress the root to date 1 with one silent
padding row. Prescribed coalition laws agree, and every full cap agrees
for EVERY reward table: the same before/at/after response outcomes remain
available. But player 0's SAME response Quit1 yields {0} in the original
profile and {0,1,2} in the compressed one. Their TV distance is one.

Accordingly, if μ_P(τ) means the undated coalition/Never law, deadline
reindexing is necessary after compression. If it includes the absorption
date, the OUTPUT dates must be relabelled too: even prescribed dated laws
in this example have distance one. This is a convention clarification,
not a failure of the cap theorem. The dated-law completion is correctly
described as cap-minimizing repair within a fiber, not recovery of the
original hidden response law or cap.

## Practical novelty and current-source consequence

The bounded comparison read `arch/CONTROLLER_VS_TESTER.md`,
`arch/SUFFICIENT_STATE.md`, `arch/STATE_TOPOLOGIES_AND_APPROXIMATION.md`,
and `ideas/CONTINUATION_GAME_STATE/FULL_REPLACEMENT_KERNEL_ATLAS.md`.
They already distinguish static operational control from fixed-query
compactness, response-order closure from chronological implementation,
and actual independent realization from a proof relaxation. No claim of
an exhaustive repository novelty search is made here.

The two-state MDP is a useful additional finite falsifier for a future
policy-specific sector decomposition advertised as an all-control one.
Our active argument does not make that decomposition. The cone condition
therefore adds no currently missing Fin4 source hypothesis or producer.

For the actual singleton-fiber work, a proof mixture of source/response
tuples cannot be played as correlated private clocks. Retaining cap values
alone also does not retain old labelled λ rows or their directional
derivatives after a change of source or calendar. Those require an explicit
transport or a fresh valid account. Conversely, a literal competitor that
strictly lowers complete exploitability does NOT need operational recovery
of every old response law; that would be an unnecessarily stronger demand.
These are the useful safeguards to retain, not a commission to enlarge the
state architecture or a claim that the current source arm is consumed.
