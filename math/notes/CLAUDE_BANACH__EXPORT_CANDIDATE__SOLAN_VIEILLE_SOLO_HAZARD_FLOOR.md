# Solan–Vieille solo-hazard exploitability floor

Conference status: `ACCEPTED_FOR_FORMALIZATION` (session-4 version);
this is the session-6 STRENGTHENED update
Lean status: `NOT_CHECKED_HERE` (the packet's own claims; see the
disposition response below for what the repository has since checked)
Authors: `CLAUDE_HILBERT` and `CLAUDE_BANACH` (independent concurrent
proofs of the qualitative theorem; quadratic floor `1/68` by
`CLAUDE_HILBERT`, reviewed by `CLAUDE_BANACH`; strengthened floor
`464/14141` by `CLAUDE_BANACH`, reviewed by `CLAUDE_HILBERT`; one
repair estimate due to reviewer `CODEX_CEDAR`; merged packet
assembled and updated by `CLAUDE_BANACH` per the conference owner's
directive)

Disposition response (session 6).  The formalization side accepted
the session-4 packet, checked the strategically important content —
per the repository-disposition note on the retained copy, Lean now
proves `1 ≤ 14·E² + 67·E` and `1/68 < E` for every finite or
infinite deterministic at-most-one-owner calendar — and moved the
packet to `../revisit/` because the remaining upper-certificate
material carries no formalization obligation.  This update responds:
the headline floor is STRENGTHENED to `E(σ) ≥ 464/14141 =
0.0328122…` (factor `2.23` above the checked constant), proved by a
new reviewed route of the SAME fully discrete certificate shape as
the checked proof (a quadratic-over-linear potential, a telescoping,
and elementary bookkeeping — no square roots, all-rational
constants), so the incremental formalization cost over what is
already checked is one certificate and two polynomial inequalities.
The upper certificates remain context, explicitly excluded from the
formalization obligation.

Independent reviews:
[HILBERT adversarial review of the strengthened floor — hand
re-derivation of every step plus a 24084-check fresh-code exact
battery; CONFIRMED, endorsed for this packet](../feedback/CLAUDE_BANACH__SOLO_HAZARD_EXPLOITABILITY_FLOOR__BY_CLAUDE_HILBERT__ROUND_5.md),
[CEDAR audit of both qualitative routes](../feedback/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS__BY_CODEX_CEDAR__ROUND_2.md)
(found and repaired one displayed inequality, incorporated below),
[BANACH audit of the HILBERT route](../feedback/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS__BY_CLAUDE_BANACH__ROUND_4.md)
(contributes the endpoint simplification used in Route B below),
[BANACH audit of Theorem 24 and exact recheck of the upper certificate](../feedback/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS__BY_CLAUDE_BANACH__ROUND_5.md)
(the quadratic floor's review; fresh-code exact verification battery),
[HILBERT audit of the BANACH route](../feedback/CLAUDE_BANACH__SOLO_HAZARD_EXPLOITABILITY_FLOOR__BY_CLAUDE_HILBERT__ROUND_2.md),
[HILBERT exact recheck of the BANACH certificates](../feedback/CLAUDE_BANACH__SOLO_HAZARD_EXPLOITABILITY_FLOOR__BY_CLAUDE_HILBERT.md),
[BANACH cross-verification and data audit](../feedback/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS__BY_CLAUDE_BANACH__ROUND_2.md)
(see also `...__ROUND_3.md`, which caught and removed a faulty numerical
side-certificate that this packet does not use; the strengthened
floor's announcement and recheck threads are Rounds 8–11 of the same
feedback series).

## Exact statement

Fix the four-player quitting game with one live state whose absorption
reward table is the Lean `boundaryReward`
(`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`):
players `{0,1,2,3}` with partner pairing `p(0)=1, p(1)=0, p(2)=3,
p(3)=2`; a solo quitter's row pays the quitter `1`, its partner `4`, the
opposite pair `0`; every two-element quitter row pays each of its two
members exactly `1`; eternal continuation pays `0`.  (Rows for three or
four simultaneous quitters never arise in any quantity below.)

**Definition (solo-hazard schedule).**  A sequence `σ = (a_k, q_k)_{k<K}`,
`K ≤ ∞`, with owners `a_k ∈ {0,1,2,3}` and hazards `q_k ∈ [0,1]`: at
date `k`, player `a_k` quits with probability `q_k` independently of
everything, and every other player continues surely.  No structure is
assumed: any owner sequence, any hazards, finite or infinite, atoms of
any size, periodic or not.  This is exactly the class of deterministic
behavioral profiles that assign at most one player a positive quitting
hazard at each live date (before absorption the public history of a
quitting game is determined by the date, so no generality is lost by
ignoring history dependence).

The **terminal exploitability** `E(σ)` is the least `ε ≥ 0` such that
`σ` is a terminal `ε`-Nash profile against every unilateral behavioral
deviation: `E(σ) = max_i [ sup_τ U_i(σ_{−i}, τ) − U_i(σ) ]`, the
supremum over complete behavioral strategies `τ` of player `i`, with `U`
the expected terminal (absorption) payoff.  Let
`ε*(SV) := inf_σ E(σ)`.

**Theorem.**

1. (Explicit uniform floor.)  Every solo-hazard schedule satisfies

   `E(σ) ≥ 464/14141 = 0.0328122…`   (`14141 = 79·179`).

   In particular `ε*(SV) ≥ 464/14141 > 0`, and no solo-hazard
   schedule is an exact terminal equilibrium — any owner sequence,
   any hazards, finite or infinite, periodic or aperiodic, atoms of
   any size.

   (1b, the previously exported constant, kept as the formalized
   route: `14 E(σ)² + 67 E(σ) ≥ 1`, hence
   `E(σ) ≥ (√4545 − 67)/28 = 0.0148797… > 1/68` — per the
   repository-disposition note this quadratic form is now proved in
   Lean; part 1 strengthens it by the factor `2.23`.)

2. (Upper certificate.)  `ε*(SV) < 26/505 = 0.05148…`, witnessed by an
   explicit rational schedule (preload, 48-block transient, infinite
   period-8 core) with exact exploitability `0.051478590953984…`,
   verified in exact rational arithmetic on three independent code
   paths by the two authors.

Hence `ε*(SV) ∈ [ 464/14141 , 26/505 ) ⊂ [0.03281, 0.05149)`
self-contained in this packet (the lower endpoint is weak — nothing
here excludes attainment; the upper endpoint is strict); the sharper
reviewed conference bracket is `[464/14141, 889/20000)`, see "What
remains open".  Single-owner-per-date scheduling on this table is
separated from equilibrium by an explicit positive gap at every
accuracy below `0.0328`, while at accuracies `0.0515` and above
solo-hazard terminal `ε`-Nash profiles do exist.

## Conjecture-facing change

- Named live obligation narrowed:
  `../questions/PREDICTABLE_SINGLE_OWNER_DERANDOMIZATION.md` asks
  whether a deterministic causal single-owner branch schedule with
  shrinking hazards can drive ordinary terminal exploitability to zero
  on a source-matched packet.  For this actual residual-hard packet —
  the table sits in the full-normal residual-hard branch by the checked
  `periodTwo_residualHardClass`
  (`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`)
  — the answer is NEGATIVE in the strongest schedule-independent and
  now EXPLICIT form: every schedule in the at-most-one-owner class, at
  every mesh, retains a unilateral behavioral deviation gain above
  `464/14141 = 0.0328…` (previously exported, and since checked in
  Lean, at `1/68`).  The deviation necessarily depends on the schedule
  (see Boundary tests), which is permitted by the question's negative
  form.
- Architectural constraint on the two open chronological producer
  arrows (`docs/FRONTIER.md`): a universal ordinary producer cannot
  route its public building blocks through an at-most-one-owner row
  language on residual-hard tables; genuinely multi-owner phases (or a
  different endpoint route) are necessary.  The same table's checked
  two-owner period-two uniform equilibrium
  (`boundaryReward_isUniformEquilibriumPayoff`,
  `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryEquilibrium.lean`,
  proved in Lean) shows one level up suffices, so this is a sharp
  architecture separation, uniform in the accuracy.
- The checked exact no-gos on this table (anchored solo-periodic:
  `not_exists_exactAnchoredSoloPeriodic_boundaryReward`,
  `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloPeriodicNoGo.lean`,
  proved in Lean) are shown to be neither exactness artifacts nor
  periodicity artifacts, and acquire the status of special cases of a
  uniform, explicitly quantified semantic obstruction.

What remains open: the exact value of `ε*(SV)`.  This packet's own
certificate gives the upper end `26/505`; sharper exact certificates
have since been produced and verified — the hand-checkable printed
one is `E = 0.04619331568… < 231/5000` (HILBERT Proposition 34,
Section 20.6 of his notebook; triply verified), and the current
record is `E = 0.04444669123… < 889/20000 = 0.04445` (HILBERT
Proposition 36 addendum, 5270 atoms plus an infinite period-8 core,
data in `../notes/CLAUDE_HILBERT__SV_CERT_04445_DATA.md`; verified
on his evaluation-free integer h-scan and BANACH's independent
renewal-formula recheck, Round 11) — so the reviewed conference
bracket is **`ε*(SV) ∈ [464/14141, 889/20000) =
[0.032812, 0.044447)`, upper/lower ratio `1.355`**, with no
distinguished candidate value inside; float evidence (labeled)
places the pinned-regime fluid-control value near `0.04442`, and
HILBERT's organizing conjecture (his 20.8) is that the infimum
equals the fluid value and is unattained.  Also open: the transfer
to all behavioral profiles with small per-date TOTAL hazard
(de-collision, outline status in the notes); and any table beyond
this one.

## Definitions and assumptions

- Probability mode: terminal payoffs of a one-live-state quitting game;
  a nonempty simultaneous quitter set `S` absorbs at row `S`; eternal
  continuation pays `0`.  All randomization is independent per-date
  quitting; no public or private correlation device exists anywhere.
  All series below are absolutely convergent sums of nonnegative or
  bounded terms; the proof of record is fully discrete (no measure
  theory, no compactness).
- Agency: exactly one deviator at a time; the deviator may replace its
  complete behavioral strategy (full history-dependence allowed).
- Stopping/observation: on the prescribed path only the date is public;
  the deviator observes the date.
- Deviation power audit: the supremum of the deviator's terminal payoff
  over all behavioral strategies equals its supremum over deterministic
  quit times together with `Never`
  (`sSup_range_quittingTerminalPayoff_update_eq_pureTime`,
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`,
  proved in Lean).  The proofs price exactly these and nothing else.
- Horizon uniformity is NOT claimed: `E(σ)` is exploitability of the
  terminal payoff functional (the project's downstream endpoint
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  consumes terminal-Nash data; this packet supplies an explicit lower
  bound against one architecture producing such data).

## Source correspondence

- Table: `boundaryReward` and `soloReward_eval`
  (`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`);
  the two-element-row fact is `boundaryReward_pair_eq_one`
  (`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloPeriodicNoGo.lean`)
  and is visible in the sixteen match arms.  The table transcribes the
  Section 3 example of Solan and Vieille, *Quitting games*, Math. OR 26
  (2001), read here through the repository transcription; no paper
  claim is otherwise relied on.
- Prior checked no-go, strictly weaker than the exact-no-go corollary:
  `not_exists_exactAnchoredSoloPeriodic_boundaryReward` assumes
  periodicity, anchoring, and interior hazards; part 1 assumes nothing.
- Positive contrast (proved in Lean):
  `boundaryReward_isUniformEquilibriumPayoff` and the residual-hard
  classification `periodTwo_residualHardClass`,
  `periodTwo_residualHard_fullCore_nonstationary_but_uniform`
  (`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`).
- Novelty: no repository declaration or paper source states a
  quantitative or uniform lower bound for this class; Solan–Vieille
  2001 prove existence results and the stationary analysis, not
  class-uniform exploitability floors.

## Proof

Notation: `p = p(i)` is `i`'s partner, `X(i)` the opposite pair;
`R(k⁻) = Π_{j<k}(1−q_j)`, on-path masses `m_k = R(k⁻) q_k`, class
masses `μ_a = Σ_{a_k=a} m_k`, `T = Σ_k m_k ≤ 1`, pair masses
`μ_A = μ_0+μ_1`, `μ_B = μ_2+μ_3`, slacks `s_i := P_i − 1`, remaining
masses `r_a(k⁻) := Σ_{l≥k, a_l=a} m_l`.

### Lemma R (reduction; used by every route)

For deviator `i`, the deleted masses are
`m'_k = q_k Π_{j<k, a_j≠i}(1−q_j)` and `μ'^{(i)}_a(<t)` their
owner-class prefix sums.  Then:

- prescribed payoff `P_i = μ_i + 4μ_{p(i)}`;
- the deviation value of quitting at date `t` is exactly
  `D_i(t) = 1 + 3μ'^{(i)}_{p(i)}(<t) − μ'^{(i)}_{X(i)}(<t)`, and
  `Never` is dominated by late quitting;
- `E(σ) = max_i [ sup_{t ≤ ∞} V_i(t) − s_i ]` with
  `V_i(t) := 3μ'_p(<t) − μ'_X(<t)`; the empty prefix gives
  `E(σ) ≥ 1 − P_i` (floor deviations).

*Proof.*  On path all absorptions are singletons: `i` collects `1` per
unit of its own solo mass and `4` per unit of its partner's, giving
`P_i`.  A deviator alive at `t` collects `4` per unit of prior partner
deleted mass, `0` per unit of prior cross deleted mass, and quits into
either its solo row or a two-element row containing it — both pay it
exactly `1` — so `D_i(t) = 4μ'_p(<t) + (1 − μ'_p(<t) − μ'_X(<t))`.
`Never` replaces the final `1` by `0` on the residual.  The behavioral
supremum equals the pure-time supremum by the cited checked theorem.  ∎

### Step B (deflated gaps and the budget identity; HILBERT Lemma 21)

Let `ε := E(σ)`, `G_i(k⁻) := Π_{j<k, a_j=i}(1−q_j)`, and define the
**deflated gap** `h_i(k⁻) := G_i(k⁻)(s_i + ε − V_i(k⁻)) ≥ 0`
(nonnegative precisely because `V_i ≤ s_i + ε` everywhere, by the
definition of `ε` via Lemma R).  Because `R = G_i · Π_{j<k,a_j≠i}(1−q_j)`,
the deleted mass of a non-own atom is `m/G_i`, and own atoms cancel in
`V_i`.  The dynamics of `h_i` across atom `k` are therefore exactly:

- owner `p(i)`: `h_i ← h_i − 3m_k`;
- owner in `X(i)`: `h_i ← h_i + m_k`;
- owner `i`: `h_i ← h_i(1−q_k)`, an additive loss of `h_i(k⁻)q_k`.

With friction `F_i := Σ_{a_k=i} h_i(k⁻) q_k ≥ 0`, telescoping and the
master identity `μ_{X(i)} − 3μ_{p(i)} = T − P_i` give, for every player
simultaneously,

`ε = F_i + h_i(∞) + (1 − T)`,

all three terms nonnegative, all series convergent.  Consequences:
`1 − T ≤ ε` and `F_i ≤ ε` for each `i`.  Telescoping from `k` to `∞`
gives the tail representation
`h_i(k⁻) = 3r_{p(i)}(k⁻) − r_{X(i)}(k⁻) + h_i(∞) + F_i(≥k)`, whence
`h_i(k⁻) ≥ [3r_p − r_X]⁺(k⁻)` at every boundary.  Floors: `s_i ≥ −ε`
(Lemma R at `t = 0`) and `Σ_i s_i = 5T − 4`; the pair system inverts
exactly to `μ_i = (3 + 4s_{p(i)} − s_i)/15`.

### Part 1 proof of record: the combined-certificate floor (BANACH Theorem 15.4; reviewed by HILBERT, Round 5 of the BANACH feedback series)

Three exact facts on top of Step B, each one line from it:

- (start)  `h_i(0⁻) = s_i + ε`, so
  `Σ_i h_i(0⁻) = 1 − 5δ + 4ε` with `δ := 1 − T` (from
  `Σ_i s_i = 5T − 4`); and `δ ≤ ε` (Step B).
- (cap)  `3m_k ≤ h_{p(a_k)}(k⁻)` at every atom (the partner
  coordinate falls by `3m_k` and stays nonnegative).
- (part 7)  Summing Step B's tail representation over `i`, with
  `Σ_i(3r_p − r_X) = Σ_a r_a = R − δ`:
  `R(k⁻) − Σ_ih_i(k⁻) = δ − Σ_ih_i(∞) − Σ_{l≥k}φ_l ≤ δ`, where
  `φ_l := h_{a_l}(l⁻)q_l` (so `Σ_{a_l=i}φ_l = F_i`).  At `k = 0`
  this is the exact budget `Σ_lφ_l + Σ_ih_i(∞) = 4(ε − δ)`.

**The certificate.**  With `M₁ := Σh_i²`, `M₂ := h_0h_1 + h_2h_3`,
`M₃ := (h_0+h_1)(h_2+h_3)`, `S := Σh_i`, define on the orthant

`B_c(h) := [2M₁ + 9M₂ + 5M₃]/17`,   `Ψ_c := B_c/S`  (`Ψ_c(0) := 0`).

Since `M₁ + 2M₂ + 2M₃ = S²` identically,
`B_c = [2S² + 5M₂ + M₃]/17`, so `(2/17)S² ≤ B_c ≤ (13/68)S²` on the
orthant (upper: `5M₂ + M₃ ≤ (5/4)S²` by per-pair AM–GM), with the
lower bound an equality exactly on the four axes; and
`0 < ∂_aΨ_c ≤ 7/17` for every `a` (the gradient matrix of `17B_c`
has row entries in `[4, 9]`).

**Certificate lemma (the combined step inequality).**  For every
`h ≥ 0` with `S > 0`, every owner `a`, and every
`m ∈ [0, h_{p(a)}/3]`, with `t := m/S ≤ 1/3` and
`c^{(a)}` the vector with `0` at `a`, `3` at `p(a)`, `−1` at the two
cross players:

`Ψ_c(h) − Ψ_c(h − m c^{(a)} − h_a t e_a) ≤ h_a t`.

*Proof.*  Take `a = 0` (table symmetry).  Multiplying by `17SS'/t`
(`S' := Σh' = S − m − h_a t > 0`; `t = 0` trivial) and expanding the
quadratic form exactly, the condition is equivalent to
`Φ(h, t) ≤ 0` with

`Φ := −(S+h_0)P + S(2S² + 3Sh_0 − h_0² + 4h_0h_1) + tS(15h_0² − S²)`,
`P := 17B_c = 2S² + 5M₂ + M₃`.

`Φ` is linear in `t`, so its endpoints decide.  At `t = 0` the
condition rearranges to
`(S + h_0)(5M₂ + M₃) ≥ S·h_0·(5h_1 + h_2 + h_3)`, which holds by the
exact expansion
`5M₂ + M₃ = h_0(5h_1 + h_2 + h_3) + 5h_2h_3 + h_1(h_2 + h_3)`
(discarded terms nonnegative; `S + h_0 ≥ S`).  At the cap
`t = h_1/(3S)` the substitution collapses exactly to

`Φ = −[ h_0²(h_2+h_3) + S²h_1/3 + (S+h_0)(5h_2h_3 + h_1(h_2+h_3)) ]`,

a sum of nonpositive terms.  (Equality holds exactly on the own-axis
rays `h_1 = h_2 = h_3 = 0`.)  ∎

**Dominance.**  Along the real trajectory, atom `k` (owner `a`,
hazard `q`, mass `m = Rq`, drop `φ_k = h_aq`) moves
`h(k⁺) = h(k⁻) − mc^{(a)} − φ_ke_a` (Step B).  If `R ≤ S`
(`q ≥ m/S`): split at the tied point `u := h − mc − h_a(m/S)e_a`
(in the orthant by the cap and `t ≤ 1/3`); the certificate lemma
pays the first part, and the remaining pure-drop segment from `u` to
`h(k⁺)` costs at most `(7/17)h_a(q − m/S)` by the gradient bound;
total `≤ h_aq = φ_k`.  If `R > S`: the real successor exceeds the
tied one in coordinate `a` only, so monotonicity gives decrement
`≤ h_a m/S = φ_k·R/S`.  Hence always

`Ψ_c(h(k⁻)) − Ψ_c(h(k⁺)) ≤ φ_k · max(1, R(k⁻)/Σh(k⁻))`.

**Assembly (part 1).**  `ε > 0` (else part 7 at `k = 0` and the
certificate telescoped along the exhausting trajectory give
`2/17 ≤ 0`; alternatively either qualitative route below).  Let
`k*` be the largest atom index with `Σ_{l≥k}φ_l ≥ δ`; by part 7,
`R ≤ Σh` for every `k ≤ k*`, and `Σ_{k>k*}φ_k < δ` (at `δ = 0`
every atom is of the first kind).  Set `κ := 17/58` and stop at the
first boundary `K` with `Σh(K⁻) < κε`.  For `k < K` the dominance
bound gives decrement `≤ φ_k` (`k ≤ k*`) or
`≤ φ_k(1 + δ/(κε))` (`k > k*`, using `R ≤ Σh + δ` and
`Σh(k⁻) ≥ κε`), so the telescoped total is
`≤ Σφ + δ²/(κε)`.  With the start floor
`Ψ_c(h(0⁻)) ≥ (2/17)(1 − 5δ + 4ε)`, the stop cap
`Ψ_c(h(K⁻)) ≤ (13/68)κε`, and the budget `Σφ ≤ 4(ε − δ)`:

`(2/17)(1 − 5δ + 4ε) ≤ (13/68)κε + 4(ε − δ) + δ²/(κε)`.

Using `δ² ≤ δε`, the `δ`-coefficient `−4 + 1/κ + 10/17` vanishes
exactly at `κ = 17/58`, leaving
`2/17 ≤ [4 − 8/17 + (13/68)(17/58)]ε = (14141/3944)ε`, i.e.
`ε ≥ 464/14141`.  If no stop occurs, `σ_∞ := Σh(∞) ≥ κε` and the
EXACT budget `Σφ = 4(ε−δ) − σ_∞` replaces the endgame term by
`(13/68 − 1)σ_∞ < 0`, a strictly stronger bound.  ∎

The whole proof of part 1 is: Lemma R, Step B, the three one-line
facts, one two-endpoint polynomial verification, and elementary
bookkeeping — fully discrete, all constants rational.  Original
statement and expanded proof: Sections 15.1–15.3 of
`../notes/CLAUDE_BANACH__SOLO_HAZARD_EXPLOITABILITY_FLOOR.md`;
adversarial review (hand re-derivation of every step, independent
24084-check exact battery, independent assembly implementation):
`../feedback/CLAUDE_BANACH__SOLO_HAZARD_EXPLOITABILITY_FLOOR__BY_CLAUDE_HILBERT__ROUND_5.md`.

### Part 1b: the formalized quadratic floor (HILBERT Theorem 24; reviewed by BANACH, Round 5 of the HILBERT feedback series)

**Lemma 24.1 (atomic friction floor).**  For every player `i`,
`F_i ≥ S_i := Σ_{k: a_k=i} ν_k m_k` with
`ν_k := 3r_{p(i)}(k⁻) − r_{X(i)}(k⁻)`.

*Proof.*  At an own atom, `q_k = m_k/R(k⁻) ≥ m_k`.  If `ν_k ≥ 0`, the
tail representation gives `h_i(k⁻)q_k ≥ ν_k q_k ≥ ν_k m_k`; if
`ν_k < 0`, then `h_i(k⁻)q_k ≥ 0 > ν_k m_k`.  Sum over `i`'s atoms
(absolutely convergent: `|ν| ≤ 3`, `Σm ≤ 1`).  ∎

**Lemma 24.2 (potential identity; exact, path-independent).**

`S_0 + S_1 + S_2 + S_3 = 3μ_0μ_1 + 3μ_2μ_3 − μ_Aμ_B =: Q(μ)`.

*Proof.*  Across atom `k` (owner `i`, mass `m_k`) only `r_i` changes,
by `−m_k`.  For `i ∈ {0,1}`: `Δ_k(r_0r_1) = −m_k r_{p(i)}(k⁻)` and
`Δ_k(r_Ar_B) = −m_k r_B(k⁻)`, so the atom's summand `ν_k m_k` is
exactly `−3Δ_k(r_0r_1) − 3Δ_k(r_2r_3) + Δ_k(r_Ar_B)` (the `B`-pair
term vanishing; symmetrically for `i ∈ {2,3}`).  Telescoping from
initial values `μ` to final values `0` — for `K = ∞` the partial sums
are `Q(μ) − (3r_0r_1 + 3r_2r_3 − r_Ar_B)(K⁻)` and the parenthesis
tends to `0` with `Σ_a r_a(k⁻) = T − Σ_{j<k}m_j → 0` — gives the
display.  ∎

**Lemma 24.3 (mass polygon).**  If `ε ≤ 2/7`, write `σ̄ := 1 − ε`;
then `Q(μ) ≥ φ(ε) := 1/15 − (7/15)ε − (14/15)ε²`.

*Proof.*  Feasibility: `P_i ≥ σ̄` for all `i` (floor deviations) and
`T = μ_A + μ_B ≤ 1`; adding a pair's two floors, `5μ_A ≥ 2σ̄`,
`5μ_B ≥ 2σ̄`.  Given pair sums `(a,b)`, the two floors of pair `A`
confine `μ_1` to `[(σ̄−a)/3, (4a−σ̄)/3]` (nonempty iff `a ≥ (2/5)σ̄`;
both endpoints have nonnegative masses, and `a ≤ σ̄` holds on the
triangle since `a ≤ 1 − (2/5)σ̄ ≤ σ̄` exactly when `ε ≤ 2/7`); the
product `μ_0μ_1` is concave in `μ_1`, so it is minimized at an
endpoint, and BOTH endpoints give `(σ̄−a)(4a−σ̄)/9 ≥ 0`; likewise pair
`B`.  Hence on `𝒯 = {a,b ≥ (2/5)σ̄, a+b ≤ 1}`:

`Q(μ) ≥ q(a,b) := (σ̄−a)(4a−σ̄)/3 + (σ̄−b)(4b−σ̄)/3 − ab`.

The Hessian `[[−8/3, −1], [−1, −8/3]]` is negative definite, so `q` is
concave and minimized at a vertex of `𝒯`.  Values: symmetric vertex
`2σ̄²/25`; the two lopsided vertices `((2/5)σ̄, 1−(2/5)σ̄)` and its
swap give `(7/3)σ̄ − (14/15)σ̄² − 4/3 = φ(ε)`.  The difference
`2σ̄²/25 − φ = (76/75)σ̄² − (7/3)σ̄ + 4/3` has roots `20/19` and
`5/4`, both outside `[5/7, 1]`, and is positive at `σ̄ = 1`, hence the
minimum is `φ(ε)`.  ∎

**Theorem (part 1b).**  If `ε > 2/7` then `67ε > 1` trivially.
Otherwise chain: `4ε ≥ Σ_i F_i ≥ Σ_i S_i = Q(μ) ≥ φ(ε)`, i.e.
`60ε ≥ 1 − 7ε − 14ε²`, i.e. `14ε² + 67ε ≥ 1`, i.e.
`ε ≥ (√4545 − 67)/28`.  In particular `ε = 0` is impossible (exact
no-go), and `ε*(SV) ≥ (√4545−67)/28 > 1/68`.  ∎

The whole part-1b proof is: Lemma R, Step B, Lemmas 24.1–24.3 —
finite/countable telescoping of bounded series, one discrete summation
by parts, and a two-variable concave vertex minimization.  Nothing
else.  Per the repository-disposition note this route is the one
already checked in Lean; part 1 above strengthens the constant by
replacing Lemmas 24.1–24.3 with the combined certificate while
keeping Lemma R and Step B unchanged.

### Independent second proofs of the qualitative statement

Both authors also proved the qualitative statement (`E > 0` for every
schedule; `ε* > 0`) independently, BEFORE the explicit constant, by two
structurally different routes that are preserved here for their
mechanism content (each was independently audited; see the review
links).

**Route A (pair-death; HILBERT Theorem 22).**  At `ε = 0`: `T = 1`,
`F_i = 0` (so every own atom with `q_k > 0` fires at `h_i(k⁻) = 0`),
`h_i(∞) = 0`, `s ≥ 0`, `Σs = 1`, and `μ_i = (3+4s_p−s_i)/15 ≥ 2/15`.
Call pair `B` dead when `h_2 > 0` and `h_3 > 0`: death is absorbing
(cross atoms add `+m` to both; own atoms with `q > 0` are blocked; a
partner atom of positive mass `m` needs the other member's gap
`≥ 3m > 0`, blocked at `0`).  Since `μ_2 ≥ 2/15`, `min(s_2,s_3) = 0`;
relabel (table automorphism) so `s_0 = s_2 = 0`.  Before the first
positive-mass `A`-atom, `h_2 ≡ 0` and positive-mass `3`-atoms are
blocked; such an `A`-atom exists (`μ_A ≥ 4/15`); immediately after it
`h_2 = m > 0` and `h_3 > 0`: pair `B` dead forever, so `μ_3 = 0`,
contradicting `μ_3 ≥ 2/15`.  ∎

**Route B (exposure paths, attainment, quit-at-peak; BANACH Theorems
7.2, 8.3, Corollary 8.4).**  Parametrize schedules as monotone
staircase exposure paths `x ∈ 𝒫` (nondecreasing, `x(0)=0`,
`ℓ¹`-speed `≤ 1` on `[0,4]`); every functional of Lemma R extends
continuously to `𝒫`, which is compact (Arzelà–Ascoli), and
`E(path) = E(schedule)` exactly on staircases (within a block the
prefix functional is linear, so path prefixes add no deviation
options); hence `ε* = min_𝒫 E`, attained.  At a minimizer with
`E = 0`: the Abel bound `∫β dK_i ≤ (sup K_i)β(start)` for
nonincreasing `β ≥ 0`, applied with `β = y_i`, combines with the exact
identities `∫y_i dK_i = 3μ_p − μ_X` and
`Σ_i[∫y_i dK_i − g_i] = 4(1−T)` to force `T = 1`, all four violations
`0`, and each player to move only where its prefix functional sits at
its global supremum (`quit-at-peak`), which equals its slack.  The
support-opening analysis (whichever pair's move support starts second,
its opener faces strictly banked cross relief, contradicting its exact
zero-progress condition; the balanced case contradicts `Σg_i = 1`)
excludes such a minimizer.  Repair note: the originally displayed
inequality `(∗∗)` in the companion compactness route (HILBERT
Theorem 23 Step 1) was found false as written by `CODEX_CEDAR` and
replaced by the stronger `F_i ≥ ∫ [3r_p − r_X]⁺ dμ_i`, re-verified
independently by BANACH; with BANACH's endpoint simplification
(`Σ r*(1) = 0` forces all limit gaps to vanish at the endpoint) the
limit argument closes.  Full details: Sections 7–8 of
`../notes/CLAUDE_BANACH__SOLO_HAZARD_EXPLOITABILITY_FLOOR.md` and
Sections 14–16 of
`../notes/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS.md`.

### Part 3: the upper certificate (HILBERT Proposition 20′; triply verified)

The schedule (all hazards rational with denominator `10⁵`; numerators
listed): preload atoms
`(0, 28821), (2, 6221), (3, 13450), (0, 5214), (3, 58), (1, 22)`;
transient of 48 blocks with owner word `(0,1,2,3)¹²` and numerators
`8945, 5679, 7943, 5958, 9316, 5668, 8093, 5960, 9010, 5687, 7987,
5961, 9253, 5679, 8142, 5961, 8992, 5675, 7954, 6000, 9528, 5677,
8106, 5955, 9269, 5516, 7793, 5993, 9254, 5769, 7882, 6057, 8950,
5740, 7906, 6120, 9363, 5684, 8087, 5821, 8377, 5712, 7785, 6338,
8439, 5949, 8170, 5910`;
infinite periodic core with owner word `(0,1,2,3,0,1,2,3)` and
numerators `8656, 5652, 8459, 5815, 9655, 5690, 8471, 5892`.

Exact exploitability `E = 0.05147859095398441… < 26/505`, per-player
violations `(0.05147501…, 0.05147760…, 0.05147859… (max, player 2),
0.05147833…)`, masses `μ = (0.511280, 0.109311, 0.189704, 0.189704)`,
`T = 1` (the periodic core absorbs almost surely).

*Verification (three independent code paths, named for audit).*
(i) Exact `Fraction` arithmetic in the geometric renewal closed forms
(the infinite tail summed exactly; prefix suprema via the monotone
interpolation `sup_n V(n,j) = max(V(0,j), V∞)`) — HILBERT, recorded in
the verification-discipline entries of Sections 13/19 of
`../notes/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS.md`; (ii) exact
`Fraction` evaluation of the 200-core-repetition truncation through an
independently written block evaluator — HILBERT, same record;
(iii) exact `Fraction` evaluation of the 40- and 60-core truncations
through a third, freshly written evaluator with a rigorous tail
bound — BANACH, recorded in
`../feedback/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS__BY_CLAUDE_BANACH__ROUND_5.md`:
truncation at boundary `N` changes each `P_i` by at most
`4 · (on-path residual survival)` and each prefix supremum by at most
`4 · (deleted-game residual survival)`, both below `10⁻¹²` at
`N = 60` cores, while `26/505 − E = 6.56 · 10⁻⁶`.  ∎

A fully finite backup certificate with the weaker bound
`E = 0.05178431213547… < 259/5000` (BANACH Proposition 3: four preload
atoms and 60 repetitions of an eight-block cycle, 484 blocks total, no
truncation involved) was verified exactly by both authors and is kept
in the notes; formalizers wanting a finite witness first should use it.

## Boundary tests

- Positive side (the floor cannot be coarse): the Part 3 certificate
  is a solo-hazard terminal `0.0515`-Nash profile, so the exact no-go
  does not propagate to accuracies coarser than `26/505`, and any
  correct floor constant is below that.
- Attempted falsifier for naive proof shapes: an explicit twenty-block
  schedule (BANACH Proposition 4, verified exactly by both authors;
  data in `../notes/CLAUDE_BANACH__SOLO_HAZARD_EXPLOITABILITY_FLOOR.md`)
  makes all eight quit-now/quit-late violations of all four players
  `≤ −1/125` while its true exploitability is `≈ 0.4955`: no fixed
  menu of deviation times, and (BANACH Section 9, LP evidence with
  proved structural explanation) no fixed-weight linear aggregation of
  the valid constraint family, can prove any positive floor.  The
  proof of record indeed prices schedule-dependent interior times —
  through the friction terms `h_i(k⁻)q_k`, whose locations depend on
  the schedule.
- Table-specificity (the theorem is not a general solo no-go): the
  three-player Flesch–Thuijsman–Vrieze table (`terminalReward` rows of
  `Literature/FleschThuijsmanAndVrieze1997.lean`) admits an EXACT
  solo-hazard cyclic equilibrium (owners `(1,2,3)` cyclically, hazards
  `1/2`, value `(1,2,1)` — the known FTV equilibrium).  Any attempted
  strengthening to a table-free statement is false.
- Exact anchors: the uniform proportional schedule has exploitability
  exactly `1/12`; the checked Lean no-go
  `not_exists_exactAnchoredSoloPeriodic_boundaryReward` is implied by
  part 1 restricted to its class (consistency, not circularity: the
  proof nowhere uses it).
- Tightness audit (exact arithmetic).  Part 1b's chain on the
  484-block certificate: `4ε = 0.2071 ≥ ΣF_i = 0.2071 ≥ ΣS_i = Q(μ)
  = 0.0404 ≥ φ(ε) = 0.0400` — its budget and polygon steps are tight
  at the near-optimal regime, and its remaining factor sits entirely
  in Lemma 24.1's discard of the `1/R(k⁻)` weight.  Part 1 keeps
  that weight (the certificate lives on the deflated gaps
  themselves), which is exactly where the improvement comes from;
  its remaining factor against the certified upper end `889/20000`
  is `1.355`, and the identified residual losses are the aggregation
  of the four friction budgets and the floor-vs-value gap of the
  certificate (`min_Δ` of the aggregate combined-game value is only
  bracketed in `[2/17, ≈ 0.15]`).  At the start state of the
  near-optimal architecture (the partner-vertex ray
  `h(0⁻) = (0, s_1+ε, 0, 0)`) both the certificate floor `2/17` and
  the budget `Σφ ≈ 4ε` are exactly tight.
- Verification battery (exact `Fraction` arithmetic, three agents
  across sessions): the budget identity and potential identity as
  exact equalities, the friction floor, the polygon bound, and the
  final inequality on the 484-block certificate, on structured edge
  cases (empty; single sure atom; sure-quit atoms with post-atom
  blocks; uniform proportional; pair-only; one-player; tiny;
  near-sure), and on 3400+ random rational schedules (3000 HILBERT
  session 4, 400 fresh BANACH Round 5); the polygon minimum confirmed
  by independent minimization at six accuracies plus 20000-point exact
  polytope sampling per accuracy.  Zero violations.
- Verification battery for part 1 (exact `Fraction` arithmetic, both
  authors, independent implementations): the combined step inequality
  at all 455 states of the denominator-12 simplex grid with twelve
  moves each plus 4000 random rational states (BANACH) and 24084
  fresh-code checks including vertices, edges, and near-degenerate
  states (HILBERT); the two endpoint collapses and the `Φ`-reduction
  as exact polynomial identities at 2000+ random rational points per
  identity, per implementation; the full assembly chain
  (h-trajectory, caps, part 7, exact budget, `k*` split, per-atom
  decrement bounds, telescoping, final floor) on 360 random
  schedules, edge cases with sure and post-sure-quit atoms, the
  484-block certificate, truncations of the Proposition 34 schedule
  (BANACH), and a 533-atom truncation of the Proposition 30
  certificate (HILBERT).  Zero violations.

## Adapter and consumer

- Input adapter (existing checked Lean): the table `boundaryReward`
  with its simp facts; the class placement `periodTwo_residualHardClass`.
  The solo-hazard class is defined directly on behavioral profiles of
  the project semantics — the adapter is the identity on the
  deterministic at-most-one-owner-per-date class (class audit in the
  Exact statement).
- Deviation audit (existing checked Lean): the pure-time extremality
  theorem, converting the packet's pure-time computations into
  statements about all behavioral deviations.
- Output consumers: (i) the negative side of
  `../questions/PREDICTABLE_SINGLE_OWNER_DERANDOMIZATION.md` for this
  table, now with an explicit constant; (ii) the architecture ladder on
  the flagship residual-hard table: any future universal producer must
  emit genuinely multi-owner rows (or use a different endpoint route),
  since its single-owner fragment cannot approximate this table's
  equilibrium; (iii) the checked exact no-go
  `not_exists_exactAnchoredSoloPeriodic_boundaryReward` becomes a
  special case of a uniform, explicit semantic obstruction.
- New ordinary mathematics is everything from Lemma R onward.

## Lean handoff

Suggested order (narrowest first; do not encode the conclusion as a
structure field):

1. Define `SoloHazardSchedule` (owners `ℕ → Fin 4`, hazards
   `ℕ → unitInterval`, explicit length or cofinite-zero convention),
   its on-path masses, prescriptions, deleted prefix potentials, and
   terminal exploitability against pure times plus `Never`; connect to
   behavioral deviations by
   `sSup_range_quittingTerminalPayoff_update_eq_pureTime`.
2. Lemma R for `boundaryReward` on top of that: finite row-fact case
   analysis (`soloReward_eval`, `boundaryReward_pair_eq_one`).
3. Step B: the h-dynamics and budget identity are countable
   telescoping of bounded nonnegative series — `tsum` algebra; the
   master identity and the mass–slack inversion are `ring` facts.
4. The part-1b route (Lemmas 24.1–24.3 and the chain): per the
   repository-disposition note this is DONE — Lean proves
   `1 ≤ 14 * E σ ^ 2 + 67 * E σ` and `1/68 < E σ` for the class.
   (The packet has not inspected the declarations; the disposition
   note is the source for this status.)
5. **The part-1 strengthening (the new formalization payload;
   everything already built for part 1b is reused).**  On top of
   steps 1–3: (i) define `B_c` and `Ψ_c` and prove the three
   orthant bounds (`(2/17)S² ≤ B_c ≤ (13/68)S²`, gradient bounds) —
   `ring`/`nlinarith` facts from the identity
   `M₁ + 2M₂ + 2M₃ = S²`; (ii) the certificate lemma: after clearing
   denominators it is TWO explicit polynomial inequalities on the
   orthant (the `t = 0` rearrangement and the capped-`t` collapse),
   each a sum-of-nonnegative-terms identity — `ring_nf` plus
   `positivity`-shaped goals, no analysis; (iii) dominance and the
   `k*` assembly: finite index manipulation and one countable
   telescoping, same `tsum` toolkit as Step B.  Statement targets:
   `∀ σ : SoloHazardSchedule, 464/14141 ≤ E σ`, and the bracket
   corollary `ε* ∈ Set.Ico (464/14141) (26/505)`-shaped statements
   as desired.  All constants rational; no square roots anywhere in
   part 1.
6. Useful finite tests: the `1/12` uniform anchor; the 484-block
   finite certificate as an exact witness that any floor constant is
   `< 259/5000`; the FTV solo equilibrium as a guard against
   over-generalized statements.
7. The compactness routes (A/B) need Arzelà–Ascoli and a.e.
   differentiability machinery and are NOT the recommended
   formalization path; they are preserved for mechanism content only.

## Scope and nonclaims

- The packet's own claims are `M`-level evidence, not checked in
  Lean by the authors; the part-1b constant is reported checked in
  Lean by the repository-disposition note (the packet does not
  itself inspect those declarations).
- One table, one strategy class (at most one positive hazard per live
  date).  It does not refute the finite quitting uniform-equilibrium
  conjecture — the same table has a checked uniform-equilibrium payoff
  one architecture level up — and proves nothing about general tables,
  multi-owner phases, or correlated devices.
- No bound on behavioral profiles with several small positive hazards
  per date; the de-collision transfer is an outline in the notes and
  NOT claimed here.
- The exact value of `ε*(SV)` is open; the reviewed window is
  `[464/14141, 889/20000)` and the upper-certificate descent is
  still live (float evidence `≈ 0.04442` and falling; no candidate
  value is distinguished, and the leading conjecture — that the
  pinned value equals the fluid-control value and is unattained —
  is HILBERT's 20.8, not a claim of this packet).  The withdrawn
  `158/3125` upper claim (HILBERT Proposition 20) is excluded: its
  printed data failed an exact recheck
  (`...__BY_CLAUDE_BANACH__ROUND_3.md`); Proposition 20′ above is
  its verified replacement.  EXCLUDED from this packet's accepted
  claims (superseded intermediates never separately reviewed, or
  single-author): BANACH's Theorems 13.1 (`1/787`) and 14.6
  (`4/165`), both superseded by part 1; and BANACH's parametric
  Theorems 15.5–15.6 (explicit floors for the whole `SV(β)` family,
  `β > 3` — single-author as of this update; a future packet
  candidate once reviewed).
- No claim that the two-owner architecture is universally sufficient.
