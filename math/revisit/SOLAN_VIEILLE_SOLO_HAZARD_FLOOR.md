# Solan–Vieille solo-hazard exploitability floor

The strategically important universal lower theorem is proved in Lean for
every finite or infinite deterministic at-most-one-owner calendar, including
`1 ≤ 14 * E^2 + 67 * E` and `1 / 68 < E`. The packet's precise upper
certificate is independently reproducible but has no compact kernel-checked
evaluator, and its exact numerical value is not currently important to the
conjecture boundary. The packet is therefore retained here rather than keeping
an unnecessary numerical formalization obligation in `exports/`.

Authors: `CLAUDE_HILBERT` and `CLAUDE_BANACH` (independent concurrent
proofs of the qualitative theorem; explicit floor by `CLAUDE_HILBERT`,
reviewed by `CLAUDE_BANACH`; one repair estimate due to reviewer
`CODEX_CEDAR`; merged packet assembled by `CLAUDE_BANACH` from the two
session-4 packets per the conference owner's directive)
Independent reviews:
[CEDAR audit of both qualitative routes](../feedback/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS__BY_CODEX_CEDAR__ROUND_2.md)
(found and repaired one displayed inequality, incorporated below),
[BANACH audit of the HILBERT route](../feedback/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS__BY_CLAUDE_BANACH__ROUND_4.md)
(contributes the endpoint simplification used in Route B below),
[BANACH audit of Theorem 24 and exact recheck of the upper certificate](../feedback/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS__BY_CLAUDE_BANACH__ROUND_5.md)
(the explicit floor's review; fresh-code exact verification battery),
[HILBERT audit of the BANACH route](../feedback/CLAUDE_BANACH__SOLO_HAZARD_EXPLOITABILITY_FLOOR__BY_CLAUDE_HILBERT__ROUND_2.md),
[HILBERT exact recheck of the BANACH certificates](../feedback/CLAUDE_BANACH__SOLO_HAZARD_EXPLOITABILITY_FLOOR__BY_CLAUDE_HILBERT.md),
[BANACH cross-verification and data audit](../feedback/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS__BY_CLAUDE_BANACH__ROUND_2.md)
(see also `...__ROUND_3.md`, which caught and removed a faulty numerical
side-certificate that this packet does not use).

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

   `14 E(σ)² + 67 E(σ) ≥ 1`,

   hence `E(σ) ≥ (√4545 − 67)/28 = 0.0148797… > 1/68`.  In particular
   `ε*(SV) > 1/68 > 0`, and no solo-hazard schedule is an exact
   terminal equilibrium — any owner sequence, any hazards, finite or
   infinite, periodic or aperiodic, atoms of any size.

2. (Upper certificate.)  `ε*(SV) < 26/505 = 0.05148…`, witnessed by an
   explicit rational schedule (preload, 48-block transient, infinite
   period-8 core) with exact exploitability `0.051478590953984…`,
   verified in exact rational arithmetic on three independent code
   paths by the two authors.

Hence `ε*(SV) ∈ [ (√4545−67)/28 , 26/505 ) ⊂ [0.01487, 0.05149)`
(the lower endpoint is weak — nothing here excludes attainment; the
upper endpoint is strict): single-owner-per-date scheduling on this
table is separated from equilibrium by an explicit positive gap at
every accuracy below `0.0148`, while at accuracies `0.0515` and above
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
  `1/68`.  The deviation necessarily depends on the schedule (see
  Boundary tests), which is permitted by the question's negative form.
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
have since been produced and verified — currently
`E = 0.04619331568… < 231/5000 = 0.0462` (HILBERT Proposition 34,
Section 20.6 of his notebook, a 142-atom transient plus a near-fluid
periodic tail), verified on three independent code paths (his renewal
evaluator; his evaluation-free Proposition 32 scan; BANACH's
independent Proposition 1 recheck, Round 8) — so the conference
bracket is `ε*(SV) ∈ [(√4545−67)/28, 231/5000)` with no distinguished
candidate value inside and the certificate descent still live at
`≈ 0.0462`; the packet's accepted claims remain as stated.  Also open: the transfer to all behavioral profiles
with small per-date TOTAL hazard (de-collision, outline status in the
notes); and any table beyond this one.

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

### Part 1–2 proof of record: the explicit floor (HILBERT Theorem 24; reviewed by BANACH, Round 5)

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

**Theorem (parts 1–2).**  If `ε > 2/7` then `67ε > 1` trivially.
Otherwise chain: `4ε ≥ Σ_i F_i ≥ Σ_i S_i = Q(μ) ≥ φ(ε)`, i.e.
`60ε ≥ 1 − 7ε − 14ε²`, i.e. `14ε² + 67ε ≥ 1`, i.e.
`ε ≥ (√4545 − 67)/28`.  In particular `ε = 0` is impossible (exact
no-go), and `ε*(SV) ≥ (√4545−67)/28 > 1/68`.  ∎

The whole proof of record is: Lemma R, Step B, Lemmas 24.1–24.3 —
finite/countable telescoping of bounded series, one discrete summation
by parts, and a two-variable concave vertex minimization.  Nothing
else.

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
- Tightness audit of the proof of record (exact arithmetic): on the
  484-block certificate, `4ε = 0.2071 ≥ ΣF_i = 0.2071 ≥ ΣS_i = Q(μ) =
  0.0404 ≥ φ(ε) = 0.0400` — the budget and polygon steps are
  essentially tight at the near-optimal regime; the constant's
  remaining factor (`≈ 3.1` against the certified upper end
  `231/5000`, and shrinking as upper certificates improve) sits
  entirely in Lemma 24.1's discard of the `1/R(k⁻)` weight (the
  lopsided polygon vertex has exactly the three-floors-sacrificed mass
  structure of the numerical optima, so the polygon step is not loose
  accounting).
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
4. The proof of record (Lemmas 24.1–24.3 and the chain): fully
   discrete; the polygon lemma is a two-variable concave vertex
   minimization over an explicit triangle (`nlinarith`-shaped goals).
   Statement targets:
   `∀ σ : SoloHazardSchedule, 1 ≤ 14 * E σ ^ 2 + 67 * E σ` and the
   corollaries `¬ IsExactTerminalNash boundaryReward σ` and
   `(√4545 − 67)/28 ≤ ε*` (or the rational weakening `1/68 < ε*` to
   avoid the square root).
5. Useful finite tests: the `1/12` uniform anchor; the 484-block
   finite certificate as an exact witness that any floor constant is
   `< 259/5000`; the FTV solo equilibrium as a guard against
   over-generalized statements.
6. The compactness routes (A/B) need Arzelà–Ascoli and a.e.
   differentiability machinery and are NOT the recommended
   formalization path; they are preserved for mechanism content only.

## Scope and nonclaims

- Nothing here is checked in Lean; the packet is `M`-level evidence.
- One table, one strategy class (at most one positive hazard per live
  date).  It does not refute the finite quitting uniform-equilibrium
  conjecture — the same table has a checked uniform-equilibrium payoff
  one architecture level up — and proves nothing about general tables,
  multi-owner phases, or correlated devices.
- No bound on behavioral profiles with several small positive hazards
  per date; the de-collision transfer is an outline in the notes and
  NOT claimed here.
- The exact value of `ε*(SV)` is open; the certified window is
  `[(√4545−67)/28, 231/5000)` and the upper-certificate descent is
  still live (float evidence `≈ 0.0462` and falling; no candidate
  value is distinguished).  The withdrawn `158/3125` upper claim
  (HILBERT Proposition 20)
  is excluded: its printed data failed an exact recheck
  (`...__BY_CLAUDE_BANACH__ROUND_3.md`); Proposition 20′ above is its
  verified replacement.  Two stronger lower-bound claims exist in the
  notes and are EXCLUDED from this packet's accepted claims because
  they are single-author and not yet independently reviewed: BANACH's
  Theorem 13.1 (`ε* ≥ 1/787`, an independent calibration certificate,
  now superseded) and BANACH's Theorem 14.6
  (`ε* ≥ 4/165 = 0.0242…`, session 5, via the gap-simplex certificate
  `B*` and the h-lift — Section 14 of
  `../notes/CLAUDE_BANACH__SOLO_HAZARD_EXPLOITABILITY_FLOOR.md`).  If
  Theorem 14.6 passes adversarial review, this packet's Part 1
  constant should be upgraded to `4/165` (the proof of record's
  structure is unchanged: the budget identity feeds a stronger
  certificate).
- No claim that the two-owner architecture is universally sufficient.
