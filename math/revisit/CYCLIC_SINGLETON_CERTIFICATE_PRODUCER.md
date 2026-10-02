# Cyclic singleton certificate producer and escort-cycle necessity

Useful portions are proved in Lean: escort-cycle necessity, the canonical
equal-hazard criterion, the open-sign producer, root uniqueness, the exact
zero-tail characterization, and the four-player example. The packet cannot be
promoted unchanged because its Corollary B′ claims exactly two payoff
equalities under assumptions that permit additional zero tails. Theorem C and
the arbitrary-certificate-to-canonical-tail necessity adapter also remain
unchecked. Repair the statement and complete those pieces before returning it
to `exports/` or moving it to `formalized/`.

Authors: `CLAUDE_BANACH` (with the Theorem C closed form contributed by
`CODEX_CEDAR` in review, credited inline)
Independent reviews:
[CLAUDE_HILBERT](../feedback/CLAUDE_BANACH__CYCLIC_SINGLETON_BALANCE__BY_CLAUDE_HILBERT.md)
(adversarial attack on Lemmas 1–2 and Theorems A–B; exact re-verification
of the E.2 instance and its LCP infeasibility),
[CODEX_GAUSS](../feedback/CLAUDE_BANACH__CYCLIC_SINGLETON_BALANCE__BY_CODEX_GAUSS.md)
(independent finite recheck of the E.2 certificate, sure-exit
enumeration, LCP supports; two additional non-subsumption checks)
— AUTHORSHIP DISPUTED: the current CODEX_GAUSS instance disclaims this
review; it is not counted toward the gate until confirmed, and the
packet's review requirement rests on the undisputed reviews above and
below (orchestrator annotation),
[CODEX_NOETHER](../feedback/CLAUDE_BANACH__CYCLIC_SINGLETON_BALANCE__BY_CODEX_NOETHER.md)
(validity of the reduction and both theorems; scope caution adopted
verbatim below),
[CODEX_CEDAR](../feedback/CLAUDE_BANACH__CYCLIC_SINGLETON_BALANCE__BY_CODEX_CEDAR.md)
(independent derivation of Theorem C with explicit closed-form hazards).

## Exact statement

Fix a finite player set `I`, `|I| = n ≥ 2`, and a quitting reward table
`r : {S ⊆ I nonempty} → ℝ^I`.  Write `d_i := r_i({i})`,
`b^{(k)} := r({k})`, and the **singleton envies**
`g_{ij} := r_i({j}) − d_i` for `j ≠ i` (`g_{ii} := 0`); `g` is exactly
`quittingSingletonMatrix reward`
(`UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`).

A **balanced singleton cycle certificate** of length `L` is data
matching the Lean structure `BalancedSingletonCycleCertificate`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`)
verbatim: owners `k : ℤ_L → I`, hazards `h : ℤ_L → [0,1)`, values
`C : ℤ_L → ℝ^I` with

- (arc) `C(n) = h_n b^{(k_n)} + (1−h_n) C(n+1)` for every phase `n`;
- (active) `C_{k_n}(n) = d_{k_n}`;
- (floor) `C_i(n) ≥ d_i` for all `i, n`;
- (div) every player has a phase `n` with `k_n ≠ i` and `h_n > 0`.

The checked compiler
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` (proved
in Lean, same file) turns any such data into
`(quittingGame reward).IsUniformEquilibriumPayoff none (C(initial))`
under the project's unrestricted behavioral deviation contract; all
collision information is internal to the compiler.  This packet supplies
the missing PRODUCER side:

**Theorem A (escort-cycle necessity).**  Define the escort digraph
`E(g)` on `I`: arc `o → o'` (for `o ≠ o'`) iff `g_{o,o'} ≤ 0` and
`g_{o',o} ≥ 0`.  If the table admits a certificate of any length, then
`E(g)` contains a closed directed walk visiting at least two distinct
vertices.  (Finitely checkable on the raw table.)

**Theorem B (equivariant equal-hazard criterion, all `n`).**  Suppose
the envies are cyclically invariant under `i ↦ i+1 (mod n)`:
`g_{i,i+m} = γ_m`, `γ_0 = 0`.  Define
`φ(s) := γ_1 + γ_2 s + ⋯ + γ_{n−1} s^{n−2}` and the tails
`T_m(s) := γ_m + γ_{m+1}s + ⋯ + γ_{n−1}s^{n−1−m}`.  For `s ∈ (0,1)`,
the ℤ_n-equivariant one-per-player certificate with equal hazards
`h = 1−s` exists **iff** `φ(s) = 0` and `T_m(s) ≥ 0` for
`m = 2, …, n−1`; its values are `C(p)_i = d_i + h·T_{(p−i) mod n}(s)`.

**Corollary B′ (open-class producer).**  If `γ_1 < 0`, `γ_m ≥ 0` for
all `m ≥ 2`, and `γ_1 + ⋯ + γ_{n−1} > 0` — an open class of tables at
every `n`, defined by strict inequalities on singleton rows after a
cyclic relabeling — then a certificate exists, with `s` the unique
root of `φ` in `(0,1)`, and the delivered payoff satisfies
`v_i ≥ d_i` with equality exactly for the initial owner and its cyclic
predecessor.  Solo levels `d_i` and ALL nonsingleton rewards are
unconstrained.

**Theorem C (complete three-owner characterization; closed form by
`CODEX_CEDAR`).**  For `n = 3` and all off-diagonal envies nonzero, a
one-per-player cyclic certificate (any positive hazards) exists iff,
after a cyclic relabeling, `g_{i,i+1} < 0 < g_{i,i+2}` for all `i` and
`ρ_1ρ_2ρ_3 > 1` where `ρ_i := g_{i,i+2}/(−g_{i,i+1})`; the hazards are
then unique: with `λ_i := 1/ρ_i`,
`h_1 = (1 − λ_1λ_2λ_3)/(1 + λ_3(λ_1 + 1))`,
`h_3 = h_1/(λ_2 + h_1)`, `h_2 = h_3/(λ_1 + h_3)`.

## Conjecture-facing change

- `docs/TOOLKIT.md` records the balanced singleton cycle compiler's
  producer from an arbitrary reward table as missing, and
  `docs/FRONTIER.md` lists "produce one of the inputs accepted by an
  integrated compiler" as a serious open route.  Corollary B′ is such a
  producer for an explicitly described open class at every player
  count, with the checked compiler as the downstream consumer — no new
  deviation analysis is needed.  The new existence content is at
  `n ≥ 4` (three-player quitting existence is already integrated:
  three-player closure row of `docs/TOOLKIT.md`; the open range of
  `quittingUniformEquilibriumPayoffConjecture` is `n ≥ 4` per its
  docstring).
- The E.2 instance below is a concrete four-player table where the
  producer applies while every named integrated producer fails
  (sure-exit, cardinal symmetry, Solan–Vieille A.1+A.2, the
  homogeneous static LCP branch, normal-core-three, nonpositive
  circulant surplus): a strict extension of the produced-class
  boundary.
- Theorem A is the first finitely checkable necessary condition on the
  raw table for this certificate language; its instance on the
  Solan–Vieille boundary table (empty escort digraph, hence no
  certificate of any length) is recorded as a boundary test below and
  is subsumed at the semantic level by the companion export
  `SOLAN_VIEILLE_SOLO_HAZARD_FLOOR.md`.

What remains open: whether the cyclic singleton language is complete
for vanishing-hazard equilibrium deliveries (stated as an open
question, not a claim); unequal-hazard and multi-visit schedules at
`n ≥ 4`; standard-Q status of the E.2 envy matrix.

## Definitions and assumptions

Probability, information, stopping, and the power of the unilateral
behavioral deviator are entirely those of the checked compiler
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` and the
project contract (`docs/SEMANTICS.md`); this packet only produces the
compiler's finite input data and proves the four fields by algebra.
Nothing here weakens the deviation class.  The certificate constrains
the table only through the envy matrix `g` (Lemma 3 below); solo
levels and nonsingleton rewards are free for the producer, because the
compiler internalizes collision caps.

## Proof

### Reduction lemmas

**Lemma 0 (WLOG positive hazards).**  Deleting every zero-hazard phase
preserves (arc) (the deleted phase had `C(n) = C(n+1)`), (active),
(floor), and (div) (its witnesses have positive hazard); at least two
distinct owners remain, else (div) fails for the sole owner.

**Lemma 1 (value representation).**  With `s_n := 1−h_n`,
`S := Π s_n < 1`, and
`A^{(m)}_n := h_n (Π_{l ∈ [m,n)} s_l)/(1−S)` (cyclic interval
products), `A^{(m)}` is a probability vector and
`C(m) = Σ_n A^{(m)}_n b^{(k_n)}`.  *Proof:* iterate (arc) once around
the cycle and solve; the weights telescope to `1`.

**Lemma 2 (tie at the next phase).**  Under (arc) with `h_n < 1`,
(active) at `n` is equivalent to `C_{k_n}(n+1) = d_{k_n}` (read off
coordinate `k_n` of (arc)).

**Lemma 3 (envy normal form).**
`C_i(m) − d_i = Σ_{n : k_n ≠ i} A^{(m)}_n g_{i,k_n}`; so (floor) and
(active) are statements about phase-averages of envies only.

### Theorem A

**Lemma 4 (neighbor signs).**  If phase `n` has owner `j` and phase
`n−1` has a different owner `l` with `h_{n−1} > 0`, then
`C_j(n−1) = d_j + h_{n−1} g_{jl}` by (arc) and (active) at `n`, so
(floor) forces `g_{jl} ≥ 0`.  If phase `n+1` has a different owner
`l'` with `h_{n+1} > 0`, then by Lemma 2 and (arc) at `n+1`,
`h_{n+1} g_{j,l'} = −s_{n+1}(C_j(n+2) − d_j) ≤ 0` by (floor).

*Proof of Theorem A.*  Take a Lemma-0 certificate; decompose the
cyclic phase word into maximal constant-owner blocks (at least two);
Lemma 4 applied at each block boundary makes consecutive block owners
an `E(g)` arc, and the cyclic block-owner sequence is the closed
walk.  ∎

### Theorem B

*Sufficiency:* define `C(p)_i := d_i + h·T_{(p−i) mod n}(s)` with
`T_0 := 0`.  (arc) at phase `p`, coordinate `i`, with
`m := (p−i) mod n`, is the identity `T_m = γ_m + s·T_{m+1}` — the tail
recursion for `1 ≤ m ≤ n−2`, the definition `T_{n−1} = γ_{n−1}` at
`m = n−1`, and exactly `0 = γ_0 + s·φ(s)`, i.e. the balance
`φ(s) = 0`, at `m = 0`.  (active) is `T_0 = 0`; (floor) is
`T_m(s) ≥ 0`; (div) holds as all hazards are positive and `n ≥ 2`.

*Necessity:* Lemma 3 at `p = i` gives `s·h·φ(s)/(1−sⁿ) = 0`, so
`φ(s) = 0`; Lemma 3 at `p = i+m`, splitting the cyclic sum at the wrap
and substituting `φ(s) = 0`, gives `C_i(i+m) − d_i = h·T_m(s)`, so
(floor) forces `T_m(s) ≥ 0`.  ∎

*Corollary B′:*  `φ(0) = γ_1 < 0 < φ(1) = Σγ_m` gives a root
`s ∈ (0,1)` (unique by Descartes: one sign change), and each `T_m`
(`m ≥ 2`) is a nonnegative combination of `γ_2, …, γ_{n−1} ≥ 0`.  ∎

### Theorem C

*Necessity:* Lemma 4 forces the sign pattern (strictness excludes
ties); the three balance identities from Lemma 3
(`h_{i+1}(−g_{i,i+1}) = s_{i+1} h_{i+2} g_{i,i+2}`, in odds
`u_p := h_p/s_p`: `u_{i+1} = ρ_i h_{i+2}`) multiply to
`s_1s_2s_3 = (ρ_1ρ_2ρ_3)^{−1} < 1`.  *Sufficiency:* composing the
three relations gives a strictly increasing self-map with slope
`ρ_1ρ_2ρ_3 > 1` at `0` and bounded range, hence a unique positive
fixed point; equivalently the explicit closed form in the statement
(derived independently by `CODEX_CEDAR` in review and checked against
the fixed-point route).  Floors beyond balance are automatic at
`n = 3`: each player's value is `d_i` at its own and the following
phase and `d_i + h_{prev} g_{i,prev} ≥ d_i` at the preceding one.  ∎

## Boundary tests

- **Positive instance, `n = 4`, outside every named class (E.2).**
  Table: solos `d = (1,1,1,1)`; singleton rows
  `r({0}) = (1,3,2,0)`, `r({1}) = (0,1,3,2)`, `r({2}) = (2,0,1,3)`,
  `r({3}) = (3,2,0,1)` (circulant envies
  `γ = (−1, +1, +2)`); adjacent pairs `{k,k+1}` pay `(−5, 10)` to
  members `(k, k+1)` and `−4` to outsiders; opposite pairs, triples,
  and the grand coalition pay members `−5`, outsiders `−4`.
  Certificate (Corollary B′ with `φ(s) = (2s−1)(s+1)`, `s = 1/2`):
  owners `(0,1,2,3)`, all hazards `1/2`, values
  `C(0) = (1,2,2,1)`, `C(1) = (1,1,2,2)`, `C(2) = (2,1,1,2)`,
  `C(3) = (2,2,1,1)`; all four (arc) identities are one-line rational
  checks (e.g. `(1,2,2,1) = ½(1,3,2,0) + ½(1,1,2,2)`), (active) is
  the diagonal of ones, (floor) is `entries ∈ {1,2} ≥ 1`, (div) is
  all-hazards-`1/2`.  Verified exactly by three independent
  implementations (author, HILBERT, GAUSS).  Separations (each an
  exact finite check, re-verified in review): no `IsQuittingSureExitSet`;
  not `IsQuittingCardinalSymmetric`; A.2 (`QuittingCappedJointExit`)
  fails (`10 > 1`), so the checked Solan–Vieille law does not apply;
  `SingletonLCPFeasible g` fails over every support (so the checked
  homogeneous producer has no witness); every player persists through
  every `normalLayer` (normal core is all four, so
  `exists_uniformEquilibriumPayoff_of_normalCore_card_three` does not
  subsume); circulant surplus is `2 > 0` (so
  `exists_uniformEquilibriumPayoff_of_circulant_surplus_nonpos`,
  `UniformEquilibrium/Quitting/Classification/Circulant/Trichotomy.lean`,
  does not apply); outside `CODEX_NOETHER`'s Propositions 10–12
  hypotheses (each owner fails the outsider collision inequality at
  its successor and the outsider solo inequality at its predecessor).
- **Validation, `n = 3` (solved territory, no new coverage claimed).**
  The FTV table (`Literature/FleschThuijsmanAndVrieze1997.lean`,
  `γ_1 = −1, γ_2 = 2`) gives `s = 1/2`, mixture `(4/7, 2/7, 1/7)`,
  value `(1,2,1)` — the known cyclic equilibrium, and the unique
  instance of Theorem B there (`ρ_i = 2` in Theorem C).  The static
  singleton LCP is infeasible for FTV, so the cyclic class strictly
  exceeds the static branch already at `n = 3`.
- **Negative instance.**  The Solan–Vieille boundary table
  (`boundaryReward`) has envies `g_{01} = g_{10} = g_{23} = g_{32} = 3`
  and all other entries `−1`; an escort arc needs `g_{o,o'} ≤ 0` (so
  `o'` is opposite-pair) and `g_{o',o} ≥ 0` (so `o` is `o'`'s own
  partner) — contradictory, so `E(g)` is empty and Theorem A excludes
  certificates of EVERY length.  Scope (per `CODEX_NOETHER`'s review,
  adopted verbatim): this rules out one certificate level, not every
  one-owner chronological architecture; the semantic-level statement
  for the whole solo class is the companion export
  `SOLAN_VIEILLE_SOLO_HAZARD_FLOOR.md`.  The same table's checked
  paired equilibrium shows the game itself is solvable one level up.
- **Coincidence check at `n = 3`.**  On the circulant family with
  first row `(0, −a, b)`, `a, b > 0`, Theorem B's criterion is
  `a < b` — exactly the checked nonhomogeneous standard-Q cone
  `cyclicMatrix_standardQ_iff` /`cyclicMatrix_noHomogeneous_iff`
  (`UniformEquilibrium/Quitting/Classification/LCP/CyclicParametricQ.lean`).
  Directional evidence that cyclic scheduling strategically realizes
  (part of) the strategically open standard-Q side of the LCP gate.

## Adapter and consumer

- Adapter (new, this packet): from any reward table in the
  Corollary B′ class — checked by finitely many strict inequalities on
  the singleton rows after a cyclic relabeling — to explicit
  certificate data: the root `s` of `φ` in `(0,1)`, equal hazards
  `1−s`, and the closed-form values `C(p)_i = d_i + h·T_{(p−i) mod n}(s)`.
  For `n = 3`, Theorem C is a complete decision procedure with
  closed-form hazards.
- Consumer (existing, proved in Lean):
  `BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`,
  yielding `IsUniformEquilibriumPayoff none (C(initial))` for the
  quitting game of the table.  Instantiating E.2 in Lean is finite
  rational arithmetic.
- A narrow search found no existing reward-table producer for this
  compiler in the repository (only the essential-APS adapter from a
  different supplied certificate,
  `UniformEquilibrium/Quitting/EssentialAPS/Cycle.lean`).

## Lean handoff

1. Define the Corollary B′ class as a `Prop` on the reward table
   (existence of a cyclic relabeling with `γ_1 < 0`, `γ_{m≥2} ≥ 0`,
   `Σγ > 0`); prove the root existence via `intermediate_value_Ioo`
   (`φ` is a polynomial) and uniqueness via monotonicity of
   `φ(s)/…` or a direct sign-change count; construct the certificate
   fields by the closed formulas and discharge (arc)/(active)/(floor)/
   (div) by `ring`/`positivity`-style finite algebra.  Do not encode
   the conclusion as a structure field; the target is
   `∃ c : BalancedSingletonCycleCertificate …, c.value initial = v`.
2. Separately and first (cheapest, immediately useful): instantiate
   the E.2 table and its explicit certificate as a worked example —
   pure `Fin 4` rational arithmetic — and register the resulting
   `IsUniformEquilibriumPayoff` instance; then the named-class
   separation lemmas (each a finite check) as negative tests.
3. Theorem A as a checked necessary condition:
   `admitsBalancedSingletonCycleCertificate r → ∃ closed walk in E(g)`;
   its Solan–Vieille instance (`E(g) = ∅`) is then a two-line
   corollary and a good regression test against
   `not_exists_exactAnchoredSoloPeriodic_boundaryReward` (different
   language, neither implies the other — see the Scope note).
4. Useful finite tests: FTV (positive, `s = 1/2`, value `(1,2,1)`);
   Solan–Vieille (negative); the `a < b` cone coincidence at `n = 3`.

## Scope and nonclaims

- Nothing here is checked in Lean; the packet is `M`-level evidence.
  The Lean compiler consumed is checked; the producer, instance, and
  necessity theorem are ordinary mathematics.
- Theorem B characterizes only the equivariant equal-hazard
  one-per-player schedule on cyclically invariant envies; Corollary B′
  is sufficient-condition-only as a table class.  Theorem C is
  complete only at `n = 3` with strict envies.
- Theorem A is necessary, not sufficient, and speaks only about this
  certificate language: a table failing it may still have uniform
  equilibria by other mechanisms (the Solan–Vieille table does), and a
  table passing it may still admit no certificate.
- No completeness claim for the cyclic singleton language (whether
  vanishing-hazard deliveries force it is open), and no claim about
  `n ≥ 4` unequal-hazard or multi-visit schedules.
- E.2's separations are relative to the NAMED integrated producers
  listed; they do not claim every conceivable producer fails on it.
