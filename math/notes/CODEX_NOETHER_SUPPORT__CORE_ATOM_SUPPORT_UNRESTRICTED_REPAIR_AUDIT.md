# Core atom counts under unrestricted repair

Identity: CODEX_NOETHER_SUPPORT.

Current status: the supplied unbounded-support theorem passes independent
mathematical review. The complete source, unrestricted deviations, signed
Never correction, and all finite examples were checked. An independent
standard-library exact checker passes. No Lean file or export was changed;
this is an internal supporting result, not an answer to arbitrary Fin4.

## Exact question

Four players independently choose stopping laws on ℕ∪{Never}. Zero is
paid at Never. For the cyclic core C={0,1,2}, with successor modulo three,
let a=(0,1,1) and, for every nonempty coalition S, set

    r_i(S)=1_{i∈S}(1−2·1_{i+1∈S})−a_i,  i∈C,
    r₃(S)=−1_{3∈S and S∩C≠∅}.

This is a complete canonical singleton table s=(1,0,0,0), bounded by M=2.
The terminal shifts −a_i do not apply to Never. Let U be expected terminal
payoff, B the supremum over every unilateral complete law, and
E=max_i(B_i−U_i). Let k_i count the dates at which i's own law has positive
finite mass; Never is excluded from this count.

Question: can a uniform finite bound on even one nonpivot core law's support
be repaired to arbitrarily small E by changing every other player's complete
law without restriction? The answer is no:

    k₁≤N ⇒ E>(1/16)256^(−N),
    k_i≤N ⇒ E>(1/32)256^(−N) for any i∈C.              (1)

All other laws may be infinite, have arbitrarily late atoms, or place mass
at Never. These quantifiers are strictly stronger than a restriction on the
pivot's own repair support. They do not restrict strategies to stationary
play or bounded memory.

## Independent root calculation

For an actual continuation v, the ranges are
v₀∈[−1,1], v₁,v₂∈[−2,0], v₃∈[−1,0]. Let
α_i=∏_{j≠i}(1−q_j), w_i=v_i+a_i. Then w_i∈[−1,1]. Direct conditioning
gives core Quit-minus-Continue

    e_i=1−2q_{i+1}−α_iw_i.                             (2)

At a root the ordinary mixed regret is (1−q_i)e_i when e_i≥0, and
q_i(−e_i) otherwise. For player 3, with c=∏_{i∈C}(1−q_i), its endpoints
are Q₃=−(1−c) and C₃=cv₃.

If some core q_k≥3/4 and every root regret were ≤δ=1/16, the cyclic
predecessor p has e_p≤−1/4, hence q_p≤1/4. The remaining core j then
has e_j≥1/4, hence q_j≥3/4. Now e_k≤−1/4, so its regret is at least
3/16, contradiction. If instead q₃≥3/4, no core hazard can be ≥3/4
by this argument. A core hazard ≤1/4 would force its predecessor to be
≥3/4 using α≤1−q₃. Thus all core hazards exceed 1/4, giving c<27/64.
Therefore C₃−Q₃≥1−2c>5/32 and player 3's regret exceeds 15/128.

Consequently every root with a hazard at least 3/4 has regret >1/16.
This calculation uses an actual continuation in its reward box and ordinary
mixed regret. It requires no supported-action optimality or cap attainment.

## A missing initial atom

If q₁=0, player 0 can Quit immediately for one. Were E≤δ, then
U₀≥1−δ. Let G be the terminal event that 0 quits and 1 does not.
Since r₀ equals one on G and is nonpositive elsewhere, Pr(G)≥1−δ.
On G, player 1 is passive and receives −1; its rewards everywhere else
are nonpositive. Thus U₁≤−1+δ. Its immediate-Quit payoff −2q₂ must be
at most U₁+δ, so q₂≥7/16.

The date-zero event “2 quits and 0 Continues” precludes G and gives
player 0 zero. Hence U₀≤1−q₂(1−q₀), implying q₀≥6/7. The root bound
above gives an allowed one-stage deviation with gain >δ, contradiction.
Thus q₁=0 forces E>1/16, whatever the other complete laws are.

Let P_t be prescribed joint survival to date t. If P_t>0, the conditional
suffix is again a product of complete laws: survival conditions on the
intersection of the four independent events {T_i≥t}. For every coordinate,
copying its prescribed behavior before t and replacing its entire suffix
shows

    P_t d_i(p^t)≤d_i(p), hence P_t E(p^t)≤E(p).         (3)

Taking the supremum is valid even without an optimizing response. This is
an ex ante reach-weighted inequality, not an unweighted subgame claim.

Assume k₁≤N and E≤δ256^(−N). Inductively P_t≥256^(−t), for
0≤t≤N. Equation (3) gives E(p^t)≤δ. Every hazard is then strictly below
3/4, so P_{t+1}>P_t/256. The missing-atom result gives q₁^t>0 at each
of those N+1 reached dates. Positive joint survival implies positive own
survival, so the original law of player 1 has a positive atom at each
date 0,…,N. This contradicts its atom bound and proves the first part
of (1). Shifting a fixed number of atoms far into the calendar cannot
escape the proof, since it forces positive initial consecutive atoms.

## Why the other two core coordinates also work

Let z be joint-Never mass. Modify only player 0's own Never outcomes by
moving that mass to a late finite date T. Originally player 0 is passive
and receives zero whenever another player quits. The contributions from
opponents' finite tails and date-T atoms vanish as T→∞. All-Never
opponents give the deviator its singleton one. Thus the gain tends to z,
and z≤d₀≤E.

Remove the terminal core shifts, keeping Never zero, to obtain the
unshifted cyclic table. For every prescribed or deviated profile π,

    U_i^{unshifted}(π)=U_i^{original}(π)+a_i Pr_π(absorption).

Subtracting prescribed payoff and bounding deviated absorption by one
gives E_unshifted≤E_original+z≤2E_original. This is an inequality
using actual nontermination mass, not an exact strategic equivalence under
terminal translation.

For the unshifted table the missing-initial-atom proof is cyclically
symmetric. If q_i=0, its predecessor h can Quit for one, hence its positive
terminal event has mass at least 1−δ. On that event i does not quit, so
Pr(i quits at absorption)≤δ and U_i≤δ. Immediate Quit by i gives
1−2q_j≤2δ, where j is its successor. Hence q_j≥7/16 and the same
event bound forces q_h≥6/7, contradicting the root lemma.

Thus original E≤1/32 forces a positive initial hazard at every core
coordinate. Apply this statement separately to every reached original
suffix in (3). The original root lemma still supplies survival >1/256.
The preceding induction proves the second part of (1).

## Positive realization and exact finite tests

The stationary profile with all three core hazards 1/2 and player 3 Never
is exact terminal Nash with U=B=(0,−1,−1,0). For a core deviator the
other two cores absorb almost surely; their deleted survival is 4^(−t).
The unshifted expected payoff is zero under every replacement, and the
terminal shift then applies surely. Player 3 obtains its maximum zero by
Never. The same deleted clocks provide uniform finite-horizon convergence.

Truncating the stationary clocks after N≥1 dates gives the exact values

    U=(0,−1+8^(−N),−1+8^(−N),0),
    B=(4^(−N),−1+4^(−N),−1+4^(−N),0),
    E=4^(−N).                                        (4)

The independent finite laws

    T₀: 0↦4/7, Never↦3/7,
    T₁: 0↦1/2, 1↦1/3, Never↦1/6,
    T₂: 0↦1/2, 1↦1/4, 2↦1/4,
    T₃: Never surely

give every nonempty core coalition probability 1/7, exactly the stationary
equilibrium's complete terminal law. But U=(0,−1,−1,0) while
B=(1/24,−1,−11/14,0). Thus complete coalition-law preservation does
not preserve response caps or eliminate the support lower bound.

The manuscript's named checker `check_cyclic_support_barrier.py` was not
found in the available math filenames. I wrote an independent checker,
[CODEX_NOETHER_SUPPORT__CHECK_UNBOUNDED_CORE_SUPPORT.py](../experiments/CODEX_NOETHER_SUPPORT__CHECK_UNBOUNDED_CORE_SUPPORT.py),
using direct product-law enumeration and all pure response dates through
one date after the cutoff, plus Never. It verifies (4) for N=1,…,6, the
seven-coalition law and its caps, and 8704 root/tail endpoint tests computed
from the complete reward table rather than formula (2). It runs with

    python experiments/CODEX_NOETHER_SUPPORT__CHECK_UNBOUNDED_CORE_SUPPORT.py

and performs no file writes. All checks pass. The grid is finite regression
evidence only; (1) rests on the analytic proofs above.

## Source audit and scope

The audited supplied source is
[CANONICAL_FIN4_UNBOUNDED_SUPPORT_UNDER_FULL_REPAIR.md](../gpt/CANONICAL_FIN4_UNBOUNDED_SUPPORT_UNDER_FULL_REPAIR.md).
Exact declaration inspection followed the finite-repair route in
`docs/FRONTIER.md`:

- `range_pivotBehavior_exploitability_eq_range_stoppingLaw` and
  `exists_objective_minimizer_eq_behavioral_infimum`
  (`UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`):
  the inner optimization is over every behavioral pivot strategy.
- `smallPivotRepairValue_iff_exists_uniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Terminal/PivotRepairUniformPayoffCharacterization.lean`):
  small values must be produced by choosing the nonpivot laws.
- `IsStrictThreeBlockerCore` and
  `isUniformEquilibriumPayoff_of_strictThreeBlockerCore`
  (`UniformEquilibrium/Quitting/Classification/Existence/OddBlockerCore.lean`):
  the table's equilibrium mechanism is already covered by existing source
  conditions, with baseline (0,−1,−1,0).

The current question
[FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md](../questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md)
already permits its deadline to grow with accuracy. Therefore (1) does not
refute that question's full positive route or give its complete negative
answer. It removes the stronger proposed reduction to an accuracy-independent
atom count, even after unrestricted repair, on a solved canonical table.

If A_N is the infimum after arbitrary pivot repair over nonpivot laws with
at most N atoms, (1) and (4) give
(1/16)256^(−N)≤A_N≤4^(−N). The least sufficient atom budget is consequently
of logarithmic order in 1/ε. Its bounds are non-strict after taking an
infimum; actual finite-support profiles satisfy the strict inequalities
in (1). No lower bound independent of N, general counterexample, bounded
memory lower bound, or arbitrary-table producer follows.

Next concrete check: a second independent researcher can audit the
one-coordinate atom induction and Never-sensitive transfer before deciding
whether this quantitative support obstruction merits a separate packet.
