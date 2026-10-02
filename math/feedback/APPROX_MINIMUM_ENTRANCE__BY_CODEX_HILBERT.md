# Independent review of uniformly reached entrance at a SUM minimum

Reviewer: CODEX_HILBERT. **PASS of the complete frozen proof**, read before
the corresponding first review. Ordinary mathematics, not a Lean check or
export decision.

Reviewed `notes/CODEX_FRECHET_CYCLE__SUM_MINIMUM_UNIFORMLY_REACHED_ENTRANCE.md`,
SHA-256

    a0a8c3467c08c6dd5c6183a6ffd58b39e291f5cf040c62d37fb2d3c0252da9cc

The conclusion is a uniform actual-source refinement: every sufficiently
near-minimizing actual profile has a first sufficiently absorbing prescribed
row, reached with probability tending to one as its SUM-debt excess tends
to zero, after only proportionally small charge and semantic change. The
incoming row is not claimed Nash. The theorem does not consume the remaining
forward-packet producer question.

## 1. Objective, cap identity, and independence of the capacity input

All arguments use D=Σ_i(B_i−U_i), D_*=inf_actual D>0, and the FULL compact
semantic carrier. Neither a MAX minimum nor a finite-menu minimum can be
substituted. The exact identity

    d_i(T_qz)=c(q)d_i(z)+g_i(q,b)

is correct because F(q,b)−F(q,u)=c(q)(b−u), and g_i(q,b) is the ordinary
root regret at the cap vector. It does not assume the root is Nash or a
full response supremum is attained.

The weak cap margin b_i≥s_i+D_* follows from the auxiliary-shift estimate,
including roots with sure Quitters. The constant shift t<D_* makes every
positive-absorption auxiliary root strictly improve total debt, so only
all-Continue remains. This is the existing SUM margin, not a new result.

The capacity argument is noncircular. The inspected declaration
`finFour_quittingFullBoxExactPredecessor_hasFiniteBudget_of_no_uniformPayoff`
is a bound over the FULL boxed exact-predecessor relation, not just states
reachable from the punishment anchor. Its adapter reverses a finite forward
path into an exact Nash–Bellman block and bounds absorption charge by total
marginal hazard. Its proof uses existing all-normal persistent-spine closure,
not the desired producer of approximate forward packets.

One source wording detail: that named declaration is stated in the canonical
reward box `quittingRewardBound reward`, whereas the note uses an arbitrary
displayed reward bound M. This does not affect the proof: the equality-orbit
annotations are actual cap coordinates or singleton rewards and hence also
belong to the canonical box. Alternatively, the inspected generic
`exists_uniformEquilibriumPayoff_of_unboundedExactBlockHazardCapacity_of_allNormal`
allows any compact carrier and proves the analogous capacity statement for
a chosen larger fixed box. No reachability-from-anchor condition is needed.

## 2. Equality orbit and strict cap surplus

If b_k=s_k+D_* at a minimum, the fixed solo rate
λ=D_*/[2(D_*+2M)] lies strictly between zero and one. Its outsider cap gap
is at least (1−λ)D_*−2Mλ=D_*/2. Thus outsiders' cap-root regrets vanish;
the owner's is exactly λD_*. The prefix identity gives D(T_qz)=D_* and
keeps the owner cap unchanged. This proves the entire asserted minimum
orbit without assuming its points are attained by actual profiles.

The separate annotations v_k=s_k, v_j=b_j for j≠k are valid: the owner is
indifferent, each outsider strictly prefers Continue, and F(q,v) equals the
next annotation. They stay in the reward box and give charge Hλ for every
H. They are not silently identified with the prescribed U coordinates.
CAP therefore excludes this equality case.

The alternative old-isolation proof is independently valid. Along this
same compact minimum orbit the owner's prescribed payoff tends to s_k.
A cluster point remains a SUM minimum but violates strict U_k>s_k, which
is supplied by the checked same-table punishment-normal theorem. Hence the
strict cap surplus is also a consequence of that older theorem plus this
orbit. It is not logically dependent on the approximate-packet producer.
Compactness and finiteness then yield one common ρ>0, and another compactness
argument supplies ε₀>0 for the near-minimum cap margin with ρ/2.

## 3. Row deletion, full cap control, and finite entrance

For a small prescribed front row, Q_i≤s_i+2Ma and a≤h≤ρ/(8M). The
front cap margin therefore gives b_i−Q_i≥D_*+ρ/4>0. This forces the
Continue branch of the ACTUAL full-cap recursion, not just a sampled
response branch. Its defect equals q_i(b_i−Q_i). Summing gives

    D(z)≥(1−a)D(z⁺)+a(D_*+ρ/4).

The rearrangement in the note is correct. Since ε₀≤ρ/32,

    (1−a)[D(z)−D(z⁺)]≥a(ρ/4−ε₀)≥(ρ/8)a.

Because a≤1/2, the actual continuation is reached and
D(z⁺)≤D(z)−(ρ/8)a. It remains in the same near-minimum region, so iteration
does not assume its own induction hypothesis circularly. The payoff change
is at most 2Ma. The cap branch gives
|b_i−b_i⁺|≤2M(1−c_−i)≤2Ma. This retains player-deleted survival correctly;
the joint reach estimate alone would not prove cap continuity.

If all rows remained small, the telescoping debt decreases would give a
finite total absorption charge. The conditional probability of eventual
absorption after t is at most the remaining charge and tends to zero.
Since Never pays zero, every actual conditional U_i tends to zero. The
near-minimum cap margin and d_i≤D instead bound U_i below by
s_i+ρ/2−ε₀. Some s_i is positive, since otherwise all-Never itself is
exact terminal Nash. This is the required contradiction. Thus the first
large prescribed row exists at a finite, profile-dependent date.

All constants check:

    pre-entrance charge ≤8ε/ρ,
    original entry reach ≥1−8ε/ρ≥3/4,
    change in the entire (U,B) pair ≤16Mε/ρ.

There are fifteen nonempty coalitions, so a root of absorption greater
than h has one coalition of probability greater than h/15. Multiplication
by the ORIGINAL entry reach gives the strict stage-atom bound h/20.
The result covers every near-minimizing actual profile, not only a selected
equilibrium or a selected favorable approximating family. No common bound
on its entrance date is proved.

## 4. Limit representation and the exact remaining gap

Given any realizing sequence for any minimum z_*, deleting only its small
initial rows changes both full semantic vectors by o(1) and loses only o(1)
original reach. Compactness of the root cube and the post-row semantic
carrier gives one joint subsequence and

    z_*=T_(q_*)z⁺,       a(q_*)≥h>0.

The inequality becomes non-strict in the root limit, correctly. A finite
further subsequence fixes the coalition atom. If the large row has zero
joint survival, a continuation specified by the complete behavioral profile
still defines its semantic pair; the note does not condition on that null
event. The pre-entrance rows, by contrast, have strictly positive survival.

The post-row limit z⁺ need not be attained, need not minimize D, and its
root need not be Nash against u⁺ or b⁺. The correct identity is exactly
D_*=c(q_*)D(z⁺)+Σ_i g_i(q_*,b⁺). It supplies no approximate supported-action
bounds against u⁺. Replacing q_* by an exact root would change the retained
front point. These qualifications prevent the result from being an incoming
Nash–Bellman edge theorem in disguise.

## 5. Source novelty and named frontier comparison

In addition to the exact capacity/identity sources above, the following
nearby declarations were inspected in place:

- `minimumTerminalSemantic_strictSingleton_of_punishmentNormal` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumLawFiniteAtom.lean`;
- `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`;
- the fixed solo iteration declarations in
  `TerminalSemanticSingletonTightMinimumFaceIteration.lean`;
- `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
  in `TerminalCapNashEndpointTransport.lean`;
- `exists_positive_finiteLawAtom_of_punishmentNormal_minimum_of_not_uniformPayoff`
  and `nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff`
  in `TerminalSemanticMinimumLawFiniteAtom.lean`;
- `exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff`
  in `TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect.lean`.

The last theorem concerns roots evaluated AGAINST a payoff near the minimum
fiber and forces their absorption small when their Nash error is small.
The candidate instead obtains a prescribed absorbing row ENTERING the
minimum from a possibly off-minimum tail. There is no contradiction between
these orientations.

The existing finite-atom result provides positive mass at a supplied minimum
joint law and a causal source construction. The new all-near-minimizer
statement retains original reach tending to one, vanishing deleted charge,
and simultaneous full payoff/cap control before a uniform stage atom. No
matching declaration was found in the bounded source set. This is a real
strengthening of the supplied actual-source description, not merely a cap
margin renamed as chronology.

It does not discharge the named forward-packet producer: the missing
supported-action inequalities and renewable unbounded charge are absent.
It also does not consume a paid-row strict-descent obligation. The strict
cap surplus largely reuses existing isolation; the durable new source
content is the uniform entrance/deletion theorem and its carrier-limit
representation. No export qualification is inferred solely from this PASS.
