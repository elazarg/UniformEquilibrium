# A reached SUM-minimum entrance does not yet supply an outgoing packet

Identity: CODEX_HILBERT. Ordinary mathematics; no Lean or export claim.

**Conclusion.** The retained-tail/root-optimization test returns the existing
off-minimum continuation budget. It produces no new outgoing edge, strict
global competitor, or arbitrary-charge packet. The exact calculation below
identifies the missing implication and stops this fixed-tail subroute.

## 1. Complete semantics and the supplied entrance

There are four players, bounded terminal rewards r_i(S) for nonempty quitting
coalitions S, and zero payoff if nobody ever quits. Strategies are independent
laws on ℕ∪{Never}, equivalently complete behavioral strategies. Let U(p) and
B(p) denote the prescribed payoff and the supremum over ALL unilateral
behavioral responses. Put

    K=closure{(U(p),B(p)):p is an actual product profile},
    d_i(u,b)=b_i−u_i,       D(u,b)=Σ_i d_i(u,b),
    D_*=min_[z∈K] D(z)>0.

This is a SUM minimum, not a MAX minimum.

The entrance theorem in
`CODEX_FRECHET_CYCLE__SUM_MINIMUM_UNIFORMLY_REACHED_ENTRANCE.md`
supplies, for each minimum point z*, an incoming product root and carrier tail

    z*=T_q z⁺,             a(q)≥h,       0<h<1.          (1)

The entrance lower bound may be decreased to ensure h<1.

Both coordinates are co-realized: there are actual tails p_n⁺ and roots q_n
with semantic pairs tending to z⁺ and q_n→q, whose prefixed semantic pairs
tend to z*. These arise from actual near-minimizing profiles after deleting
a prefix of vanishing absorption charge and reach tending to one. The tail
z⁺ need not minimize D or be attained. The root q is not asserted Nash.

For x∈[0,1]⁴, write c(x)=∏_i(1−x_i), a(x)=1−c(x), and
α_i(x)=∏_(j≠i)(1−x_j). Let Q_i(x) be the Quit endpoint and C_i(x,v) the
Continue endpoint against continuation value v_i. Thus

    C_i(x,v)=Σ_[∅≠S⊆I\{i}] Pr_x(S)r_i(S)+α_i(x)v_i,
    F_i(x,v)=x_iQ_i(x)+(1−x_i)C_i(x,v),
    A_i(x,v)=max(Q_i(x),C_i(x,v)),
    g_i(x,v)=A_i(x,v)−F_i(x,v)≥0.

The exact full-cap prefix is T_x(u,b)=(F(x,u),A(x,b)). In particular,

    d_i(T_xz)=c(x)d_i(z)+g_i(x,b),
    D(T_xz)=c(x)D(z)+G(x,b),       G=Σ_i g_i.          (2)

Indeed F_i(x,b)−F_i(x,u)=c(x)(b_i−u_i). The cap endpoint A retains
arbitrary later responses and Never, not merely root actions followed by the
prescribed tail. Continuity and actual prefixing prove T_xz⁺∈K for every x:
prefix x to the SAME actual tails p_n⁺ and pass to the limit.

All Continue is not automatically the identity on an arbitrary tail pair:
its new cap is max(s_i,b_i), where s_i=r_i({i}). No such identity is used.

## 2. What global root optimization actually gives

Let Δ=D(z⁺)−D_*≥0. Global minimality implies that q minimizes the whole
continuous root-cube objective

    Φ(x)=c(x)(D_*+Δ)+G(x,b⁺)≥D_*,       Φ(q)=D_*.

Consequently

    G(q,b⁺)=a(q)D_*−c(q)Δ.                           (3)

This balances absorbed continuation debt against newly introduced root
regret. It does not minimize G alone and does not imply g_i(q,b⁺)=0.
It also does not imply ordinary Nash against the actual u⁺.

An exact product Nash root x against b⁺ exists by finite-game Nash existence.
For every such root, G(x,b⁺)=0, so global minimality gives

    c(x)>0,       a(x)≤Δ/(D_*+Δ).                    (4)

This is the existing cap-Nash excess budget. It gives no positive absorption
lower bound for the replacement root, and no transfer of the incoming h.
When Δ=0, every exact cap-Nash replacement is all Continue.

There is also a direct weighted-packet reading. For the cap annotations
v₀=b⁺ and v₁=b*, the Bellman residual is exactly g(q,b⁺), and the ordinary
root regret is the same vector. Thus both weighted error requirements at
tolerance ε are precisely

    max_i g_i(q,b⁺)≤ε a(q).                          (5)

Equation (3) supplies only max_i g_i≤D_*a. In the minimum-return case Δ=0,
it supplies the opposite bound max_i g_i≥D_*a/4, so these cap annotations
cannot have arbitrarily small weighted error. In the off-minimum case, (5)
requires

    c(q)Δ≥a(q)(D_*−4ε).                             (6)

If ε<D_*/4, this forces c(q)>0 and
Δ≥h(D_*−4ε)/(1−h). In particular a small-error cap step with fixed positive
charge must start a definite distance OFF the minimum fiber. This is a
necessary condition, not a way to select such a step or renew its charge.

All statements include c(q)=0: then (3) gives G=D_*, and (5) is impossible
for ε<D_*/4. There is no division by deleted or prescribed survival there.

## 3. Exact retained-root test on the already recorded SIGN table

Use the existing table r_i(S)=2−1[i∈S]. The actual tail p plays independent
Quit probability 1/2 for every player once, followed by all Never. Its full
semantic pair, computed in
`CODEX_HILBERT__QUANTITATIVE_PREFIX_IMPROVEMENT_AND_ANCHORED_TRAP.md`, is

    u_i=11/8,       b_i=15/8,       D(p)=2.

For every possible new product root x,

    Q_i(x)=1,
    C_i(x,b)=2−α_i(x)/8>1,
    U_i(x::p)=2−x_i−(5/8)c(x).

Hence all Continue is the UNIQUE exact cap-Nash root against this tail, but
the exact full-debt objective over the entire root cube is

    D(x::p)=Σ_i x_i+(5/2)c(x)−(1/8)Σ_i α_i(x).       (7)

This is multiaffine, so its value is an independent-product convex average
of its vertex values. For a vertex with k sure quitters these are

    k=0: 2;       k=1: 7/8;       k=2,3,4: k.

Therefore the minimum over ALL root modifications is 7/8, attained exactly
at the four pure singleton roots. To see exactness of this last assertion,
an independent Bernoulli root supported only on singleton coalitions must
have exactly one coordinate equal to one and all others zero.

Each minimizing root absorbs surely and incurs cap-root regret 7/8 in its
sole quitter, whereas its unique cap-Nash replacement absorbs zero. This is
an actual fixed-tail optimization with full behavioral caps, not an abstract
endpoint example. Exact rational enumeration of the sixteen vertices also
checks the displayed values; multiaffinity is the proof for mixed roots.

This does NOT falsify the GLOBAL positive-minimum hypothesis in (1): the
whole table has a pure singleton-Quit/all-other-Never exact terminal Nash
profile, so D_*=0. It falsifies only the attempted local substitution
“optimize all root coordinates with the tail fixed ⇒ obtain a charged Nash
root.” Changing the other players' retained tails is essential even here.

## 4. Exact stopping point and source correspondence

The unproved implication is not another inequality inside (2). It is an
operation on actual complete laws which leaves the retained-tail prefix
class and either gives D<D_* or supplies arbitrarily long weighted forward
packets with arbitrarily small error. The entrance theorem supplies neither
such an operation nor a renewal after an off-minimum cap step.

Choosing the known exact cap-Nash roots only gives (4); using the prescribed
root gives (3). Neither transfers fixed prescribed absorption into small
root regret or charged Nash absorption. No new outgoing edge was obtained.

The narrow source checks were:

- `quittingTerminalSemanticPair_rootThenContinuation`,
  `continuous_quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticPrefix_mem_carrier`, in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` and
  `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`,
  in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`.
- `capNash_absorptionMass_mul_debtSum_le_debtExcess` and
  `capNash_absorptionMass_le_debtExcess_div_debtSum`, in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`.
- `minimumTerminalSemantic_auxiliaryNash_budget`,
  `minimumTerminalSemantic_auxiliaryNash_eq_allContinue`, and
  `minimumTerminalSemantic_auxiliaryNash_criticalFace`, in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.
- `exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff`,
  in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect.lean`.
  Its neighborhood is around minimum PRESCRIBED payoffs, not automatically
  around the off-minimum continuation or the cap annotations used above.

The existing retained-tail timing-identity and off-minimum re-exactification
notes were checked as no-go boundaries. This note does not claim a new
producer theorem or reopen their fixed-tail refinements.

The next mathematical question, left open here, is whether a genuinely
nonlocal change of the co-realizing complete laws can pay for the
off-minimum excursion while producing small weighted root errors. No further
retained-root optimization is proposed.
