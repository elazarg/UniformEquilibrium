# Same-potential outside fiber: joint-law comparison checkpoint

Author: CODEX_TARSKI_PREMIUM.

Status: bounded finite-cube test completed and stopped. The complete
shifted-tester comparison is recorded in §6, but it supplies no forced
improvement or new obstruction under the SAME-H hypotheses.
The exact calendar, full-response objective, and known/new split are below.
The cap-Nash interpolation test is completed and retired separately in
[the stopped comparison](../notes/CODEX_TARSKI_PREMIUM__DEBT_SUBLEVEL_POTENTIAL_MINIMUM_STOPPED_TEST.md).
The reviewed actual outside-source theorem is unchanged. No export or
Lean change is proposed for this checkpoint.

## 1. One table, one potential, actual source laws

Fix a signed Fin4 quitting table r with rewards bounded by M>0 and Never
zero. Assume its unrestricted actual terminal-regret infimum m is positive.
The same-table no-UE reduction supplies normality and a positive singleton,
hence one robust universal polynomial H on [−M−2,M+2]^4. Its exact-edge
consequence is

    H(v)−H(F(q,v))≥a(q)

for EVERY exact root Nash q at EVERY boxed annotation v. No worst-table
replacement or multiplier transport is used in this test.

Let Y be the compact actual prescribed-payoff image, s_i=r_i({i}),
C={v:v_i≥s_i for all i}, and C⁺ its strict version. The
[reviewed actual-source theorem](../notes/CODEX_TARSKI_PREMIUM__ACTUAL_OUTSIDE_POTENTIAL_MINIMUM_AND_FULL_CAP_CONTRACTION.md)
selects z minimizing the SAME H over Y\C⁺, with

    z∉C,       H(z)<min_(Y∩(C\C⁺))H.

Every exact root at z sends it into Y∩C⁺ and has all player-deleted
Continue factors at most κ_z<1. Every actual σ with U(σ)=z therefore
satisfies E(q⊕σ)≤κ_z E(σ), but also E(σ)≥m/κ_z. This off-minimum
fiber bound is an existing conclusion, not a new comparison proved here.

## 2. One literal common calendar and its complete testers

For N≥20 write

    A_N={0,…,N−1,Never},       X_N=∏_i Δ(A_N).

These are actual independent stopping laws, not finite-menu Nash laws.
Let m_N=min_(p∈X_N)E(p), and choose any actual full-objective minimizer p_N.
The complete pure-response set against X_N is

    T_N={0,…,N,Never}.

Every later finite date has the same payoff as date N; it is NOT generally
equivalent to Never. All behavioral caps equal maxima over T_N because
every full response is a mixture of pure deadlines and Never. Thus E is
a finite maximum of continuous multiaffine gain polynomials on X_N.
Compactness gives m_N and p_N. The checked full-profile approximation
theorem implies m_N decreases to the unrestricted infimum m. This uses
full regret approximation, not payoff-only calendar compression.

Let

    R_z={σ∈X_20:U(σ)=z}.

The exact payoff-realization theorem makes R_z nonempty; continuity makes
it compact. All σ in this family use precisely the SAME calendar A_20,
embedded without retiming into A_N. No cap equality between these
realizers is asserted. Keeping the entire finite simplex fiber is enough;
its marginals need not be separately forced to have at most five atoms.

For σ∈R_z and t∈[0,1]^4, form the four independent whole-law mixtures

    x_i(t,σ)=(1−t_i)(p_N)_i+t_i σ_i.                     (1)

All x remain in X_N. Each player privately chooses between two complete
clocks; there is no common source label or correlated profile mixture.
Then choose ANY exact root q at the ACTUAL payoff U(x), and prepend it.
The resulting laws lie in X_(N+1): the new root is date zero, the old
calendar is shifted by one, and Never stays Never. Its full tester set is
exactly T_(N+1)={0,…,N+1,Never}. This includes the new late test.

## 3. The genuine full-objective comparison

The proposed finite optimization is

    Ψ_N=min E(q⊕x(t,σ)),
        σ∈R_z, t∈[0,1]^4, q exact Nash at U(x(t,σ)).     (2)

Its feasible set is nonempty and compact: root Nash inequalities are
closed polynomial inequalities in the actual finite data and roots exist
at every continuation payoff. The objective retains all complete tests
in T_(N+1). Thus (2) is an attained actual-law optimization, not a
supplied successful-root assertion or an equilibrium convexification.

The elementary but important known bracket is

    m_(N+1)≤Ψ_N≤m_N.                                    (3)

The lower bound follows from the literal calendar inclusion. For the upper
bound take t=0 and any exact payoff-Nash root at U(p_N); the complete
positive-part cap splice weakly decreases every debt. It follows that
Ψ_N→m automatically, whether m is zero or positive. The bracket does NOT
refute a theorem deriving m=0 from the hypothetical positive-gap source:
that desired theorem would itself contradict the working assumption.
It only prevents presenting this restricted optimization or a tiny finite-
calendar decrease as a new vanishing-regret producer.

The candidate positive test is precise: can the SAME-H outside-minimizer
field force a fixed η>0 and arbitrarily large N with Ψ_N≤m_N−η?
Together with (3) and m_N→m that would be a contradiction. Merely
exposing another root, obtaining Ψ_N<m_N with vanishing improvements, or
recovering the endpoint contraction at t=1 does not pass this test.
No such fixed decrease has been derived.

## 4. Existing cube machinery versus the one new source field

For fixed σ, let p^S replace exactly players in S by σ_i. The prescribed
payoffs and EVERY complete pure-response gain satisfy

    g_a(x(t,σ))=Σ_(S⊆I) w_S(t)g_a(p^S),
    w_S(t)=∏_(i∈S)t_i ∏_(i∉S)(1−t_i).                  (4)

This is the already-known full independent replacement cube. It is not
made convex by its probabilistic notation, and a negative weighted
average does not control every active tester. The new-root full objective
can be computed from these same actual laws and the exact prefix cap
formula, but this computation supplies no sign.

The narrow comparison read on this pass includes:

- [RENY's simultaneous active-response recombination boundary](../notes/CODEX_RENY__SIMULTANEOUS_ACTIVE_RESPONSE_RECOMBINATION_BOUNDARY.md):
  already retains all four mixture weights, all active testers, and the
  newly exposed late response. Its endpoint laws come from active
  responses; (4) is not new here.
- [the common-clock recombination theorem](../notes/CODEX_FRECHET_CYCLE__QUANTILE_COMMON_RECOMBINATIONS_AND_CROSS_FACE_REGRESSION.md):
  already represents an entire fixed recombination box with full-cap
  control. No such approximation is needed for our common finite calendar.
- [the coupled-calendar certificate](../notes/CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE.md):
  already supplies simultaneous enlarged-domain first-order information.
  We do not attach its reward-normal weights to this different source.
- [the full replacement atlas](../ideas/CONTINUATION_GAME_STATE/FULL_REPLACEMENT_KERNEL_ATLAS.md)
  and `arch/SUFFICIENT_STATE.md`: actual marginal laws retain the required
  cross-response information; no lower-order state closure is asserted.

The ONLY new field relative to this machinery is the global condition
selecting z from the SAME universal H and the restriction σ∈R_z. It gives
an all-root contraction at the far endpoint, but that endpoint is already
off minimum by m/κ_z. The actual payoffs of every hybrid and mixture lie
in Y, so their H values obey the genuine outside-region lower bound when
they lie outside C⁺. This does not currently determine the signs of the
mixed full-response terms in (4) or compare their exploitability with m_N.
That is the exact remaining implication, not an omitted KKT calculation.

## 5. Production interfaces and stopping point

Named declarations inspected for this setup:

- `exists_finiteDeadlineTimingProfile_approximation`,
  `UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`:
  arbitrary actual profiles have finite-law approximants with prescribed-
  payoff and unrestricted-exploitability control, above any given deadline.
- `quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff`,
  `isCompact_quittingActualTerminalPayoffSet`, and
  `exists_sparse_finiteCalendarLaws_of_mem_closure_actualPayoff`,
  `UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffClosure.lean`:
  used only to obtain the nonempty compact actual payoff fiber R_z.
- Exact root existence in `Quitting/Root/NashExistence.lean` and the
  complete semantic prefix/debt identities in
  `Quitting/Root/TerminalSemanticPair.lean`, relative to `UniformEquilibrium/`.

Decision at this checkpoint: the operation is legal and genuinely changes
all four laws, but its finite cube algebra and optimization are prior.
Only a forced sign from the SAME-H fiber restriction could make this a
new consumer. No sign, global counterexample, or positive-minimum
contradiction is claimed. This is the single parked next question, not
a new exported annotation language or a family of proposed variants.

## 6. Resumed exact comparison and stopped sign test

Keep ALL data, calendar inclusions and source quantifiers in §§1–3.
For a selected σ,t write u=U(x), α_i=∏_(j≠i)(1−q_j), and let

    Q_i=expected reward if i Quits in the new row,
    A_i=expected reward on nonempty opponent Quit sets in that row,
    G_i=Q_i−A_i−α_i u_i.

These are computed at the actual new product root q. Before assuming
q is Nash, the exact complete-response equations are

    g'_(i,0)=(1−q_i)G_i,
    g'_(i,k+1)=α_i g_(i,k)(x)−q_i G_i.                 (5)

Here k runs through EVERY old finite tester 0,…,N and through Never;
the shifted Never tester is still Never. The new late finite tester is
N+1, separately from Never. Indeed its response value is A_i+α_i V_i,k,
whereas prescribed payoff is q_iQ_i+(1−q_i)A_i+cU_i.
Subtracting and using c=(1−q_i)α_i proves (5). Thus no row with zero
multiplier weight, no outside owner, and no late behavior is discarded.

Substitution of the independent four-law expansion gives

    g'_(i,k+1)=α_i Σ_S w_S(t)g_(i,k)(p^S)−q_iG_i.       (6)

At an exact payoff-Nash root q, q_iG_i=max(0,G_i) and the first
expression in (5) is nonpositive. Consequently, with

    d_i(p^S)=max_(k∈T_N) g_(i,k)(p^S),
    C_i(t,σ)=Σ_S w_S(t)(d_i(p^S)−m_N),

the genuine all-tester quantitative bound is

    E(q⊕x) ≤ max_i [α_i(m_N+C_i(t,σ))−max(0,G_i)]_+.    (7)

The inequality is only the finite maximum bounded by the sum of finite
maxima; equality need not hold because different corners can have different
maximizing testers. In particular (7) is not a convexification of the
independent law family. Equation (6), rather than (7), remains the exact
testerwise account.

For η with 0<η<m_N, one sufficient sign for the desired gap would be

    α_i C_i(t,σ)
      ≤(1−α_i)m_N+max(0,G_i)−η          for EVERY i.      (8)

This is deliberately not promoted as a new sufficient-condition packet.
It exposes precisely the unknown joint corner debts; merely assuming (8)
would insert the desired cap control instead of deriving it. At t=0 the
account reduces to the old weak prefix improvement. At t=1 it reduces
to contraction of an already off-minimum fiber. For interior t it retains
all fourteen proper nonempty corners, whose debts have not been priced.

One honest additional variational fact was tested. Because z is strictly
outside C, every σ realizing z is a local minimum of H∘U on the space
of actual independent laws. Hence, for any owner j and any complete
replacement ρ_j, the legal one-coordinate chord gives

    ∇H(z)·(U(σ[j←ρ_j])−z)≥0.                         (9)

The chord stays outside C⁺ for sufficiently small positive parameter.
This is scalar prescribed-payoff information; it contains neither the
response laws in (6) nor the corner maxima in (7). It is the familiar
actual-payoff scalarization consequence applied at the new outside source,
not an additional bound on unrestricted regrets. I found no deduction of
(8), or of its sharper exact testerwise counterpart, from (9) and the
universal root inequality.

Decision: stop this particular one-cube comparison. The calendar and
response accounting are complete, but the only quantitative conclusion
with a source-supplied sign remains m_(N+1)≤Ψ_N≤m_N and the already
proved outside-fiber separation. This is not an exact no-UE countermodel
or a disproof of a global contradiction theorem. In particular no solved
table with an isolated convenient root was substituted for the SAME
universal H.

The distinct global variational alternative selected next is recorded in
[FULL_REGRET_MINIMAX_PATH_DEFORMATION_TEST](../notes/CODEX_TARSKI_PREMIUM__FULL_REGRET_MINIMAX_PATH_DEFORMATION_TEST.md).
It changes the comparison object from one mixture cube to an entire
actual-profile path and its MAX-regret barrier. The old component-as-word
argument is not revived: potential increases along the external path are
never counted as Bellman charges.
