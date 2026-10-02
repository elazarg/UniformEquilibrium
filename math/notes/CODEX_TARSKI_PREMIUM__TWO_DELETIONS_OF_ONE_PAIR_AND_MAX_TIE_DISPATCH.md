# Two deletions of one pair: a common-clock inequality and MAX-tie dispatch

Identity: CODEX_TARSKI_PREMIUM.

Status: ordinary mathematics, not Lean-checked. The common-clock inequality
below is proved, including Never. At an actual sequence approaching a
hypothetical positive GLOBAL maximum-regret infimum, if prescribed pair mass
vanishes while one deletion exposes positive mass, it forces a complementary
observer's near-cap gain to come from outside that pair. It does not
sign the hidden collision, force both observers to need that pair, or produce
a lower-regret profile. This bounded consumption test stops at that distinction.
No export is proposed.

## 1. Question and actual source

There are four players, with independent complete stopping times
T_k in N union {infinity}. Infinity means permanent Never. If the earliest
finite time has coalition S, player k receives r_k(S); all-Never gives zero.
Assume |r_k(S)| <= M. A behavioral deviation is unrestricted. Write U_k(p)
for prescribed terminal payoff, B_k(p) for its full behavioral response cap,
d_k(p)=B_k(p)-U_k(p), and E(p)=max_k d_k(p).

The global source is m=inf_p E(p)>0 and actual profiles p_n with E(p_n)->m.
No actual minimizer, common calendar, or convergence of the clocks is assumed.
For the canonical single-pivot repair problem, the exact repair/source
equivalence identifies the same infimum after optimizing the pivot law and
selecting all three independent finite opponent laws. Full finite
approximation allows actual finite profiles approaching that infimum; it does
not preserve an attained law or a prescribed payoff target.

The checked all-player MAX-tie theorem implies

    d_k(p_n) -> m for every k.                                  (1)

To justify the sequential statement, a subsequence violating it has a further
convergent subsequence of bounded semantic pairs (U,B). Its limit lies in the
closed semantic carrier and minimizes continuous MAX debt there, since
closure does not change that infimum. Scale rewards uniformly by 1/M and
apply `minimumTerminalSemantic_maximumDebt_allPlayersTie`. This contradicts
the failed coordinate limit. Here M>0 follows from m>0. This argument
transports only (U,B), not dated counterfactual laws or clocks.

The concrete question is whether the new independent-clock two-pair law,
applied with common clocks to the source and its deletions, makes the hidden
pair term in the stopped serialization calculation acquire a sign or a
second required observer.

## 2. A common-clock two-deletion inequality

Fix complementary pairs {a,b} and {i,j}. Put

    w_t = P(T_a=t) P(T_b=t),
    S_k(t) = P(T_k>t),                 including Never,
    q = sum_t w_t,
    D_i = sum_t w_t S_j(t),            pair {a,b} after deleting i,
    D_j = sum_t w_t S_i(t),            pair {a,b} after deleting j,
    X = sum_t w_t S_i(t) S_j(t).       prescribed pair {a,b}

Deleting a player means replacing that player's clock by literal Never.
All these quantities use the SAME other marginal laws. The inequalities
inside the pair events are strict: a triple tie is not the pair {a,b}.
The finite tie probability q need not be a first-stopping probability.

Then

    D_i D_j <= q X.                                            (2)

Proof. For a finite cutoff K, use the corresponding truncated sums. Direct
expansion gives

    q_K X_K - D_i,K D_j,K
      = sum_{s<t<K} w_s w_t
          (S_i(s)-S_i(t))(S_j(s)-S_j(t)) >= 0.                 (3)

Both survivor tails are decreasing. All four truncated sums increase to
their complete values and are bounded by one, so taking limits proves (2).
This proof allows arbitrary unbounded laws, finite sure clocks, and positive
individual or joint Never atoms. It does not condition on an endogenous
stopping time or correlate the clocks.

If q=0, every w_t=0 and D_i=D_j=X=0; no division is made. If q>0, combine
(2) with the checked two-disjoint-pair law. Writing Y for prescribed pair
{i,j} mass and Z=P(all four Never), one obtains

    sqrt(D_i D_j / q) + sqrt(Y) + sqrt(Z) <= 1.                (4)

Indeed sqrt(D_i D_j/q)<=sqrt(X), while the existing theorem gives
sqrt(X)+sqrt(Y)+sqrt(Z)<=1. Thus (4) genuinely combines two deleted laws
with the prescribed law. Separate applications to unrelated profiles would
not give (2).

In particular,

    X=0 and D_i>0  ==>  D_j=0.                                (5)

More quantitatively, D_i>=h>0 gives D_j<=q X/h<=X/h.

The strict hidden-pair mass behind i is

    H_i = sum_t w_t P(T_i<t) S_j(t) <= D_i.                    (6)

It is also at most the prescribed singleton-i mass, by event inclusion.
Consequently H_i>=h and X small force D_j small by (2). This does NOT
require that the only discrepancy between D_i and X is H_i: ties involving
i contribute separately to D_i-X and have not been discarded.

## 3. Pure-time profiles: the replacement changes the relevant factor

The inequality applies to every actual pure-time replacement, but its
factors must be recomputed. For example, replace i by Quit at time ell and
retain j's actual law. Define

    A(ell) = sum_{t<ell} w_t,
    X_i(ell) = sum_{t<ell} w_t S_j(t).

Here D_i stays unchanged, while the OTHER deleted pair mass becomes
A(ell), not the original D_j. Therefore

    D_i A(ell) <= q X_i(ell).                                 (7)

The complementary prescribed pair mass in this response profile is
P(T_j=ell) S_a(ell) S_b(ell), and its joint Never mass is zero.
Using those quantities in (4) gives the literal two-pair constraint at
every finite response date ell. For i=Never, A=q and X_i=D_i; (7) is
equality, complementary pair mass is zero, and the deleted-profile Never
mass remains explicit in the original square-root law.

If instead j changes its clock, D_j is unchanged but D_i generally changes.
In particular, a near-cap response of j that preempts {a,b} can kill D_i
in the response profile. One cannot combine its complementary pair mass
with the OLD positive D_i by pretending these came from the same clocks.
All unused dates, the joining date itself, and Never are covered by these
literal replacement rules.

## 4. What the positive global MAX source actually forces

For any player j, let nu_j(t,Q) denote the first finite coalition law of
its three opponents, and let N_j be their joint Never probability. Thus
Q is nonempty and does not contain j. Set s_j=r_j({j}) and z_j=P(T_j=infinity).
Conditional on (t,Q), the prescribed payoff of j is

    K_j(t,Q) = P(T_j<t) s_j + P(T_j=t) r_j(Q union {j})
                 + P(T_j>t) r_j(Q).                          (8)

For a pure response ell (finite or Never), let R_j(ell;t,Q) be s_j if
ell<t, r_j(Q union {j}) if ell=t, and r_j(Q) if ell>t. Never exceeds
every finite t. Then the COMPLETE response gain is exactly

    g_j(ell)
      = sum_{t,Q} nu_j(t,Q)[R_j(ell;t,Q)-K_j(t,Q)]
          + N_j s_j[1_{ell finite}-(1-z_j)].                  (9)

The last term retains deleted Never separately from prescribed joint Never.
For a canonical nonpivot it is zero because s_j=0, not because N_j=0.
Unrestricted behavioral caps equal the supremum of these pure gains.

Isolate the contribution of Q={a,b} in (9), calling it C_j^{ab}(ell).
All raw rewards and K_j lie in [-M,M], so uniformly over EVERY response,

    |C_j^{ab}(ell)| <= 2M D_j <= 2M q X/D_i     if D_i>0.      (10)

Let G_j^{other}(ell)=g_j(ell)-C_j^{ab}(ell); it contains all other
opponent coalitions and the literal Never term. At p_n choose an actual
pure response ell_n within epsilon_n->0 of B_j(p_n). This is produced by
the supremum defining the cap, without assuming cap attainment. Equations
(1), (9), and (10) give

    G_j^{other}(ell_n)
      >= m-o(1)-2M q_n X_n/D_i,n.                             (11)

For finite laws supported through time K_n, one may instead choose an
exact maximizing response from times 0,...,K_n+1 and Never; the extra date
represents EVERY later finite Quit. No common fixed response pool is used.

In particular, if one fixed pair and one fixed deletion satisfy
H_i,n>=h>0 and X_n->0, then

    D_j,n->0,       G_j^{other}(ell_n) >= m-o(1).              (12)

Labels can be fixed on a subsequence when the retained hidden-pair lower
bound is originally supplied among finitely many labels. No lower bound
on a hidden pair, or upper bound X_n->0, is itself inferred from globality.

This is the resulting source dispatch: a macroscopic pair hidden behind
one player, with vanishing prescribed pair mass, forces the complementary
owner's near-cap gain AWAY FROM that same pair. All-player ties do not
force two observers to need it. The other contribution may come from
another pair, a singleton, a triple, preemption, same-date joining, or (for
a signed-singleton owner) the displayed Never term. These possibilities
are not eliminated by (2) or (4).

## 5. Exact calibration of the alternative, not a global counterexample

The following two canonical tables test the attempted inference from the
listed local quantities alone. They are solved tables and NOT realizations
of the hypothetical positive global source.

For every nonempty S, choose h=0 or h=3 and define

    r_0(S) = 1 if 0 in S;
             2 if S={1,2};
             h if S={1};
             0 otherwise.
    r_k(S) = -1 if 0 in S and k not in S, else 0,   k=1,2,3.

Never is zero and own singletons are (1,0,0,0). Use the actual clocks

    T_0=0, T_1=T_2=1, T_3=Never.

For pair {1,2} and complementary owners 0,3, the exact values are
q=D_0=H_0=1 and D_3=X=Y=Z=0. Both tables have

    U=(1,-1,-1,-1),  B=(2,0,0,0),  debts=(1,1,1,1).

The complete pure response rows at times 0,1,2,Never are

    player 0: (1,1,2,2);
    each nonpivot: (0,-1,-1,-1).

Every later date equals date 2. Player 3's full gain one is the joining
response Quit0 against deleted singleton {0}; its {1,2} contribution is
zero. In that response profile, the complementary pair {0,3} has mass one
but D_0 has changed to zero, exactly as Section 3 requires.

Serializing the hidden {1,2} collision with player 1 first changes its
pivot reward by h-2: negative for h=0 and positive for h=3. All displayed
law quantities, full caps, and four tied debts stay the same. Thus neither
the pair inequalities plus the four tie equalities nor this label pattern
alone supplies the missing sign. All four players Quit0 is exact terminal
Nash for BOTH tables, so their GLOBAL infimum is zero. This calculation
does not refute any implication using the full positive-global-infimum
hypothesis. The actual use of that hypothesis is (1) and (11)-(12), not
the nonminimal calibration.

Exact arithmetic checks: all 10,000 four-clock profiles on {0,1,Never}
with third-grid marginal probabilities satisfy identity (3), including
6,112 cases X=0. Direct raw-outcome enumeration verifies both complete
response arrays and the all-Quit0 equilibrium. A further 3,200 exact checks
of (9), over 200 third-grid profiles, all four owners, and the complete
times 0,1,2,Never, include the all-Never and after-menu terms. These are
tests; the proofs above establish the arbitrary-law statements.

## 6. Known/new boundary and source audit

The integrated two-pair group-exclusion consumer already converts prescribed
pair masses into a payoff obstruction when its specified raw pair-average
reward bounds hold. Those reward bounds are NOT consequences assumed here.
Applying its payoff comparison to a deleted profile also does not make its
payoffs the original players' response gains. Equation (9) is needed for
that comparison and leaves the alternative terms explicit.

The additional calculation here is the common-clock covariance identity
(3), followed by the same-source MAX-tie dispatch (11). Narrow searches for
joint deletion, pair/deletion products, and covariance/Chebyshev found no
matching pair-mass declaration or note. This is a bounded source comparison,
not a claim to have exhausted every existing inequality.

Sources inspected:

- `docs/TOOLKIT.md`, actual two-pair route.
- `Quitting/Paths/BehaviorFirstStoppingPairLaw.lean`:
  `quittingBehaviorTwoDisjointPairMasses_sqrt_sum_add_never_le_one` and
  `quittingBehaviorTwoDisjointPairMasses_finiteLeftover_ge_two_sqrt_mul`.
- `MathUE/Probability/IndependentFirstStoppingPair.lean`:
  `twoDisjointFirstStoppingPairMasses_sqrt_sum_add_never_le_one`, its complete
  stopping-law definitions and finite-cutoff limit proof.
- `Quitting/Paths/TwoPairGroupExclusion.lean`:
  `hasQuittingActualNonconcentratedGroupExclusion_half_of_twoPairRewardBounds`.
- `Quitting/Terminal/PairAverageSurplus.lean`:
  `quittingTwoCoordinateAverageSurplus_terminalPayoff_le`, including its
  singleton-weighted Never correction and raw row hypotheses.
- `Quitting/Paths/CounterfactualStoppingLaw.lean`:
  `quittingBehaviorDeviationPayoffCap_eq_pureTime` and actual independent-law
  intervention semantics.
- `Quitting/Terminal/FiniteDeadlineFullReplyCap.lean`:
  `quittingFiniteDeadlineTimingProfile_pureTime_eq_never_add_of_le`.
- `Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`:
  `minimumTerminalSemantic_maximumDebt_allPlayersTie`, for GLOBAL MAX and
  the compact semantic carrier, not SUM or a fixed-calendar minimum.
- `Quitting/Terminal/SinglePivotRepairSourceEquivalence.lean`:
  `singlePivotFiniteMenuScalarSource_iff_smallPivotRepairValue`.
- [Sufficient-state boundary](../arch/SUFFICIENT_STATE.md), and the stopped
  [serialization calculation](CODEX_TARSKI_PREMIUM__JOINT_OPPONENT_SERIALIZATION_AND_COMPLETE_REPAIR_TEST.md).

Stop conclusion: the pair law rules out two large complementary deletions
of a prescribed-rare pair and yields the actual alternative near-cap gain
(11). It does not orient that other gain, improve the full repair value, or
create an incompatible finite cycle of labels/times. The remaining concrete
question would be whether the responses produced in (11), across several
hidden pairs at one genuine near-minimizing source, have a timing/label
incompatibility forced by a further GLOBAL comparison. No such incompatibility
is proved, and no unsupported pigeonhole or supplied observer is substituted.
