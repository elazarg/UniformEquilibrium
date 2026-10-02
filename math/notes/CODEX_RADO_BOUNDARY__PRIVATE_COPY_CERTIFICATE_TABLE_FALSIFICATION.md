# A rational table defeats the proposed maximum private-copy gap test

Author: CODEX_RADO_BOUNDARY.

Status: bounded negative-certificate test stopped by an exact positive
profile on the chosen table. Ordinary mathematics, not independently
reviewed or checked in Lean. No counterexample to uniform equilibrium,
new parameter-wide producer, matching completeness, or export is claimed.

The candidate was outside the specific positive source regions checked
before the test. It was not certified hard. An actual two-phase equilibrium
now rules out EVERY strictly positive all-profile regret certificate on
this table, including the proposed maximum of independent-copy tests.
The complete-law accounting identity in Section 2 survives globally.

## 1. One chosen table, and the certificate being tested

There are four players, with zero live and Never payoff. The complete
rational terminal table is

| Coalition | Reward vector |
| --- | --- |
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (2,3/2,1,1) |
| 02 | (3/2,1,1,0) |
| 03 | (5/4,0,1,3/2) |
| 12 | (0,1,7/4,1) |
| 13 | (1,7/4,0,5/4) |
| 23 | (1,1,5/4,7/4) |
| 012 | (1,0,0,0) |
| 013 | (0,1,0,0) |
| 023 | (0,0,0,1) |
| 123 | (0,0,1,0) |
| 0123 | (−1,−1,−1,−1) |

The own pair-member row sums are (19/4,17/4,4,9/2). Hence neither
stationary row-sum source in the
[preceding stationary notebook](CODEX_RADO_BOUNDARY__ASYMMETRIC_PAIR_MEMBER_STATIONARY_BOUNDARY.md)
applies. The table is not a common-c completion; its four active member
rewards on either cross matching are unequal. Some cross rewards exceed
6/5, so the named independent-cross rectangle below does not supply it.
This is a bounded source comparison, not an exhaustive classification.

For an arbitrary independent product law p on ℕ∪{∞}, let t*(p) be its
earliest date with positive finite mass in any marginal, using zero if all
marginals are Never. For each owner i the proposed tests were

- Never;
- deterministic dates t*(p) and t*(p)+1;
- an independent copy of p_j, for each j≠i;
- an independent copy of p_j followed by a one-date delay, for each j≠i,
  with ∞+1=∞.

Each copy is sampled privately and independently of the ACTUAL opponent
clock. The test may inspect the source law to choose a distribution, but
it never learns another player's realized clock. Let T(p) be the maximum
of zero and the expected gains of these 36 tests. The attempted negative
conclusion was T(p)≥γ for every independent profile and some fixed γ>0.
No completeness of this tester family was assumed.

The fixed-weight version was rejected before table calculation: the
[private successor-resampling no-go](CODEX_TARSKI_PREMIUM__PRIVATE_SUCCESSOR_RESAMPLING_WEIGHTED_SUM_NO_GO.md)
constructs actual response-mixture law fixed points for that template.
Its theorem does NOT settle a maximum of individual gains. The present
maximum-test failure instead follows from an actual equilibrium of this
particular table.

## 2. Global product-law order/tie accounting retained by the test

Write p_j(t)=Pr(T_j=t), s_j(t)=Pr(T_j>t), and n_j=Pr(T_j=∞). For
nonempty S⊆I∖{i}, the exact first-opponent coalition mass at t is

    ν_i(t,S)=∏_(j∈S)p_j(t) ∏_(j∉S,j≠i)s_j(t).

Let f_i(t;p) be the payoff from the literal deterministic response t,
and W_i(p) the payoff from literal Never. Then

    f_i(t;p)=Σ_(u<t) Σ_(∅≠S⊆I∖{i}) ν_i(u,S)r_i(S)
       +Σ_(S⊆I∖{i}) r_i(S∪{i})
                      ∏_(j∈S)p_j(t) ∏_(j∉S,j≠i)s_j(t),
    W_i(p)=Σ_t Σ_(∅≠S⊆I∖{i}) ν_i(t,S)r_i(S).         (1)

The empty-S term of the second sum is the own singleton. All simultaneous
ties are retained. The Never value is the displayed opponent-absorption
expectation, not an artificial zero. Bounded rewards make these sums
absolutely convergent.

Affineness in the replaced COMPLETE marginal gives the exact identities

    U_i(p)=Σ_t p_i(t)f_i(t;p)+n_iW_i(p),
    gain_i(copy j,p)=Σ_t[p_j(t)−p_i(t)]f_i(t;p)
                                      +(n_j−n_i)W_i(p),
    gain_i(copy j + 1,p)=Σ_t p_j(t)f_i(t+1;p)
                                      +n_jW_i(p)−U_i(p).       (2)

These hold for arbitrary unbounded independent stopping laws, including
positive Never atoms. In the copy test, a tie with the actual j clock has
the product probability p_j(t)², not the probability p_j(t) of a shared
draw. Equations (1)–(2) are the surviving global identities. They do not
give a sign without additional, valid payoff inequalities.

## 3. The exact candidate profile and previously derived active equations

Use phases A,B,A,B,… . In phase A only players 0 and 2 may Quit, with
Continue probabilities a,c. In phase B only players 1 and 3 may Quit,
with Continue probabilities b,d. All draws are independent.

Set

    P=(3−c)/2,       Q=(7−3d)/4,       R=(5−b)/4,
    V_A=(P,Q/d,1,R/b),
    V_B=(P/c,Q,1/a,R).                               (3)

Every active Quit and Continue endpoint is already the corresponding
displayed value. The four quiet Continue equations are equivalent to

    F₀=P(1−bcd)−c(1−b)(1+3d)=0,
    F₁=Q(1−acd)−d(1−a)(1+3c)=0,
    F₂=1−abd−4ab(1−d)=0,
    F₃=R(1−abc)−4ab(1−c)=0.                          (4)

These are IDENTICAL to the four active/quiet continuation relations
already derived in Section 2 of NOETHER's
[independent cross-reward rectangle](CODEX_NOETHER_SUPPORT__INDEPENDENT_CROSS_REWARD_BOX_PERIOD_TWO_SOURCE.md),
specialized to active member vector (3/2,7/4,1,5/4). The inspected source
hash was `067f0ef12591b29f3a4a01307e80f4c4ba02605780c2d81a32c87f5fae68fb86`.
No new generic four-rate equations or periodic compiler are claimed.
The rectangle theorem's parameter bound is not being extended silently;
Section 4 gives a direct small certificate for this ONE table.

For independently checkable polynomial arithmetic, (4) expands to

    F₀=(bc²d+3bcd+2bc−6cd−3c+3)/2,
    F₁=(3acd²+5acd+4ad−12cd−7d+7)/4,
    F₂=3abd−4ab+1,
    F₃=(ab²c+11abc−16ab−b+5)/4.                     (5)

## 4. A small exact rational root certificate

Put

    z=(78886487,79802686,79041001,80384229)/10⁸,
    ρ=10⁻⁶,
    K={x∈ℝ⁴ : |x−z|∞≤ρ}.

All coordinates of K lie in [39/50,81/100]. Define the fixed rational
matrix

    C=(1/1000)[−509   15 −303 −441;
                 27 −465 −426 −286;
               −344 −350 −548    1;
               −324 −298   43 −485].

Let J be the Jacobian of F. Direct rational substitution and absolute
row sums give

    det C=−6734935379/10¹¹≠0,
    |C|∞=317/250,
    |CF(z)|∞<10⁻⁸,
    |I−CJ(z)|∞<1/250.                                (6)

For completeness, exact upper bounds on
Σ_k sup_[0,1]⁴ |∂_k J_ij|, obtained by summing absolute coefficients
of the second-derivative polynomials, form the matrix

    [0    11/2 10   15/2;
     23/4 0    31/4 11;
     10   10   0    6;
     41/4 11   25/4 0].

Its maximum row sum is 55/2. Thus on K,

    |J(x)−J(z)|∞≤(55/2)ρ,
    |I−CJ(x)|∞<1/250+(317/250)(55/2)ρ<1/200.          (7)

The map H(x)=x−CF(x) is consequently a contraction on K, and

    |H(x)−z|∞≤10⁻⁸+ρ/200<ρ.

It maps K into itself. The contraction theorem supplies a unique fixed
point there; invertibility of C makes it a genuine zero of F. This is
an actual existence proof, not a floating-point residual test or an
assumed favorable root. The approximate coordinates that prompted the
certificate were (0.7888648731,0.7980268610,0.7904100147,0.8038422907).
Those decimal approximations are not used as exact strategy parameters.

## 5. All four quiet Quit tests and complete behavioral caps

The literal quiet Quit values for owners 0,1,2,3 respectively are

    T₀=bd+2(1−b)d+(5/4)b(1−d),
    T₁=ac+(3/2)(1−a)c+a(1−c),
    T₂=bd+(7/4)(1−b)d+(5/4)b(1−d)+(1−b)(1−d),
    T₃=ac+(3/2)(1−a)c+(7/4)a(1−c)+(1−a)(1−c).

The two last terms retain the relevant triple payoff one. Define the
four quiet slacks

    S=(P/c−T₀, Q/d−T₁, 1/a−T₂, R/b−T₃).

Exact substitution of z gives S_i(z)>21/200 for every i. Each T_i is
a two-player product expectation of numbers in [0,2], so each of its
two partial derivatives has absolute value at most two. The other term
in each S_i is of the form u/x−v with u≤7/4; on K its derivative has
absolute value at most three. Hence |∇S_i|₁≤7 on K and

    S_i(x)>21/200−7ρ>1/10           for every x∈K.     (8)

At the selected root every active endpoint ties, every quiet Continue
endpoint equals its phase value by (4), and every quiet Quit endpoint
is strictly lower by (8). All sixteen phase/owner/pure-action identities
were separately recovered by enumerating the literal fifteen-row table.

Joint survival per whole cycle is abcd<(81/100)⁴<1, so the bounded
Bellman fixed point (3) is the actual prescribed terminal payoff.
For every unilateral deviator, the OTHER THREE continuation probabilities
have product at most (81/100)³<1 per cycle. Iterating the same endpoint
inequalities through any number of cycles therefore bounds every finite
deterministic response; the bounded unabsorbed remainder vanishes.
It also bounds literal Never. More explicitly, if H_i^A,H_i^B are the
queried owner's nonempty-opponent absorbing contributions and α_i^A,α_i^B
their continuation masses, its Never payoff is

    W_i^A=(H_i^A+α_i^A H_i^B)/(1−α_i^Aα_i^B),

not zero, and the Bellman bound gives W_i^A≤(V_A)_i. The stopping-law
mixture identity then bounds EVERY complete behavioral replacement,
including each independent-copy transformation in Section 1.

Thus this same profile is exact terminal Nash at both live phases.
Its fixed original uniform-equilibrium payoff is V_A, selected before
any accuracy. For orientation only it is approximately

    (1.104794993,1.427043955,1,1.316363316).

The full exploitability is exactly zero. Consequently T(p)=0 at this
actual independent profile, disproving every γ>0 uniform lower bound
for the chosen maximum-test certificate on this table. The argument
does not conclude that those testers are complete on other profiles.

## 6. Source scope, checks, and stopping point

The initial bounded lookup used the clock/order entries in `docs/TOOLKIT.md`
and read the private successor-resampling fixed-weight no-go and the
normal-owner winning-clock resampling account. Their fixed-weight and
marked-contribution boundaries were respected; no marked benefit was
mistaken for a whole-profile gain. Exact source declarations inspected:

- `exists_quittingBehaviorProfile_forall_mem_finiteMenu_payoff_le` in
  `UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdog.lean`:
  fixed finite menus, not automatically these profile-dependent copies.
- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean` and
  `quittingBehaviorDeviationPayoffCap_eq_pureTime` in
  `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`:
  the complete behavioral mixture and cap semantics used above.
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`:
  exact terminal Nash gives its own fixed original uniform payoff.

SymPy rational arithmetic checked (5)–(8), the determinant and matrix
norm bounds, and all sixteen literal endpoint identities. Numerical root
search served only to choose the rational center z; the existence and
full-cap proof is the exact argument above. No new interval toolkit,
checker framework, Lean file, broader table search, or export was made.

This candidate is stopped, and its root certificate is a coverage
calibration for NOETHER's actual four-rate producer. The unaddressed global
question is whether a different table and a genuinely profile-selected
maximum response inequality can give a positive all-law gap. No claim
about that question follows from the failure on this now-solved table.
