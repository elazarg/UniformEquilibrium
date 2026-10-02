# Independent review of capped-clock deviation domination

Reviewer identity: CODEX_DYNKIN_CLOCK.

The claim reviewed is in
[`CAPPED_CLOCK_DEVIATION_DOMINATION.md`](../gpt/CAPPED_CLOCK_DEVIATION_DOMINATION.md),
with mathematical judgment concentrated on Sections 1–7. The complete packet
was read; the balanced-spine sharpness theorem in Section 9 is outside this
review's affirmative verdict.

## Verdict

The exact deterministic-clock characterization and its transfer to every
independent behavioral profile are correct in ordinary mathematics. This is
the substantive theorem: finitely many raw reward inequalities produce a
comparison with separate legal child deviations, for every profile, including
signed rewards, infinite supports, simultaneous quitting and positive Never
mass. No best-response attainment or suffix equilibrium is needed.

The nonincreasing-evaluation extension, multiple-outsider bounds, terminal
Never correction, fixed-target transfer and Farkas alternative are valid
consequences. The finite-search recipe needs one explicit qualification:
its stated reply list is complete for consecutive menus beginning at zero,
but not for an arbitrary sparse calendar. An exact counterexample and repair
appear below. This qualification does not invalidate the existence theorem.

Equation (7), the positive-singleton charge on joint Never mass, is an existing
repository result, not an additional theorem increment. Its independent proof
using late caps is valid. No Lean compilation or axiom check is claimed by this
review; the new capped-clock theorem is not thereby Lean-checked.

## Exact hypothesis and deterministic comparison

Let I be finite, let the nonempty child set S be a proper subset of I, and fix
k outside S. All players outside S prescribe Never. The reward r(A) is an
arbitrary real vector for each nonempty quitting coalition A; live and Never
pay zero. Set s_i = r_i({i}) and fix nonnegative weights λ_i, i in S.

The three raw requirements are

    s_k ≤ Σ_i λ_i s_i;
    s_k − r_k(A) ≤ Σ_i λ_i [s_i − r_i(A)];
    r_k(A ∪ {k}) − r_k(A)
        ≤ Σ_i λ_i [r_i(A ∪ {i}) − r_i(A)],

where the last two hold for every nonempty A contained in S. For a deterministic
child clock tuple T and outside deadline t, compare the outsider's replacement
of Never by t with the separate child replacements T_i ↦ min(T_i,t).

If the original finite first date precedes t, every gain is zero. If it equals
t, the difference is precisely the joining inequality. If t precedes an
original finite first date with coalition A, the gains are s_k − r_k(A) and
s_i − r_i(A), giving the future inequality. If all child clocks are Never and
t is finite, the gains are s_k and s_i, giving the Never inequality. For
t = Never every gain vanishes, including the all-Never tuple.

Conversely, the all-Never tuple with t = 0, the tuple placing A at date 1 with
t = 0, and the tuple placing A at date 0 with t = 0 recover these three types
of inequalities exactly. This proves necessity and sufficiency for this fixed
compiler with these fixed nonnegative weights. Deterministic tuples are
independent laws, so the same equivalence holds if universal expectation
comparison replaces universal pointwise comparison. Neither converse states
necessity for arbitrary cap domination or equilibrium extension.

## Evaluation weights and private implementation

For nonincreasing f taking values in [0,1], with f(Never) = 0, write

    a = s_k − Σ_i λ_i s_i,
    b(A) = r_k(A) − Σ_i λ_i r_i(A).

The only additional temporal calculation is

    f(t)a − f(τ)b(A)
      = [f(t) − f(τ)]a + f(τ)[a − b(A)] ≤ 0

when t < τ < Never. Both coefficients are nonnegative, and both quantities
they multiply are nonpositive. This works for signed rewards; multiplying an
arbitrary signed payoff comparison by different weights would not suffice.
If each raw inequality has violation at most η, the same coefficients sum to
f(t) ≤ 1, so the additive error is η. The remaining cases have the same bound.
The displayed Cesaro formula presupposes a positive horizon H.

Before absorption the public history is the unique all-Continue history of
its length. Thus each complete behavioral strategy supplies a deterministic
sequence of live-history hazards and an independent first-stopping law.
Actions after absorption cannot change payoffs. This establishes why arbitrary
behavioral deviations in this game are covered by the clock formulation.

For an outside law ν, draw Z with law ν independently of the original independent
tuple T. In the i-th counterfactual, min(T_i,Z) is independent of T_-i, since
(T_i,Z) is independent of T_-i. Its inclusive survival probability at date n is

    Pr(min(T_i,Z) ≥ n) = Pr(T_i ≥ n) Pr(Z ≥ n).

Where this is positive, the hazard is 1 − (1 − q_i(n))(1 − q_ν(n)). This is an
ordinary legal behavioral replacement; zero-survival histories can have any
hazard. The construction also retains the product Never atom and requires no
finite-support approximation.

Using one Z in the proof integral does not introduce a public random signal.
Each summand refers to a different unilateral experiment with its correct
product marginal. Bounded rewards justify integration. Each such response gain
is at most its child's complete response debt d_i^f. Since λ_i ≥ 0, taking the
supremum over all ν yields d_k^f ≤ Σ_i λ_i d_i^f without exchanging a supremum
with an expectation or assuming an optimizer exists.

Quiet outsiders have deterministic Continue actions at every live history.
Dropping these coordinates gives exactly the original child history, both
under prescribed play and after a child deviation. Therefore child payoffs
and complete caps are unchanged. For several outsiders, this argument applies
to each separately; a unilateral deviation cannot generate a coalition with
two outsiders. The maximum-regret and total-regret inequalities in Section 4
follow by taking the finite maximum or summing the coordinate inequalities.

## Terminal Never correction and a fixed child target

With only the future and joining inequalities, let

    p∞ = Pr(all child clocks are Never),
    a₊ = max(s_k − Σ_i λ_i s_i, 0).

For terminal payoff, all finite-absorption cases remain protected. The only
possible excess occurs on joint Never, giving

    d_k ≤ Σ_i λ_i d_i + a₊ p∞.

For a child j, capping its own clock at L changes no first outcome once L
exceeds the realized finite absorption time. On joint Never the gain is s_j.
All gains have magnitude at most twice a common reward bound. Bounded
convergence and the complete cap therefore imply d_j ≥ s_j p∞. If s_j > 0,

    d_k ≤ Σ_i λ_i d_i + (a₊/s_j)d_j.

This identifies the full correction, including infinite-support sources and
unattained caps. The division requires s_j > 0. Without that hypothesis or
vanishing joint Never, the fourteen inequalities alone do not imply a quiet
extension: a one-player child with all its payoffs zero, outside solo reward
one, and outside reward one on both child-only and joint quitting coalitions
satisfies the future and joining inequalities with λ = 0. The all-Never child
is exact Nash, while its quiet parent lift has outside debt one.

The fourteen-row positive-singleton variant preserves every specified child
uniform target, a conclusion slightly more explicit than the packet's
terminal-existence wording. Fix a child uniform target v_S and child profiles
σ_m whose delivery and uniform Nash errors tend to zero. For each fixed m and
each fixed behavioral deviation, passage to terminal payoff gives the same
Nash inequality; this proves a terminal bound for all deviations without
interchanging a supremum and a limit. The child terminal payoff approaches
v_S. Apply the corrected debt bound to the same σ_m. The outside terminal
coordinates lie in a fixed finite-dimensional bounded cube, so select a
subsequence on which they converge to v_out. Parent terminal regrets tend to
zero and parent terminal payoffs tend to (v_S,v_out). Fixed-target terminal
acceptance then makes (v_S,v_out) a parent uniform payoff. The target is fixed
before the requested accuracy, and the child laws in every selected quiet
lift are unchanged.

This fourteen-row argument uses terminal uniformization to obtain a horizon
threshold for each chosen profile. It does not assert the evaluation-by-
evaluation finite-horizon debt bound available under all fifteen inequalities,
or retain the original child's finite-horizon error threshold.

If finite child laws are preferred, their approximation must preserve this
specified target as well as regret. The repository's fixed-target finite-menu
equivalence supplies exactly that. Arbitrary low-regret approximants alone
would only prove existence of some child coordinates.

## Sparse-calendar counterexample and finite-search repair

Consider two child players a,b. Player a prescribes Never; player b quits at
date 0 or date 2 with probabilities 1/2 each. Specify a's payoffs by

    r_a({a}) = 1,   r_a({b}) = 0,   r_a({a,b}) = −1.

Player b's payoffs may all be zero. The exact terminal response values for a
are

| Quit date | 0 | 1 | 2 | 3 | Never |
|---|---:|---:|---:|---:|---:|
| Payoff | 0 | 1/2 | −1/2 | 0 | 0 |

The displayed calendar {0,2}, its first final post-calendar date 3, and Never
give maximum zero; the omitted gap date 1 gives the complete cap 1/2. This
counterexample already includes date zero, so adding only zero does not repair
arbitrary sparse menus. A third child with clock Never can be added without
changing it.

A precise repair is to enumerate laws on {0,...,H−1,Never}, and compute replies
at {0,...,H,Never}; use H = 0 for the empty finite prefix. Against such laws all
finite replies at or after H have the same terminal value, since every
opponent has already quit or selected Never. These lists are complete.
Alternatively an arbitrary sparse calendar must include a representative of
each nonempty gap and of the initial and final intervals in its reply list.

On a fixed corrected menu every pure reply value is a finite polynomial in
the prescribed independent probabilities. The full cap is a finite maximum,
hence continuous. Dovetailing H and rational probability denominators therefore
finds a profile below any positive accepted-class tolerance, using finite-law
approximation and the child existence theorem. The argument is a terminating
search for the accepted rational three-player-child class; it supplies no
uniform complexity bound or universal deletion theorem.

## Duality and mathematical increment

The displayed row signs in Vλ ≥ b are correct. If λ,z ≥ 0 give Vλ − z = b,
then any y ≥ 0 with Vᵀy ≤ 0 satisfies b·y ≤ 0. Conversely separation from the
closed finitely generated cone generated by the V columns and negative unit
vectors supplies precisely such a y with b·y > 0 when feasibility fails.
Rational feasibility and rational infeasibility witnesses are ordinary finite
linear-program facts. They refute only this compiler's applicability.

The independent contribution is the raw-table-to-capped-deviation comparison
and its use with unrestricted child equilibria. Integration, taking full
caps, compact target selection, rational density, and Farkas duality are sound
consequences. In particular the positive-singleton Never estimate already
exists as `prod_stoppingLaw_none_mul_singleton_le_terminalDebt` in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`.

The exact declaration and source dependency inventory is recorded in the
[owned notebook](../notes/CODEX_DYNKIN_CLOCK__CAPPED_CLOCK_DOMINATION.md).
