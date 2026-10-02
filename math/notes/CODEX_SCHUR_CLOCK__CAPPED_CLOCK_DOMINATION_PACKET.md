# Capped-clock deviation domination and quiet extension

Authors: the author of the [source argument](../gpt/CAPPED_CLOCK_DEVIATION_DOMINATION.md);
CODEX_SCHUR_CLOCK (self-contained formulation and source correspondence).
Independent mathematical reviews:
[CODEX_DYNKIN_CLOCK](../feedback/CAPPED_CLOCK_DEVIATION_DOMINATION__BY_CODEX_DYNKIN_CLOCK.md),
[CODEX_SCHUR_CLOCK](../feedback/CAPPED_CLOCK_DEVIATION_DOMINATION__BY_CODEX_SCHUR_CLOCK.md).
The [coordinator review](../feedback/CAPPED_CLOCK_DEVIATION_DOMINATION__BY_CODEX_COORDINATOR.md)
records their combined conclusions and the qualifications incorporated here.
Independent reviews of the complete corrected mathematical text:
[CODEX_CAUCHY](../feedback/CODEX_SCHUR_CLOCK__CAPPED_CLOCK_DOMINATION_PACKET__BY_CODEX_CAUCHY.md),
[CODEX_ALEXANDROV_GATE](../feedback/CODEX_SCHUR_CLOCK__CAPPED_CLOCK_DOMINATION_PACKET__BY_CODEX_ALEXANDROV_GATE.md).

The new statements below are ordinary mathematics. The named existing Lean
declarations are dependencies, not formal verification of the new compiler.

## Exact statement

Let I be a finite nonempty player set. For every nonempty coalition A ⊆ I,
let r(A) ∈ ℝᴵ be its reward vector. The game has a single live state and
independent private Continue/Quit actions. The first nonempty quitting
coalition absorbs the game. Live stages and infinite all-Continue play pay
zero. There are no restrictions on the signs of terminal rewards. Write
s_i = r_i({i}).

Choose a nonempty proper child set S ⊂ I. Its game has the restricted rewards
r_S(A) = (r_i(A))_(i∈S), for nonempty A ⊆ S. Every player outside S will play
Never. For each outsider k choose numbers λ_ki ≥ 0, i ∈ S, satisfying

    (N_k)  s_k ≤ Σ_(i∈S) λ_ki s_i;

    (F_k,A)  s_k − r_k(A) ≤ Σ_(i∈S) λ_ki [s_i − r_i(A)];

    (J_k,A)  r_k(A ∪ {k}) − r_k(A)
                 ≤ Σ_(i∈S) λ_ki [r_i(A ∪ {i}) − r_i(A)],

where F and J range over every nonempty A ⊆ S. When i ∈ A, its summand in J
is zero. No empty-coalition reward is introduced. For a three-player child
and one outsider these are fifteen scalar reward inequalities, in addition
to nonnegativity of the three weights.

**Theorem 1: deviation compiler.** For every independent behavioral child
profile σ, every outsider k, every complete unilateral outside law ν, and
every nonincreasing function f : ℕ ∪ {∞} → [0,1] with f(∞) = 0, there are
explicit legal unilateral child replacements σ_i ∧ ν such that

    U_k^f(ν, σ) − U_k^f(∞, σ)
      ≤ Σ_(i∈S) λ_ki [U_i^f(σ_i ∧ ν, σ_−i) − U_i^f(σ)].       (1)

Here ∞ denotes Never, U^f pays f(t)r(A) when A quits first at finite t, and
σ_i ∧ ν is the law of min(T_i,Z) for independent T_i ∼ σ_i and Z ∼ ν.
Different summands are separate unilateral experiments. Consequently, if
d_i^f is complete response regret and Lσ is the quiet parent lift,

    d_k^f(Lσ) ≤ Σ_(i∈S) λ_ki d_i^f(σ),
    d_i^f(Lσ) = d_i^f(σ)                         (i ∈ S).        (2)

The raw conditions are necessary and sufficient for the corresponding
terminal pathwise inequality for every deterministic child clock tuple and
every deterministic outside deadline, with the same fixed λ_k.

**Theorem 2: terminal relaxation and fixed targets.** Suppose only F and J
hold for each outsider. Let

    p∞(σ) = Pr_σ(T_i = ∞ for every i ∈ S),
    a_k = max(s_k − Σ_(i∈S) λ_ki s_i, 0).

For terminal evaluation,

    d_k(Lσ) ≤ Σ_(i∈S) λ_ki d_i(σ) + a_k p∞(σ).                (3)

If some j ∈ S has s_j > 0, this implies

    d_k(Lσ) ≤ Σ_(i∈S) λ_ki d_i(σ) + (a_k/s_j)d_j(σ).         (4)

Under either all the N,F,J conditions, or F,J together with a positive child
own singleton, every specified child uniform-equilibrium payoff v_S extends
to a parent uniform-equilibrium payoff v satisfying v|S = v_S.

**Theorem 3: a raw four-player existence class.** For I = {0,1,2,3}, if some
three-player deletion satisfies either criterion in Theorem 2, then the
parent game has a uniform-equilibrium payoff. The admission conditions depend
only on the reward table and a finite system of linear inequalities. No
equilibrium, continuation, absorption schedule, or strategically safe child
profile is an admission premise. For rational rewards, finite rational child
laws with any prescribed positive terminal-regret tolerance can be found by
a terminating exact enumeration described below.

## Conjecture-facing change

The prior exact deletion gate requires the omitted player to be untempted on
every quietly lifted profile, through a join-antitone condition and an
unconditional continue floor. Theorem 3 gives a strictly larger sufficient
raw-table class: an outside gain may instead be charged to a child's own
response gain. The arbitrary three-player existence theorem supplies the
child, and the terminal all-errors consumer supplies the parent uniform
payoff. This is a new special-case existence route with an actual-data
adapter, not just a verifier whose strategic source remains unproduced.

A concrete accepted family has the paired singleton matrix and no balanced
singleton cycle of any length, on the parent or its child. All thirty-three
unconstrained nonsingleton coordinates in that family may be fixed first;
the remaining eleven outsider coordinates can always be chosen to pass the
raw criterion. Thus its admission is not defined by the existence of a
desired strategy or certificate. The exact fixture is an illustration of
this family, not the sole existence conclusion.

The general finite-quitting conjecture remains open: some solved tables fail
every deletion LP, and no completeness assertion for this compiler is made.

## Strategic inputs and admission

For the general comparison theorem the supplied child profile is arbitrary;
no equilibrium or absorption property is required. Its output is the actual
min-pushforward response law and the corresponding gain inequality.

For the four-player existence theorem the only new admission data are raw
reward entries, nonnegative weights satisfying the finite inequalities, and,
for the fourteen-row variant, a strictly positive child own singleton. These
are finite numerical conditions. An actual child uniform payoff and its
behavioral profiles are supplied for every restricted three-player table by
`quittingGame_exists_uniformEquilibriumPayoff_threePlayer`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`).
Relabeling the three surviving players by {0,1,2} merely renames the histories,
independent actions, rewards, and deviations.

The child strategies are extended by deterministic Never laws. Parent target
selection uses finite-dimensional compactness and the existing terminal
uniformization consumer. The rational finite-law producer uses the existing
full-cap finite-law approximation theorem. No strategic witness is left
assumed in Theorem 3, and there is no recursion requiring additional sources.
The balanced-spine theorem near the end is an auxiliary sharpness statement;
none of its supplied-spine hypotheses is used to admit the raw class.

## Definitions, information, and payoff modes

A clock is an element of ℕ ∪ {∞}, ordered with ∞ after every finite date.
For a clock tuple T, let τ = min_i T_i. If τ is finite, its first coalition
is A = {i : T_i = τ}; if τ = ∞, the terminal outcome is Never. A law on this
countable clock space is a probability mass function, possibly with infinite
finite support and a positive Never atom. A profile is the product of the
players' separately chosen laws.

This represents every behavioral strategy relevant to payoffs in the game.
Before absorption, the public history at date t is the unique history with
t all-Continue action profiles. A behavioral strategy therefore has a
deterministic sequence of hazards on these histories. Private randomization
is independent across players. Conversely, a clock law μ induces hazard

    q_μ(t) = μ({t}) / Pr_μ(T ≥ t)

when the denominator is positive, with arbitrary hazards on unreachable
histories. After absorption all actions are payoff-irrelevant. The same
correspondence applies to an unrestricted replacement of a player's complete
behavioral strategy. It allows no observation of future private clocks and
requires no public correlation device.

For evaluation f define U_i^f(σ) as the expectation of f(τ)r_i(A), taking
the payoff to be zero on Never. Since the table is finite there is M ≥ 0
with |r_i(A)| ≤ M, so all expectations and response suprema are finite. Put

    B_i^f(σ) = sup_ν U_i^f(ν, σ_−i),
    d_i^f(σ) = B_i^f(σ) − U_i^f(σ),
    E_f(σ) = max_i d_i^f(σ),       D_f(σ) = Σ_i d_i^f(σ).

The supremum ranges over every complete private clock law. Regret is
nonnegative because the original law is allowed. An optimizer is not assumed.
Without a superscript the evaluation is terminal: f(t) = 1 for finite t.

Under the repository convention the quitting date itself is still a live
stage with zero payoff; the absorbing reward starts at the next stage. For
integer H ≥ 1 the H-stage Cesaro evaluation is

    f_H(t) = max(H−t−1,0)/H,       f_H(∞) = 0.

For discount factor β ∈ (0,1), normalized geometric stage weights give
f(t) = β^(t+1). More generally every normalized nonnegative stage weighting
induces a nonincreasing tail weight in [0,1]. Terminal, discounted, and
finite-horizon statements are distinguished throughout.

A vector v is a uniform-equilibrium payoff if for every ε > 0 there are one
profile σ and one integer H₀ ≥ 1 such that, for every H ≥ H₀,

    max_i |U_i^(f_H)(σ) − v_i| ≤ ε,       E_(f_H)(σ) ≤ ε.

The vector v is fixed before ε. The profile and threshold may depend on ε.
Each regret bound quantifies over complete behavioral replacements, not only
the actions or dates displayed by σ.

## Source correspondence

The new content is the finite raw-table criterion for the min-clock deviation
compiler, its quantitative regret bounds, the resulting larger deletion
class, and the strict-triple sharpness proof. The following existing results
are used with their original semantic meanings:

- `quittingBehaviorStoppingLaws_update`,
  `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws`, and
  `quittingBehaviorDeviationPayoffCap_eq_pureTime`
  (`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`) identify
  independent first-outcome laws, literal unilateral replacements, and full
  behavioral caps. The clock construction here uses that same private-law
  model.
- `prod_stoppingLaw_none_mul_singleton_le_terminalDebt`
  (`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`) is the
  existing joint-Never debt estimate. Its proof by late capping is included
  below for completeness; the estimate is not credited as new.
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
  provide the fixed-target sequence consumer and the all-errors existence
  equivalence. Their underlying profile uniformization is
  `quittingGame_isUniformεEquilibrium_of_terminalNash`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean`).
- `exists_finiteDeadlineTimingProfile_approximation` and
  `isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation`
  (`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`)
  approximate actual profiles by finite product laws with simultaneous payoff
  and unrestricted-regret control, including a specified target.
- `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`)
  proves child existence for every three-player reward table; it is not
  reproved or treated as a conjectural input here.
- `QuittingBlockJoinAntitone`, `quittingBlockContinueFloor`,
  `QuittingBlockDispensable`, and
  `quittingGame_exists_uniformEquilibriumPayoff_of_blockDispensable`
  (`UniformEquilibrium/Quitting/Classification/BlockDeletion.lean`) specify
  the exact deletion class used in the strict comparison below.
- `quittingBlockJoinCap` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_vanishingAbsorption`
  (`UniformEquilibrium/Quitting/Classification/BlockDeletionInequality.lean`)
  are the distinct quantitative deletion route; no implication that its
  hypotheses are supplied by the new criterion is used.
- `BalancedSingletonCycleCertificate`
  (`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`) and
  `IsQuittingSingletonEscortEdge`,
  `BalancedSingletonCycleCertificate.escortEdge_of_coarse_bridge`, and
  `BalancedSingletonCycleCertificate.exists_escortCycle`
  (`UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`) provide the
  exact balance fields and arbitrary-period escort necessity used for the
  no-cycle comparison.

These declarations and their relevant statements were inspected directly
after bounded navigation through the frontier and toolkit. No new Lean
declaration, compilation result, or axiom audit is asserted. No external paper
theorem is a premise of this packet. A narrow overlap search in the cited
deletion/terminal neighborhood and the literature transcription lane found
no existing weighted min-clock compiler. The strict mathematical comparisons
below establish the claimed local increment; no worldwide priority or
exhaustive literature-classification assertion is made.

The accompanying [primary-source scope audit](../feedback/QUIET_EXTENSION_CLASSES__SOURCE_SCOPE_BY_CODEX_COORDINATOR.md)
records the original-paper comparison. Solan, *Three-Player Absorbing Games*
(1999), Definitions 3.1–3.2 and Theorem 3.3, is a prior behavioral fixed-target
existence result without a reward-sign restriction; the child existence
claim is accordingly a dependency. Solan and Vieille, *Quitting Games*
(2001), Theorem 1.2, assumes unit own singletons and bounds each quitter's
coalition reward by one. The fixture below violates the latter hypothesis
at coalition {0,2}, where both members receive two. These are bounded
hypothesis and attribution comparisons. Neither paper theorem supplies the
outside min-clock adapter, and neither is substituted for the inspected
Lean child theorem.

## Proof of the compiler and regret bounds

Fix one outsider k and suppress k in λ. For a deterministic child tuple T
and a deadline t, replace Never by t for k. For each i ∈ S make a separate
counterfactual replacing only T_i by min(T_i,t). Let G_k^t(T) be the outside
gain and G_i^t(T) be the corresponding child gain.

For terminal payoff there are five exhaustive cases.

1. If t = ∞, every replacement leaves the tuple unchanged, so all gains vanish.
2. If τ < t, where τ is the original finite child first date, the same
   coalition occurs at the same date in every experiment, so all gains vanish.
3. If τ = t < ∞ with first child coalition A, the outside outcome becomes
   A ∪ {k}, and the i-th child outcome becomes A ∪ {i}. J gives
   G_k^t(T) ≤ Σ_i λ_i G_i^t(T).
4. If t < τ < ∞ with later first child coalition A, the outside counterfactual
   quits alone at t, as does the respective child i in its experiment. The
   gains are s_k−r_k(A) and s_i−r_i(A), and F gives the same bound.
5. If t < ∞ and τ = ∞, the gains are s_k and s_i. N gives the bound.

Conversely, universal terminal pathwise domination recovers N by taking all
child clocks Never and t = 0. Taking exactly A at date 1, all other children
Never, and t = 0 recovers F. Taking exactly A at date 0, all other children
Never, and t = 0 recovers J. This proves the stated characterization. The
same characterization holds for universal expectation domination over
independent laws, because deterministic tuples are among those laws and
the forward implication integrates.

For a general nonincreasing f, all cases except the fourth simply multiply
the relevant inequality by one nonnegative weight. In the fourth case set

    α = s_k − Σ_i λ_i s_i,
    ψ(A) = r_k(A) − Σ_i λ_i r_i(A).

Then α ≤ 0 by N and α−ψ(A) ≤ 0 by F. The evaluated left-minus-right residual is

    f(t)α − f(τ)ψ(A)
      = [f(t)−f(τ)]α + f(τ)[α−ψ(A)] ≤ 0.                (5)

This proves pathwise domination for every such evaluation, including signed
rewards. If each of N,F,J instead has additive violation at most η ≥ 0,
both bracketed residuals in (5) are at most η. Their nonnegative coefficients
sum to f(t) ≤ 1. The evaluated domination then holds with additive η,
not 2η or an error accumulating over dates.

Now take independent T_i with laws σ_i and a clock Z with law ν independent
of the entire tuple. In the i-th experiment, min(T_i,Z) is independent of
T_−i. Its inclusive survival law satisfies

    Pr(min(T_i,Z) ≥ n) = Pr(T_i ≥ n) Pr(Z ≥ n),

so its hazard where survival is positive is
1−(1−q_i(n))(1−q_ν(n)). This proves legality as a private behavioral
replacement, including its Never atom and infinite support. It preserves
the old quit hazards before a deterministic cap date.

Integrate the pathwise comparison over the product law of (T,Z). Bounded
rewards justify expectation and the finite weighted sum. A common Z is only
a proof coupling: each summand has the marginal law of its own distinct
unilateral experiment. This proves (1). Every summand on its right is at
most d_i^f(σ), whether or not a full cap is attained. Since λ_i ≥ 0, taking
the supremum over ν gives the outside part of (2), without moving a supremum
through an expectation.

For a child player, removing deterministic outsider Continue actions leaves
exactly the old live histories and first outcomes, both on path and under
every complete child replacement. Its payoff and response cap are therefore
unchanged. This proves the child identities in (2).

The arguments apply separately to each outsider. No coalition containing two
outsiders can occur on the prescribed path or under a unilateral deviation,
so all such reward entries are unrestricted. If W_k = Σ_i λ_ki and
K = max(1, max_(k∉S) W_k), the coordinate bounds give

    E_f(Lσ) ≤ K E_f(σ),
    D_f(Lσ) ≤ Σ_(i∈S) [1+Σ_(k∉S) λ_ki] d_i^f(σ).       (6)

The additive-violation version gives d_k^f(Lσ) ≤ Σ_i λ_ki d_i^f(σ)+η_k
when the k-th certificate has row violations at most η_k.

## Terminal Never correction and fixed-target proof

With N omitted, all finite-absorption cases of the terminal proof remain
valid. The remaining excess is at most a_k on joint Never when the outside
deadline is finite, and zero when that deadline is Never. Independence and
integration bound its contribution by a_k p∞(σ). The same supremum argument
therefore proves (3).

For any child j, cap its own clock at a finite date L. On every tuple whose
original first outcome is finite, the gain is eventually zero as L tends
to infinity. On joint Never the gain is exactly s_j. The gain is bounded
in magnitude by 2M. Bounded convergence implies that these legal response
gains tend to s_j p∞(σ). Each is at most d_j(σ), hence

    s_j p∞(σ) ≤ d_j(σ).                                (7)

This is the existing joint-Never debt theorem identified above. If s_j > 0,
substitution into (3) proves (4). The resulting maximum-regret factor is

    K = max(1, max_(k∉S) [Σ_i λ_ki + a_k/s_j]).         (8)

The same proof allows a separate positive child singleton j for each outside
row, with the corresponding denominator. A supplied child profile with
p∞(σ) = 0 also removes N without any singleton-sign assumption. Without
one of these protections no vanishing-Never conclusion is used.

For fixed-target transfer, let v_S be a child uniform-equilibrium payoff and
choose ε_m > 0 decreasing to zero. For each m choose a child profile σ_m
delivering v_S with uniform-horizon regret at most ε_m. For one fixed profile
the Cesaro payoff converges to its terminal payoff: f_H(t) tends to one for
every finite t and stays zero at ∞, so bounded convergence applies.
Consequently |U_i(σ_m)−(v_S)_i| ≤ ε_m.

For each fixed complete child deviation, the same convergence applies to its
payoff. Passing to the limit in its finite-horizon Nash inequalities shows
its terminal gain is at most ε_m. Since this argument holds for every
deviation, E(σ_m) ≤ ε_m. It does not exchange a supremum and a limit.

Quietly lift the same σ_m. Either (6) at terminal evaluation or (8) gives
E(Lσ_m) ≤ Kε_m for a constant independent of m. The outside terminal vectors
lie in the compact cube [−M,M]^(I∖S). Choose a subsequence on which they
converge to v_out. The complete parent terminal payoff tends to
v = (v_S,v_out), and its terminal Nash error tends to zero.

The existing fixed-target terminal sequence theorem has precisely the
following content: terminal approximate Nash profiles with errors tending
to zero and terminal payoffs tending to one fixed vector v make v a uniform-
equilibrium payoff. Apply
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` to the
selected sequence. This proves the last assertion of Theorem 2, including
the fourteen-row version. In that version the new uniform horizon threshold
comes from terminal uniformization; the original child's finite-horizon
threshold is not asserted to work for the outside coordinates.

With N retained, (6) also transfers the original selected family's regret
evaluation by evaluation. For each required accuracy one may directly take
a sufficiently accurate child profile and then enlarge its threshold until
the outside Cesaro payoffs are close to its outside terminal vector. Both
routes choose v once before the final accuracy is requested.

For a three-player child the unconditional source theorem supplies v_S and
its profiles for every restricted table. The preceding argument then proves
Theorem 3. This is the complete raw-data-to-UE chain.

## Exact LP certificates and finite-law production

For one outside row write the reward system as Vλ ≥ b, λ ≥ 0, with rows

    Never:     V = (s_i)_i,                  b = s_k;
    future A:  V = (s_i−r_i(A))_i,           b = s_k−r_k(A);
    join A:    V_i = r_i(A∪{i})−r_i(A),      b = r_k(A∪{k})−r_k(A).

It is infeasible exactly when there is a finite vector y with

    y ≥ 0,       Vᵀy ≤ 0,       b·y > 0.               (9)

To see this, let C be the cone generated by the columns of V and the negative
coordinate vectors. Then b ∈ C means exactly Vλ−z = b with λ,z ≥ 0.
The cone is closed: in any conic representation, a dependence among used
generators lets one subtract a scalar multiple of that dependence until a
positive coefficient becomes zero, retaining nonnegative coefficients.
Iteration leaves linearly independent used generators. Each independent
generator cone is closed by the continuous inverse on its linear span,
and there are only finitely many subsets. Thus C is a finite union of closed
cones.

If b ∉ C, let c be a nearest point of C to b and put y = b−c. The nearest-
point inequality applied to each segment from c to a point of C gives
y·(x−c) ≤ 0 for every x ∈ C. Taking x = 0 and x = 2c yields y·c = 0;
hence y·x ≤ 0 for x ∈ C and y·b = |y|² > 0. The negative coordinate
generators force y ≥ 0 and the V columns force Vᵀy ≤ 0. Conversely these
conditions immediately contradict Vλ−z = b. This proves (9).

For rational data a feasible finite linear system has a rational solution:
rational Gaussian elimination for equalities and rational interval choices
in Fourier–Motzkin elimination for inequalities give one. The strict dual
condition can be scaled to b·y ≥ 1, so rational certificates exist on that
side as well. Standard finite rational LP elimination therefore supplies
an exact primal or dual certificate. For the fourteen-row criterion omit
the Never row and retain the explicitly checked positive child singleton.

For a rational three-player-child table passing a criterion, compute the
rational amplification factor K. Given rational tolerance ε > 0, the
following search produces a parent terminal ε-approximate equilibrium.

1. Dovetail integers H ≥ 0 and rational probability denominators. Enumerate
   independent child laws supported on the consecutive menu
   {0,1,...,H−1,∞}.
2. For each law compute each child's pure terminal reply values at every
   date in {0,1,...,H} and at ∞. Their maximum is its full response cap.
3. Accept a child profile with E(σ) < ε/K, and append deterministic Never
   laws for the outsiders.

The reply list is complete: after date H−1, every opponent has either already
quit or selected Never. Thus every finite reply date t ≥ H has the same
terminal value as H. A randomized response is an average of pure-date and
Never responses, so it cannot exceed their supremum. All earlier dates are
explicitly tested. When H = 0, prescribed play is all-Never and the reply
list is {0,∞}. This proof concerns terminal payoffs.

For a fixed menu, payoff and each tested pure reply are finite polynomials
in independent probabilities, with rational coefficients. The full cap is
a finite maximum of these polynomials and is continuous. Existing finite-law
approximation and the child existence theorem give a real finite-menu child
profile with regret strictly below ε/K. Rational density on that same menu,
using the strict margin, gives a rational one. The dovetailed enumeration
therefore terminates. No uniform date bound or efficiency bound is claimed.

For a specified child target, the fixed-target finite-menu theorem supplies
approximants with both payoff and regret control. This gives the same fixed-
target mathematical selection as above. The rational algorithm just described
takes a table and tolerance; it does not assume an oracle for an arbitrary
real target. Arbitrary low-regret profiles without target control are not
used to claim preservation of a previously specified v_S.

## Accepted paired family and strict class comparison

Fix the singleton rewards

    r({0}) = (1,4,0,0),       r({1}) = (4,1,0,0),
    r({2}) = (0,0,1,4),       r({3}) = (0,0,4,1).

Delete player 3 and choose λ = 2e₂. Then N is 1 ≤ 2 and the other fourteen
conditions are exactly

    r_3(A) ≥ 2r_2(A)−1,
    r_3(A∪{3})−r_3(A) ≤ 2[r_2(A∪{2})−r_2(A)],         (10)

for every nonempty A ⊆ {0,1,2}. Every completion satisfying (10) has a
uniform-equilibrium payoff by Theorem 3. For every actual child profile,

    d_3^f(Lσ) ≤ 2d_2^f(σ),
    d_i^f(Lσ) = d_i^f(σ)                  (i = 0,1,2), (11)

for every nonincreasing evaluation f, with all simultaneous child quitting
retained.

There are eleven nonsingleton coalitions and forty-four nonsingleton reward
coordinates. The child has four nonsingleton coalitions, whose three child
coordinates give twelve arbitrary entries. The seven nonsingleton coalitions
containing 3 give another twenty-one arbitrary child-coordinate entries.
After these thirty-three entries are chosen, choose the four passive
player-3 entries on child nonsingletons above their lower bounds in (10).
The three child singleton lower bounds already have slacks 1,1,3. Finally
choose each of the seven player-3 joining entries below its upper bound.
Each is a distinct coordinate, so no constraints conflict. These are all
remaining eleven nonsingleton coordinates.

For comparison, λ = 0 makes the general criterion

    s_k ≤ 0,       s_k ≤ r_k(A),       r_k(A∪{k}) ≤ r_k(A).

The first two are exactly s_k ≤ min(0, min_(∅≠A⊆S) r_k(A)); the last is
join antitonicity. Thus this is precisely `QuittingBlockDispensable` for
the block I∖S. The new class contains the old exact deletion class, and
the fixture below proves that the inclusion is strict.

The fixed singleton-difference matrix Γ_ij = r_i({j})−s_i is

    Γ = [ 0  3 −1 −1;
          3  0 −1 −1;
         −1 −1  0  3;
         −1 −1  3  0 ].

An escort edge i → j requires i ≠ j, Γ_ij ≤ 0, and Γ_ji ≥ 0. No pair has
those signs: reciprocal within-pair entries are both positive and reciprocal
cross-pair entries are both negative. The same is true on every principal
restriction. The existing arbitrary-period escort necessity therefore
excludes every balanced singleton cycle, irrespective of period, repeated
owners, zero-hazard phases, or active subset, both on the parent and its
child. This exclusion depends only on the fixed singleton columns and
holds for the entire family (10).

## Exact boundary tests

### Complete rational positive fixture

The following table uses coalition strings to denote sets of players.

| Coalition | r₀ | r₁ | r₂ | r₃ |
|---|---:|---:|---:|---:|
| 0 | 1 | 4 | 0 | 0 |
| 1 | 4 | 1 | 0 | 0 |
| 2 | 0 | 0 | 1 | 4 |
| 3 | 0 | 0 | 4 | 1 |
| 01 | 2 | 2 | 1 | 2 |
| 02 | 2 | 1 | 2 | 4 |
| 03 | 2 | 0 | 1 | 2 |
| 12 | 0 | 2 | 2 | 4 |
| 13 | 1 | 2 | 0 | 2 |
| 23 | 1 | 1 | 2 | 2 |
| 012 | 1 | 2 | 0 | 0 |
| 013 | 0 | 1 | 0 | −1 |
| 023 | 0 | 0 | 0 | 1 |
| 123 | 0 | 0 | 1 | 0 |
| 0123 | −1 | −1 | −1 | −1 |

For λ = 2e₂ the N slack is 1. In child-coalition order
0,1,01,2,02,12,012, the F slacks are (1,1,1,3,1,1,1), and the J slacks
are (2,2,1,2,3,4,1). For every one-player deletion the own singleton is 1,
the old continue floor is 0, and the old join cap is 2. The exact deletion
gate fails for each player, whereas the new certificate succeeds.

The profile q = (1,2/3,2/3,0) at date zero, followed by Never, is exact
terminal Nash. Its payoffs and complete caps are

    U = B = (13/9, 2, 2/3, 4/3).

For player 0, the immediate reply value is 13/9, every strictly later
finite reply has value 1, and Never has value 8/9. For players 1 and 2,
sure player 0 forces absorption at zero and both action endpoints tie,
at 2 and 2/3 respectively. Player 3 has Continue value 4/3 and immediate
Quit value −2/9; all later replies and Never equal Continue. Randomizing
dates cannot exceed these complete pure-date caps.

There is no pure terminal Nash profile. For every nonempty first coalition
the following membership change has gain at least one:

| First coalition | Profitable membership change | Gain |
|---|---|---:|
| 0 | 2 joins | 2 |
| 1 | 2 joins | 2 |
| 01 | 0 leaves | 2 |
| 2 | 0 joins | 2 |
| 02 | 1 joins | 1 |
| 12 | 0 joins | 1 |
| 012 | 2 leaves | 1 |
| 3 | 0 joins | 2 |
| 03 | 1 joins | 1 |
| 13 | 2 joins | 1 |
| 013 | 0 leaves | 1 |
| 23 | 2 leaves | 2 |
| 023 | 0 leaves | 1 |
| 123 | 1 leaves | 1 |
| 0123 | 0 leaves | 1 |

Every displayed leaving move retains a nonempty first coalition, so hidden
later pure clocks do not affect it. Joining is implemented at the first
date. All-Never admits a solo gain of one. This proves the assertion for
arbitrary deterministic first dates, not only date zero.

The accepted class contains a full reward neighborhood. Under an entrywise
perturbation of radius ρ the N slack changes by at most 3ρ and each F or J
slack by at most 6ρ. Thus ρ < 1/6 preserves the certificate. Membership gains
change by at most 2ρ, so the pure-equilibrium obstruction persists for
ρ < 1/2. The escort signs change by at most 2ρ and therefore persist for
ρ < 1/2 as well. These facts already give a full-dimensional separation
neighborhood with ρ < 1/6; no degree theorem is needed.

### Failure of all deletion LPs on another solved table

For every nonempty A ⊆ {0,1,2,3}, define

    r₀(A) = 1 if 0∈A, and 2·1_(2∈A) otherwise;
    r₁(A) = (2·1_(0∈A)−1)·1_(1∈A);
    r₂(A) = (2·1_(1∈A)−1)·1_(2∈A);
    r₃(A) = 1_(3∈A).

For deletion of 0 the F row at A = {3} has child coefficient vector
(−1,−1,0) and outside bound 1. No nonnegative λ satisfies it. For deletion
of k = 1,2,3, the J row at the full child coalition has coefficient vector
zero and outside bound 1. In each case the single corresponding dual
coordinate y = 1 gives (9), even after the Never row is removed.

The parent nevertheless has exact terminal Nash: player 3 quits at zero
surely, and each of 0,1,2 independently chooses Quit0 or Never with equal
probabilities. The payoff is (1,0,0,1). The sure anchor screens active
players' later responses. For player 0 both immediate action endpoints are
1; for players 1 and 2 both endpoints are 0. Player 3's reward never exceeds
1 and its prescribed action attains 1. Thus all complete caps equal the
payoff. The example proves noncoverage of the raw compiler, not equilibrium
nonexistence. The broader unchanged-child obstruction attached to this table
is not needed as a premise here.

### Dropping the Never protection without a positive singleton

Take a one-player child a with own singleton zero. Let outsider k have
s_k = 1, r_k({a}) = 1, and r_k({a,k}) = 1; all a rewards may be zero.
The F and J rows hold with λ = 0. The child all-Never profile is exact Nash,
but its quiet lift has outside regret one. This falsifies a general
fourteen-row transfer without a positive child singleton or vanishing joint
Never. Inequality (3) remains exact: its correction is one.

### Sparse-calendar cap failure and the consecutive repair

Take two child players a,b. Player a prescribes Never and b quits at date
0 or 2 with probabilities 1/2 each. Set

    r_a({a}) = 1,       r_a({b}) = 0,       r_a({a,b}) = −1,

and let b's payoffs all be zero. Exact terminal reply values for a are

| Reply date | 0 | 1 | 2 | 3 | Never |
|---|---:|---:|---:|---:|---:|
| Value | 0 | 1/2 | −1/2 | 0 | 0 |

Testing only the supported dates 0,2, one final post-calendar date 3, and
Never reports cap zero and misses the true cap 1/2. The failure survives
adding a third child who always plays Never. The finite producer above
uses every date below H and the extra date H, so it includes each gap.
For a sparse implementation one must instead test a representative from
every nonempty initial, intervening, and final gap, in addition to its atoms.

### Exact regression evidence

The [companion checker](../gpt/VERIFY_CAPPED_CLOCK_DEVIATION_DOMINATION.py)
uses standard-library rational `Fraction` arithmetic. Its test functions
verify 25,600 pathwise comparisons on sixteen signed tables and five
evaluations, eighty full-cap transfers, eighty randomized-response
comparisons, fifteen exact recoveries of raw inequalities, twenty
positive-singleton relaxations deliberately violating N, the fixture's exact
slacks and full caps, and the four one-row dual obstructions.

The checker was read before running its functions. Reproduction without
writing its JSON output is:

```sh
python -B - <<'PY'
import runpy
m = runpy.run_path('gpt/VERIFY_CAPPED_CLOCK_DEVIATION_DOMINATION.py',
                  run_name='independent_review')
for name in ('test_fixture', 'regressions', 'boundary_tests',
             'positive_singleton_relaxation', 'unchanged_child_no_go_duals'):
    print(name, m[name]())
PY
```

The sparse-calendar example was separately evaluated exactly, obtaining the
five displayed fractions. All these checks are finite evidence. The
universal behavioral assertions rest on the pathwise proof and the stated
semantic correspondence, not a finite test's presumed class completeness.

## Auxiliary theorem: strict inverse-row sharpness

This theorem concerns an exact balanced singleton strategy class, not the
raw-class admission criterion. It sharpens the limit of continuation-floor
row extensions without requiring or duplicating an active-cycle producer.

Let S = {0,1,2} and T_ij = r_i({j})−s_i. Suppose

    T = [ 0  −b₀  a₀;
          a₁   0 −b₁;
         −b₂  a₂   0 ],

where every a_i,b_i is strictly positive and a₀a₁a₂ > b₀b₁b₂. Then
B = T⁻¹ is entrywise strictly positive; this follows directly from the
cofactor formula, whose numerator entries are positive products a_i b_j,
a_i a_j, or b_i b_j and whose determinant is a₀a₁a₂−b₀b₁b₂.
Put h_j = Σ_i B_ij > 0 and

    C = (b₀b₁b₂)/(a₀a₁a₂) ∈ (0,1).

This pattern also covers every invertible zero-diagonal three-by-three
matrix with strictly positive inverse, up to player relabeling. Indeed a
zero off-diagonal entry of TB = identity forces each row's two off-diagonal
entries to have opposite strict signs, because the corresponding B entries
are positive and an all-zero row is impossible. Using BT = identity gives
the same property for each column. The positive entries therefore form one
three-cycle and the negative entries the reverse cycle. A diagonal cofactor
of the relabeled inverse is a positive product divided by det T, so det T
is positive, giving the stated product inequality.

Consider a one-owner-at-a-time infinite child schedule. At each date n,
only o_n ∈ S may quit, with hazard q_n ∈ [0,1); the other two Continue.
Assume joint absorption, actual terminal continuation vectors v^n for each
suffix, singleton floors v_i^n ≥ s_i for all i,n, and exact owner ties
v_(o_n)^n = s_(o_n) whenever q_n > 0. These hypotheses describe the exact
balanced spine under consideration; no conclusion for approximate ties is
implied. Joint absorption holds at every suffix because every finite prefix
has strictly positive survival.

Let μ^n be the suffix probability distribution of the player whose singleton
first absorbs. It is a probability vector and

    z^n = v^n−s = Tμ^n ≥ 0,       h·z^n = 1.           (12)

The second identity follows from μ^n = Bz^n and Σ_i μ_i^n = 1. The exact
arc equation is

    z^n = q_n T e_(o_n) + (1−q_n)z^(n+1).             (13)

Zero-hazard rows leave z unchanged. Across a positive owner-i row, the i-th
coordinate is zero on both sides because T_ii = 0 and q_n < 1.

Delete zero rows and group successive equal positive owners into blocks.
There must be infinitely many positive rows: otherwise a finite product
of positive survival probabilities would leave positive Never mass. There
cannot be a final infinite block of owner i: suffix absorption would then
give its singleton reward vector as the actual continuation, violating the
floor of the player with T_ji < 0. Thus every block ends at a finite date
and the effective owner changes infinitely often.

At an owner change i → j, the boundary z has z_i = z_j = 0. It is therefore
one of the three vertices e_ℓ/h_ℓ of the simplex (12). The block-i arc,
in coordinate j, implies T_ji ≥ 0 because its starting floor is nonnegative
and the ending coordinate is zero. The next positive j-row, in coordinate i,
implies T_ij ≤ 0. These strict table signs force j = i+1 modulo three.
Hence every spine visits all three vertices in that cyclic order.

Let g_j = r_k({j})−s_k be an outside singleton row and w = gB. The outside
continuation surplus is gμ^n = wz^n. At the three forced vertices it equals
w_j/h_j. Consequently, for every such spine,

    r_k's continuation is at least s_k at every suffix
                  if and only if gT⁻¹ ≥ 0 entrywise.    (14)

Necessity uses visits to all vertices; sufficiency uses z^n ≥ 0 at every
suffix. No best-response interpretation of an isolated floor failure has
been assumed in this equivalence.

For a quantitative response statement, a complete owner-i block begins at
e_(i+1)/h_(i+1) and ends at e_(i−1)/h_(i−1), with indices modulo three.
Let p_i be its total absorption probability and c_i = 1−p_i its survival.
Its merged version of (13), in the two nonzero coordinates, gives

    p_i = 1/[a_(i+1) h_(i+1)],
    c_i = b_(i−1) h_(i−1)/[a_(i+1) h_(i+1)].           (15)

These lie strictly between zero and one: hT is the all-ones row, so
a_(i+1)h_(i+1)−b_(i−1)h_(i−1) = 1. Multiplying the three c_i gives C.
Splitting a block into multiple dates does not change its merged survival.

From an arbitrary initial date, the first block can be partial. Its initial
z lies on the owner-i simplex edge between the entry and exit vertices.
Writing it as θ times the entry vertex plus 1−θ times the exit vertex,
with θ ∈ [0,1], the merged arc has absorption probability θp_i and survival
1−θp_i ≥ c_i. Thus from any starting phase each chosen vertex is reached
after at most one partial and two complete blocks, at a finite date, with
child survival at least C. No bound on the lengths of those blocks or the
zero-hazard gaps is required.

Suppose |r_i(A)| ≤ M for every parent reward entry and each individual child
row hazard is at most δ. Define

    Δ = max_j max(−w_j/h_j,0).

If Δ > 0, wait until a vertex realizing Δ and quit there. Conditional on
reaching that date, the outsider's Continue value is s_k−Δ. Its Quit payoff
differs from s_k only if the one active child also quits, an event of
probability at most δ; the conditional loss is at most 2Mδ. Its conditional
gain is therefore at least Δ−2Mδ. Earlier child absorption is identical under
the prescribed and deviating laws. If this lower bound is positive, multiply
it by the survival lower bound C; otherwise use the nonnegative response
regret. In all cases,

    d_k ≥ C max(Δ−2Mδ,0).                              (16)

The legal deviation is one deterministic deadline depending only on the
given schedule, not on unrevealed clocks. Longer balanced words, additional
zero phases, or finer splits cannot remove a negative inverse-row coordinate
in this exact class. Periodic balanced certificates are included: their
opponent-divergence field gives absorption, and bounded cyclic Bellman
equations equal actual continuation values by iterating one full-period
survival contraction. Thus no additional presumed continuation law is used
when applying the statement to an actual certificate.

Finally, the new F conditions restricted to child singleton coalitions say
g ≥ λT. If B ≥ 0, multiplication gives gB ≥ λ ≥ 0. Hence the capped-clock
criterion cannot repair a negative inverse row on the same strict triple.
Its additional reach comes from accepting child equilibria outside this
balanced-singleton class, as the paired family demonstrates. Conversely,
arbitrary collision rewards can violate J without changing any singleton
floor criterion. No nesting with every other row-extension class is claimed.

## Adapter, semantic consumer, and Lean handoff

The actual-data adapter for Theorem 3 is: restrict a four-player table to a
three-player child, solve one finite raw LP, obtain actual child approximate
equilibria from the unconditional child theorem, and append deterministic
Never. Theorem 1 or 2 controls every complete outside replacement on those
same laws. The terminal all-errors or fixed-target sequence consumer then
produces the parent uniform payoff. For rational tables the consecutive-
calendar enumeration makes the approximate-profile part an explicit
terminating procedure. No favorable root, finite-memory class completeness,
or recursively compatible continuation is supplied as an input.

A narrow formalization can separate four declarations in mathematical order:

1. A raw certificate containing only the nonnegative weights and N,F,J reward
   inequalities, followed by the deterministic first-outcome inequality and
   its necessity witnesses.
2. A min-pushforward law on the extended clock space, its product-survival
   identity, and the integrated unilateral response inequality using the
   actual behavioral-law adapter.
3. Full-regret quiet-lift comparison, the terminal relaxation reusing
   `prod_stoppingLaw_none_mul_singleton_le_terminalDebt`, and fixed-target
   transfer through the existing sequence consumer.
4. The explicit Fin4 raw-class theorem and paired-family instance, consuming
   `quittingGame_exists_uniformEquilibriumPayoff_threePlayer` after relabeling.

No certificate field should assume the desired response bound, a favorable
child equilibrium, a continuation floor, absorption, cap attainment, or the
parent conclusion. The general min-clock proof requires no such field.
The strict-triple auxiliary theorem can be formalized independently using
exact arcs, the normalized simplex, and the existing escort transition lemma;
it does not require redesigning the cycle producer.

Relevant exact regressions are the fifteen pure-clock necessity witnesses,
the signed positive fixture, the all-Never failure without its protection,
and the sparse-calendar missed response. Any implementation should use the
narrow source-file checks and trust checks required by the root policy.
No Lean implementation, compilation, or trust audit is part of this packet.

## Scope and nonclaims

The existence conclusion covers exactly the stated raw sufficient class,
including its fourteen-row positive-singleton variant. Its deviations are
unrestricted behavioral deviations in the original independently randomized
quitting game. This is not a completeness theorem for a bounded controller,
finite calendar, balanced cycle, unchanged-child map, or any universal
strategy grammar. Failure of a primal LP or existence of its Farkas dual
does not imply failure of uniform equilibrium.

The packet does not solve arbitrary four-player quitting games, the full
finite-quitting conjecture, or the general stochastic-game conjecture. It
does not supply a uniform complexity bound for rational search. The
fourteen-row bound is terminal and does not assert the original arbitrary
profile's evaluation-by-evaluation finite-horizon transfer. The inverse-row
sharpness theorem requires exact balanced spines and supplies no stability
theorem for approximately balanced ones. Existing three-player existence,
joint-Never debt, terminal uniformization, and finite-law approximation are
dependencies, not new theorem claims.
