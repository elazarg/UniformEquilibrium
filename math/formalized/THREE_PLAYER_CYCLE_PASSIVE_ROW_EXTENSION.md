# Three-player cycle inheritance from singleton row cones

## Exact statement

Let I be a finite player set and let r assign a real vector r(A) ∈ ℝ^I to
every nonempty subset A ⊆ I. In the live state, every player simultaneously
chooses Continue or Quit. The stage payoff is zero while live. The first
nonempty quitting coalition determines the absorbing state, whose payoff
vector r(A) is received at every subsequent stage. Perpetual Continue, also
called Never, pays zero. Randomization is independent and private. A unilateral
deviation may replace a player's complete behavioral strategy, without any
restriction on time, memory, or dependence on the public history.

Define, with receiver i indexing rows and singleton owner j indexing columns,

    s_i = r_i({i}),           Γ_ij = r_i({j}) − s_i.

Thus Γ_ii = 0. For a specified three-element subset S ⊆ I put T = Γ_SS.
Every matrix inequality below is entrywise.

**Theorem 1, raw-table sufficient class.** Suppose

    T is invertible,         T⁻¹ ≥ 0,
    Γ_kS T⁻¹ ≥ 0             for every k ∈ I \ S.              (H)

Then there is one vector v ∈ ℝ^I such that for every ε > 0 there are one
behavioral profile σ and an integer H₀ ≥ 1 satisfying, for every H ≥ H₀,
every i ∈ I, and every behavioral replacement τ_i,

    |γ_i^H(σ) − v_i| ≤ ε,
    γ_i^H(σ[i ← τ_i]) ≤ γ_i^H(σ) + ε.                       (UE)

Here γ^H is expected average payoff over stages 0 through H−1. Every outside
player k ∉ S can use Never in each selected profile. Own-singleton levels
s_i, all nonsingleton rewards, and singleton columns indexed outside S have
no restrictions beyond the displayed conditions on Γ_kS and Γ_SS.

If T⁻¹ > 0, the proof gives an explicit v from singleton data alone and
finite independent stopping laws. For any bound M > 0 on absolute rewards
and terminal tolerance 0 < η ≤ M, these laws have maximum terminal regret at
most η, terminal target error at most η/6, and at most

    K [3 + (4M/η)(t₀+t₁+t₂)]                              (1)

dates, where the positive odds t_i and ρ < 1 are explicit below and K ≥ 1
is any integer with ρ^K ≤ η/(6M). This is O(η⁻¹ log(1/η)) for a fixed
strict input table. Rational reward data give rational laws; choosing rational
M and η makes the entire finite construction use exact rational arithmetic and integer
comparisons. This is a calendar-size estimate, not a bit-complexity estimate.
No such uniform complexity estimate across weak-inverse boundary points is
asserted.

For four players, a necessary condition for absence of a uniform-equilibrium
payoff is therefore: for every triple S with invertible T and T⁻¹ ≥ 0, the
remaining row Γ_kS T⁻¹ has a negative coordinate.

## Conjecture-facing change

The theorem gives a direct reward-table criterion and an actual strategy
producer for a finite-player existence class. Its strict subcase contains a
nonempty open class of four-player singleton matrices with R₀ degree +1,
including arbitrary nonsingleton completions. The exact example and its
integer degree calculation are given below. Thus the criterion applies
within the R₀ degree-one class; degree one alone is not asserted sufficient.

The inverse test produces a three-player cycle, and the nonnegative
row-factorization adapter extends that cycle to all players. The supplied-child
lemma below is an adapter; Theorem 1 supplies
its child data from the literal reward table, so that theorem assumes no
strategic witness.

## Strategic inputs and definitions

Before absorption the public history is uniquely determined by the date:
every previous action was Continue and every previous state was live. A
behavioral strategy therefore determines hazards a_i(t) ∈ [0,1] along this
history. Its private first-quit law on ℕ ∪ {∞} is

    p_i(t) = a_i(t) ∏[u<t](1−a_i(u)),
    p_i(∞) = lim[n→∞] ∏[u<n](1−a_i(u)).

Conversely, a law on ℕ ∪ {∞} is implemented by its conditional hazards
p_i(t)/P(T_i ≥ t) wherever that denominator is positive. The hazards at
unreachable dates are immaterial. Independent private laws implement the
same first-quitter outcome law as behavioral play. After absorption, choices
cannot change rewards. This gives the complete behavioral deviation class,
including any choice of a strategy made separately for each horizon.

For a product of these laws write U_i for terminal expected payoff, with
nonabsorption contributing zero. Write

    B_i = sup[τ_i] U_i(σ[i ← τ_i]),
    E(σ) = max[i∈I](B_i − U_i(σ)).

Thus E is maximum unilateral terminal regret. The estimates are not estimates
for the sum of player regrets. Rewards are bounded because the table is
finite; fix M > 0 with |r_i(A)| ≤ M. No best response need attain B_i.

A **balanced singleton cycle** on a nonempty finite player set J consists of
an integer m ≥ 1, phase owners o(p) ∈ J, hazards 0 ≤ q_p < 1, and vectors
u^p ∈ ℝ^J, with phases p read modulo m, such that

    u^p = q_p r({o(p)}) + (1−q_p)u^(p+1),                 (2)
    u^p_{o(p)} = s_{o(p)},
    u_i^p ≥ s_i                         for all p and i,
    for every i ∈ J, some p has o(p) ≠ i and q_p > 0.     (3)

The last condition is opponent divergence. It implies a positive-hazard
phase and therefore C = ∏[p<m](1−q_p) < 1. It also implies, for every i,

    ρ_i = ∏[p<m, o(p)≠i](1−q_p) < 1.                    (4)

Because 1−q_p > 0, (2) and owner equality imply
u^(p+1)_{o(p)} = s_{o(p)}. Hence an owner is tied at both endpoints of its
phase, including phases with zero hazard.

Theorem 1 produces all required strategic data: S is part of the raw
hypothesis; a labeling, hazards, and child values are derived from T; the
outside weights are Γ_kS T⁻¹; and all ambient values, subdivisions, clocks,
cutoffs, and horizon thresholds are constructed below. There is no assumed
punishment value, selected equilibrium, continuation oracle, public lottery,
return map, or strategic completeness premise. The weak case uses explicitly
constructed nearby tables and compact selection of their prescribed payoff
vectors, not an assumed limiting strategy.

## Source correspondence

The active-cycle construction and its semantic consumers have the following
repository interfaces. The proof below also gives the explicit strategy
construction and the estimates needed for the stated conclusion.

- `RightSingletonCycle`, `rightP`, `rightQ`, `rightR`, `rightS`, `rightT`,
  `rightU`, `rightAlpha`, `rightBeta`, `rightGamma`, and `rightCoarse`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/CyclicCompiler.lean`)
  supply the active construction. With the notation in the proof,
  `(rightP,rightQ,rightR,rightS,rightT,rightU) = (b₀,a₀,b₁,a₁,b₂,a₂)`;
  `(q₀,q₁,q₂) = (rightAlpha,rightBeta,rightGamma)`; and
  `s_S+z^p = rightCoarse p`. The declarations `right_balance_one`,
  `right_balance_two`, `right_balance_three`, `right_coarse_arc`,
  `right_coarse_active`, `right_coarse_floor`, and `right_coarse_contracts`
  establish the corresponding identities and conditions.
  `rightSingletonCycle_isUniformEquilibriumPayoff` consumes this construction
  for three players. Its importing compiler is
  `UniformEquilibrium/Quitting/Cycles/SingletonArcCycle.lean`.
- `BalancedSingletonCycleCertificate` and
  `BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`)
  already cover arbitrary finite ambient player sets and owner maps. Their
  fields are (2)–(3), with a selected initial phase. The same file's
  `BalancedSingletonCycleCertificate.isTerminalNash_and_hasValue` supplies
  exact terminal delivery and full behavioral Nash bounds after subdivision.
  The finite reward table supplies the collision bound automatically.
- `FinFourIntegralTournamentBalancedSingleton.certificate`, `outsiderTail`,
  `outsiderTail_recurrence`, `outsiderTail_pos`, and
  `target_isUniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Classification/LCP/FinFourIntegralTournamentBalancedSingleton.lean`)
  already implement a special three-owner lift. Their source is a literal
  matrix `tournamentSkewMatrix t A` with an integral tournament A and t > 1.
  That special lift does not state the arbitrary nonnegative row adapter.
- `normalizedSoloMatrix_eq_singleton_sub` and
  `QuittingAnchoredCyclicPatienceSystem`
  (`UniformEquilibrium/Quitting/Cycles/AnchoredCyclicPatience.lean`) fix the
  receiver/owner convention and distinguish singleton floors from joining
  inequalities. `quittingGame`
  (`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Game.lean`)
  pays zero at the quitting live stage and the terminal reward thereafter.
- `quittingGame_hasUniformDeviationUpperApproximation`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean`)
  and `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
  are the signed terminal-to-uniform and fixed-payoff semantic endpoints.
  The latter file also contains
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`.
- The degree convention is that of Gowda,
  *Applications of Degree Theory to Linear Complementarity Problems*
  (1993), Section 2, formulas (5), (6), and the R₀ degree definition. The
  [author-hosted original paper](https://userpages.umbc.edu/~gowda/papers/trGOW93-01.pdf)
  gives the componentwise minimum map and support-index sign convention.
  No quitting-game existence claim is taken from that paper.

For comparison, Solan, *Three-Player
Absorbing Games* (1999), Definitions 3.1–3.2 and Theorem 3.3, permits behavioral
strategies and supplies a fixed target with finite-horizon delivery and
deviation caps for every sufficiently large horizon, together with additional
liminf/limsup requirements, without reward-sign restrictions. Its three-player
scope does not supply an ambient outsider adapter.
[Original paper, printed pp. 673–674](https://www.math.tau.ac.il/~eilons/three.pdf).

Solan–Vieille, *Quitting Games* (2001), Theorem 1.2, assumes unit own singletons
and payoff at most one to each player who joins a quitting coalition. Theorem 1
here allows completions violating the latter assumption. The paper's Proposition
2.2 instead requires an additional one-shot root condition; membership in (H)
alone is not asserted to supply that condition.
[Original paper, printed pp. 267 and 270](https://www.math.tau.ac.il/~eilons/quitting19.pdf).
These are hypothesis comparisons; neither paper supplies the row-factorization
adapter proved below.

## Proof

### 1. General nonnegative row inheritance

Let J ⊆ I be nonempty. Restrict r to coalitions and recipients in J, retaining
the same own singletons. Suppose this induced game has a balanced singleton
cycle as defined above. For every k ∉ J suppose a supplied row w_k ∈ ℝ^J
satisfies

    w_k ≥ 0,               Γ_kJ = w_k Γ_JJ.               (5)

Then the same owners and hazards form an ambient balanced singleton cycle,
with the original child values and

    z^p = u^p − s_J,
    v_k^p = s_k + w_k z^p                 for k ∉ J.      (6)

Indeed subtracting s_J from (2) gives

    z^p = q_p Γ_JJ e_{o(p)} + (1−q_p)z^(p+1).

Multiply by w_k, use (5), and add s_k. This is exactly the ambient reward
recursion (2) in coordinate k. The child floors imply z^p ≥ 0, so (6)
supplies the outside floor. Child owner equalities and opponent divergence
are unchanged. Choose any i ∈ J; its divergence condition supplies a
positive-hazard phase. For every outside player that owner is an opponent,
so outside divergence holds too. All ambient cycle fields are thus proved.
Weights need not sum to one. Own singletons and Never were not strategically
translated: the calculation uses differences from s only as algebra.

The compiler proved in Parts 4–6 gives (UE) for this supplied ambient cycle.
This lemma needs neither invertibility nor three child players. Its child
cycle is an explicit hypothesis; the raw theorem removes that hypothesis by
the following construction.

### 2. Strict inverse test and the existing active cycle

Assume T⁻¹ > 0 and set B = T⁻¹. An off-diagonal equation in TB = I is a
zero positive-weighted sum of the two off-diagonal entries in a row of T.
The row cannot vanish, so those entries are nonzero with opposite signs.
Equations in BT = I give one positive and one negative entry in each column.
The positive entries form a fixed-point-free permutation of three labels,
which is a three-cycle. After relabeling S as 0,1,2,

    T = [ 0   −b₀   a₀;
          a₁   0   −b₁;
         −b₂   a₂   0 ],                 a_i,b_i > 0.

Put Δ = a₀a₁a₂ − b₀b₁b₂. This is det T, and B₀₀ = b₁a₂/Δ > 0,
so Δ > 0. Conversely the inverse is

    T⁻¹ = Δ⁻¹ [ b₁a₂  a₀a₂  b₀b₁;
                 b₁b₂  a₀b₂  a₀a₁;
                 a₁a₂  b₀b₂  b₀a₁ ],

which is strictly positive when Δ > 0. This proves the exact strict-inverse
characterization used to access the existing active construction.

Set A_i = a_i/b_i, P = A₀A₁A₂ > 1, and

    D₀ = 1+A₁+A₀A₁,    D₁ = 1+A₂+A₁A₂,    D₂ = 1+A₀+A₂A₀,
    t_i = (P−1)/D_i,    q_i = t_i/(1+t_i),    c_i = 1/(1+t_i).

All q_i,c_i lie strictly between zero and one. Direct factoring gives

    1+t₀ = A₁D₂/D₀,    1+t₁ = A₂D₀/D₁,    1+t₂ = A₀D₁/D₂,
    t₀ = A₂q₁,         t₁ = A₀q₂,         t₂ = A₁q₀,
    C = c₀c₁c₂ = 1/P < 1.                                (7)

For example q₀ = (P−1)/(A₁D₂), so A₁q₀ = t₂; the other identities
follow from the displayed factorizations, and their product gives C.
These are the rates `rightAlpha`, `rightBeta`, `rightGamma` defined above.

Use owner i in phase i, ordered 0,1,2, and define

    x₀ = a₀q₂,         x₁ = a₁q₀,         x₂ = a₂q₁,
    z⁰ = (0,x₁,0),     z¹ = (0,0,x₂),     z² = (x₀,0,0).

Every x_i is positive. Equations (7) imply

    z^i = q_i T e_i + c_i z^(i+1).                        (8)

For phase zero the nontrivial cancellation is
c₀x₂ = c₀a₂q₁ = q₀b₂; its positive coordinate is x₁ = a₁q₀.
For phase one the cancellation is c₁x₀ = q₁b₀; for phase two it is
c₂x₁ = q₂b₁. Thus all coordinates of (8) have been checked.
The owner has zero surplus both before and after its phase. Adding s_S
proves the child Bellman recursion, owner equalities, and singleton floors.
Every child player has two positive-hazard opponent phases. This produces
the balanced child directly from T.

### 3. Ambient values and exact phase-floor criterion

Under (H), put w_k = Γ_kS T⁻¹ for every k outside S. These weights are
computed from the raw table and satisfy (5). Part 1 constructs the ambient
phase values v^p, with active coordinates s_S+z^p and outside coordinates
s_k+w_kz^p. Fix v = v⁰ before selecting any accuracy.

The phase values are actual terminal values. Iterating their Bellman
recursion around n cycles expresses the initial vector as the sum of the
absorbing reward contributions before those cycles plus Cⁿ times the same
finite vector. The last term tends to zero. Therefore the Bellman values
are the infinite-cycle terminal expectations, and |v_i^p| ≤ M.

For this constructed triple the outside phase surpluses are w_{k1}x₁,
w_{k2}x₂, w_{k0}x₀. Because all x_i > 0, the three passive phase floors
hold if and only if w_k ≥ 0. This is exactness for these floors of this
particular child cycle, not necessity for arbitrary ambient equilibrium.

### 4. Subdivision and full behavioral control

The following argument applies to every balanced singleton cycle on I,
including the one produced above. Denote its coarse values by v^p and set
v=v⁰. The renewal argument of Part 3 applies because C<1, so these are actual
terminal values bounded by M. Set t_p = q_p/(1−q_p), choose 0 < δ < 1,
and set N_p = max(1,⌈t_p/δ⌉). During phase p use only its owner, at local
dates l = 0,...,N_p−1, with hazard

    h_{p,l} = q_p/(N_p−lq_p).                              (9)

The denominator is positive. Write d_l = 1−lq_p/N_p. Then
1−h_{p,l} = d_{l+1}/d_l, so the continuation product is 1−q_p. Also
0 ≤ h_{p,l} ≤ t_p/N_p ≤ δ. The coarse hazards and their survival products
are preserved exactly. Let L = ∑[p<m]N_p be the length of a microcycle.

At local date l, the conditional probability of some remaining quit in that
phase is

    f_l = (N_p−l)q_p/(N_p−lq_p),           0 ≤ f_l ≤ q_p.

Writing R = r({o(p)}) and W = v^(p+1), the actual value is
f_l R + (1−f_l)W. For q_p > 0 this is the convex combination with weight
f_l/q_p of the two coarse endpoints q_p R+(1−q_p)W and W. For q_p = 0
both endpoints and every intermediate value equal W. Consequently every
coordinate stays above its singleton and the active owner's value remains
exactly its singleton throughout its block. Denote these periodic values
by V_i(t), with V_i(0) = v_i.

Fix a queried player i. At date t define H_i(t) as the absorbing reward
contribution if i Continues and β_i(t) as the probability that all opponents
Continue. With one scheduled owner j and hazard h, these are 0 and 1 if
j=i, and h r_i({j}) and 1−h otherwise. The preceding equalities give

    V_i(t) = H_i(t) + β_i(t)V_i(t+1).                     (10)

For a quiet player this is the prescribed recursion. For the active owner
it is the equality of its adjacent singleton values. Thus (10) holds for
the queried player's Continue action regardless of its prescribed hazard.

The payoff Q_i(t) from quitting at that date, conditional on every opponent
having survived, equals s_i if i owns the phase. Otherwise

    Q_i(t) = (1−h)s_i + h r_i({i,j})
           ≤ s_i + 2Mδ ≤ V_i(t) + 2Mδ.                  (11)

For the active owner Q_i(t)=V_i(t). Let
b_i(t)=∏[u<t]β_i(u) be opponent survival to date t. Iterating (10) gives

    v_i = ∑[u<t]b_i(u)H_i(u) + b_i(t)V_i(t),
    U_i(Quit at t) = v_i + b_i(t)(Q_i(t)−V_i(t)).         (12)

Equation (4) is the probability that all opponents survive one microcycle,
because subdivision preserves the phase survival products. It is below one.
Boundedness of V_i therefore makes b_i(t)V_i(t) tend to zero. Letting t
increase in (12)'s first identity proves U_i(Never)=v_i, including signed
values. Equations (11)–(12) bound every finite quitting-date response by
v_i+2Mδ. Every behavioral replacement is a mixture of those dates and Never,
as proved in the stopping-law representation. Integration gives

    U_i(σ)=v_i,       B_i(σ)≤v_i+2Mδ,       E(σ)≤2Mδ.    (13)

This is a bound against all complete behavioral deviations. There is one
endpoint error at the deviator's quit date; no error is accumulated through
the preceding Continue dates, which satisfy exact equality (10).

### 5. Finite independent clocks and terminal estimates

Retain K ≥ 1 full microcycles and put N=KL. Replace every private clock
at date N or later by ∞, independently for each player. This gives a product
of finite-date-or-Never laws σ^K, with every outside player still Never.
Renewal and (13) give

    U_i(σ^K) = (1−C^K)v_i.                                (14)

Fix any full replacement of player i. Couple each censored opponent clock
to its original clock. If any opponent quits before N, the first-quitting
outcome under that replacement is identical in the two games. Therefore
different outcomes require that every opponent survives to N, an event of
probability ρ_i^K depending only on the opponents. Terminal payoffs differ
by at most 2M on that event. Taking suprema over all replacements yields

    B_i(σ^K) ≤ v_i + 2Mδ + 2Mρ_i^K.

Since |v_i|≤M and C≤ρ_i, with ρ=max_iρ_i<1,

    E(σ^K) ≤ 2Mδ + 2Mρ^K + MC^K ≤ 2Mδ + 3Mρ^K,
    |U_i(σ^K)−v_i| ≤ MC^K.                              (15)

All after-support deadlines and Never remain in B_i. In particular censoring
has not restricted the deviator to the retained support.

For terminal tolerance 0<η≤M, choose δ=η/(4M) and K≥1 with
ρ^K≤η/(6M). Equations (15) give the claimed terminal bounds. Since
N_p≤1+t_p/δ, the three-phase case gives (1). Every hazard (9) and every
finite stopping mass is rational when the singleton data are rational.
K is obtained by successive exact powers of ρ; no logarithm oracle is needed.

### 6. Signed finite-horizon comparison and fixed target

Consider any prescribed laws supported on dates 0,...,N−1 and Never. If
absorption first occurs at t, the H-stage average contribution is

    a_H(t)r_i(A),       a_H(t)=max(H−t−1,0)/H,

and nonabsorption contributes zero. For t<N,
|1−a_H(t)|≤(N+1)/H. Thus prescribed average and terminal payoff differ
by at most M(N+1)/H.

For a pure deviating date t<N, all possible absorption is early, so its
average payoff is at most its terminal payoff plus M(N+1)/H. If t≥N,
the opponents' finite quits remain early; on the event that all opponents
choose Never, the only possible late reward is s_i. When s_i≥0, its average
contribution is at most its terminal contribution, and the same bound applies
using that deadline's terminal payoff. When s_i<0, compare instead with the
Never replacement: the early opponent outcomes agree, and the late singleton
average contribution is nonpositive. Never itself has only early opponent
absorption. Mixing over dates and Never proves, uniformly over all behavioral
replacements,

    γ_i^H(σ[i←τ_i]) ≤ B_i(σ) + M(N+1)/H.

Consequently, for every H≥1,

    γ_i^H(σ[i←τ_i]) − γ_i^H(σ) ≤ E(σ)+2M(N+1)/H.         (16)

The negative-singleton case cannot be proved by comparing a late negative
average with its own negative terminal payoff; the Never comparison above
is essential.

In the strict raw-table case v was chosen in Part 3. Given ε>0, take
η=min(M,ε/2), use Part 5's laws, and choose H₀≥1 with
2M(N+1)/H₀≤ε/2. For H≥H₀, (15)–(16) give regret ≤ε and delivery error
at most η/6+ε/4≤ε. The same selected laws work for every such horizon.
This proves the strict case and proves the balanced-cycle consumer used in
Part 1 without an unproduced strategic input.

### 7. Weak inverse: density, literal table perturbation, and selection

Let B=T⁻¹≥0 and K₀=J₃−I₃, where J₃ is the all-ones matrix. For small
e>0 with e‖BK₀‖<1 in a submultiplicative matrix norm,

    T_e=T−eK₀=T(I₃−eBK₀),
    T_e⁻¹=B+eBK₀B+e²BK₀BK₀B+⋯.                         (17)

The series converges absolutely; multiplication by I₃−eBK₀ telescopes
its finite partial sums, whose remainder tends to zero. Every coefficient
in (17) is nonnegative.

Fix entry (i,j). If B_ij>0 or (BK₀B)_ij>0, (17) is positive there.
Otherwise the supports of row i and column j of B are nonempty, and

    0=(BK₀B)_ij=∑[u≠v]B_iu B_vj

forces both supports to equal one singleton {k}. There is a positive entry
B_uv with u,v≠k: otherwise both rows outside k would be supported only in
column k and would be linearly dependent. The term

    B_ik (K₀)_ku B_uv (K₀)_vk B_kj > 0

occurs in BK₀BK₀B. Thus T_e⁻¹>0 for every sufficiently small e>0.
The diagonal is unchanged, T_e→T, and invertibility follows from (17).

Keep the original weights w_k=Γ_kS B fixed. Define the perturbed singleton
comparison table by its S-by-S block T_e, outside rows
Γ_kS^e=w_kT_e, and unchanged columns outside S. Keep all s_i and all
nonsingleton rewards fixed, and reconstruct singleton rewards as
r_i^e({j})=s_i+Γ_ij^e. Diagonal entries stay zero, so every own singleton
is indeed unchanged. This is a literal reward table converging to r, with

    Γ_kS^e T_e⁻¹=w_k≥0.

It satisfies the strict hypotheses. If d=‖r−r'‖∞, every fixed profile and
every fixed replacement have identical outcome laws under r and r', and
their terminal expected payoffs differ by at most d. Taking suprema and
subtracting prescribed payoffs gives

    |B_i^r(σ)−B_i^{r'}(σ)|≤d,
    |E_r(σ)−E_{r'}(σ)|≤2d.                              (18)

Choose e_n↓0, indexed by n≥1, in the interval where (17) holds. For r^{e_n}, Part 5 produces
finite laws σ_n with terminal regret at most 1/n. In the original game,
E_r(σ_n)≤1/n+2‖r^{e_n}−r‖∞→0. The vectors U^r(σ_n) lie in the compact
cube [−M,M]^I. Select a convergent subsequence with limit v.

For any ε>0, choose one member of that subsequence whose original regret is
at most ε/2 and whose original terminal payoff is within ε/2 of v. It is
supported on some finite number N of dates plus Never. Taking
H₀≥4M(N+1)/ε and using (16) gives regret ≤ε for every H≥H₀; prescribed
delivery error is at most ε/2+ε/4≤ε. Its outside laws are Never. This proves
(UE) with one fixed v, without requiring convergence of strategies or uniform
calendar bounds across n. It completes Theorem 1.

## Exact class example and boundary tests

### An open four-player degree-one class

On I={0,1,2,3}, take

    Γ = [ 0  −1   2  −2;
          2   0  −1   1;
         −1   2   0   1;
         −1   2   2   0 ].

For S={0,1,2}, direct multiplication gives

    T⁻¹=(1/7)[2,4,1; 1,2,4; 4,1,2],
    w₃=Γ₃S T⁻¹=(8,2,11)/7.

Here a_i=2, b_i=1, q_i=c_i=1/2, and the ambient surpluses are

    z⁰=(0,1,0,2/7),    z¹=(0,0,1,11/7),    z²=(1,0,0,8/7).

Thus every real s and every assignment of the 44 nonsingleton reward
coordinates, with singleton rewards r_i({j})=s_i+Γ_ij, have the fixed target

    v=s+(0,1,0,2/7).                                    (19)

For completeness, LCP(Γ,b) means h≥0, Γh+b≥0, and
h_i(Γh+b)_i=0 for every i. The matrix is R₀ if LCP(Γ,0) has only the zero
solution. Define f_b(x)=min(x,Γx+b) coordinatewise on ℝ⁴, and κ(Γ) as
the Brouwer degree of f₀ near its sole zero. For an R₀ matrix, positive
homogeneity and compactness of the unit sphere give ‖f₀(x)‖≥c‖x‖ for
some c>0, using the sup norm throughout. Since ‖f_b−f₀‖∞≤‖b‖∞, bounded right-hand-side homotopies
have no zeros outside one large ball. Homotopy invariance identifies κ with
deg(f_b) there. At a strictly complementary root of support A, the derivative
has active rows Γ and inactive rows of the identity; its determinant is
det Γ_AA. Additivity therefore sums these determinant signs over regular
roots. This is the degree convention in the primary source cited above.

At b=−1, every support of size at least two has the following unique support
candidate. Coordinates and outside slacks use increasing player order.

| Support A | det Γ_AA | Candidate h_A | Outside slack Γ_{Aᶜ,A}h_A−1 |
|---|---:|---|---|
| 01 | 2 | (1/2,−1) | (−7/2,−7/2) |
| 02 | 2 | (−1,1/2) | (−7/2,1) |
| 03 | −2 | (−1,−1/2) | (−7/2,−1/2) |
| 12 | 2 | (1/2,−1) | (−7/2,−2) |
| 13 | −2 | (1/2,1) | (−7/2,1) |
| 23 | −2 | (1/2,1) | (−2,−1/2) |
| 012 | 7 | (1,1,1) | (2) |
| 013 | −7 | (1,1,−1) | (−1) |
| 023 | 2 | (−2,−1/2,−1) | (−11/2) |
| 123 | 2 | (−1/2,1,2) | (−5/2) |
| 0123 | 3 | (5/3,11/3,−7/3,−14/3) | () |

Every entry follows by solving Γ_AA h_A=1 and then multiplying the outside
rows. Empty support has slack −1 and fails. Singleton support cannot solve
its active equation because Γ_ii=0. The sole admissible root is therefore
h=(1,1,1,0), with slack (0,0,0,2).

Every principal determinant of size at least two is nonzero. A nonzero
homogeneous complementary vector with support A of that size would give a
nonzero vector in the kernel of Γ_AA, impossible. Every column contains a
negative entry, which excludes homogeneous singleton support. Thus Γ is R₀.
The unique inhomogeneous root is strictly complementary and det Γ_SS=7>0,
so κ(Γ)=+1.

All these nonzero determinants, negative column witnesses, failure witnesses
for rejected supports, positive accepted coordinates, and positive accepted
outside slack persist in a sufficiently small zero-diagonal neighborhood.
Strict positivity of T⁻¹ and w₃ persists too, by continuity of inversion.
Hence such a neighborhood consists of R₀ degree-one matrices satisfying the
strict theorem. The map between singleton rewards and (s,Γ) is an invertible
linear change of coordinates on the zero-diagonal slice. Allowing s and every
nonsingleton reward to vary gives a nonempty open set in full reward-table
space. Formula (19) applies to the displayed matrix; nearby matrices use their
own target formula from Part 3.

### Bounded comparisons with named classes

The full determinant is 3 and

    Γ⁻¹=(1/3)[ 2, 2,  2,−1;
                5, 2,  8,−4;
               −4,−1, −7, 5;
               −8,−2,−11, 7 ].

Thus this example fails both conditions det Γ<0 and Γ⁻¹≥0.
The principal on {0,3} is
[0,−2;−1,0]. It has no LCP solution at b=(−1,−1), because both slack
coordinates are negative for every nonnegative vector. Its homogeneous
nonnegative inequalities force both coordinates to zero. Thus it is neither
standard Q nor homogeneously feasible. The elementary projective convention
allows either a positive cemetery weight, which rescales to a standard LCP
solution, or zero cemetery weight, which gives a nonzero homogeneous solution.
This explains the named equivalence
`isProjectiveQMatrix_iff_standard_or_homogeneous` and the principal test
`IsProjectiveQBarMatrix`
(`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`):
the full ambient matrix here fails projective Q-bar. This says nothing about
the reward-dependent punishment-normal-principal variant.

The negative-entry graph, with edge i→j when Γ_ij<0, is exactly
0→1, 0→3, 1→2, 2→0, 3→0. A cycle visiting 3 must use 0 immediately
before and after it, so there is no negative Hamiltonian cycle. Therefore the
negative-successor condition in `SignedFourCycleSingletonData`
(`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`)
fails under every relabeling. The two negative entries in the pair {0,3}
also exclude the literal integral-tournament family, whose paired entries
are t and −1 with t>1. These comparisons do not exclude every cyclic
construction or every reward-dependent existence theorem.

### Exact attempted falsifiers

1. **Dropping the outside floor fails.** Use the same active T, s=0, and
   Γ_kS=(−2,0,1), so w_k=(0,−1,0). Its phase-zero surplus is −1. Set
   that player's pair rewards to zero. Its initial Never payoff is −1 but
   quitting immediately pays zero under every subdivision. Its gain is one.
   An arbitrary unchanged child equilibrium therefore cannot replace (H).
2. **A floor alone does not control coarse joining.** With w_k=0, s_k=0,
   and pair rewards equal to R>0, the outside Never value is zero and joining
   a date with active-owner hazard h pays hR. Fixed coarse hazards can give
   positive regret. Equation (9) makes this at most Rδ.
3. **Weak inverse is a genuine boundary.** For
   T=[0,0,1;1,0,0;0,1,0], the inverse is a permutation matrix. For
   0<e<1/2 set a=1−e. The literal perturbation T−e(J₃−I₃) is
   [0,−e,a;a,0,−e;−e,a,0], with determinant a³−e³ and inverse
   (a³−e³)⁻¹[ea,a²,e²;e²,ea,a²;a²,e²,ea]. Multiplication verifies this
   expression and positivity. The equal hazards are (1−2e)/(1−e), tending
   to one as e↓0. The boundary proof uses selection, not uniform calendar
   bounds or a direct substitution of a unit hazard into the strict formula.
4. **The triple test is not exhaustive.** For
   Γ=[0,3,−1,−1;3,0,−1,−1;−1,−1,0,3;−1,−1,3,0], every principal
   triple has one positive reciprocal pair of size 3 and a third vertex with
   both incident comparisons −1. Its determinant is 6; the inverse diagonal
   at that third vertex is −9/6=−3/2. No triple has a nonnegative inverse.
   This excludes the table from (H), without asserting failure of equilibrium.

## Actual-data adapter, semantic consumer, and Lean handoff

The strict source-to-conclusion chain is

    literal reward table and (H)
      → strict inverse sign characterization after relabeling
      → RightSingletonCycle data and its explicit rates/coarse values
      → weights Γ_kS T⁻¹ and the ambient row-inheritance lemma
      → BalancedSingletonCycleCertificate on the full player set
      → its existing fixed uniform-payoff consumer.

Parts 4–6 also give a complete direct strategy proof and quantitative finite
laws for this chain. The weak case additionally uses the zero-diagonal matrix
approximation, the corresponding literal outside-row perturbation, the
2-Lipschitz maximum-regret bound, and compact fixed-payoff selection. The
semantic conclusion is exactly the predicate in
`quittingUniformEquilibriumPayoffConjecture`
(`UniformEquilibrium/Quitting/Conjecture/Basic.lean`), at the original game's
live state. No no-UE contradiction premise or arbitrary-game producer is used.

Natural formalization units are: the zero-diagonal three-by-three strict
inverse characterization; a general extension of a supplied
`BalancedSingletonCycleCertificate` along nonnegative singleton row factors;
their composition for a selected triple; the weak-inverse perturbation and
literal reward adapter; and the exact four-player example. Suggested theorem
shapes quantify directly over a reward table, a three-player embedding, matrix
invertibility and the displayed inequalities. The cycle and continuation
values belong in the constructed output, not in the hypotheses of the raw
theorem. The supplied-child lemma retains its child certificate hypothesis
and is not presented as an arbitrary-game producer.

`RightSingletonCycle` and `BalancedSingletonCycleCertificate` are reusable
dependencies; duplicating their existing compiler is unnecessary for Lean.
For the weak boundary the existing terminal-all-errors or convergent-target
semantic endpoint can consume the constructed profiles. The exact matrix
products, rate identities, and finite support inventory above are useful
rational test instances. Relevant checks are the touched Lean modules and
their dependency closure, plus the repository trust and documentation checks;
no speculative refactor or new trusted axiom is part of this handoff.

## Scope

The result is an explicit sufficient class, including an open four-player
degree-one example and the weak-inverse boundary. It proves neither that
every degree-one matrix has a suitable triple nor that balanced singleton
cycles represent every equilibrium. It does not extend arbitrary child
equilibria unchanged, require nonnegative own singletons, restrict
nonsingleton completions, or use public correlation. The strict target is
explicit; the weak target is selected by compactness.
