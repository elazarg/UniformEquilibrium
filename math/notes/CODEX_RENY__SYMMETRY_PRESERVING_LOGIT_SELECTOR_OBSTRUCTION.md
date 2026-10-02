# Symmetry-preserving logit selection fails on the canonical cyclic table

Identity: CODEX_RENY. Complete ordinary mathematical proof draft, not
independently reviewed or Lean-checked. This note tests one approximate
finite-menu selector and stops that symmetry-preserving mechanism. It does
not exclude nonsymmetric logit selection, solve the universal selector, or
propose an export.

## 1. The actual candidate

For a finite timing menu F_N={0,…,N−1,Never}, let f_i(t,p_−i) be the
original expected terminal payoff from pure stopping time t. For τ>0 define

    Λ_i(p)(t)=exp(f_i(t,p_−i)/τ) / Σ_(u∈F_N) exp(f_i(u,p_−i)/τ).

A fixed point p=Λ(p) is Nash for the finite game in which player i
maximizes U_i(p)+τH(p_i), with H(p_i)=−Σ_t p_i(t)log p_i(t).
The map is continuous on the finite product of simplices, so a fixed
point exists by Brouwer. Equivalently, strict concavity of the own entropy
objective gives this unique softmax response.

Every such fixed point satisfies original menu regret

    E_N(p)≤τlog(N+1).                                      (1)

Indeed the regularized comparison with a pure best response gives its
original improvement at most τH(p_i), and 0≤H(p_i)≤log(N+1).
Thus τlog(N+1)≤ε produces a genuine original finite-menu ε-Nash law,
not an exact-menu Nash law in disguise.

When the table is invariant under cyclic permutation of players 1,2,3,
the logit map preserves the subspace p_1=p_2=p_3. This subspace is a
product of two simplices, one for the pivot and one common nonpivot law.
Brouwer therefore also produces a symmetry-preserving logit fixed point.
The tested selector chooses such a point, allowing arbitrary deadlines
and temperatures consistent with (1).

This construction differs from exact finite-menu Nash, optional censoring,
or a stationary hazard ansatz. Every law on F_N is permitted, ordinary
menu error is positive, and the common nonpivot law may be nonstationary.
The theorem below shows that preserving this player symmetry is fatal.

## 2. The table and exact theorem

Use the explicit canonical table independently checked in
[the finite-menu separation note](CODEX_RENY__CANONICAL_EXACT_FINITE_MENU_SEPARATION.md)
at R=2,h=1. It is fully specified here. There are players 0,1,2,3, and
predecessor/successor i⁻,i⁺ are cyclic on 1,2,3. For every nonempty S:

    r₀(S)=1 if 0∈S, and 2 otherwise;
    rᵢ(S)=0                              if i∈S;
           −1                             if i∉S and 0∈S;
           2·1_(i⁻∈S)−1_(i⁺∈S)          otherwise,       i=1,2,3.

Infinite all-Continue pays zero. All coordinates lie in [−1,2] and own
singleton values are (1,0,0,0). Each player independently samples one law
on the nonnegative integer dates plus Never. A deviator may replace its
complete law, including unbounded finite support and Never. No common
random label or observation of another player's private time is allowed.

Write U_i for prescribed payoff, B_i for the unrestricted cap, d_i=B_i−U_i,
and E=max_i d_i. Set

    δ=1/192,              c_sym=1/[48(2+3·192³)]>0.

**Theorem.** For every common law μ on ℕ∪{Never}, and every independent
pivot law ν on the same space,

    E(ν,μ,μ,μ)≥c_sym.                                     (2)

The laws need not be finitely supported, proper, diffuse, or geometric.
They may have arbitrarily large simultaneous stopping atoms. No optimal
response is assumed attained.

Consequently, for every N≥1 and every symmetry-preserving logit fixed
point with τlog(N+1)<c_sym, its pivot late scalar satisfies

    L₀(p)≥c_sym,                                         (3)

although E_N(p)≤τlog(N+1). This includes every choice among the symmetric
fixed points and every choice of deadlines and small temperatures.

## 3. Quiet-pivot accounting retains all collision atoms

Fix μ and put a=μ(Never). In the quiet profile p°=(Never,μ,μ,μ), cyclic
symmetry makes each nonpivot's prescribed payoff equal to one number u°.
Let W° be any nonpivot's payoff from Never against the other two μ laws
and the quiet pivot. Let T_2 be the probability that two independent μ
times tie at a finite date; let T_3 be the corresponding three-way
finite tie probability.

For an active-only first coalition, the sum of the three nonpivot rewards
is one if its size is one or two, and zero if its size is three. Hence

    u°=(1−a³−T_3)/3.                                    (4)

Against a Never deviator the two remaining active clocks are identically
distributed. A unique first quitter gives average reward (2−1)/2=1/2;
a tie gives reward one. Therefore

    W°=(1−a²+T_2)/2.                                    (5)

Subtracting,

    W°−u°=(1−a)²(1+2a)/6 + T_2/2 + T_3/3
           ≥(1−a)²/6.                                  (6)

This is not a no-collision approximation. Simultaneous atoms enter with
nonnegative signs in the inequality used below.

## 4. The pivot's late test bounds all interception of future activity

Let T_0 have law ν, let T_1,T_2,T_3 be independent with law μ, and let
z=ν(Never). In this section a subscripted T_j denotes a stopping time,
not the tie probabilities in Section 3. Order Never after every finite
date. Define

    β=Pr(T_0 finite, T_0≤min(T_1,T_2,T_3),
         and at least one of T_1,T_2,T_3 is finite),
    γ=(1−z)a³.

Thus β counts a pivot interruption of activity that would eventually
occur; γ counts pivot-only absorption when all three active clocks are
Never. The total probability that the pivot joins the first coalition
is β+γ. Since the total absorption probability is 1−za³,

    U₀=2(1−za³)−(β+γ)=2−β−(1+z)a³.                     (7)

Write S(t)=Pr_μ(T≥t), including Never. The pivot's payoff from pure finite
date t is 2−S(t)³, because it earns two if an opponent stops strictly
earlier and one otherwise. As t tends to infinity this approaches 2−a³.
Taking the unrestricted response supremum gives

    d₀≥β+za³,     hence β≤E and za³≤E.                  (8)

Conditioning only on the independently drawn pivot time also gives

    β=Σ_(t finite) ν(t)[S(t)³−a³].                       (9)

The late value in (8) need not be attained at a finite time. Only the
supremum bound is used.

## 5. Pivot punishment can only lower the symmetric prescribed payoff

Couple p=(ν,μ,μ,μ) and p° by the same three active stopping times. Sum
the three nonpivot rewards on each outcome.

- If an active coalition stops strictly before the pivot, the sums agree.
- If the pivot stops before all active finite times, its sum is −3,
  whereas the quiet sum is zero or one.
- If the pivot ties k active players at the first finite date, the sums
  are −(3−k) with the pivot and one without it for k=1,2; both are zero
  for k=3.

Thus the original sum never exceeds the quiet sum. On the event that all
three active clocks are Never and the pivot is finite, it decreases by
exactly three. Cyclic symmetry still makes the three original payoffs
equal to one number u. Consequently

    u≤u°−γ.                                             (10)

This pathwise comparison does not assume independence conditional on a
terminal outcome. It uses the original independent tuple coupling.

## 6. A pure quantile-cut reply escapes almost all pivot punishment

For any 0<η<1, there is a finite pure reply of each nonpivot whose payoff
against p is at least

    W°−4η−3β/η³.                                       (11)

If 1−a≤η, the probability either of its two quiet opponents ever stops
is at most 2η. Since rewards have absolute value at most two, W°≤4η.
Immediate Quit guarantees zero, proving (11) in this case.

Otherwise set F(t)=Pr_μ(T≤t), and choose the first finite t with

    F(t)≥1−a−η.

Such a t exists because the threshold is strictly below the total finite
mass. Minimality, with F(−1)=0, gives

    S(t)=1−F(t−1)>a+η.

Let the deviator Quit at t+1. Under quiet opponents, its payoff differs
from Never only if at least one opponent has a finite time at or after
t+1; the total probability of that event is at most 2η. The payoff
difference is at most two per event, so its quiet payoff is at least
W°−4η.

Adding the actual pivot law can change that finite-reply payoff only if
the pivot stops at or before t. A tie with the deviator at t+1 pays the
deviator zero in both games and does not enter this exception. All payoff
values are in [−1,2], so the decrease is at most 3Pr(T_0≤t).

For every pivot time v≤t, monotonicity and (9) give

    S(v)³−a³≥S(t)³−a³>η³.

It follows that Pr(T_0≤t)≤β/η³, proving (11). Importantly, the reply is
at the date **after** the crossing atom. The proof therefore covers a
large atom jumping over the threshold and does not require a nonatomic
clock or a gap before that atom.

## 7. Uniform symmetric-law gap and the selector failure

From (6), (10), and (11), a nonpivot's full debt is at least

    (1−a)²/6 + (1−z)a³ −4η−3β/η³
      ≥(1−a)²/6+a³−E−4η−3E/η³.                         (12)

For every a∈[0,1],

    (1−a)²/6+a³≥1/24:

if a≤1/2 the first term is at least 1/24, and if a≥1/2 the second
term is at least 1/8. Since E bounds this nonpivot debt, (12) implies

    (2+3/η³)E≥1/24−4η.                                 (13)

Taking η=δ=1/192 proves (2) with the displayed c_sym. This constant is
only a convenient positive witness; it is not optimized.

For a finite-menu canonical profile, every nonpivot's omitted finite
reply has the same payoff as Never, while the pivot's omitted finite
reply is W₀+D₀. Therefore the exact identity is

    E=max(E_N,L₀).

Together with (1) and (2), this proves (3). All stopping times used in
the proof are legal full behavioral deviations. The quantile-cut reply
need not belong to the tested finite menu; the final exact identity
locates the remaining finite-menu failure at the pivot scalar.

## 8. Boundary tests and the successful asymmetric witnesses

For a deterministic common finite clock and quiet pivot, all three
nonpivots quit together. Their prescribed payoff is zero, while Never
against the other two gives one. Thus E=1; large simultaneous atoms do
not falsify the bound.

If μ is all-Never, the pivot debt is z and every nonpivot debt is 1−z.
Hence E=max(z,1−z)≥1/2 for an arbitrary pivot law. The pure Quit-now
response guarantees the nonpivot value zero even if the pivot also stops
at date zero. This checks the all-Never endpoint explicitly.

If μ is geometric with common hazard x∈(0,1] and the pivot is Never,
then T_2=x/(2−x) and T_3=x²/(3−3x+x²). The nonpivot pure-date payoffs
increase to W°, so B_i=W° and

    E=(1+T_2)/2−(1−T_3)/3→1/6 as x↓0.

At x=1/2, E=8/21. Diffuse symmetric clocks therefore do not approach
equilibrium either. These explicit cases are tests, not substitutes for
the arbitrary-law quantile proof.

Exact-rational finite checks covered 300 independently generated common
nonpivot/pivot law pairs, including date-zero atoms and Never. They verified
the interception identity (7), the tie formulas (4)–(5), the prescribed
payoff inequality (10), and 1200 quantile-cut replies at η=1/2,1/4,1/8,
1/192. Separate checks verified a deterministic common clock and all-Never
nonpivots with pivot Never probabilities 0,1/3,1/2,1. All passed. These
checks use the previously inspected exact stage-coalition evaluator in
`gpt/check_example.py`; they are regression evidence, not an independent
proof of the unbounded-law theorem.

In contrast, the independently checked asymmetric cyclic witnesses on
the same table prescribe pivot Never and

    p_i(3k+i−1)=2^(−k−1),    0≤k<K,
    p_i(Never)=2^(−K),       i=1,2,3.

They satisfy E_(3K)=L₀=E=8^(−K). Their finite supports occupy distinct
calendar phases, so p_1=p_2=p_3 is false. The infinite version is exact
behavioral Nash. Thus (2) is a strategy-symmetry obstruction on a solved
table, not a counterexample to equilibrium or approximate selection.

## 9. Named source comparison and remaining mechanism

The route was the canonical finite-menu and finite-profile approximation
entries of `docs/TOOLKIT.md`, followed only to named sources:

- `exists_exactFiniteDeadlineTimingNash` in
  `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineNashExistence.lean`
  supplies exact menu Nash, not small pivot excess. The entropy argument
  above instead produces positive-error finite-menu sources.
- `singlePivot_fullExploitability_eq_max_menuExploitability_scalar` in
  `UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`
  is exactly the final full-debt identity used in Section 7.
- The optional-censor analysis in
  `notes/CODEX_HILBERT__OPTIONAL_CENSOR_NASH_SELECTION.md` and the proper
  pivot-envelope analysis in
  `notes/CODEX_FRECHET_CYCLE__GLOBAL_ENVELOPE_ALL_SELECTOR_COUNTEREXAMPLE.md`
  concern different restricted strategy domains and their exact Nash
  selections. They do not bound all unbounded identical nonpivot laws.
- The canonical exact-menu and periodic examples in
  `notes/CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md` and the
  finite-menu separation note cited above do not by themselves exclude
  symmetric positive-error sources at changing deadlines.
- `gainValue_scaledCyclicWeight_symmetricRow_le` and
  `not_isSupportPerfectRow_symmetricRow` in
  `UniformEquilibrium/Quitting/Cycles/WeightedRowMotionSeparation.lean`
  concern one symmetric hazard root at a specified continuation. The
  current bound covers the entire complete law μ and an arbitrary pivot
  law, with no stationary or fixed-continuation hypothesis.
- `notes/CODEX_FRECHET_CYCLE__WHOLE_LAW_LOGIT_CANONICAL_BOUNDARY.md`
  excludes common-temperature uniform-prior whole-law logit solutions
  in fixed TV neighborhoods of two specified successful witnesses, and
  proves a defective nearest-exact branch under joint deadline/cooling
  scaling. Its conclusions concern all logit solutions in those
  neighborhoods, not all identical nonpivot laws at arbitrary distance.
- `notes/CODEX_FRECHET_CYCLE__TIME_PRIOR_LOGIT_GEOMETRIC_PRODUCER.md`
  produces a successful weighted-logit selection on its already-solved
  geometric table using fixed player-dependent priors. Its final
  portability test excludes certain prior families near the other
  specified periodic witness. Neither statement supplies the complete
  identical-law bound (2), and neither rules out arbitrary remote
  nonsymmetric low-regret branches for the table studied here.

The bounded lookup found no matching complete symmetric-law gap. This
is not a repository-wide or literature-wide novelty claim. The table's
underlying UE and exact-menu separation are not new here.

The tested symmetry-preserving logit mechanism is stopped. A nonsymmetric
logit fixed-point selection with N tending to infinity remains unexcluded,
but no such good branch has been produced. The successful cyclic laws are
approximate Nash; they have not been shown to be exact logit fixed points.
For a fixed N, every zero-temperature limit of logit fixed points is exact
menu Nash by (1) and finite continuity, and VANISH's uniqueness then forces
its bad law. Hence a viable logit branch would have to vary the deadline
and break the three-law symmetry together. This is the precise surviving
question, not an assertion that such a branch exists.
