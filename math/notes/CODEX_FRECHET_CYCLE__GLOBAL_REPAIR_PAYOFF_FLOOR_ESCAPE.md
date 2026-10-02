# A two-date contraction of global geometric-repair minima below the payoff floor

Author: `CODEX_FRECHET_CYCLE`.

Status: ordinary-mathematics proof draft, awaiting independent mathematical
and source-overlap reviews. No Lean implementation or export. For an
arbitrary canonical four-player table, a global relaxed repair optimizer
whose prescribed payoff is below an own-singleton reward admits the explicit
two-date contraction (T) below. No periodic certificate, small-regret tail,
or exact timing equilibrium is supplied. The payoff-floor conclusion for
positive limiting minima does **not** solve the remaining branch. Its
qualitative analogue already exists for the unrestricted terminal-semantic
maximum-debt carrier; the proposed extra content is the finite-menu
decrement, literal calendar incidence, and relaxed-boundary handling.

## 1. Data, semantics, and the exact finite optimization

Fix four players `I={0,1,2,3}` and an arbitrary reward vector `r(S)` for each
nonempty coalition `S⊆I`. Assume

```text
s_i := r_i({i}),       (s_0,s_1,s_2,s_3)=(1,0,0,0),
|r_i(S)|≤M,            M≥1.
```

Every player independently chooses a stopping law on `ℕ∪{Never}`. At the
first finite stopping date, precisely the players stopping then form the
terminal coalition; all-Never pays zero. A player's unilateral behavioral
deviation is an arbitrary stopping law: on the unique live all-Continue
history, its private randomization is equivalent to such a law. In
particular, its unrestricted payoff cap is the supremum over all pure
finite stopping dates and Never. Write

```text
U_i(p) = prescribed terminal payoff,
B_i(p) = unrestricted unilateral payoff cap,
d_i(p) = B_i(p)−U_i(p)≥0,          E(p)=max_i d_i(p).
```

This note concerns terminal regret. It does not by itself assert a uniform
equilibrium or an error/absorption-producing sequence.

For `N≥0`, put `F_N={0,…,N−1,Never}`. All three nonpivot laws `p_1,p_2,p_3`
range independently over the full simplices on F_N. The pivot coordinates
are

```text
μ_0,…,μ_(N−1), λ,ν≥0,       Σ_(t<N) μ_t+λ+ν=1,
0≤α≤λ.
```

When `0<α≤λ`, the literal implementing pivot law is

```text
p_0(t)=μ_t              (t<N),
p_0(N+ℓ)=α(1−α/λ)^ℓ    (ℓ≥0),
p_0(Never)=ν.
```

When `λ=0`, its tail is empty. When `α=0<λ`, the coordinates are relaxed
LP data, not an actual stopping law. They retain the prescribed coalition
law and are approximated by positive α with the same other coordinates.

Here is the complete objective, including the late and Never deviations.
For the pivot, let Q_t be its payoff from Quit t against the three
nonpivots, and let W_0 be its payoff from Never. Put

```text
D_0=∏_(j=1)^3 p_j(Never),             L_0=W_0+D_0,
B_0=max({Q_t:t<N}∪{L_0}),
U_0=Σ_(t<N) μ_t Q_t+λL_0+νW_0.
```

For a nonpivot j, set

```text
a_j=r_j({0}),      b_j=r_j({0,j}),
ρ_j=∏_(ℓ∉{0,j}) p_ℓ(Never).
```

Let π_(j,t) be its payoff from Quit t for `t<N`. Let A_j be its expected
payoff on the event that one of its opponents first stops before N, when
j continues through that period. These are finite polynomial expressions
in the displayed probability coordinates. They are independent of α. Then

```text
U_j=Σ_(t<N) p_j(t)π_(j,t)
      +p_j(Never)(A_j+ρ_j a_j λ),
B_j=max({π_(j,t):t<N}
        ∪{A_j+ρ_j a_j λ, A_j+ρ_j b_j α}).
```

For positive α these are exactly the actual payoffs and unrestricted caps.
This is the geometric-repair formula in
[`GEOMETRIC_COMPRESSION.md`](../archive/GEOMETRIC_COMPRESSION.md), Sections 1–2.
The definitions above extend it continuously to the relaxed α boundary.
In particular every relaxed debt is nonnegative, by positive-α
approximation. Minimize `max_i(B_i−U_i)` over **all** the probability
coordinates just displayed, and denote the result by m_N. Equivalently,
minimize z subject to `0≤z≤2M` and all the displayed cap-minus-payoff
inequalities. Thus m_N is a joint global minimum, not a coordinate minimum
and not a minimum among exact timing Nash profiles.

The coordinate set is compact and the objective is continuous, so a global
optimizer exists. Also `0≤m_N≤2M`. Every relaxed optimizer has `|U_i|≤M`,
because positive-α implementation leaves every U_i unchanged. If its
boundary is `α=0<λ`, choosing a small positive α increases any cap, and
therefore E, by at most `Mα`. Consequently m_N is also the infimum of E
over the literal geometric family at N. The stated compression theorem
identifies this with the infimum over arbitrary pivot laws against the
finite opponents; no stronger completeness hypothesis is used here.

The literal geometric family at N embeds in that at N+1: regard its first
tail atom as an additional finite head atom, and retain the remaining
geometric tail. Passing to infima handles relaxed boundary points. Hence
`m_(N+1)≤m_N`.

## 2. Statement and the root-absorption form

Choose **any** global optimizer at N. Write U for its prescribed payoff
vector and `m=m_N>0`. Define

```text
η=max_i(s_i−U_i)_+.
```

The payoff-floor escape is

```text
m_(N+2) ≤ m_N − η m_N²/(128 M²).                         (T)
```

The useful intermediate statement is stronger in a different direction.
Form the finite two-action quitting root game in which a nonempty root
coalition receives r(S), and all-Continue receives the **actual prescribed
continuation vector U**, not the cap vector B. Let q be any exact mixed
Nash root, with independent Quit probabilities q_i, and put

```text
a(q)=1−∏_i(1−q_i).
```

Then

```text
m_(N+2) ≤ m_N − a(q)m_N²/(32M).                          (R)
```

Every such exact root exists by finite mixed Nash existence. Every one
satisfies `a(q)≥η/(4M)`, which gives (T). All the constructions below use
only this finite root game, the optimizer's actual payoff vector, and a
complete best reply in an explicitly bounded menu. They do not import a
successful tail or a known periodic schedule.

## 3. Exact prefix debt formula and forced absorption

First suppose the chosen optimizer is literally implementable. Prefix one
new date at zero with root q, and shift the complete old profile one date
later on all-Continue. This is an independent product of stopping laws:
each player privately samples its root action and, if it continues, its
old clock. Denote the new profile by p′.

For each i write `c_i=∏_(j≠i)(1−q_j)`, let Q_i be its Quit endpoint at the
root, and let C_i(U) be its Continue endpoint with continuation U. If A_i
is the contribution from a nonempty coalition of quitting opponents,
then `C_i(U)=A_i+c_iU_i`. Exact root Nash gives

```text
U′_i=max(Q_i,C_i(U)),
B′_i=max(Q_i,C_i(U)+c_i d_i),
d′_i=[c_i d_i−(Q_i−C_i(U))_+]_+ ≤c_i d_i.                (P)
```

The cap equality permits a different optimal continuation for each
deviating player; it does not require a common continuation equilibrium.
Every pure date later than zero is Continue at the root followed by the
corresponding pure continuation date, and Never behaves the same way.
Taking suprema proves the formula for unrestricted deviations.

Suppose `s_i−U_i≥η>0`. Against no quitting opponent, its Quit-minus-Continue
gap is `s_i−U_i`. Against a nonempty quitting opponent coalition S the gap
is `r_i(S∪{i})−r_i(S)`, between −2M and 2M. Since also
`0<η≤s_i−U_i≤2M`,

```text
Q_i−C_i(U) ≥ η−4M(1−c_i).
```

If `1−c_i<η/(4M)`, this gap is strictly positive, so exact Nash forces
`q_i=1` and therefore `a(q)=1`. Otherwise
`a(q)≥1−c_i≥η/(4M)`. In either case

```text
a(q)≥η/(4M).                                            (A)
```

This is an actual-payoff root calculation. A Nash root against B would
not justify the first equality in (P).

## 4. One exceptional player and a corrective complete reply

If a=0, (R) is just monotonicity, so assume a>0. Choose k with largest
root probability q_k. The union bound gives

```text
a≤Σ_i q_i≤4q_k.
```

For every `j≠k`, its opponent-survival factor obeys
`c_j≤1−q_k≤1−a/4`. Applying (P),

```text
d′_k≤m,                  d′_j≤(1−a/4)m  (j≠k).          (S)
```

Thus the root screens every debt except possibly one. Choose a complete
best reply τ_k to p′_-k; its existence in a bounded menu is proved in
Section 5. Change only player k's whole law to

```text
p″_k=(1−θ)p′_k+θτ_k,           θ=am/(32M).
```

This is a private mixture, with no cross-player correlation. Since
`0<m≤2M` and `0<a≤1`, we have `0<θ≤1/16`. Player k's cap is unchanged,
and its new prescribed payoff is the same mixture of U′_k and B′_k.
Therefore

```text
d″_k=(1−θ)d′_k≤m−am²/(32M).                              (K)
```

For `j≠k`, changing a single opponent law by total variation at most θ
changes the expected payoff of **every fixed unilateral deviation** by
at most `2Mθ`. The same estimate holds for its prescribed payoff; taking
suprema preserves the cap estimate. Consequently

```text
d″_j≤d′_j+4Mθ≤m−am/8.                                  (O)
```

As `m≤2M`, the drop `am/8` in (O) is at least `am²/(32M)`.
Combining (K) and (O),

```text
E(p″)≤m−am²/(32M).                                      (D)
```

This repairs the exceptional player's entire clock law, not just its
root action. In particular it is not a claim that an arbitrary perturbation
of a root Nash profile remains Nash.

## 5. Unrestricted best replies and literal N+2 incidence

After the root prefix, put `L=N+1`. Every nonpivot law is supported on
`F_L={0,…,L−1,Never}`. The pivot has arbitrary head atoms before L, a
geometric tail starting at L, and possibly Never mass.

For the pivot, against these finite nonpivot laws, every finite date
`t≥L` has payoff `W_0+D_0`, with `D_0` the probability that all its
opponents choose Never. Its Never payoff is W_0, no larger. Thus a full
pivot best reply is attained among `0,…,L`.

For any nonpivot j, the Section 1 formula at cutoff L shows that all late
finite deviation payoffs lie between its Quit-L payoff and its Never
payoff. Explicitly, if the pivot tail parameters there are λ′ and α′,
with `h′=α′/λ′>0`, Quit `L+ℓ` pays

```text
A_j+ρ_j[(1−(1−h′)^ℓ)a_jλ′+(1−h′)^ℓb_jα′].
```

The endpoints are attained by Never and Quit L respectively. The empty
tail case gives the same conclusion directly. Hence **every player has
some complete pure best reply in `{0,…,L,Never}`**. The proof includes
negative spectator and collision rewards, and zero-reach histories cause
no difficulty because these are unconditional pure-deviation payoffs.

Use such a τ_k in Section 4. If `k≠0`, only that nonpivot may acquire a
new atom at L. All three nonpivots now have support in `F_(N+2)`, while
the pivot's first tail atom at L can be made part of its finite head;
the remaining tail is still geometric starting at `L+1=N+2`.

If `k=0`, its mixture changes head atoms, possibly its atom at L, and its
Never mass. At every date strictly greater than L, its old geometric tail
is merely multiplied by `1−θ`; this again is a geometric tail starting
at N+2. All nonpivots were already supported on F_L. Degenerate zero
remaining tail masses are permitted.

Thus p″ belongs literally to the geometric family used in m_(N+2).
No extra truncation, infinite menu extension, or second compression is
needed. Equation (D) proves (R) in the implementable case.

## 6. The relaxed α=0<λ source boundary at the same N+2

Now let the selected global optimizer have `α=0<λ`. For each `ε>0`,
replace α by a sufficiently small positive α_ε, keeping all other
coordinates fixed. Denote its implementing profile by p_ε. It satisfies

```text
U(p_ε)=U exactly,           E(p_ε)≤m+ε.
```

The finite root game against U therefore remains exactly the same. Fix
the same q, a, k and `θ=am/(32M)` throughout; θ uses the relaxed value
m, not the approximate value `m+ε`. Prefix q and make the corrective
complete reply for each p_ε as above. The estimates become

```text
d″_(ε,k)≤(1−θ)(m+ε)≤m−am²/(32M)+ε,
d″_(ε,j)≤(1−a/4)(m+ε)+am/8
         ≤m−am/8+ε                       (j≠k).
```

For every ε the resulting profile is in the **same** geometric family
at N+2, by Section 5; its finite menu index does not depend on α_ε or on
how late its geometric mass is concentrated. It follows that

```text
m_(N+2)≤m−am²/(32M)+ε   for every ε>0.
```

Letting ε decrease to zero proves (R), and then (A) proves (T). This is
a numerical infimum argument. It does not assign an actual law to the
nonliteral boundary, claim attainment of its regret by a literal law, or
use continuity of full regret under a weak limit of clocks.

## 7. Exact consequences, and the unconsumed branch

Because m_N is nonincreasing and nonnegative, it has a limit m_∞. Suppose
`m_∞>0`. At each N choose any global optimizer and let η_N be its largest
own-singleton payoff deficit. Rearranging (T) gives

```text
0≤η_N≤128M² (m_N−m_(N+2))/m_N² →0.                      (F)
```

The right side is independent of which optimizer was chosen. Therefore
the convergence holds uniformly over all global optimizers at N. Every
cluster point U_∞ of their prescribed payoff vectors satisfies

```text
U_(∞,i)≥s_i    for every i.                              (FLOOR)
```

There is also the root version. For any chosen optimizer, let A_N be the
largest absorption mass among exact roots against its prescribed U. The
exact-root set is compact and nonempty, so this maximum exists. From (R),

```text
0≤A_N≤32M (m_N−m_(N+2))/m_N² →0.                         (ROOT)
```

Again the bound is uniform over the choice of global optimizer. This
does not assert that all exact roots against a payoff cluster U_∞ must
be all-Continue: exact-root correspondences need not be lower
hemicontinuous, so a root existing only at the limit need not be
approximated by roots at the source U_N.

Neither (FLOOR) nor (ROOT) proves `m_∞=0`. If `U≥s`, all-Continue is an
exact root; this alone gives a=0 and no decrement. There is no established
lower bound for positive root absorption purely in terms of m_N and the
fixed table on that residual branch. A sequence of merely strict
decreases without such a lower bound would not suffice either.

## 8. Narrow source comparison and requested check

The source route was `docs/TOOLKIT.md`, its literal-prefix cap/debt
transport and renewable maximum-debt entries, followed by only the named
root and minimum declarations needed here. Inspected definitions and
declarations include:

- In `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`:
  `quittingTerminalSemanticPrefix`,
  `quittingTerminalSemanticDebt_prefix_eq_blockAct`,
  `quittingTerminalSemanticDebt_prefix_le`,
  `quittingTerminalSemanticPair_rootThenContinuation`, and
  `isZeroQuittingRootNash_allContinue_iff_singleton_le`.
  These already contain the semantic version of (P), and the exact
  all-Continue payoff-floor test.
- In `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`:
  `exists_quittingNashBellmanPredecessor`, including its imports and use
  of `stageGame.mixed_nash_exists`. This supplies the existing finite
  exact-root existence route; it does not assert the new calendar bound.
- In
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`:
  `nearMinimumTerminalSemantic_exploitabilityAuxiliaryNash_absorptionMass_le_sharp`,
  `minimumTerminalSemantic_exploitabilityAuxiliaryNash_eq_allContinue`,
  `minimumTerminalSemantic_exploitabilitySingletonMargin`, and
  `minimumTerminalSemantic_exploitabilityIs_allContinuePlateau`.
  Their hypothesis is a minimum/floor over the full terminal-semantic
  carrier. In particular the singleton-margin theorem already gives
  `B_i−s_i≥m` at a positive unrestricted maximum-debt minimum, and hence
  `U_i≥s_i`. The qualitative payoff-floor obstruction is not novel here.

The complete note
`CODEX_HAHN__FIXED_CAP_PIN_COORDINATE_DEBT_DROP.md` was read before the
derivation. It uses the actual-payoff root and a cap-pin hypothesis to
drop a fixed positive debt coordinate; it does not give the displayed
all-coordinate two-date LP contraction. The earlier bounded search in
the owned global-calendar note also records the complete readings of
the EULER finite-splice inert-boundary and SPINOZA omitted-clock-minimum
and delayed-escape notes. Their plateau warnings remain applicable.

The proposed content for independent audit is precisely (R), (T), and
their finite relaxed-domain proof, not a new qualitative unrestricted
minimum theorem. Requested checks: the complete cap formula in (P),
the mixed-reply effect on all four debts, the pure response support,
the fixed N+2 incidence at the α=0 boundary, and whether an existing
finite-minimum theorem already includes this quantitative consumer.

Concrete remaining question: can a global repair optimizer in the branch
`U≥s` force a different joint calendar move with a decrement bounded below
on positive m intervals, without supplying a periodic certificate or
already-small-regret tail? This note leaves that question unanswered.
