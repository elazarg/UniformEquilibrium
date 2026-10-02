# Absorption-weighted forward-packet repair and reward-box reduction

Identity: CODEX_HILBERT. Complete ordinary-mathematics proof draft, not
Lean-checked and not independently reviewed in this assembled form.
It preserves the first response of `gpt/APPROX.md`, whose independent
calculation/source review is
`../feedback/APPROX_WEIGHTED_REPAIR__BY_CODEX_HILBERT.md`.

The result gives equivalent finite-packet producer specifications and an
explicit length-independent repair. It does NOT produce unbounded charge
from arbitrary reward tables or from a hypothetical positive global gap.

## 1. Game, root values, and the two producer assertions

Let I={0,1,2,3}. For every nonempty S⊆I let r(S)∈ℝ⁴, and assume
|r_i(S)|≤M for a fixed M>0. Play stops at the first nonempty quitting
coalition; if everyone Continues forever the payoff is zero. A behavioral
profile is an independent product of four laws on ℕ∪{Never}. Deviations
may replace a player's complete law. Write U_i(p) for the terminal payoff,

    Cap_i(p)=sup_μ_i U_i(μ_i,p_−i),
    P_i=inf_p_−i Cap_i(p).

The opponents in the punishment infimum use independent laws; public
correlation is not included. None of the finite conversion proofs below
requires punishment normality or positive global exploitability.

For a root q∈[0,1]⁴, q_i is the Quit probability. Put

    p_q(S)=∏[i∈S]q_i · ∏[i∉S](1−q_i),
    c(q)=p_q(∅),       a(q)=1−c(q),
    F(q,v)=∑[∅≠S⊆I]p_q(S)r(S)+c(q)v.

Define the opponent product masses p_(q,−i) on subsets of I\{i} analogously,
and write c_−i(q)=p_(q,−i)(∅). The two pure-action payoffs are

    Q_i(q)=∑[T⊆I\{i}]p_(q,−i)(T)r_i(T∪{i}),
    C_i(q,v)=∑[∅≠T⊆I\{i}]p_(q,−i)(T)r_i(T)+c_−i(q)v_i.

Thus F_i=q_iQ_i+(1−q_i)C_i. Let A_i=max(Q_i,C_i), and let
Reg_i(q,v)=A_i(q,v)−F_i(q,v)≥0 be ordinary mixed-root regret.
Support-δ Nash means

    q_i>0 ⇒ A_i−Q_i≤δ,
    q_i<1 ⇒ A_i−C_i≤δ,

for every i. This is an unweighted bound for every supported action.

Fix a number B≥M. An exact forward packet with error δ>0 and charge Q≥0
consists of H≥0, values v_0,…,v_H∈[−B,B]⁴, and roots q_0,…,q_(H−1), with

    v_(t+1)=F(q_t,v_t)                 (0≤t<H),
    q_t support-δ Nash against v_t     (0≤t<H),
    v_t(i)≥P_i−δ                      (0≤t≤H),
    ∑[0≤t<H]a(q_t)≥Q.

The index is outward construction order. Its roots are played in reverse
order if this finite word is used chronologically. No inverse Bellman
evaluation is part of the definition.

Define two assertions for this fixed game:

- EP: there exists ONE finite B≥M such that exact forward packets exist
  for EVERY δ>0 and EVERY Q≥0 in [−B,B]⁴.
- WP: there exists ONE finite B≥M such that for EVERY ε>0 and EVERY Q≥0
  there are H≥0, values y_0,…,y_H∈[−B,B]⁴ and roots q_0,…,q_(H−1) with

      ‖y_(t+1)−F(q_t,y_t)‖∞≤εa(q_t)   (0≤t<H),
      Reg_i(q_t,y_t)≤εa(q_t)          (0≤t<H),
      y_t(i)≥P_i−ε                   (0≤t≤H),
      ∑[0≤t<H]a(q_t)≥Q.

Boxes are chosen before both accuracy and charge. Packets may be unrelated
at different accuracies or charge targets. No infinite compatible sequence
is assumed.

**Theorem.** EP and WP are equivalent. Furthermore EP is unchanged if its
box is required to be exactly [−M,M]⁴.

## 2. Elementary stability facts

If v∈[−B,B]⁴, every coordinate payoff of the finite root game lies in
[−B,B], so F(q,v) lies in the same box. For fixed q,

    F(q,v)−F(q,w)=c(q)(v−w).                         (2.1)

Changing only the continuation changes Q_i by zero and C_i by
c_−i(v_i−w_i). Hence the gap Q_i−C_i changes by at most ‖v−w‖∞.
Both pure-action regrets are positive parts of that gap or its negative,
so the same bound holds even when the best action changes.

For two roots q,q̂, independently couple each pair of Boolean coordinates
so that coordinate i disagrees with probability |q̂_i−q_i|. A union bound
gives joint disagreement at most Σ_i|q̂_i−q_i|. Consequently

    |a(q̂)−a(q)|≤Σ_i|q̂_i−q_i|,
    ‖F(q̂,v)−F(q,v)‖∞≤2BΣ_i|q̂_i−q_i|.             (2.2)

Applying the same coupling only to player i's opponents bounds the change
in each of Q_i and C_i by 2BΣ_(j≠i)|q̂_j−q_j|. Thus the change in their
difference is at most 4BΣ_(j≠i)|q̂_j−q_j|. These are differences of Quit
probabilities; no factor-two PMF ℓ¹ convention is being used.

## 3. Length-independent weighted repair

Fix 0<ρ≤1/8. Suppose a finite input in [−B,B]⁴ satisfies WP's displayed
inequalities with ε=Bρ². Write a_t=a(q_t).

At each original row (q_t,y_t), delete any action whose gap from the best
action is greater than β=Bρ, transferring its mass to the other action.
Call the new root q̂_t. At most one action per player is deleted. If a
deleted action has mass p, ordinary regret gives

    pβ<Reg_i(q_t,y_t)≤Bρ²a_t,

unless p=0, in which case its deletion changes nothing. In either case its
mass is at most ρa_t. Therefore

    |q̂_t(i)−q_t(i)|≤ρa_t,
    Σ_i|q̂_t(i)−q_t(i)|≤4ρa_t,
    â_t:=a(q̂_t)≥(1−4ρ)a_t≥a_t/2.                  (3.1)

All deletions are defined using the ORIGINAL row. Every action subsequently
used either survived that test or is the original best action receiving
transferred mass; its original gap is at most β.

Now set v̂_0=y_0 and recompute exactly by

    v̂_(t+1)=F(q̂_t,v̂_t).

Every value remains in [−B,B]⁴. Let e_t=‖v̂_t−y_t‖∞. Equations (2.1),
(2.2), the input Bellman error, and (3.1) give

    e_(t+1)≤(1−â_t)e_t+B(ρ²+8ρ)a_t
            ≤(1−â_t)e_t+Kâ_t,
    K=B(ρ²+8ρ)/(1−4ρ).

Since e_0=0, induction gives e_t≤K for every t. Because ρ≤1/8,

    K≤17Bρ.                                        (3.2)

This induction remains valid at a_t=0: both input defects are then zero,
the root is unchanged, and no division by that row's charge is made.
Sure absorption also presents no exception.

For any supported action of player i at q̂_t, simultaneous opponent
changes alter its gap by at most 4B·3ρa_t, and changing y_t to v̂_t adds
at most e_t. Thus every retained action has gap at most

    Bρ+12Bρa_t+17Bρ≤30Bρ≤32Bρ.

The payoff-floor estimate is

    v̂_t(i)≥y_t(i)−17Bρ≥P_i−Bρ²−17Bρ≥P_i−32Bρ.

Summing (3.1) proves that the repaired exact packet retains at least half
the original charge. Its support and floor error is at most 32Bρ,
independently of H.

To deduce WP⇒EP, keep WP's fixed box and choose
0<ρ≤min(1/8,δ/(32B)). Request ε=Bρ² and charge 2Q; the repaired packet
has the required support error, floor, and charge. This proves a finite
repair, without any assumption about how the input was obtained.

## 4. Upward translation proves EP⇒WP

Keep EP's fixed B. Given ε>0 and Q≥0, choose
0<δ≤min(1,ε/3), and take its exact support-δ packet of charge at least Q.
Translate every value by the same vector:

    y_t=v_t+2δ·1.

All y_t lie in the fixed box [−B−2,B+2]⁴. Their floors satisfy
y_t(i)≥P_i+δ, and affinity gives the exact policy residual

    y_(t+1)−F(q_t,y_t)=2δa_t·1.                    (4.1)

Fix a player and row, and write α=c_−i(q_t). The translation raises its
Continue payoff by 2δα and leaves Quit unchanged. If Continue is best
after translation, a used Quit action's new gap is at most δ+2δα≤3δ.
Its ordinary regret contribution is at most 3δq_i≤3δa_t.

If Quit is best after translation, ordinary regret is zero when Continue
has zero probability. Otherwise, if the new gap is positive, the old
support inequality implies

    0<Q_i−C_i(q_t,y_t)≤δ−2δα.

This forces α<1/2, so a_t=1−(1−q_i)α>1/2. Ordinary regret is then at
most δ≤2δa_t. A zero gap again gives zero regret. These cases exhaust
pure, mixed, tied, and all-Continue roots.

Thus every ordinary regret is at most 3δa_t≤εa_t; (4.1) has norm at most
εa_t as well. Roots and charge are unchanged. The enlarged box is chosen
once, independently of ε and Q. This proves EP⇒WP.

The equivalence is at the level of all-accuracy producers. It does not
claim a same-tolerance, same-box equivalence for one supplied packet.

## 5. Reduction of EP to the reward box

Suppose EP holds in [−B,B]⁴. If B=M there is nothing to prove. Otherwise
fix δ>0, Q≥0, put η=δ/2, and set

    L=max(0, log((B−M)/η)).

The terminal contribution to F(q,v) lies coordinatewise in [−Ma(q),Ma(q)].
Hence, writing dist∞ for distance to the reward box,

    dist∞(F(q,v),[−M,M]⁴)≤c(q)dist∞(v,[−M,M]⁴).

Along any exact packet this gives

    dist∞(v_t,[−M,M]⁴)
      ≤(B−M)∏[s<t]c(q_s)
      ≤(B−M)exp(−∑[s<t]a(q_s)).                  (5.1)

Request an original packet of support/floor error δ/2 and charge at least
Q+L+1. Let j be the first accumulated-charge crossing of L, or j=0 if
L=0. Since each row charge is at most one,

    ∑[t<j]a(q_t)≤L+1,
    ∑[j≤t<H]a(q_t)≥Q.

By (5.1), coordinatewise projection of v_j onto [−M,M]⁴ changes it by
at most η. Keep all roots from j onward and recompute exact values from
that projected boundary. The reward box is invariant, and (2.1) gives
uniform change at most η at every retained value. Support transfer from
Section 2 and the original floors now give error δ in both requirements.
Charge is unchanged on the retained suffix. Relabeling it from zero proves
EP in [−M,M]⁴. This includes L=0, zero row charge, sure absorption, Q=0,
and a possibly empty retained suffix.

## 6. Exact consumer and unresolved mathematical source

`QuittingFiniteForwardPacket` in
`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`
has precisely EP's finite data, forward orientation, support predicate,
punishment floors, and charge. The declaration
`quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets`
consumes EP to give one fixed uniform-equilibrium payoff against every
unilateral behavioral deviation. Therefore WP is also a sufficient source
for that conclusion, through the finite repair proved here.

The local support-purification ingredients already appear in
`SurvivalCrossingRepair.lean`; finite exact recomputation appears in
`FinitePrefixCompatibility.lean`; absorption-weighted cyclic policy-error
correction appears in `Projective/Lasso.lean`. The independent feedback
records the exact declarations and the distinction from the combined
finite-packet theorem above. No new Lean theorem is claimed.

The substantive question left open is to produce these finite data with
unbounded charge at EVERY positive weighted tolerance, from a given table
in the contrary case of positive full-regret gap and punishment normality.
Arbitrarily large H is insufficient because all rows could have zero charge,
or their total charge could stay bounded. The proof neither excludes that
failure nor constructs the requested source. It changes the equivalent
mathematical requirements on a producer, not the existence status of one.
