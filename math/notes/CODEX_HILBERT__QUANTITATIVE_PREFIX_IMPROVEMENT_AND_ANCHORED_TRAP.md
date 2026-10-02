# Quantitative one-prefix improvement and an actual anchored trap

Identity: CODEX_HILBERT. Ordinary-mathematics reconstruction of the new-scope
parts of the second response in `gpt/SIGN.md`, SHA-256
`8077f067cddaad3812db6032a07bce16c189e6e73de528d43e3bc196a392297f`.
The complete original review is `../feedback/SIGN__BY_CODEX_HILBERT.md`.
This assembled note is not independently reviewed or Lean-checked.

The first result improves any unequal-debt carrier point by one legal root,
without a prescribed-payoff singleton floor. The second shows that strict
descent from all-Never can nevertheless enter a prefix hull with a positive
regret floor. Neither result excludes a positive GLOBAL minimum or produces
a counterexample to uniform-equilibrium existence.

## 1. Model and exact prefix operation

There are four players. Each nonempty quitting coalition S receives a reward
r(S)∈ℝ⁴ with |r_i(S)|≤R, where R>0. Infinite all-Continue pays zero.
Players use independent laws on ℕ∪{Never}; all unilateral behavioral
replacements are allowed. Let U(p) be the terminal payoff, B(p) the full
response-cap vector, and

    K_r=closure{(U(p),B(p)):p is an actual product profile},
    d_i=b_i−u_i≥0,       E(z)=max_i d_i,
    η(r)=min_[z∈K_r] E(z).

The carrier is compact, lies in [−R,R]⁴×[−R,R]⁴, and is preserved by each
continuous product-root prefix. For q∈[0,1]⁴ put
c=∏_i(1−q_i), α_i=∏_(j≠i)(1−q_j), and s_i=r_i({i}).
Let Q_i(q) be the expected reward when i Quits at the new root. Write

    C_i(q,v)=∑[∅≠S⊆I\{i}]p_(q,−i)(S)r_i(S)+α_i v_i

for Continue, using the opponents' independent product masses. Then

    T_q(u,b)=(u′,b′),
    u′_i=q_iQ_i(q)+(1−q_i)C_i(q,u),
    b′_i=max(Q_i(q),C_i(q,b)).                         (1)

The second branch retains the unrestricted continuation cap, including
Never and arbitrary later responses. Actual input profiles give actual
prefixes; finite input profiles remain finite. A carrier input need not be
attained, and prefixing does not assert otherwise.

## 2. An unconditional unequal-debt improvement

**Theorem.** For every z∈K_r with E=E(z)>0 and m=min_i d_i, there is a
product root q such that

    E(T_qz)≤E−E(E−m)/(16R).                           (2)

No assumption u≥s, punishment normality, or minimality of z is imposed.

First record the auxiliary-root inequality. If q is exact Nash in the
finite root game with continuation v=b−h·1, h≥0, let
J_i=max(Q_i,C_i(q,v)) be its prescribed root payoff. Since
C_i(q,b)=C_i(q,v)+α_i h, the cap in (1) is at most J_i+α_i h. Meanwhile
u′_i=J_i+c(u_i−v_i). Subtracting gives

    d′_i≤c d_i+h(α_i−c).                             (3)

This comparison does not substitute v for the actual tail u.

Put g_i=b_i−s_i and Δ=E−m≥0. Since z belongs to the carrier,
0≤m≤E≤2R and g_i≤2R.

If some g_i≤E/6, select a finite-game Nash root against b−(E/2)·1.
Equation (3) and α_i−c≤1−c give

    E(T_qz)≤E−(E/2)(1−c).

For the selected player, Quit's advantage when all opponents Continue is
κ=E/2−g_i≥E/3. If it Quits surely, 1−c=1. Otherwise Continue is supported,
and comparing the two root endpoints gives

    0≥Q_i−C_i(q,v)≥α_iκ−2R(1−α_i).

The nonempty-opponent terms compare two terminal rewards and are bounded
below by −2R; the possibly out-of-box auxiliary value occurs only in κ.
Thus

    1−c≥κ/(2R+κ)≥E/(6R+E),
    E(T_qz)≤E−E²/[2(6R+E)]≤E−E²/(16R).

Since Δ≤E, this proves (2) in this case.

Otherwise all g_i>E/6. Choose k with d_k=m and let only k Quit, at rate

    t=Δ/(12R+E).

This is a legal probability; if Δ=0 it is zero. For j≠k the Continue-cap
branch exceeds the Quit branch by at least

    (1−t)g_j+t[r_j({k})−r_j({j,k})]
      ≥(1−t)E/6−2Rt=m/6≥0.

For k, Continue also determines its cap because g_k>0. Consequently

    d′_j=(1−t)d_j              (j≠k),
    d′_k=(1−t)m+t g_k.

The inequality t(2R+Δ)≤Δ and g_k≤2R imply d′_k≤(1−t)E. Hence

    E(T_qz)≤(1−t)E
             =E−EΔ/(12R+E)
             ≤E−EΔ/(16R),

proving the theorem. It guarantees a strict improvement when m<E; it need
not guarantee one when all debts tie.

**Corollary.** For every carrier point of positive E,

    E(z)−η(r)≥E(z)[E(z)−min_i d_i(z)]/(16R).           (4)

Indeed T_qz remains in the global carrier. In particular, if η(r)>0 and
some d_i(z)=0, then

    E(z)≥η(r)+η(r)²/(16R).                            (5)

Thus near-minimum debt coordinates approach equality quantitatively. These
are MAX statements; m is the smallest coordinate, not a SUM minimum.

## 3. Strict descent from all-Never can lose future prefix access to zero

Give every quitter reward 1 and every nonquitter reward 2:

    r_i(S)=2−1[i∈S]          for every nonempty S.

The actual all-Never semantic point is e=(0,1), with E(e)=1. Prefix the
independent root q_i=1/2 for all four players. Joint survival is 1/16 and
each opponent-deleted survival is 1/8. The resulting finite actual profile
has

    u_i=2(1−1/16)−1/2=11/8,
    b_i=max(1,2(1−1/8)+(1/8)·1)=15/8,
    E(T_qe)=1/2<1.                                  (6)

Its cap includes a response at the NEW next date, not only the one-date
menu used by the prescribed profile.

Nevertheless all further finite root words from this point, and their
semantic limits, have E≥1/8. To prove this, define the closed set

    C={(u,b)∈[−2,2]⁴×[−2,2]⁴:
          u_i≤b_i, b_i≥15/8 for every i, Σ_i u_i≤7}.

The point (6) lies in C. At any new root y, the two cap endpoints are

    Q_i(y)=1,
    C_i(y,b)=2(1−α_i)+α_i b_i,

so b′_i≥2−α_i/8≥15/8. Every nonempty terminal coalition has total reward
8−|S|≤7, hence Σ_i u′_i≤7(1−c)+cΣ_i u_i≤7. The reward box is invariant.
Finally u≤b implies u′_i≤max(Q_i,C_i(y,b))=b′_i by (1). Therefore
T_y(C)⊆C for EVERY product root y, and every point in C satisfies

    E(u,b)≥(1/4)Σ_i(b_i−u_i)
            ≥(4·15/8−7)/4=1/8.                      (7)

This is not a positive global-gap example. Let player 0 Quit immediately
and everyone else play Never. Its prescribed payoffs and full caps both
equal (1,2,2,2): the owner can earn only 1 by any finite Quit and 0 by
Never, while every other player already receives its maximal reward 2.
It is exact terminal Nash, so η(r)=0.

Define the future-prefix value, allowing the empty word, by

    H(z)=inf_[finite root words w] E(T_wz).

The example proves H(e)=0 but H(T_qe)≥1/8, despite E dropping from 1 to
1/2. This refutes automatic preservation of good future-prefix access by
an arbitrary strict descent. It does NOT refute a carefully selected root,
or a selector minimizing the successor E: a pure singleton root is already
perfect at e. Changing complete strategies is also outside the trapped
prefix class.

## 4. Existing ingredients and remaining boundary

The exact semantic prefix and carrier closure are supplied by
`quittingTerminalSemanticPrefix` and
`quittingTerminalSemanticPrefix_mem_carrier` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
The auxiliary estimate (3) is the scalar-shift specialization of
`quittingTerminalSemanticDebt_prefix_le_auxiliaryNash` in
`UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`.

The earlier `CODEX_HILBERT__GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES.md`
gives a quantitative solo-prefix improvement under u≥s. The two-case
argument above removes that restriction by first handling a small cap
moat through auxiliary Nash. It does not repeat the older all-ties or
harmonic proofs, and does not improve the all-tied strict-interior consumer.

`quittingControllerWordInf_source_le_prefixed` and its bounded-box variant
in `UniformEquilibrium/Quitting/ControllerTester/RenewableBarrierSaturation.lean`
already show that H can only increase under further prefixes: the future
word set becomes smaller. The example supplies an explicit ACTUAL strict
increase while current E falls. Its excluded all-Never seed is available
elsewhere in the global carrier, not in this selected descendant's hull.

The remaining question is to select genuinely good global competitors, or
exclude positive global minima by additional structure. Neither a rule
accepting any strict current descent nor the quantitative unequal-debt
bound alone proves that such a selection exists.
