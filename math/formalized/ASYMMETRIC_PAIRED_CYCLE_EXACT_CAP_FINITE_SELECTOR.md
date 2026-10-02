# Asymmetric paired-cycle equilibria with exact finite response caps

Original mathematical source: the external author of `PAIRED_QUITTING_SELECTOR.md`,
SHA256 `784fb8d61e6818b4e1d21784b89a7472d124f10afa274e4f12d4263701f7a4fa`.
The proof below is self-contained. Independent mathematical reviews:
[CODEX_TARSKI_PREMIUM](../feedback/PAIRED_QUITTING_SELECTOR__BY_CODEX_TARSKI_PREMIUM.md)
and [CODEX_FRECHET_CYCLE](../feedback/CODEX_TARSKI_PREMIUM__ASYMMETRIC_PAIRED_CYCLE_EXACT_CAP_SELECTOR__BY_CODEX_FRECHET_CYCLE.md).
The new class theorem is ordinary mathematics, not a named Lean theorem.

## 1. Full data and theorem

Let I consist of n=2m players, m≥2, partitioned into m disjoint pairs with a
fixed cyclic order. Write p(i) for i's partner. Every nonempty coalition S
pays a fixed finite real vector r(S). Infinite all-Continue pays zero. Players
randomize independently; arbitrary unilateral behavioral strategies are
equivalently complete stopping laws on ℕ∪{Never}. No public randomization
or observation of opponents' future private stopping choices is available.

For every i define s_i=r_i({i}), b_i=r_i({p(i)}), P_i=r_i({i,p(i)}).
Assume

    9/10≤s_i≤11/10,       −1/10≤b_i≤1/10,       19/10≤P_i≤21/10.

For each other pair B={k,l}, also assume

    19/10≤r_i({k}),r_i({l})≤21/10,
    −1/10≤r_i({k,l})≤1/10,
    r_i({i}∪T)≤s_i+1/50        for ∅≠T⊆B.                    (R)

All other reward coordinates are arbitrary. Strict inequalities give a
nonempty open region in the full finite reward space: the conditions for
different recipient coordinates do not conflict, and their center values
1,0,2 with joining rewards 1 supply an interior point.

Theorem. There are hazards 1/100<q_i<1/2 such that the following actual
profile is exact terminal Nash at every live suffix: cycle through the
pairs in the specified order, let just that pair independently Quit using
its q_i, and let every inactive player Continue. Its initial payoff v is
one uniform-equilibrium payoff, with

    s_i<v_i≤21/10.

Let C=∏_i(1-q_i). Keep K≥1 complete cycles and move every later finite
stopping outcome to Never independently. For the resulting finite product
law σ^K, the prescribed values and FULL behavioral caps satisfy

    U_i(σ^K)=(1-C^K)v_i,     B_i(σ^K)=v_i,
    B_i(σ^K)-U_i(σ^K)=C^K v_i.                              (1)

Thus E(σ^K)≤(21/10)(99/100)^(nK). Every table in (R) fails product-low
premiums, and its actual equilibrium payoff strictly dominates all own
singletons; in particular weak singleton payoff exclusion also fails.

## 2. One simultaneous field for every player

For i let h=q_{p(i)} and define

    X_i=s_i+h(P_i-s_i),       Y_i=s_i+h(P_i-b_i)/(1-h).

X_i is the proposed value at its active phase. It obeys

    h b_i+(1-h)Y_i=X_i.                                     (2)

For another pair B={k,l}, with hazards u=q_k,v=q_l, let

    R_i,B=u(1-v)r_i({k})+(1-u)v r_i({l})+uv r_i({k,l}),
    c_B=(1-u)(1-v),            T_i,B(z)=R_i,B+c_B z.

Starting from X_i at i's next active phase, compose the m-1 other pair
maps backward in chronological Bellman order. The result Ψ_i(X_i) is the
proposed continuation immediately after i's active phase. Solve

    H_i(q)=Y_i-Ψ_i(X_i)=0                for every i.         (3)

Here are the face estimates needed for existence. For just one other pair,
write H_i,B=Y_i-T_i,B(X_i). At fixed h this is separately affine in the six
reward inputs (s_i,b_i,P_i,r_i({k}),r_i({l}),r_i({k,l})) and in u,v.
The s_i,P_i coefficients are positive and the other four coefficients
negative throughout the hazard box. Their extrema therefore occur at the
corresponding reward endpoints and at the four u,v corners. Exact arithmetic
gives:

| u | v | Upper bound at h=1/100 | Lower bound at h=1/2 |
| --- | --- | --- | --- |
| 1/100 | 1/100 | −29689/9000000 | 128627/100000 |
| 1/100 | 1/2 | −67811/180000 | 1913/2000 |
| 1/2 | 1/100 | −67811/180000 | 1913/2000 |
| 1/2 | 1/2 | −289/3600 | 51/40 |

At h=1/100, every T_i,B(X_i)>Y_i>X_i. Each T_i,B is increasing.
Repeated application therefore leaves the full composition above Y_i.
Thus H_i<0 on its partner's lower face for ANY number of other pairs.

At h=1/2, X_i≤8/5, while every pair map preserves the upper bound 21/10:
it is a convex combination of its argument and three rewards at most 21/10.
Consequently Ψ_i(X_i)≤21/10, whereas Y_i≥27/10. Thus H_i>0 on the upper
partner face.

The field G_j(q)=(1-q_j)H_{p(j)}(q) is polynomial and has the same face
signs. Rectangular Poincare--Miranda applied on [1/100,1/2]^I gives one
interior vector q with every G_j, hence every H_i, zero. The relabeling
uses the partner involution. It solves all players' equations together;
independent scalar root selections would not suffice.

## 3. All phase incentives and complete deviations

Define i's quiet-phase values by the successive maps T_i,B from X_i.
Equation (3) identifies the value immediately after its active phase with
Y_i. Equation (2) then makes its active Quit and Continue endpoints both
X_i, independently of its own mixing probability.

For every quiet pair with 0<u,v≤1/2, its conditional probability of a tie
given absorption is uv/(u+v-uv)≤1/3. Its conditional passive payoff to i is
therefore at least

    (2/3)(19/10)+(1/3)(−1/10)=37/30 > 11/10≥s_i.

Start at X_i>s_i and apply the other pair maps. Every intermediate value
stays strictly above s_i and at most 21/10. If the currently active quiet
pair absorbs with probability α=1-c_B, continuing pays at least
s_i+(2/15)α. Quitting pays at most s_i+(1/50)α by (R), including the
singleton outcome when that pair both Continue. Therefore Continue is
strictly better, by at least (17/150)α. Every phase and every player has
now been checked in the ORIGINAL reward table.

The candidate values satisfy prescribed Bellman recursion. Joint survival
over a cycle is C<1, so iteration identifies them with actual terminal
values. For any deviating player i, unchanged opponents have cycle survival

    D_i=∏_{j≠i}(1-q_j)≤(99/100)^(n-1)<1.

Iterate the action inequalities against its arbitrary behavioral choices.
The terminal remainder tends to zero because the deviation cannot prevent
opponent absorption and its probability of reaching K cycles is at most
D_i^K. This includes Never and unbounded randomized clocks. It proves exact
terminal Nash at every suffix, not merely against periodic deviations.

For completeness, with a finite coordinate reward bound M, expected
absorption time plus one is at most m/(1-(99/100)^(n-1)) uniformly over
unilateral deviations. Expected terminal and H-stage average payoffs differ
by at most M times that bound divided by H. Hence finite-average deviation
gains tend uniformly to zero, and the prescribed averages approach the
single fixed v. This is the required uniform-payoff conclusion.

## 4. Exact cap-preserving finite laws

Index the chosen pair phases by a(i)∈{0,...,m-1}. The finite law is explicit:

    Pr(T_i=mt+a(i))=q_i(1-q_i)^t       for 0≤t<K,
    Pr(T_i=Never)=(1-q_i)^K.

The infinite profile renews after mK dates. Its discarded suffix has joint
probability C^K and conditional payoff v, proving the payoff identity in (1).

To prove the full-cap identity, first take any pure date t<mK. Censoring
does not change its payoff: it forces absorption by t if earlier opponents
have not already absorbed. A pure date t≥mK yields s_i after all opponents
survive to the cutoff; Never yields zero there. Both are bounded by the
legal response against the infinite profile which waits to mK and then
resumes prescribed play, because the resumed value is v_i≥s_i≥0.
All these complete responses are therefore bounded by v_i. Averaging proves
B_i(σ^K)≤v_i for every behavioral law.

Conversely, quit at i's first active date a(i). Its earlier prescribed
actions were all Continue, and at this active phase Quit attains the active
value. Bellman recursion makes its initial payoff exactly v_i. This date is
inside every K≥1 finite calendar, so censoring preserves this attained
response. Thus B_i(σ^K)≥v_i and (1) follows. This is a lemma about these
literal profiles, not a cap-preserving compression of arbitrary strategies.

Product-low fails by activating only one pair at any positive hazards:
each active player's Quit endpoint is s_i+q_{p(i)}(P_i-s_i)>s_i.
The exact periodic payoff is strictly above s in every coordinate, as
Section 3 established, so it is itself an actual counterexample to payoff
exclusion. Neither observation suggests nonexistence of equilibrium.

## 5. Canonical Fin4 consumer

For four players choose pairs {0,2},{1,3}, starting with {0,2}. Change
terminal rewards to rhat_0=r_0/s_0 and rhat_i=r_i-s_i for i≠0, leaving
Never zero. The own singletons become (1,0,0,0).

Against the constructed INFINITE profile every unilateral deviation absorbs
almost surely. Consequently its exact Nash comparisons transform by the
stated positive scale or additive shift, and its transformed payoff is
vhat_0=v_0/s_0, vhat_i=v_i-s_i. In particular vhat≥shat≥0.
Apply Section 4 afresh in the transformed table. It gives

    Uhat_i(σ^K)=(1-C^K)vhat_i,       Bhat_i(σ^K)=vhat_i,
    Ehat(σ^K)≤(5/3)(99/100)^(4K).

The bound uses vhat_0≤5/3 and vhat_i≤6/5 for i≠0. At every requested
accuracy choose K large enough. The same finite laws then satisfy BOTH
canonical menu inequalities E_N≤ε and L_0≤ε, by the named single-pivot
full-exploitability identity. Their selected nonpivot marginals also have
optimal full-regret pivot-repair value no larger than this bound, since the
displayed pivot law is one admissible competitor.

Fixing the original four singletons at one and varying every other reward
inside the strict inequalities gives a nonempty open subset of the canonical
56-dimensional reward space. The finite-profile translation identity was
not used: finite truncations have positive Never mass.

## 6. Source correspondence and mathematical scope

`Math.Topology.exists_rectangular_zero_of_strict_face_signs` in
`MathUE/Topology/RectangularPoincareMiranda.lean` supplies the finite rectangle
zero principle. The cleared field used above matches its global-continuity
hypothesis. Existing exact periodic consumers include
`FourPlayerPairedSingleton.periodTwoProfile_isExactTerminalNash` and
`FourPlayerPairedSingleton.periodTwo_isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`.
They concern the specific Solan–Vieille table, whose pair participant rewards
equal its singleton rewards by
`SolanVieilleBoundary.boundaryReward_pair_eq_one` in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`.
The current raw region instead has strictly positive own-pair premiums.
The canonical finite-menu consumer uses
`singlePivot_fullExploitability_eq_max_menuExploitability_scalar` in
`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`.

The earlier
[alternating-pair corpus construction](../notes/CODEX_DESCENDANT__TRACKED_CORPUS_ALTERNATING_PAIR_EQUILIBRIA.md)
already gives asymmetric exact profiles throughout four explicit open balls,
with geometric approximation of complete caps. Alternating pairs,
Poincare–Miranda, asymmetry, and open neighborhoods are therefore not new
mechanisms here. The additional statement is this explicit raw reward region,
its every-even-size producer, and the exact complete-cap identity (1).
Neither containment of every previously solved class nor separation from
all other existence criteria is claimed.

The theorem covers a partition of the ENTIRE player set into pairs. It
supplies no odd-player extension, arbitrary outside-player completion, or
producer for an arbitrary normalized reward table. The infinite profile is
exact Nash; its finite truncations have the explicit positive debt (1),
which tends to zero. The source's separate selected late pivot repair and
rational residual algorithm are not statements of this packet.

