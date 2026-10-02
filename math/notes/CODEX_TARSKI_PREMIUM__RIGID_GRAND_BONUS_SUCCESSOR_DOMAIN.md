# A successor-invariant domain for rigid proper-participant rewards

Author: CODEX_TARSKI_PREMIUM.

Status: a complete ordinary-mathematical invariant-domain lemma, not an
equilibrium existence proof. This bounded positive class attempt is stopped
at the missing absorption/actual-tail step. No new source mechanism covering
the whole class, exact stationary theorem, Lean implementation, or export
is claimed. The construction concerns the NEW game directly; it does not
require capped-game Nash, small hazards, or monotone grand-event mass.

## 1. Exact class and question

There are four players I={0,1,2,3}. Every own singleton is one. For every
proper nonempty coalition S and participant i∈S, r_i(S)=1. Grand-coalition
rewards are r_i(I)=1+b_i with b_i>0. Every passive reward r_i(S), i∉S,
is an arbitrary finite real. Preabsorption and Never pay zero.

The intended conclusion is terminal ε-Nash at every ε>0 against all
behavioral deviations, hence one fixed uniform-equilibrium payoff. Players
randomize privately and independently before absorption; no common random
clock or correlated profile mixture is allowed. Late finite stopping and
Never remain admissible deviations.

That intended conclusion is NOT proved here. The surviving result is an
explicit compact domain invariant under every exact one-root Nash successor.

## 2. Direct new-game root calculation

For product hazards q∈[0,1]^4 and continuation annotation v, define

    Q_i(q)=1+b_i∏_{j≠i}q_j,
    c_i(q)=∏_{j≠i}(1−q_j),
    B_i(q)=Σ_{∅≠T⊆I\{i}}
               [∏_{j∈T}q_j ∏_{j∉T∪{i}}(1−q_j)] r_i(T),
    C_i(q,v)=B_i(q)+c_i(q)v_i,
    F_i(q,v)=q_i Q_i(q)+(1−q_i)C_i(q,v).

These are the literal Quit endpoint, Continue endpoint, and prescribed
one-stage successor. The formula for Q uses the fact that only the event
where every opponent quits changes an own participant reward from one.
All passive data enter B, not Q.

At an exact root Nash, F_i≥Q_i≥1 for every i. If q_i>0, the supported
Quit action has payoff F_i=Q_i. These facts include q_i=1 and inactive
players q_i=0; they are immediate from the two endpoint comparisons and
the convex-mixture identity.

For stationary opponents with positive opponent absorption a_i=1−c_i,
Never has payoff N_i=B_i/a_i. Thus the relevant stationary comparison is

    H_i(q)=B_i(q)−a_i(q)Q_i(q),

not the Quit formula alone. An active stationary Nash player needs H_i≤0
(with equality if it mixes genuinely); an inactive one needs H_i≥0.
The arbitrary passive table can make these signs unrestricted. At zero
opponent absorption the Never value is zero and must be treated separately.

## 3. Explicit compact invariant domain

Choose R≥1 bounding every absolute terminal reward. Then R≥1+b_i. Define

    L={v∈[1,R]^4: some v_i=1},
    K={Q(q):q∈[0,1]^4},
    D=L∪K.

Proposition. D is compact and nonempty. For EVERY v∈D and EVERY exact
Nash root q against v, its successor F(q,v) belongs to D.

Proof. L is closed in a compact box. K is the continuous image of the
compact hazard cube, lies in ∏_i[1,1+b_i]⊆[1,R]^4, and contains the
all-one vector. Hence D is compact and nonempty.

Let A={i:q_i>0}. If A is empty, F=v∈D. If A is nonempty and proper,
then for each active i an inactive opponent has zero hazard, so Q_i=1
and F_i=1. Every coordinate F_j≥Q_j≥1 by Nash, including inactive j.
Also F_j≤R, since F is a convex combination of terminal rewards and v.
Therefore F∈L. Finally, if A=I, every coordinate is active, so F=Q(q)∈K.
These three cases exhaust all exact supports and all sure-Quit boundaries.

The full-activity part has an explicit algebraic shape. Put

    z_i=(u_i−1)/b_i,
    t=(∏_i z_i)^(1/3).

When u∈K and every u_i>1, the unique hazard vector producing u is

    q_i=t/z_i.                                       (1)

Indeed z_i=∏_{j≠i}q_j, so ∏_i z_i=(∏_i q_i)^3. Conversely, positive
z with t≤z_i≤1 gives q_i∈(0,1], ∏_i q_i=t, and Q(q)=u. The attachment
K∩L consists precisely of the four segments where at most one coordinate
exceeds one, and that coordinate lies in [1,1+b_i]. A single zero hazard
gives such a segment; two zero hazards give the all-one vector.

This is a raw geometric calculation. It does not assert that every point
of K is the actual payoff of an equilibrium or of a terminating sequence.

## 4. Exact positive checks and the stopping point

Two elementary chambers of this class are directly solved:

- If r_i(I\{i})≤1+b_i for every i, everyone quitting at date zero is exact
  terminal Nash. Any one deviator either joins and receives 1+b_i, or
  continues and receives r_i(I\{i}); the other three players force immediate
  absorption, so later plans and Never add no further opportunity.
- If some k has r_j({k})≥1 for every j≠k, then k quitting surely at zero
  and every other player choosing Never is exact terminal Nash. The owner
  receives one rather than Never's zero. An outsider can only join for its
  proper-pair participant reward one or retain the stated passive payoff.

These are existing sure-exit types, not a new solution of arbitrary passive
completions.

Invariance of D does not supply an absorbing root. All-Continue is exact
root Nash at EVERY v∈D, and it is strict when all v_i>1. It can even be
the unique root Nash throughout the positive part of K in a solved table.
For example, let every b_i=1 and every passive reward equal three. For
v_i>1 and a_i>0,

    Q_i≤1+a_i < 1+2a_i ≤ 3a_i+(1−a_i)v_i=C_i;

if a_i=0, C_i=v_i>1=Q_i. Thus Continue strictly dominates Quit at every
opponent root, so the sole root Nash is all-Continue. Yet any pure singleton
is an exact terminal equilibrium by the second chamber above.

Consequently it would be false to supplement the invariant-domain lemma
with universal positive-absorption root existence on D. A successful source
must select actual absorbing play in a more discriminating way and realize
its continuation annotations as actual tails. Neither task is supplied by
(1) or by every-root invariance. No chain of conditional consumers is built
around this missing step.

The optional exact-stationary target is also too strong in general. A short
warning fixture uses a three-player cyclic core and a spectator. Give all
proper participants one and all grand participants 3/2. The spectator gets
two whenever a core coalition quits without it. Core passive rewards when
only the spectator quits are zero. Within the core, player i gets passive
singleton rewards zero from i+1 and three from i−1, and passive reward two
when both others quit; remaining passive entries may be zero. Any stationary
Nash with core activity must keep the spectator inactive, since its Never
value two exceeds every Quit value. With the spectator inactive, an active
core player's necessary condition is q_{i+1}−2q_{i−1}≥0. All-three activity
contradicts the cyclic inequalities; two-player activity makes one active
inequality negative; a lone quitter has an outsider paid zero who can join
for one. A lone spectator and all-Never also permit a core Quit deviation.
This warns against stationary-only production; no terminal gap is claimed.

## 5. Narrow source/literature correspondence and scope

The route was selected from `docs/TOOLKIT.md`, followed by narrow searches
for constant own-quitting rewards and grand-coalition bonuses. Directly read:

- `quittingRootQuitPayoff_eq_sum_opponentCoalitionMass` and its Continue
  counterpart in `UniformEquilibrium/Quitting/Root/OpponentCoalitionPayoff.lean`.
- `quittingRootSuccessorPayoff`, the endpoint definitions, and
  `quittingRootSuccessorPayoff_eq_endpointMix` in
  `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`.
- `quittingRootCoordinateNashDefect` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean` and
  `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`.

The original [Solan–Vieille quitting-game theorem](https://www.math.tau.ac.il/~eilons/quitting19.pdf)
requires a quitter's joint reward not exceed its singleton; positive grand
bonuses violate that hypothesis. A narrow primary-source lookup, including
[the absorption-path paper](https://link.springer.com/article/10.1007/s10107-022-01807-6),
did not identify a theorem that automatically covers this entire arbitrary-
passive class. This is a limited search result, not a worldwide novelty or
nonexistence assertion. Correlated-equilibrium results have different agency
and cannot be used here without removing their correlating device.

The only new proved object in this bounded attempt is the explicit compact
successor-invariant domain and its algebraic full-activity part. It is neither
an absorbing producer nor a supplied-object-to-UE theorem. The raised-game
terminal approximate-existence question remains unresolved by this note.
