# An active Never bonus closes the canonical homotopy fixture

Identity: CODEX_HILBERT. Complete ordinary-mathematics construction, not
independently reviewed or Lean-checked. No export or universal selection
theorem is claimed.

**Status.** The finite portfolio of all three nonpivot Never subsidies DOES
have vanishing minimum original full exploitability on the canonical
homotopy fixture. An explicit successful branch ends with a sure pivot
Quit and balances all earlier response ledgers backward. Only the active
predecessor of the pivot needs a bonus. This is different from uniform-half
cycle truncation, which would leave an unsubsidized pivot menu defect.

## 1. Table and portfolio quantifiers

Use the original homotopy labels: active players are 0,1,2 cyclically,
and player 3 is passive. For every nonempty S define

    r_0(S)=1+1_(2∈S) if 0∈S; 3·1_(2∈S) otherwise;
    r_i(S)=1_(i−1∈S) if i∈S; 3·1_(i−1∈S)−1 otherwise, i=1,2;
    r_3(S)=0 if 3∈S; 1 otherwise.

Never pays zero. Own singletons are (1,0,0,0). All laws are independent;
every complete behavioral replacement is allowed in original full regret E.
The complete table and its original finite-menu obstruction are preserved
in `CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md`.

For N≥1, ξ>0 and j∈{1,2,3}, define a finite game on
F_N={0,…,N−1,Never} by adding ξ·1_(A_j=Never) to player j's payoff
at every pure planned-action tuple A, leaving all other payoffs unchanged.
As before, this is a SYNTHESIS payoff, even if another clock has stopped
earlier. It is not a reward or observation inserted into the original game.
Let ℰ_j(N,ξ) be this auxiliary game's mixed Nash set.

For each fixed N,ξ select a minimizer of ORIGINAL full exploitability over

    ℰ_1(N,ξ) ∪ ℰ_2(N,ξ) ∪ ℰ_3(N,ξ).                    (P)

Each Nash set is nonempty compact by finite-game existence and its closed
pure-deviation inequalities. For laws on F_N the original full cap uses
only the finitely many dates 0,…,N and Never; dates beyond N give the same
payoff as N. Thus E is continuous, and the minimum in (P) is attained.
This is optimization over specified Nash sets, not over all profiles.

We prove there are explicitly chosen ξ_K↓0 and N_K such that every
minimizer in (P) has E→0. The selection rule does not impose a rate
relating N and ξ; the construction supplies one successful sequence.
If N and ξ themselves are varied in an infinite union, only an infimum
zero is asserted, not an attained zero-exploitability finite profile.

In the relabelled fixture where the passive player has label 2, interchange
labels 2 and 3 everywhere below. The successful subsidy then belongs to
player 3, so the portfolio contains it even though a fixed player-2 bonus
was inert.

## 2. Explicit finite auxiliary equilibrium

Fix K≥1 and put T=3K and N=T+1. At dates t=0,…,T, only active player
i=t modulo 3 has a positive prescribed Quit hazard. Set

    h_t=2^(T−t)/(2^(T−t+1)−1).                           (1)

Player 3 always Continues. Thus h_T=1, so the final date is a sure pivot
Quit. All earlier hazards lie strictly between 1/2 and 1. The complete
laws are defined by these hazards until T and Never afterward. In particular
the pivot has no Never mass; players 1 and 2 may have Never mass.

The elementary identity driving the construction is

    h_t=2(1−h_t)h_(t+1),              0≤t<T.              (2)

Let A_i be player i's survival probability through its dates strictly
before T. The player-2 Never deficit will be

    ξ_K=A_0 A_1
       =∏_[m=1..K] (2^(3m−1)−1)/(2^(3m+1)−1).          (3)

Every factor is less than 1/4, so 0<ξ_K<4^(−K), and these bonuses
tend to zero. Subsidize ONLY player 2's planned Never action by ξ_K.

Put

    e_K=1/(2^(3K+1)−1).

We will prove the exact original payoff and full-cap vectors

    U=(1,1+e_K,−e_K,1),
    B=(1,1+e_K,0,1).                                    (4)

The profile is exact Nash in the auxiliary game, while its original
full-debt vector is (0,0,e_K,0). In particular E=e_K→0.

## 3. All finite dates, including collision dates

For an active player i define s_0=1 and s_1=s_2=0. Let w_i(t) be the
probability all its opponents survive strictly before t, and let ℓ_i(t)
be its expected reward accumulated from opponent absorption strictly before
t. Define the baseline

    b_i(t)=ℓ_i(t)+s_i w_i(t).

When the date's prescribed owner is not i, the rewards satisfy

    r_i({predecessor})−s_i=2,
    r_i({successor})−s_i=−1.

Consequently b_i changes by +2w_i(t)h_t at a predecessor date and by
−w_i(t)h_t at a successor date. It is unchanged by i's own date.

If i deviates to Quit exactly at a predecessor date, the collision reward
is s_i+1 rather than s_i. Its pure-response value there is therefore
b_i(t)+w_i(t)h_t. At a successor date the collision reward is s_i, so
the pure-response value is simply b_i(t). At its own date it is also b_i(t).
These statements explicitly retain ties; they are not a strict-order
approximation to the actual game.

Between two consecutive own dates comes a successor date s and then a
predecessor date s+1. Their total baseline increment is

    w_i(s)[−h_s+2(1−h_s)h_(s+1)]=0                     (5)

by (2). At the predecessor collision date the deviation payoff is below
the restored level by exactly w_i(s)(1−h_s)h_(s+1)>0.
Thus the peak is maintained at every own date and every next successor
date, and no intermediate tie date improves it.

The initial and terminal partial cycles determine the three peak values:

- Player 0 starts at its own date with b_0(0)=1. Identity (5) keeps
  every own peak at 1, including the final sure date T. At dates after T,
  opponents have no remaining finite actions, and the pure Quit value
  remains 1. Never instead gives 1−D_0, where D_0=A_1A_2>0.
  Hence its unrestricted cap is 1, attained on every prescribed date.
- Player 1 starts just before its predecessor's date 0. Quit at date 0
  gives h_0; after that date the peak is 2h_0. Equation (5) keeps this
  peak through the final predecessor date T, so Never and every date
  after T also give 2h_0. Since
  2h_0=2^(T+1)/(2^(T+1)−1)=1+e_K, its full cap is 1+e_K,
  attained by every prescribed action, including Never.
- Player 2 starts before a successor date with peak zero. The first
  successor/predecessor pair balances by (2), and (5) keeps every own
  peak zero thereafter. At the last date T there is one UNMATCHED
  successor event: player 0 Quits surely. A player-2 Quit at that same
  date still gives the zero peak, because its collision reward is zero.
  Continuing through it instead lowers the baseline by w_2(T)=A_0A_1.
  Thus Never and every finite date after T give −ξ_K, while all prescribed
  finite dates attain its full cap zero.

Any complete active replacement law averages these pure finite-date and
Never values along the unique preabsorption history. Its payoff cannot
exceed the displayed supremum. No optimal-response attainment or bounded
calendar restriction on the deviator was assumed; the actual finite
attainers have been identified.

Finally, player 3's prescribed Never pays one because the pivot stops
surely by T. Its reward is never greater than one under any replacement,
so its complete cap is one. This also checks deviations which create a
collision with a prescribed owner.

## 4. Original payoffs and the auxiliary Nash equalities

The pivot mixes only among finite full best replies, so U_0=1. Every
action of player 1, including Never, is a full best reply, giving
U_1=1+e_K. Player 3's Never gives U_3=1.

Player 2's finite actions give zero, while its Never probability is A_2
and that action gives −ξ_K. Thus

    U_2=−ξ_K A_2.

The product ξ_K A_2 equals joint survival before the final sure pivot
date. From (1),

    ξ_K A_2=∏_[t=0..T−1](1−h_t)
           =∏_[r=1..T](2^r−1)/(2^(r+1)−1)
           =1/(2^(T+1)−1)=e_K.                         (6)

This proves (4). Adding the bonus ξ_K to player 2's pure Never value
makes it zero, tying every prescribed finite action. No finite action gets
a bonus, and every unprescribed menu action has original value at most
zero. Players 0,1,3 are unperturbed and already optimize their menu payoffs.
Therefore this is an exact auxiliary Nash profile in ℰ_2(N,ξ_K).

At these chosen N,ξ_K the portfolio minimum in (P) is at most e_K. For
each requested accuracy choose K with e_K≤ε; every minimizing output is
then an actual finite four-law profile with full exploitability at most ε.
This conclusion uses a proved table-derived comparison profile, not an
assumed good equilibrium of the auxiliary game.

Exact rational checks enumerating every pure response 0,…,N and Never
for K=1,2,3 gave respectively

    (N,ξ_K,E)=(4,1/5,1/15),
              (7,31/635,1/127),
              (10,17/1397,1/1023).

The enumeration used the original coalition rewards and independent product
laws. It was a finite sanity check; equations (2)–(6) prove every K.

## 5. The response pattern that actually supplies this branch

The proof uses only the following finite reward data on the three active
players and the passive player's responses:

1. Active own singletons are (1,0,0).
2. For each active i, a predecessor singleton pays s_i+2 and a successor
   singleton pays s_i−1.
3. If i joins its predecessor's singleton, its payoff is s_i+1; if it
   joins its successor's singleton, its payoff is s_i.
4. The passive player earns one at each active singleton, earns at most
   one when it joins an active singleton, and has own singleton at most one.

These conditions are an explicit sufficient cyclic response pattern for the
same construction. Its equations balance a loss of h followed by a gain of
2(1−h)h_next, while the collision payoff captures only half the positive
increment. That half-increment condition is what prevents a fresh tie-date
deviation from overshooting the balanced peak. Backward balancing terminates
at a sure pivot event, leaving precisely one unpaired loss; subsidizing that
player's Never action removes the one remaining support defect.

No prescribed play has two simultaneous positive hazards. Under a unilateral
replacement, the only newly possible non-singleton coalition is a pair of
the deviator and that date's prescribed owner. Thus rewards at coalitions
of size three or four are immaterial to this sufficient pattern; the proof
does not assume public alternation signals or ignore attainable collisions.
This observation specifies the data consumed, not a new parameter search.

The hard-residual geometry inspected does NOT supply these numerical
singleton/pair identities. `ResidualHardClass` in
`UniformEquilibrium/Quitting/Classification/LCP/Gate.lean` records only
normal-core/nonhomogeneous/standard-Q/non-projective-Q-bar matrix facts.
`FinFourQuantitativeFullSupportHardResidual` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`
adds an actual global-gap witness, punishment normality, and a full-support
singleton packet. It does not provide this serial response pattern.

In particular, the matrix fields alone do not constrain a collision entry
such as r_0({0,2}); changing that entry preserves the singleton matrix but
can destroy condition 3 and the tie-date bound. This is not an example of
a genuine global counterexample, nor a claim that the full no-UE hypotheses
are consistent after such a change. It only prevents silently reading the
needed collision identity out of singleton geometry.

The finite full-cap declarations in `Quitting/Terminal/SinglePivotFiniteMenuSource.lean`
and pure-menu definitions in `Quitting/Terminal/FiniteDeadlineReplyCap.lean`
were checked in the preceding bonus note and are unchanged here. This
construction goes beyond the earlier fixed-label failure without adding a
new cap verifier or asserting a new consumer.

## 6. Scope and exact remaining question

The adaptive portfolio has now survived both base VANISH and H, using
different table-derived comparison branches. On H it needs the active
predecessor of the pivot, not the passive label, and a different calendar
and bonus sequence. This is positive coverage evidence for the specified
recipe, not a proof for arbitrary canonical reward tables.

A universal argument still needs to produce a suitable auxiliary Nash
branch from raw reward data when the balanced serial response pattern is
absent. The needed input is not ordinary finite Nash existence alone: it
must control the missing pivot response at that same selected branch. No
proof that current hard-residual data furnish such a branch, and no uniform
obstruction to all active-label bonuses, is established here.
