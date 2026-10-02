# Sharp finite-deadline Nash ceiling for quitting games

## Status and relation to the requested conjecture

This is an ordinary mathematical derivation, accompanied by exact-arithmetic
finite-instance checks. It is not a Lean-checked theorem. It does **not** prove
or refute uniform-equilibrium existence for arbitrary four-player quitting games.

The derivation strengthens the scalar upper bound in the uploaded
`CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING.md` by using all
of its datewise inequalities rather than their unweighted sum. A modified
version of the two-active-player construction in
`CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md` attains the
strengthened bound. The modification changes the first player's collision
reward from zero to minus one and makes its singleton reward a parameter.
No claim of literature-wide novelty is made.

The April 2, 2026 paper *The APS approach for undiscounted quitting games*,
DOI 10.1007/s00182-026-00982-6, characterizes a restricted class of equilibrium
payoffs; its Introduction explicitly allows that class to be empty. It does
not provide a universal construction used in this note.

## 1. Model and unrestricted deviations

There are finitely many players. The first nonempty quitting coalition S
pays r(S), and infinite all-Continue play pays zero. Assume |r_i(S)| <= M.
Before absorption the only public history is the elapsed all-Continue history.
An independent behavioral strategy therefore has the same terminal behavior
as an independently drawn stopping time in N union {infinity}. Conditional
hazards realize every such law, including its Never atom. A complete unilateral
behavioral deviation is another stopping law. Its expected payoff is an average
of pure-time payoffs, so its supremum is the supremum over finite pure times
and Never.

The K-deadline timing game permits the pure times

    0, ..., K-1, infinity,

where K >= 1. This is not the K-stage average-payoff game: it is a finite
normal-form restriction of the terminal-payoff game. After the permitted
finite dates, its prescribed behavioral realization plays Never.

For a profile p, write U_i(p) for its terminal payoff, B_i(p_-i) for its
unrestricted behavioral deviation cap, and E(p) = max_i (B_i-U_i).

## 2. Exact universal bound

For 0 < x <= 1 define

    rho = (1+x)/2,
    g_K(x) = [1/x + (1/2) sum_{m=0}^{K-1} rho^m]^{-1}.

Set g_K(0)=0. Equivalently, for 0 < x < 1,

    g_K(x) = x(1-x)/(1-x rho^K),

and g_K(1)=2/(K+2). Put

    C_K = max_{0 <= x <= 1} g_K(x).

**Theorem.** Every mixed Nash equilibrium of every K-deadline timing game
with rewards in [-M,M] satisfies

    E(p) <= M C_K.

This bound is sharp even with four players and only two active players.
Moreover, the same C_K is the sharp worst-table bound when the equilibrium
selector may choose the best exact deadline equilibrium separately at each
reward table. In particular,

    C_1=2/3,  C_2=1/2,  C_3=2/5,  and lim_{K->infinity} C_K=1/4.

### Proof of the upper bound

The case M=0 is immediate. Fix a player with positive unrestricted debt d.
Let s=r_i({i}). Let a be the probability that every opponent chooses Never,
and let h_t be the probability that the opponents' earliest finite quitting
time is t, for 0 <= t < K. Thus

    a + sum_t h_t = 1.

Write V_infinity for the player's payoff from Never, V_t for its payoff
from quitting at t<K, and L for its common payoff from any finite t>=K.
Deadline Nash and pure-time extremality give

    U_i = max(V_infinity, V_0, ..., V_{K-1}),
    B_i = max(U_i,L),
    d = L-U_i > 0.

Since L-V_infinity = a s, we have s>0 and d <= a s. Set

    x=s/M in (0,1],   delta=d/M.

Comparing late Quit with Quit at t gives

    delta <= 2 h_t + (1-x) sum_{u>t} h_u.              (1)

Indeed, if the opponents quit before t, the outcomes coincide. At t, leaving
rather than joining changes the reward by at most 2M. At a later opponent
quit, the difference between that opponent-only reward and the singleton
reward is at most M-s. On all-opponents-Never, both actions give s.

Let H_t = sum_{u=t}^{K-1} h_u, with H_K=0. Equation (1) implies

    H_t >= delta/2 + rho H_{t+1}.

Backward iteration and delta <= x a give

    1 = a+H_0
      >= delta/x + (delta/2) sum_{m=0}^{K-1} rho^m.

Therefore delta <= g_K(x). Zero-debt coordinates satisfy the same
nonnegative universal bound trivially. This proves the upper bound.

### The first three constants and the limit

Let S_K(x)=sum_{m=0}^{K-1} ((1+x)/2)^m. The sign of the derivative of

    g_K(x)=x/[1+x S_K(x)/2]

is the sign of

    1 - (x^2/4) sum_{m=1}^{K-1} m ((1+x)/2)^{m-1}.

For K<=3 the subtracted quantity is at most K(K-1)/8 < 1. Thus g_K is
increasing on [0,1] and its maximum is g_K(1)=2/(K+2). This gives the
three constants displayed above.

For each x, g_K(x) decreases to x(1-x), including at x=0 and x=1.
All functions involved are continuous on the compact interval [0,1],
so the convergence is uniform by the elementary monotone compactness
argument: for any epsilon>0, the increasing open sets

    {x : g_K(x)-x(1-x)<epsilon}

cover [0,1]; a finite subcover and nesting give one K that works for every x.
Taking maxima gives C_K -> 1/4. In fact C_K>1/4 for every finite K, since

    g_K(1/2) = (1/4)/[1-(1/2)(3/4)^K] > 1/4.

For K>=4 the maximizer is the unique x in (0,1) satisfying

    x^2 sum_{m=1}^{K-1} m ((1+x)/2)^{m-1} = 4.

The left side is strictly increasing; at x=0 it is zero and at x=1 it is
K(K-1)/2>4.

## 3. A four-player family attaining the bound

Normalize M=1. Let the players be 1,2,3,4, with 3 and 4 dummies. Fix
0<x<=1. For every nonempty coalition S, let A=S intersect {1,2} and set

| A | empty | {1} | {2} | {1,2} |
|---|---:|---:|---:|---:|
| r_1(S) | 0 | x | 1 | -1 |
| r_2(S) | 0 | -1 | -1 | 0 |

For a dummy d, set r_d(S)=-1 when d belongs to S, and zero otherwise.
This defines all fifteen nonempty coalition rewards. Never pays zero.

Fix K and write delta=g_K(x), rho=(1+x)/2. Define independent stopping laws:

    P(T_1=t)=1/(K+1)        for t=0,...,K-1,infinity;
    P(T_2=t)=(delta/2) rho^{K-1-t}    for 0<=t<K;
    P(T_2=infinity)=delta/x;
    T_3=T_4=infinity.

The definition of delta proves that the second law sums to one.

### Direct verification of deadline Nash

Player 2's reward is zero when its stopping time matches player 1's, including
infinity, and minus one otherwise. Since player 1 is uniform on the K+1
permitted actions, every permitted pure response gives

    -K/(K+1).

For player 1, put a=delta/x and h_t=(delta/2)rho^{K-1-t}. Never gives
V_infinity=1-a. Every late finite Quit gives

    L=1-a+x a=1-a+delta.

The displayed geometric law satisfies, for every t<K,

    2 h_t + (1-x) sum_{u>t} h_u = delta.

These are exact reward differences for this table, not merely upper bounds.
Hence V_t=L-delta=V_infinity at every permitted finite date. Player 1 is
indifferent among all permitted actions. A dummy receives zero from Never
and can never obtain a positive reward. Thus the profile is deadline Nash.

### Its full behavioral regret

The same pure-time calculation gives

    d_1=delta,   d_2=d_3=d_4=0,
    E(p)=g_K(x).

There are no omitted deviations other than the one common late finite value:
against these finite-support opponents, every t>=K has the same terminal
payoff. Randomized or history-dependent deviations are covered by pure-time
extremality.

Selecting an x maximizing g_K proves sharpness of the universal upper bound.

## 4. Uniqueness: changing the deadline Nash selector does not help

We prove uniqueness by induction on K, retaining arbitrary off-path strategies
rather than silently removing them.

At a reached date, a dummy's positive probability of quitting would give it
strictly negative expected payoff, whereas Never always gives zero. Every
dummy therefore continues at that date.

Let p,q be the current quit probabilities of players 1 and 2.
If p=1, player 2 strictly prefers to join, so q=1; player 1 then strictly
prefers Continue (reward 1) to Quit (reward -1), a contradiction.

Suppose q=1. Player 1 must Continue, and player 2 receives -1. Consider
player 2 changing to Never. Its payoff is -1 when player 1 belongs to the
first quitting coalition and zero otherwise. If the latter event has positive
probability, Never is a strict improvement. Otherwise player 1 belongs to
the first quitting coalition almost surely at a finite future date. Some
such date t has positive probability. If player 2 quits at t, it receives
zero on that positive-probability collision event and at least -1 everywhere
else, again a strict improvement. This argument allows arbitrary off-path
dummy quitting. Therefore q<1 as well.

The all-Continue event now has positive probability. The conditional tail
must itself be Nash in the remaining deadline timing game: a profitable tail
deviation could be spliced after this survival history. By induction, its
active payoff is a uniquely determined (u_n,v_n), where n is the number of
remaining dates, with u_n<x and v_n>-1.

The root action differences, Quit minus Continue, are

    Delta_1 = x-u_n-q(2+x-u_n),
    Delta_2 = p(2+v_n)-(1+v_n).

They have a unique mixed intersection in the interior of the unit square;
the four pure corners are not Nash. Thus the root is uniquely determined:

    p_n=(1+v_n)/(2+v_n),
    q_n=(x-u_n)/(2+x-u_n).

The predecessor payoffs satisfy

    u_{n+1}=(x+u_n)/(2+x-u_n),
    v_{n+1}=-1/(2+v_n),
    u_0=v_0=0.

For 0<x<1 their solutions are

    u_n=x(1-rho^n)/(1-x rho^n),
    v_n=-n/(n+1).

For x=1 the first solution is u_n=n/(n+2). In all cases the required strict
inequalities u_n<x and v_n>-1 hold. In particular,

    p_n=1/(n+2).

The resulting stopping laws are exactly those of Section 3. Every survival
history through the deadline has positive probability, so the preceding
dummy argument also forces their full deadline laws to be Never. This proves
uniqueness, not just uniqueness of a chosen backward-induction construction.

Consequently the same C_K is also

    sup_r min_{p in NE_K(r)} E_r(p)

on normalized four-player tables.

## 5. Every sharpness game nevertheless has a uniform-equilibrium payoff

For an integer L>=1 prescribe:

    player 2 quits at date 0;
    player 1 independently chooses a uniform time in {1,...,L};
    players 3 and 4 play Never.

The prescribed terminal payoff is the fixed vector

    v=(1,-1,0,0),

independently of L and x. Player 1 already receives its maximum reward 1;
a dummy already receives its maximum reward zero. If player 2 changes its
strategy, a pure time in {1,...,L} gives -1+1/L, by matching player 1's
single atom. Date 0, Never, and all later dates give -1. Thus

    E(p^L)=1/L.

This verification covers every behavioral deviation. It uses an off-path
punishment: player 1's later stopping law is reached only if player 2 refuses
to quit at date zero.

There is also a direct finite-horizon verification. Use the convention that
absorption at date t supplies its absorbing reward from that date onward,
so its H-stage average weight is (H-t)_+/H. Against any unilateral deviation
by player 2, absorption occurs by date L because player 1 stops surely by then.
Replacing a terminal reward by its H-stage average changes player 2's payoff
by at most L/H for H>L. The other three players cannot exceed their prescribed
payoffs. Hence

    max_i finite-horizon gain_i <= 1/L+L/H,

and the prescribed payoff is exactly v. Choosing L large and then H large
proves directly that v is a uniform-equilibrium payoff. If the convention
starts the absorbing reward one period later, add at most 1/H to the error.

The example is therefore a counterexample to universal exact-deadline Nash
approximation, not to quitting-game equilibrium existence.

## 6. What is and is not established

The argument gives, for arbitrary bounded quitting games and any finite number
of players, terminal profiles with regret at most M/4+epsilon, for every
positive epsilon. For four-player games it proves a sharp performance barrier
of the exact-deadline-Nash method, even allowing favorable equilibrium
selection. It strengthens the attached Euler note's three-date ceiling from
20-8 sqrt(6) to the exact value 2/5 and gives the exact scalar ceiling at every
deadline.

It does not make the unrestricted infimum zero for arbitrary reward tables,
and no positive-gap table is produced. In particular, neither the bound
C_K -> 1/4 nor the unique bad deadline equilibria imply a positive lower bound
on the unrestricted infimum. Section 5 explicitly disproves that inference
for the sharpness family.

The remaining general obligation is to construct profiles outside this exact
hard-deadline Nash class with arbitrarily small regret, or prove a positive
regret lower bound over **all** independent behavioral profiles for one table.
Neither obligation is discharged here.

## Reproduction

Run

    python check_deadline_ceiling.py

The standard-library script uses rational arithmetic. It checks 72 deadline
profiles and 72 off-path punishment profiles, their full finite-support
pure-deviation caps, the saturated geometric inequalities, and selected
finite-horizon bounds. These checks are bounded evidence; the proofs above,
not the computation, establish the statements for all K and x.
