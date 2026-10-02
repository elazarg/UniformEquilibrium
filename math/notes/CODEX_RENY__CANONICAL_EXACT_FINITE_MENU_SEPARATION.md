# Canonical single-pivot exact-menu separation

Identity: CODEX_RENY. Ordinary mathematical theorem, independently reviewed
but not Lean-checked or exported. This is a self-contained preservation of
the construction supplied in `gpt/FINITE_MENU_EXACT_APPROX_SEPARATION.md`,
not a claim of independent authorship of that construction. Its independent
audit and source qualification are in
[the review](../feedback/VANISH__BY_CODEX_RENY.md).

## Statement and game

There are four players I={0,1,2,3}. A strategy is a probability law on
the nonnegative integer dates and Never. Laws are independently sampled.
The first finite stopping date ends the game, paying the reward of the
nonempty coalition stopping at that date. All-Never pays zero. Every full
unilateral replacement law is permitted; no public correlation or
observation of another player's sampled time is available.

Fix R>1 and h>0. Index players 1,2,3 cyclically, with predecessor i⁻ and
successor i⁺. For every nonempty coalition S set

    r₀(S) = 1                         if 0∈S;
            R                         if 0∉S.

    rᵢ(S) = 0                         if i∈S;
            −h                        if i∉S and 0∈S;
            2·1_(i⁻∈S) − 1_(i⁺∈S)   otherwise,                  i=1,2,3.

This completely specifies the table, with bound max(2,R,h) and own
singleton vector (1,0,0,0). Write U for prescribed terminal payoff, B for
the full behavioral cap, and E=max_i(B_i−U_i).

For N≥1, the finite menu is F_N={0,…,N−1,Never}. Let Bⁿ be the cap over
that menu and E_N=max_i(Bⁿ_i−U_i). Also set

    W₀=U₀(Never,p_−0),
    D₀=∏_(i=1,2,3) pᵢ(Never),
    L₀=W₀+D₀−U₀.

For a law supported on F_N, every finite reply at or after N gives W₀+D₀
to the pivot and gives the Never payoff to each other player. Thus
E=max(E_N,L₀).

The following statements hold.

1. For every N≥1 there is exactly one Nash product law in the finite menu.
   Its E_N is zero and its L₀ is 1−1/R, independently of N.
2. For every K≥1 there is an explicit product law on F_(3K) with
   E_(3K)=L₀=E=8^(−K).
3. The table has an exact infinite-support behavioral Nash equilibrium,
   but no exact behavioral Nash equilibrium with finite stopping-law
   support for every player.
4. At R=2,h=1, player 1's total variation distance between the displayed
   approximate law at N=3K and the unique exact-menu Nash law is
   1−2^(−K), tending to one.

## Proof of complete exact-menu classification

First omit player 0 and consider one product row of players 1,2,3 with
continuation value zero. Their Quit values are zero and Continue values are

    Cᵢ(x)=2x_(i⁻)−x_(i⁺).

Only x=0 is Nash. Indeed, if x_m=max_i x_i>0, then
C_(m⁺)≥x_m>0 and hence x_(m⁺)=0. Player m uses Quit, so
C_m=2x_(m⁻)≤0 and x_(m⁻)=0. But then C_(m⁻)=−x_m<0, which requires
x_(m⁻)=1, a contradiction.

Now fix any exact finite-menu Nash law, not assumed subgame perfect.
Suppose a row reached with positive joint survival has certain absorption.
The conditional row is product, so some player quits surely there.

If a nonpivot quits surely, player 0 receives R>1 from Continue and 1
from Quit. Thus the pivot must Continue. Each nonpivot has two legal
conditional replacements: Quit now; or Continue now and Quit at the next
date. At the last permitted date use Never for the second replacement.
The second replacement pays exactly zero on the all-Continue branch of
the current row: either the player quits next date and every coalition
containing it pays zero, or everyone plays Never after the last date.

Because current prescribed absorption is certain, each prescribed value
is exactly its three-player one-row value with empty outcome zero. The
two Nash comparisons therefore imply the row Nash inequalities just proved
impossible in the presence of a sure quitter. This argument does not use
any arbitrary continuation law at a zero-reach history.

If instead the pivot quits surely, every nonpivot obtains −h from Continue
and zero from Quit, forcing all three to quit. The pivot would then gain
by Continue, again a contradiction.

No reached row can absorb surely. Inductively every date through the end
of the finite menu is reached, and all four Never masses are positive.
Each conditional suffix is Nash: retaining the earlier part of one law
and changing its conditional tail multiplies a strictly positive suffix
gain by the positive joint probability of reaching that date. Independence
and legal unilateral agency are preserved.

At the last row let q be the root and A=1−∏_(i=1,2,3)(1−q_i). Its values are

    Q₀=1,       C₀=R A,
    Qᵢ=0,       Cᵢ=−h q₀+(1−q₀)(2q_(i⁻)−q_(i⁺)),   i=1,2,3.

No q_i equals one by the preceding argument. Also q₀ cannot vanish:
the three-player row lemma would force all q_i=0, against which the pivot
strictly prefers Quit. Thus 0<q₀<1 and A=1/R. If any nonpivot q_i were
zero, its successor's Continue value would be strictly negative and that
successor would have to quit surely. All nonpivot coordinates are therefore
interior, and

    2q_(i⁻)−q_(i⁺)=h q₀/(1−q₀).

This three-variable linear system has determinant 7 and its solution is
constant across the three coordinates. Consequently put

    a_R=1−(1−1/R)^(1/3),       b_R=a_R/(h+a_R).

The unique last row is (b_R,a_R,a_R,a_R), with payoff v=(1,0,0,0).
All four probabilities lie strictly between zero and one.

With continuation v, the nonpivot action values keep the same formula,
whereas C₀=R A+(1−A)=1+(R−1)A. If A>0, the pivot must Continue; the
three-player row lemma then forces A=0. Hence A=0. Any q₀>0 would make
each nonpivot strictly prefer Quit, so q₀=0 too. The only such earlier row
is all-Continue and its value remains v.

Backward induction is now legitimate for all finite-menu Nash laws because
all dates were proved reached before the induction. It forces no finite
stopping before N−1 and exactly the displayed last row there. Conversely,
these rows give a finite subgame-perfect Nash law. Finally

    U₀=1,       D₀=(1−a_R)³=1−1/R,       W₀=R(1−D₀)=1,

so L₀=D₀. Nonpivots have no omitted-date improvement because their own
singletons are zero. This proves statement 1 and also E=1−1/R.

## Proof of the approximate and infinite constructions

Fix K≥1, N=3K, and J=8^(−K). Player 0 chooses Never. For i=1,2,3 set

    pᵢ(3k+i−1)=2^(−k−1),          0≤k<K,
    pᵢ(Never)=2^(−K).

Equivalently players take turns, with the designated player quitting with
conditional probability 1/2. One cycle survives with probability 1/8 and
contributes (0,7/8,0) to the nonpivot payoff vector. Thus

    U=(R(1−J),0,1−J,0).

The pivot's pure reply at date t has value R−(R−1)S(t), where S(t) is
the probability that all three opponents survive strictly before t. This
is nondecreasing. At the last menu date S(t)=2J; after the menu S(t)=J.
The Never payoff is R(1−J). Consequently

    Bⁿ₀=max(R(1−J), R−2(R−1)J),       B₀=R−(R−1)J.

For a nonpivot, every coalition containing that player pays zero. Its
pure-date payoff is therefore exactly the accumulated expected reward of
opponent absorption strictly before that date. For players 1 and 3 this
quantity starts at zero, drops below zero at the first opponent's date in
each cycle, and returns to zero at the second. Their full caps are zero.

For player 2 the accumulated value at the beginning of opponent cycle k is
1−4^(−k). After player 1's date it becomes 1, and after player 3's date it
becomes 1−4^(−k−1). Thus its cap is 1, attained already at date 1.
These calculations include every finite date and the Never limit.
Arbitrary replacement laws average these pure payoffs, so they give no
higher cap. Hence

    Bⁿ=(max(R(1−J),R−2(R−1)J),0,1,0),
    B=(R−(R−1)J,0,1,0).

The pivot menu debt is max(0,2−R)J≤J; player 2's debt is J. Also W₀=U₀
and D₀=J. Thus E_N=L₀=E=J, proving statement 2 with the same actual laws.

Letting k range over all nonnegative integers removes all nonpivot Never
mass. The same convergent sums and complete response calculation give
U=B=(R,0,1,0), an exact behavioral equilibrium. A hypothetical exact
equilibrium with all four finite supports would belong to some F_N and
would be finite-menu Nash there, contradicting statement 1's positive full
debt. This proves statement 3 without assuming limits of caps are generally
continuous.

Finally take R=2,h=1. At N=3K the two player-1 laws have disjoint finite
supports: {0,3,…,3K−3} versus {3K−1}. Their only common atom is Never,
with overlap min(2^(−K),2^(−1/3))=2^(−K). Under the probability-distance
convention TV=1−overlap, their distance is 1−2^(−K). This proves statement 4.

## Precise significance

This is a direct canonical-singleton obstruction to replacing approximate
finite-menu selection by exact finite-menu selection, even allowing fresh
selection at every deadline and over every equilibrium. It does not rule
out finite approximate laws; it explicitly constructs them. The infinite
equilibrium also rules out a positive global behavioral gap on this table.

The general qualitative exact-deadline architecture barrier is already
checked for another table. Moreover the prior ordinary proof draft
[canonical boundary homotopy](CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md)
already proves the canonical version: unique complete exact-menu Nash at
every deadline, constant positive pivot debt, an exact infinite periodic
equilibrium, and successful finite approximate laws. It consequently also
excludes every exact finitely supported equilibrium. The same TV distance
1−2^(−K) follows directly for its pivot's truncated periodic laws and
unique exact-menu laws.

The construction preserved here is therefore a different explicit fixture
with particularly simple exact cap/error formulas and the R,h family, not
a new qualitative canonical separation. The complete proof above remains
valid. No new arbitrary-table UE existence theorem, global minimum descent,
or export-level architecture exclusion is claimed.
