# Canonical Fin4: unbounded stopping support survives complete repair

## Status and exact contribution

This note proves an ordinary-mathematics lower bound on the number of finite
atoms needed in a player's stopping law. The other three players may use
arbitrary independent behavioral strategies, including unbounded stopping laws
and Never. Thus the bound remains after complete optimization of the pivot.

The example has an explicit exact stationary terminal Nash equilibrium. It is
not a counterexample to uniform equilibrium and is not a newly solved reward
class. Its negative cyclic core belongs to the already available odd-blocker
and capped-own-quitting mechanisms. What is established here is the quantitative
support obstruction, including a one-coordinate version under unrestricted
repair of all other coordinates.

No Lean proof or Lean build was performed. The accompanying Python program
checks the displayed finite profiles and their unrestricted caps in exact
rational arithmetic. Its finite grid check is a falsification check only; the
universal inequalities are proved below.

## 1. Table, full behavioral caps, and theorem

Let the players be 0, 1, 2, 3. Indices within C = {0,1,2} are read modulo 3.
For a nonempty quitting coalition S define

    r_i(S) = 1_{i in S}(1 - 2 * 1_{i+1 in S}) - a_i,    i in C,
    (a_0,a_1,a_2) = (0,1,1),
    r_3(S) = -1_{3 in S and S intersects C}.

Never pays zero; in particular the displayed terminal shifts are NOT applied
to Never. This specifies all fifteen terminal reward vectors. The own-singleton
vector is exactly (1,0,0,0), and every reward has absolute value at most 2.

For an independent behavioral profile p let U_i(p) be its terminal payoff,
B_i(p) the supremum over all complete unilateral behavioral replacements, and
E(p) = max_i(B_i(p)-U_i(p)). Define

    k_i(p) = #{finite dates t : Pr_p(T_i = t) > 0}.

Never is not counted. Dates need not be consecutive or lie below any fixed
calendar deadline.

THEOREM A. For every N >= 0 and every actual profile p,

    k_1(p) <= N  ==>  E(p) > (1/16) * 256^(-N).

There is no restriction on the complete laws of players 0, 2, or 3.

THEOREM B. For every core player i in {0,1,2},

    k_i(p) <= N  ==>  E(p) > (1/32) * 256^(-N).

In particular every exact terminal Nash profile has infinitely many finite
atoms in each core player's stopping law. After taking an infimum over
profiles, the corresponding lower bounds are non-strict.

Consequently, fixing even one of the nonpivot core laws to a bounded number
of finite atoms cannot be repaired to arbitrarily small regret by optimizing
all remaining strategies. This is stronger than a restriction on the support
of the pivot's repair or on stationary deviations.

## 2. Exact stationary equilibrium

At every live date let players 0, 1, 2 independently Quit with probability
1/2, and let player 3 always Continue. Call this profile p*.

Temporarily remove the constants a_i from the three core terminal coordinates,
leaving their Never payoffs zero. In this unshifted game every core player's
passive payoff is zero. Whenever it Quits, its next cyclic neighbor Quits with
probability 1/2, so its conditional expected Quit payoff is 1-2(1/2)=0.
Thus every unilateral behavioral strategy of that player has unshifted
expected payoff zero.

Under any such unilateral replacement, the other two core players absorb
almost surely: their deleted survival probability for t rows is 4^(-t).
Therefore the terminal shift by -a_i applies with probability one, even for
a deviator who chooses Never. Every core deviation has payoff exactly -a_i.
Player 3 can never obtain positive payoff and obtains zero by Never. Hence

    U(p*) = B(p*) = v* = (0,-1,-1,0).

This is an exact terminal Nash equilibrium. It also gives the corresponding
uniform-equilibrium payoff directly: absorption under each unilateral
replacement is bounded by a geometric opponent clock, so terminal versus
finite-average payoff errors vanish uniformly over those replacements.

Every nonempty subset of C is the terminal quitting coalition with probability
1/7. Indeed, every row gives each such subset probability 1/8 and joint
Continue has probability 1/8.

## 3. A quantitative root lemma

Every actual continuation payoff v belongs to

    V = [-1,1] x [-2,0] x [-2,0] x [-1,0].

For a one-stage product root q, put

    alpha_i = product_{j != i}(1-q_j),
    w_i = v_i + a_i,                         i in C.

Then w_i lies in [-1,1]. The Quit-minus-Continue difference for core player i is

    e_i(q,v) = 1 - 2*q_{i+1} - alpha_i*w_i.                 (3.1)

Let g_i(q,v) denote ordinary one-stage mixed-strategy regret. Thus

    g_i = (1-q_i)*e_i  if e_i >= 0,
    g_i = q_i*(-e_i)   if e_i <= 0.

For player 3, writing c_C = product_{i in C}(1-q_i),

    Q_3 = -(1-c_C),       C_3 = c_C*v_3.                   (3.2)

LEMMA 3.1. If max_i q_i >= 3/4, then max_i g_i(q,v) > 1/16.

PROOF. Suppose every g_i <= delta = 1/16.

First suppose some core q_k >= 3/4. Let p=k-1 and j=k+1 modulo 3.
Since alpha_p <= 1-q_k, (3.1) gives

    e_p <= 1-2*q_k+(1-q_k) <= -1/4.

Therefore q_p <= 4*delta = 1/4. Similarly

    e_j >= 1-2*q_p-(1-q_k) >= 1/4,

so q_j >= 1-4*delta = 3/4. It follows that e_k <= -1/4, hence

    g_k >= (3/4)(1/4) = 3/16 > delta,

which is impossible.

Now suppose q_3 >= 3/4; the preceding paragraph means all core hazards are
strictly below 3/4. If any core q_j <= 1/4, its cyclic predecessor i has
alpha_i <= 1-q_3 <= 1/4, hence e_i >= 1/4. This forces q_i >= 3/4,
a contradiction. Thus every core hazard is strictly greater than 1/4.
Consequently c_C < (3/4)^3 = 27/64. Since v_3 >= -1, (3.2) gives

    C_3-Q_3 >= 1-2*c_C > 5/32,
    g_3 > (3/4)(5/32) = 15/128 > delta.

This is the remaining contradiction. QED.

The lemma uses ordinary root regret, not a support-perfectness assumption.
It applies to arbitrary actual tails, not merely to stationary ones.

## 4. One missing initial atom forces complete regret

LEMMA 4.1. If player 1's first-row hazard is zero, then E(p) > 1/16.

PROOF. Suppose E(p) <= delta = 1/16, and write q for the first root.
Since q_1=0, player 0 obtains exactly 1 by quitting immediately. Thus

    U_0(p) >= 1-delta.

Let G be the terminal event that 0 Quits and 1 does not. Coordinate r_0 is
1 on G, -1 when both 0 and 1 Quit, and zero otherwise. Hence

    Pr(G) >= U_0(p) >= 1-delta.

Coordinate r_1 is -1 on G and is nonpositive on every other outcome, including
Never. Therefore

    U_1(p) <= -1+delta.

Player 1's immediate-Quit payoff is -2*q_2, so its regret bound gives

    q_2 >= 1/2-delta = 7/16.

The date-zero event that 2 Quits and 0 Continues precludes G and gives player
0 payoff zero. Independence and r_0 <= 1 therefore imply

    U_0(p) <= 1-q_2*(1-q_0).

Combining these inequalities yields

    1-q_0 <= delta/q_2 <= 1/7,
    q_0 >= 6/7.

Lemma 3.1 now gives root regret greater than 1/16. A one-stage change followed
by the prescribed continuation is an allowed complete behavioral deviation,
so full regret is at least root regret. This contradicts E(p) <= delta. QED.

No best-response attainment, finite horizon, or assumption about the other
players' strategy supports was used.

## 5. Chronological proof of Theorem A

Let P_t be the joint probability of reaching live date t. At every date with
P_t > 0, let p^t denote the actual conditional suffix. Complete behavioral
regret satisfies

    P_t * E(p^t) <= E(p).                                  (5.1)

For each player this follows by copying its prescribed behavior before t and
using an arbitrary suffix deviation after the unique public survival history.
Taking suprema does not require a maximizing response.

Set delta=1/16 and kappa=1/256. Suppose k_1(p) <= N and

    E(p) <= delta*kappa^N.

Inductively, for t=0,...,N, one has P_t >= kappa^t. By (5.1),

    E(p^t) <= delta*kappa^(N-t) <= delta.

Lemma 3.1 implies that every root hazard at that suffix is strictly below
3/4, because each root regret is bounded by complete suffix regret. Hence

    P_{t+1} = P_t * product_i(1-q_i^t) > kappa*P_t.

Lemma 4.1 also implies q_1^t > 0. Positive joint reach ensures positive own
survival; therefore q_1^t > 0 means Pr(T_1=t)>0 in the original stopping law.
This produces N+1 distinct finite atoms at dates 0,...,N, contradicting
k_1(p) <= N. This proves Theorem A, with the strict displayed inequality.

This argument is about support cardinality, not the largest date. Moving N
atoms arbitrarily far out in the calendar cannot evade it. Nor can a sure
quitter hide the later dates: at the relevant regret scale, Lemma 3.1 excludes
that root before reach becomes small.

## 6. Every core coordinate: proof of Theorem B

Let tilde r be the unshifted core table, adding a_i to each nonempty terminal
core reward and still keeping Never zero. Leave r_3 unchanged.

First, if z is the prescribed joint-Never probability, then

    z <= d_0(p) <= E(p).                                   (6.1)

To see this, change only player 0's original Never outcomes to a late finite
date T. Since player 0's passive reward is zero, the gain converges to z:
opponents' finite tail and date-T atom masses vanish, while all-Never
opponents yield singleton reward 1. Taking the supremum of deviation gains
proves (6.1).

For any profile pi, including a unilateral deviation, let A(pi) be its
absorption probability. The exact transformation is

    U_i^{tilde r}(pi) = U_i^r(pi) + a_i*A(pi).

It follows, using A(deviation)<=1 and (6.1), that

    E_{tilde r}(p) <= E_r(p)+z <= 2*E_r(p).                 (6.2)

For the unshifted table, the root lemma has the same proof: the three core
continuations now directly lie in [-1,1]. Its missing-initial-atom lemma is
cyclically symmetric. Here are the details for any core i with q_i=0.
Let h=i-1 and j=i+1. If unshifted full regret is at most delta=1/16,
immediate Quit by h guarantees 1, so U_h >= 1-delta. Thus the terminal event
that h Quits and i does not has probability at least 1-delta. Consequently
Pr(i is an absorbing quitter)<=delta, and U_i<=delta. Immediate Quit by i
then gives

    1-2*q_j <= U_i+delta <= 2*delta,
    q_j >= 1/2-delta.

As before, U_h<=1-q_j*(1-q_h) implies q_h>=6/7, contradicting the root lemma.
Thus any missing core initial atom gives E_{tilde r}>1/16.

By (6.2), canonical regret at most 1/32 therefore forces every core first
hazard to be positive. It also forces all four hazards below 3/4 by Lemma 3.1.
Repeat the induction in Section 5 with delta=1/32 and any core player i.
This proves Theorem B.

## 7. Upper bound and the three-law selection problem

For N>=1, give each core player the law

    Pr(T_i=t)=2^(-(t+1)),             0<=t<N,
    Pr(T_i=Never)=2^(-N),

and let player 3 play Never. Equivalently, use the stationary half-hazard
profile for N rows and then all-Never.

Its prescribed payoff and unrestricted caps are exactly

    U = (0, -1+8^(-N), -1+8^(-N), 0),
    B = (4^(-N), -1+4^(-N), -1+4^(-N), 0),
    E = 4^(-N).

For player 0, quitting before N has payoff zero; quitting at or after N gives
4^(-N); Never gives zero. For players 1 and 2, finite times before N give
-1, while late finite times and Never give -1+4^(-N). Player 3's cap is zero.
Thus the caps include every unbounded or privately randomized deviation:
randomization cannot exceed the supremum of these pure-time values.

Define A_N as the infimum of E after allowing arbitrary complete repair of
player 0, while each of the three other laws has at most N finite atoms.
Theorem A and the displayed construction give

    (1/16)*256^(-N) <= A_N <= 4^(-N),           N>=1.

The lower bound actually permits players 2 and 3 to have arbitrary stopping
laws. Only player 1's atom bound is needed.

Therefore the minimum atom budget needed for this example is
Theta(log(1/epsilon)), up to the stated constant factors. A fixed budget is
not sufficient at every accuracy, even though the game has an exact
stationary equilibrium and the inner one-player repair is unrestricted.

## 8. Same complete coalition law in three dates, different caps

Consider the following independent finite laws:

| Player | Date 0 | Date 1 | Date 2 | Never |
|---|---:|---:|---:|---:|
| 0 | 4/7 | 0 | 0 | 3/7 |
| 1 | 1/2 | 1/3 | 0 | 1/6 |
| 2 | 1/2 | 1/4 | 1/4 | 0 |
| 3 | 0 | 0 | 0 | 1 |

Every nonempty subset of C is again the terminal coalition with probability
1/7. No coalition contains 3 and Never has probability zero. Thus this is an
exact finite realization of the stationary equilibrium's ENTIRE terminal
coalition law, not merely of its payoff vector.

Nevertheless its full semantics are

    U = (0,-1,-1,0),
    B = (1/24,-1,-11/14,0),
    d = (1/24,0,3/14,0).

In particular E=3/14. The payoff and full coalition law coincide with those
of p*, while the response caps do not.

Theorem A is stronger than finding one bad compressed realization: every
finite-atom realization has positive exploitability, and no fixed atom budget
can make that exploitability arbitrarily small after complete repair of the
other players.

## 9. Relation to the current source boundary

The inspected repository reference was
88709a1034da3738fcb35ca10fc2cea45bad808d.

Relevant existing interfaces were read directly:

- `exists_objective_minimizer_eq_behavioral_infimum`
  (`UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`)
  already identifies the finite repair LP optimum with the infimum over all
  pivot behavioral strategies. The lower bound here quantifies over that full
  strategy class; it does not reintroduce a finite pivot menu.
- `UniformEquilibrium/Quitting/Classification/Existence/OddBlockerCore.lean`
  already treats passive negative three-cycle cores with arbitrary outside
  reward coordinates. The equilibrium-existence mechanism for this example is
  not presented as new.
- The attached ordered/supportwise-premium notes supply related sufficient
  classes. In this table every core participant premium is either zero or -2,
  and player 3's is zero or -1. Thus the table is already in the capped-own-
  quitting subclass, and no reward-class enlargement is being claimed.

The new argument in this note is a quantitative full-response obstruction to
bounded support, with all other complete laws unrestricted, together with an
explicit exact coalition-law realizer separating payoff data from caps.
No worldwide priority claim follows from this limited source comparison.

## 10. Scope

This does not prove arbitrary Fin4 UE, construct a positive-gap table, exclude
all polynomial nonexistence certificates, or produce the three-law selector
for arbitrary rewards. It rules out an accuracy-independent finite-atom
reduction of that selection problem, even on an explicitly solved canonical
table. Growing-support selection, stationary strategies, and infinite
behavioral laws remain available; the example uses them successfully.

To reproduce the exact finite checks, run:

    python check_cyclic_support_barrier.py

The script verifies the three-date coalition law and caps, the truncation
formulas for N=1,...,6, and 5,265 rational root-box grid points. The grid does
not replace the analytic proof of Lemma 3.1. No repository changes or commits
were made.
