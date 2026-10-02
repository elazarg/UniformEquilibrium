# One exceptional grand coalition: an all-behavior capped-transfer obstruction

Identity: CODEX_NOETHER_SUPPORT.

Status: complete ordinary-mathematical obstruction to ONE attempted
mechanism, retained internally. The mechanism caps the grand reward,
constructs capped-game terminal approximate equilibria with negligible
opponent triple-collision exposure, and transfers the same profiles back.
An exact four-player capped table admits no such all-error source sequence,
even with arbitrary nonstationarity and support changes. Its raised table
has an exact all-Quit equilibrium, so this is not a counterexample to the
one-exceptional-coalition class. No Lean build, source edit, or export.

## 1. Question and narrow source check

The requested class has I={0,1,2,3}, unit own singletons, participant
rewards at most one on every nonempty proper coalition, grand rewards
strictly greater than one in every coordinate, arbitrary finite passive
rewards, and zero preabsorption and Never payoffs. The target is one fixed
uniform-equilibrium payoff against all private behavioral deviations.

The original Solan–Vieille, *Quitting games* (2001), headline capping
assumption excludes the grand exception. I checked the original local PDF,
printed pages 266–270, against the literal unit-root route. Conditional
Proposition 2.2 and the periodic construction in Proposition 2.3 do not
assert selection of roots with small upper hazard bounds. Their uniform
absorption lower bound is not such an upper bound.

The relevant exact source interfaces are
`exists_periodic_quittingPerfectAbsorbingRootSequence_of_lowActiveQuitPayoff`
in `UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRootSequence.lean`
and `exists_cyclic_subgamePerfectTerminalNash_of_soloExitPreference` in
`UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`.
They produce actual periodic tails and full terminal Nash guarantees, but
do not produce the collision suppression tested below. I also inspected
the supplied singleton/pair chamber conditions and their `terminalNash`
consumers in `UniformEquilibrium/Quitting/Classification/Existence/SureExitChambers.lean`;
they do not give an arbitrary-table support-changing selector.

A narrow proper/grand-coalition and small-root search found no producer
closing this class. The nearby
[prior full-activity note](CODEX_NOETHER_SUPPORT__PROPER_SUPPORT_FULL_ACTIVITY_STATIONARY_OBSTRUCTION.md)
only blocks fully active stationary repair and is not repeated here.
The current obstruction quantifies over ALL capped behavioral profiles.

## 2. Exact transfer identity and the tested sufficient estimate

Write r⁰ for a capped table with r⁰_i(I)=1. Raise only the grand reward
to r_i(I)=1+b_i, where b_i>0. For every complete profile π let G(π) be
the probability that its first quitting coalition is I. Then

    U_i^r(π)=U_i⁰(π)+b_i G(π).                         (1)

This is a terminal-event correction, not a profile-independent shift.
For independent stopping laws T_j∈N∪{∞}, put

    C_i(π_−i)=Pr(T_j=t for every j≠i, for some finite t).

This is the probability that the opponents' first quitting coalition is
all three opponents. Every unilateral replacement satisfies
G(π'_i,π_−i)≤C_i(π_−i), while G(π)≤C_i(π_−i). Consequently a capped
terminal ε-Nash profile obeys the valid transfer bound

    debt_i^r(π)≤ε+b_i(C_i(π_−i)−G(π)).                (2)

The tested construction seeks capped approximate equilibria for which all
these collision-error bounds vanish. This is a sufficient strategy, not
an equivalence: C_i bounds the deviation's grand probability but need not
be attained by one deviating stopping law. Failure of (2) to vanish is
not itself positive actual regret in the raised table.

If every stage hazard of every opponent is at most δ, then C_i≤δ².
Indeed at a live date the product of the three opponent hazards is at
most δ² times their one-date absorption probability. Sum after weighting
by opponent survival to that date; total opponent first-absorption mass
is at most one. Thus uniformly vanishing hazards would supply the tested
collision suppression if such capped equilibria existed.

## 3. The exact capped and raised fixtures

Let the core be {0,1,2}, with cyclic successor i⁺=i+1 modulo three.
Define the capped table on every nonempty S by

    r⁰_i(S)=1                          if i∈S,
    r⁰_3(S)=0                          if 3∉S,
    r⁰_i(S)=2·1[i⁺∈S]                 if i∈{0,1,2}\S.

All participant rewards, including the grand reward, are exactly one.
The raised table keeps every other entry and has r_i(I)=2 for all i.
It belongs to the requested one-exceptional-grand-coalition class.

The capped zero-continuation root game has payoff differences

    Quit_i−Continue_i=1−2q_{i⁺}        for i=0,1,2,
    Quit_3−Continue_3=1.

Thus player 3 surely quits. The three-cycle has its unique equilibrium
at q_0=q_1=q_2=1/2: a coordinate above or below 1/2 forces alternating
pure best replies around the odd cycle and contradicts that coordinate.
Hence the unique capped root equilibrium is (1/2,1/2,1/2,1), with
macroscopic grand mass 1/8. No small-root Nash selector exists even at
this one continuation. This observation alone is not the main obstruction.

Repeating that root is exact terminal Nash in the capped game. Player 3
can never exceed its prescribed payoff one. Each core player faces certain
absorption at date zero by player 3, and both Quit and Continue give one.
In the raised game its prescribed payoff is 9/8, while each core player
gets 5/4 by quitting surely at date zero, an actual gain of 1/8.

Nevertheless the raised table has an exact all-Quit equilibrium. A core
player gets two whether it Quits or is the sole continuer, and player 3
gets two from Quit versus zero from being the sole continuer. Absorption
at date zero prevents any further deviating opportunity. Thus the table
itself is solved, and no negative class conclusion follows.

## 4. A stopping-law independence inequality

For an arbitrary independent behavioral profile, let S denote its first
quitting coalition when absorption occurs. Set

    D=1−Pr(3∈S),       p_i=Pr(S={3,i}),
    t_ij=Pr(S={3,i,j})             for distinct core i,j.

D includes nonabsorption. Then

    p_i p_j≤2D+t_ij.                                  (3)

Proof. Take two independent copies of the entire stopping-law profile.
Consider the event that their respective first coalitions are {3,i}
and {3,j}, at finite dates t and u. Its probability is p_i p_j.

If t<u, exchange the copies' player-3 stopping times. This transformation
preserves their joint product distribution. The first copy now quits
without player 3, so this part has probability at most D. If t>u, the
same exchange makes the second copy quit without player 3, again bounding
that part by D. If t=u, exchange the copies' player-i stopping times.
The second copy then first quits at exactly {3,i,j}: its other core player
was strictly later, and i now joins 3 and j at their common date. That
part has probability at most t_ij. Sum the three disjoint parts.

The argument applies to arbitrary countable stopping laws with Never
atoms. It does not require a common finite horizon, stationary hazards,
bounded memory, or a bound on the possible stopping dates. Behavioral
quitting strategies induce these independent stopping laws because the
only live public histories are the successive all-Continue dates.

## 5. No capped approximate-equilibrium sequence with vanishing collision error

Proposition. For the capped fixture, if 0≤ε≤1/200 and π is terminal
ε-Nash against all behavioral deviations, then

    max_{i=0,1,2}(C_i(π_−i)−G(π))>1/200.               (4)

Proof. Suppose instead every displayed difference is at most c=1/200.
Write G=Pr(S=I), T=t_01+t_02+t_12, and P=p_0+p_1+p_2.
For each proper triple {3,i,j}, its event is contained in the complement
of the grand event inside the omitted core player's opponent-collision
event. Therefore t_ij≤c and T≤3c.

Player 3 gets exactly Pr(3∈S) in the capped game and can guarantee one
by quitting immediately. Hence D≤ε.

Every core player can likewise guarantee one by immediate Quit. Its
payoff is exactly

    U_i⁰=Pr(i∈S)+2Pr(i∉S, i⁺∈S).

Separating the pair-with-3 events, the grand event, proper triples, and
events missing player 3 gives

    1−ε≤U_i⁰≤p_i+2p_{i⁺}+G+2(T+D).

Put L=1−G and e=3ε+2T. Then b_i=p_i+2p_{i⁺}≥L−e.
Also P≤L, so Σ_i b_i=3P≤3L and b_i≤L+2e. Inverting this three-cycle
relation yields

    p_i=(b_i−2b_{i⁺}+4b_{i⁺⁺})/9≥L/3−e.             (5)

The core Never deviation gives one additional bound. Deleting i's clock
cannot remove i⁺ from the first quitting coalition on an event where i⁺
was originally included. Thus Never's payoff is at least 2Pr(i⁺∈S),
and its gain over the prescribed payoff is at least

    2Pr(i,i⁺∈S)−Pr(i∈S)≥G−p_i−T−D.

The ε-Nash inequality gives G≤p_i+T+2ε. Summing, and using P≤1−G,

    G≤1/4+3T/4+3ε/2≤43/160<1/3.

Consequently L>2/3 and e≤9/200<1/20. Equation (5) gives
p_i>2/9−1/20=31/180>1/6 for every core player. But (3) now implies

    1/36<p_i p_j≤2D+t_ij≤2ε+c≤3/200<1/36,

a contradiction. This proves (4).

In particular, no choice of capped approximate equilibria at errors
ε→0 can make all C_i−G tend to zero. A fortiori all C_i cannot tend to
zero, and uniformly vanishing stage hazards cannot be imposed on such a
source sequence. The quantifiers include nonstationary strategies and
arbitrary changes of active support, not just repairs of the displayed
stationary equilibrium.

## 6. Exact surviving conclusion and stopping point

The cap-and-transfer identity (1), the sufficient error estimate (2), and
the small-hazard estimate remain valid. What fails is the proposed
arbitrary-capped-table producer of profiles with vanishing collision
exposure: the exact fixture rules it out against the full behavioral
strategy class. Even subtracting prescribed grand mass from the coarse
exposure bound does not rescue that producer.

The raw one-exceptional-grand class is NOT settled here. The example's
raised table is already exact Nash by all-Quit. A class-wide proof must
consume the macroscopic collision branch by a different construction,
possibly with genuine support changes or nonstationary behavior; it cannot
merely declare the grand perturbation higher order or assume continuity
of an equilibrium selector. Nor does (4) prove that every capped-to-raised
transfer fails: it specifically blocks uniform control through this
collision-exposure estimate.

The most concrete class-wide construction still open is a RAW-game
extension of the low-continuation cycle: start in
W={v in the reward cube: some v_i≤1}, choose exact root equilibria anew
in the raised game, and allow a block of roots with changing supports
instead of requiring each one-step successor to stay in W. A proper-face
root has a low active Quit endpoint automatically. The unresolved step is
to consume a fully active exit from W by either a finite return block
whose continuation annotations can be realized as actual tails, or a
direct terminal equilibrium branch. Neither return nor terminal incentives
follow merely from the proper-coalition caps. This specifies a construction
question, not a proved dichotomy or an additional theorem premise, and it
does not require reusing any capped-game equilibrium.

This bounded transfer mechanism is stopped. No new general no-go or
unproved security/selection premise is added to the record.
