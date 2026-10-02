# A two-premium core can require a genuinely dynamic exit

Author: CODEX_HILBERT.

Status: complete ordinary-mathematical boundary test, not independently
reviewed or Lean-checked. A specified rational canonical table has exactly
one failed positive-premium peeling support, of size two. It fails the
Solan–Vieille active-low-root choice and has a positive unrestricted
exploitability gap over ALL stationary profiles, including vanishing-rate
families. Nevertheless it has a uniform-equilibrium payoff by the existing
three-player theorem and an explicitly safe fourth-player lift. Thus this
is not a negative quitting game or a refutation of two-core UE existence.

## 1. The attempted extension and its easy covered boundary

The proposed extension was: with two possible premium recipients and the
other players having constant own-quitting rewards, a failed two-player
peeling core might yield either the old active-low-payoff root choice or
a stationary equilibrium exit. The example below refutes that disjunction
even when “stationary exit” permits unrelated stationary approximations
at every accuracy.

There is an elementary already-covered case. Let C={i,j}, with nonnegative
own solos and both pair rewards strictly above their own solos. If every
outsider weakly prefers not to join EACH of the three nonempty coalitions
contained in C, then either:

- both pair owners prefer staying to leaving, and C is a pure sure exit; or
- some owner i prefers the other singleton {j} to the pair, and {j} is
  a pure sure exit.

The singleton owner has no incentive to replace its nonnegative solo by
Never. Outsider no-join conditions give every remaining full cap. These
are exactly the existing pure singleton/pair chamber consumers, not a new
class mechanism. Removing the outsider inequalities is substantive, as
the example demonstrates.

## 2. The actual four-player table

Let I={0,1,2,3}; Never pays zero. For each nonempty S, write its core
membership pattern using players 0 and 1. Set the first two reward
coordinates as follows, independently of membership of 2 and 3:

| Core membership in S | r₀(S) | r₁(S) |
| --- | ---: | ---: |
| neither | 0 | 2 |
| only 0 | 1 | −1 |
| only 1 | 3 | 0 |
| both | 2 | 1 |

For the remaining coordinates set

    r₂(S)=0 if 2∈S;
           −1 if 2∉S and the core pattern is only 1;
           3 otherwise.

    r₃(S)=0 if 3∈S, and 1 otherwise.

These rules specify all fifteen terminal rows. The own singleton vector is
s=(1,0,0,0). Player 0 has own reward 1 or 2, with positive premium exactly
when player 1 also quits. Player 1 has own reward 0 or 1, with positive
premium exactly when player 0 also quits. Players 2 and 3 have constant own
reward zero. Thus all own premiums are nonnegative, every support containing
2 or 3 can peel that player, and the UNIQUE failed peeling support is {0,1}.

In particular P=s: immediate Quit guarantees the singleton floor under
nonnegative own premiums, and all-Never opponents give the matching upper
bound. This fact is not used to infer an equilibrium from a root.

## 3. Exact active-low-root selection fails

Take the actual one-shot continuation annotation

    v=(0,2,3,1).

Let q_i denote the independent Quit probabilities. The core players'
one-shot endpoint differences, Quit minus Continue, are

    Q₀−C₀=1−2q₁,       Q₁−C₁=4q₀−2.                       (1)

They are independent of q₂ and q₃. Indeed, when neither core player quits,
the table pays (0,2) if an outsider quits, exactly matching the first two
continuation coordinates if nobody quits. Player 3 always gets 1 from
Continue and 0 from Quit, so q₃=0 at every exact root.

The matching-pennies best-response equations (1) have the unique solution
q₀=q₁=1/2. For example q₁<1/2 would force q₀=1 and then q₁=1;
the reverse strict inequality gives the opposite contradiction. With those
core probabilities, player 2's Continue payoff is

    (3+3−1+3)/4=2>0=Q₂.

Therefore the ENTIRE one-shot game has the unique exact Nash root

    q=(1/2,1/2,0,0),        F(q,v)=(3/2,1/2,2,1).             (2)

Every active quitter receives strictly above its singleton. All-Continue
is not an alternative exact root. This is a failure of existence of a good
root choice, not merely a bad selected equilibrium among good ones.

To test the exact unit-singleton hypothesis used in the old-theory route,
add t>0 to all nonempty terminal coordinates, leave Never zero, and divide
coordinate i by d_i=s_i+t. At the transformed root continuation
v̂_i=(v_i+t)/d_i, the finite game's best-response comparisons are identical
up to positive scaling. Its unique root remains (2), and each active
payoff is still strictly above 1. Meanwhile v̂₀=t/(1+t)<1, so the source
belongs to the relevant low-coordinate set W. The chosen continuation
coordinates are themselves among the transformed terminal reward levels,
so it is in the reward-containing cube, and hence also the paper's larger
cube. Thus this obstruction persists for EVERY t>0 in the zero-solo
normalization, not just at an unrelated signed continuation.

## 4. No exact stationary full equilibrium

All comparisons below are complete behavioral caps, not one-stage caps
against an arbitrary annotation. Against stationary opponents that absorb
with positive probability, the cap is the maximum of immediate Quit and
Never. The relevant production statement is recorded in Section 7.

First a stationary Nash profile must have q₃=0. If q₃>0 and at least one
other hazard is positive, player 3 obtains 1 by Never but strictly less
than 1 under its prescribed law, because its own first-stage Quit event
pays zero. If every other hazard is zero, player 0 gets zero but can
obtain 1 by quitting immediately. Thus neither case is Nash.

Put x=q₀, y=q₁, z=q₂ with q₃=0. An active player at a stationary full
Nash profile must receive its Quit endpoint Q_i: changing only the first
action and then following the old strategy is a legal deviation, so the
root is Nash against its ACTUAL stationary continuation. In particular
that player's Never payoff cannot exceed Q_i.

If z=0, x,y>0 is impossible: player 0's Quit endpoint is 1+y≤2, while
Never receives 3 against positive player-1 hazard. If only x>0, player 1
currently gets −1 but can quit immediately for x>0. If only y>0, player 2
gets −1 but can quit for zero. If x=y=0, player 0 can quit for 1.

Suppose z>0. If x=y=0, player 0 again has a gain. If x=0<y, active
player 1 has Q₁=0 but Never receives 2 from player 2. If y=0<x, active
player 2 has Q₂=0 but Never receives 3 from player 0. Hence x,y>0.
The boundaries x=1 and y=1 are also impossible: in the first, player 2's
Never payoff is 3; in the second, player 0's Never payoff is 3>Q₀=2.
Thus 0<x,y<1.

The exact endpoints for these remaining cases are

    Q₀=1+y,   N₀=3y/(y+z−yz),
    Q₁=x,     N₁=[−x+2(1−x)z]/(x+z−xz),
    Q₂=0,     N₂=[3x−y+xy]/(x+y−xy).                         (3)

Every denominator is positive. Active players require N_i≤Q_i.
The third comparison gives y≥3x/(1−x)>3x and hence x<1/4. The first and
second give respectively

    z≥y(2−y)/(1−y²)>y,
    z≤x(1+x)/[(1−x)(2−x)]<x.                               (4)

The last strict inequality follows from 1−4x+x²>0 when x<1/4.
Equations (4) contradict y>3x. This exhausts all support and sure-hazard
cases. In particular there is no pure terminal Nash profile either.

## 5. Vanishing-rate limits also fail: a uniform stationary gap

Suppose stationary full exploitability tends to zero along qⁿ. Pass to a
subsequence with qⁿ→q*. If q*≠0, its prescribed stationary payoff is
continuous, since the one-period total absorption is positive. Complete
caps are lower semicontinuous there. To check the only boundary issue,
if a player's opponents all have zero limiting hazards, its limiting cap
is max(s_i,0)=s_i, and continuous immediate-Quit payoffs already give the
necessary lower-semicontinuity bound. Otherwise both stationary endpoints
are continuous. Therefore q* would be exact stationary Nash, contradicting
Section 4.

It remains to handle q*=0, where prescribed stationary payoffs need not be
continuous. Let h_n=Σ_i q_iⁿ>0 and pass to a limit
p_i=lim q_iⁿ/h_n. Then p≥0 and Σp_i=1. Collision probabilities are
O(h_n²), so the limiting payoff is the singleton lottery

    u=(p₀+3p₁,
       −p₀+2p₂+2p₃,
       3p₀−p₁+3p₃,
       1−p₃).                                               (5)

Immediate Quit converges to s_i, hence u≥s. For 0<p_i<1, the Never
payoff converges to [u_i−p_i s_i]/(1−p_i). Its Nash comparison implies
u_i≤s_i. For p_i=1, the singleton-lottery identity itself gives u_i=s_i.
Consequently

    p_i>0 ⇒ u_i=s_i.                                        (6)

If 0<p₃<1, (5)–(6) would give 1−p₃=0. If p₃=1, u₀=0 violates u₀≥1.
Therefore p₃=0. The three remaining inequalities u≥s become

    2p₁≥p₂,       2p₂≥p₀,       3p₀≥p₁.

They force p₀,p₁,p₂ all positive. The active equalities (6) then force

    p₂=2p₁,       p₀=2p₂,       p₁=3p₀,

which is impossible for positive masses. No vanishing-rate family escapes.

Thus the infimum of full exploitability over all stationary profiles is
strictly positive. No particular numerical lower bound is needed or
claimed. The argument handles all rates and support boundaries, not just
fixed positive hazard vectors.

## 6. The game is nevertheless solved by a genuine semantic consumer

Restrict to players {0,1,2}, using the same table on their nonempty
coalitions. The existing unconditional three-player theorem gives terminal
approximate Nash profiles at every error (via the target/terminal
equivalence). Append player 3's Never law. The first three players'
payoffs and every unilateral cap are unchanged, since 3 is absent from
all their prescribed and deviating terminal coalitions.

Player 3 has no profitable deviation: conditional on the other three
complete stopping plans, Never pays 1 if they eventually quit, and zero
otherwise. Its own quitting can only turn some of those rewards into
zero, never increase one. This is a pointwise comparison and covers
arbitrary behavioral and tied deviations. Thus the lifted four-player
profiles retain the original error. The terminal-all-errors consumer
selects one fixed uniform-equilibrium payoff of this table.

This is known three-player coverage plus an explicit safe spectator, not
a new general two-core class theorem. It shows why the failed root-choice
and stationary tests are not evidence against the quitting conjecture.

## 7. Narrow source checks and remaining question

Sources inspected for the proposed mechanism:

- `QuittingPureSingletonChamber`, `QuittingPurePairChamber`, their
  `terminalNash` and `uniformEquilibriumPayoff` declarations in
  `UniformEquilibrium/Quitting/Classification/Existence/SureExitChambers.lean`;
- `quittingStationaryUnilateralCap_pureSetRoot` and
  `isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet` in
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`;
- `quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap`
  and `quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never`
  in `UniformEquilibrium/Quitting/Stationary/CompleteBehavioralCap.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_threePlayer` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`;
- `quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The prior ordered-premium producer is recorded separately in the frozen
[weakening note](CODEX_HILBERT__ORDERED_POSITIVE_PREMIUM_WEAKENING.md).
Its continuation set and old root-choice hypothesis are tested literally
in Section 3. An exact integer enumeration of all fifteen nonempty pure
coalitions also found a profitable toggle at every one; the proof above
does not depend on that calculation.

Bounded conclusion: the automatic “two-core ⇒ old root-choice or stationary
approximation” extension fails. The example does not exclude a periodic
class producer, a changed invariant continuation set, or a general two-core
UE theorem. The remaining mathematical question is how a dynamic producer
can incorporate the outside player's response which blocks the core's
pure exit, while retaining every other player's full cap. This notebook
supplies no successful splice or unproved class-wide output as an input.
