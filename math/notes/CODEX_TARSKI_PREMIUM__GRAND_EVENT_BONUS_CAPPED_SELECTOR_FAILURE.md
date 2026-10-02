# A shared grand-coalition bonus does not supply a capped-game selector

Author: CODEX_TARSKI_PREMIUM.

Status: proved ordinary-mathematical failure of one precise ALL-BEHAVIOR
source-selection condition. No positive source mechanism was obtained.
The exact test table itself has an exact terminal equilibrium both before
and after the bonus. Thus this is NOT a counterexample to uniform equilibrium
or to the one-exceptional-grand-coalition class. This selector is stopped;
no export, Lean edit, constants optimization, or frozen-packet edit is made.

## 1. The raw question and the shared-event identity

Let I be finite with at least two players. Own singleton rewards are one.
All participant rewards in proper nonempty coalitions are at most one;
passive rewards are unrestricted finite reals. Preabsorption and Never pay
zero. Players use independent private behavioral stopping, with no correlating
device. A unilateral replacement may be any behavioral strategy, including
every finite Quit date and Never.

Let r^0 have grand-coalition reward one for every player, and change only
that coalition by

    r_i^λ(I)=1+λ b_i,             b_i>0, λ≥0.

At λ>0 this lies in the requested one-exceptional-grand class. Write p for
the actual independent stopping-law profile, with p_i(t) its atom at finite
date t and possible remaining mass at Never. Define

    Γ(p)=Pr_p(first quitting coalition is I)
        =Σ_{t≥0}∏_{i∈I}p_i(t).

The last formula uses independent complete stopping laws, not a correlated
mixture of joint profiles. For every prescribed or deviating profile,

    U_i^λ(p)=U_i^0(p)+λ b_i Γ(p).                     (1)

The grand event is the same event for all players, but its probability is
not invariant under unilateral replacement. For any deviation d_i,

    gain_i^λ(p,d_i)
      =gain_i^0(p,d_i)+λ b_i[Γ(p_{−i},d_i)−Γ(p)].    (2)

This holds for Never as well as finite or mixed deviations; it is a single
terminal-coalition correction, not an unconditional payoff shift.

For fixed opponents define the maximal unilateral event gain

    κ_i(p)=sup_{t≥0}∏_{j≠i}p_j(t),
    ρ_i(p)=κ_i(p)−Γ(p)≥0,
    ρ(p)=max_i ρ_i(p).

Indeed a deviating stopping law contributes the expectation of the kernel
∏_{j≠i}p_j(t), with kernel zero at Never. Its supremum is κ_i, and the
prescribed law is one admissible replacement. Let E_λ(p) be full terminal
exploitability: the maximum, over players and all behavioral replacements,
of the deviation gain. Then (2) gives

    E_λ(p)≤E_0(p)+λ(max_i b_i)ρ(p).                  (3)

The supremum over a SINGLE player's replacement law is essential here.
It is κ_i=sup_t∏_{j≠i}p_j(t), not the potentially larger total opponent
coincidence probability Σ_t∏_{j≠i}p_j(t). A deviator cannot assign stopping
probability one at every finite date. The theorem below rejects the exact
unilateral-response-gap selector, not merely a sufficient bound using that
sum over dates.

The natural robust capped-source selection proposal is

    For every η>0 choose an independent p with
        E_0(p)≤η and ρ(p)≤η.                         (CS)

If (CS) held, (3) would transfer to every fixed positive bonus at all
accuracies without any further equilibrium construction. The theorem below
shows that (CS) is false even in an exact four-player table in this class.
This does not say that the sufficient bound (3) must be small at an actual
equilibrium of the raised game.

## 2. Complete exact Fin4 table, with an equilibrium already visible

Take I={0,1,2,3}. For EVERY proper nonempty S and EVERY participant i∈S,
put r_i^0(S)=1. For EVERY passive entry put r_i^0(S)=0, except

    r_3^0({0,1,2})=3/2,
    r_0^0({1,2,3})=3.

Put r_i^0(I)=1. The raised table is r_i^1(I)=2 for every i; all other
entries are unchanged. Thus b_i=1, all solos are one, and every proper
participant reward is exactly one.

Let C={1,2,3}. Have these three players quit surely at date zero, with
player 0 choosing Never. This is an exact terminal Nash profile in BOTH
tables. Player 0 receives 3; joining gives only 1 or 2. Each other player
receives 1; leaving gives passive reward zero. Under any unilateral
replacement, some other player still quits surely at zero, so only that
replacement's first action matters. Arbitrarily late stopping, Never, and
behavioral mixing cannot improve these two endpoint comparisons.

This explicit equilibrium is part of the counterexample's scope: failure
of (CS) cannot be read as a terminal gap or a failure of the raw class.

## 3. The all-law selector obstruction

Theorem. For the capped table in Section 2 there is NO sequence of
independent behavioral stopping profiles p^n with

    E_0(p^n)→0 and ρ(p^n)→0.                        (4)

In particular (CS) fails. Equivalently,

    inf_p [E_0(p)+ρ(p)]>0,

where the infimum ranges over ALL independent behavioral profiles, not
stationary profiles, bounded menus, or profiles with a common deadline.

Proof. Suppose (4). Let e_n=E_0(p^n) and let T_i^n be the independent
stopping time of player i, including Never. All probabilities below are
under the product of the actual stopping laws.

Players 1 and 2 are neutral in the following exact sense. Their payoff in
the capped table is one if they belong to the first quitting coalition and
zero otherwise. They can guarantee payoff one by quitting at date zero.
Therefore

    Pr(1 belongs to the first coalition)≥1−e_n,
    Pr(2 belongs to the first coalition)≥1−e_n.

If both belong, their stopping times coincide at a finite date. Consequently

    Σ_t p_1^n(t)p_2^n(t)≥1−2e_n.                    (5)

The left side is at most sup_t p_1^n(t), since the total finite stopping
mass of player 2 is at most one. Choose a finite t_n with

    p_1^n(t_n)≥1−2e_n−1/n.

Writing u_n=p_1^n(t_n) and v_n=p_2^n(t_n), the left side of (5) is at
most v_n+(1−u_n). Thus

    u_n→1 and v_n→1.                                (6)

The date t_n is allowed to vary arbitrarily and to diverge. Nothing here
imposes a fixed finite support or a uniform horizon.

Earlier stopping by either of the remaining players has negligible mass.
For k∈{0,3}, if T_k^n<t_n and T_1^n=t_n, then player 1 is not in the
first coalition. Hence

    Pr(T_k^n<t_n)≤(1−u_n)+e_n→0.                    (7)

Put x_n=p_0^n(t_n), y_n=p_3^n(t_n). Passing to a subsequence in the compact
square, take x_n→x and y_n→y. On an event of probability tending to one,
both neutral players stop at t_n and neither other player stops earlier.
Payoffs are bounded. Conditional coalition accounting therefore gives

    U_0^0(p^n)=x_n+3(1−x_n)y_n+o(1).                (8)

For clarity, player 0 receives one when it quits at t_n, three when only
player 3 among {0,3} quits at t_n, and zero when neither does. Earlier
stops and failures of (6) account for the o(1) term. Independence turns the
two choices into x_n and y_n; the vanishing masses in (7) justify replacing
probability of stopping later by 1−x_n or 1−y_n.

The grand-coalition and unilateral grand-event quantities satisfy

    Γ(p^n)=x_n y_n+o(1),
    κ_0(p^n)=y_n+o(1),
    κ_3(p^n)=x_n+o(1).                              (9)

These are exact concentration consequences, not approximations of strategy
power. For Γ the summand at t_n is u_n v_n x_n y_n; the sum at other
dates is at most 1−u_n. For κ_0 the t_n kernel is u_n v_n y_n and every
other-date kernel is at most 1−u_n. The same calculation with x_n proves
the κ_3 formula. Thus (4) and (9) imply

    y(1−x)=0 and x(1−y)=0.

The only possibilities are (x,y)=(0,0) and (x,y)=(1,1).

If (x,y)=(0,0), (8) gives U_0^0(p^n)→0. But player 0 can guarantee one
by quitting at date zero, contradicting e_n→0.

If (x,y)=(1,1), (8) gives U_0^0(p^n)→1. Against the unchanged opponents,
player 0's Never payoff is

    3 Σ_t p_1^n(t)p_2^n(t)p_3^n(t)=3y_n+o(1)→3.

Indeed its only nonzero passive reward is three when the opponents all
quit at the same finite date. This unrestricted deviation has gain tending
to two, again contradicting e_n→0. Both limits are impossible, proving
the theorem. If the displayed infimum were zero, choosing profiles with
E_0+ρ<1/n would give the forbidden sequence; hence the infimum is positive.

## 4. Why the common bonus is not a monotone repair potential

The same table has a transparent exact incentive check. Let B={0,1,2}
quit surely at date zero and let player 3 choose Never. This is exact Nash
in the capped game: each participant gets one rather than passive zero;
player 3 gets 3/2 rather than the capped grand reward one.

After raising grand rewards to two, player 3 strictly prefers to join:
its base payoff change is −1/2 and the bonus change is +1, for net +1/2.
This takes Γ from zero to one. At the resulting grand-coalition profile,
player 0 strictly prefers to leave: its base payoff change is +2 and its
bonus change is −1, for net +1. This takes Γ back from one to zero and
arrives at the exact equilibrium C from Section 2.

The full exploitabilities along these three profiles in the raised game
are respectively 1/2, 1, and 0. Every number is an unrestricted behavioral
comparison because the other players force date-zero absorption.

Thus a newly profitable deviation at an OLD exact equilibrium must increase
Γ by (2), but the implication does not persist after the profile changes.
At Γ=1 in this table, player 0 can obtain three by Never instead of the
grand reward two, so keeping Γ=1 cannot repair its gain of one. This is a
failure of monotone event-ascent repair, not of a nonmonotone selector.

The all-law theorem in Section 3 is stronger than this local illustration:
it rules out every capped-source sequence satisfying (CS), regardless of
how it is selected or how its dates and supports change.

## 5. Source correspondence and exact stopping point

A narrow search for grand-coalition bonus perturbations and shared-event
selection found no duplicate used here. The source route was terminal
payoff transport, selected from `docs/TOOLKIT.md`. Directly inspected:

- `quittingTerminalPayoff` in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Asymptotic.lean`,
  the finite sum of actual terminal masses times coalition rewards.
- `quittingAbsorbedMassLimit_congr_reward` in
  `UniformEquilibrium/Quitting/Classification/TableExistenceBranches.lean`,
  stating that these masses and the strategy carrier do not change merely
  when the reward table changes. Together these give (1).
- `quittingTerminalPayoff_playerwiseAffine` in
  `UniformEquilibrium/Quitting/Terminal/TerminalAffineReward.lean`, which
  illustrates why terminal-only changes must retain their actual-event
  probability. It shifts ALL terminal coalitions and is not itself the
  one-grand-coalition formula claimed here.
- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`, the exact
  unrestricted-deviation stopping-law mixture interface. The event kernel
  used for κ_i has the same independent law interpretation.

No new literature theorem or Lean-checked result is claimed. The proof
uses exact finite reward data and arbitrary countable stopping laws; it
does not infer openness from closedness, use a common random clock, or
replace independent strategies with a correlated mixture.

The surviving exact statement is the identity (2) and fixed-profile bound
(3). No positive law-changing source mechanism follows from them here.
The attempted robust selector (CS) is false; the finer signed base-payoff
terms can compensate a large ρ at a genuine raised-game equilibrium, as C
already demonstrates. A successful construction must exploit such actual
incentive compensation or another source, not assume that capped-game Nash
and negligible event-response gaps can be selected together.

Concrete next question for the independent construction route: can it
control the raised game's full deviation gains directly, without requiring
the false capped-source condition (CS)? This note supplies no answer to
that positive question and stops this selection mechanism.
