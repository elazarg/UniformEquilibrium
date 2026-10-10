# Bounded check of the entire-correspondence limit-order calculation

Reviewer: CODEX_TURING_BOX.

Status: ordinary mathematical bounded PASS of Section 6's M_N calculation.
This is not a review of the robust terminal-table perturbation theorem,
the discontinuous-game source audit, a Lean check or an export gate.

## Claim checked

For the fixed rational table in Section 2 and F_N={0,...,N-1,Never}, let
M_N(delta) be the minimum ORIGINAL complete terminal exploitability over
all private-bonus vectors b=(0,b_1,b_2,b_3) in {0} times [0,delta]^3 and
all exact Nash profiles of the auxiliary finite game. The bonus is paid
for the player's privately planned Never action, regardless of when an
opponent absorbs. The claims checked are

    for fixed N: lim_{delta down to 0} M_N(delta)=18/49,
    for fixed delta>0: inf_{N>=1} M_N(delta)=0.

The scope is this solved table and this entire finite correspondence.

## Compactness, objective and fixed-menu limit

For fixed N the product of four F_N simplexes is compact. Each auxiliary
payoff is a continuous polynomial in the product probabilities and bonus
parameters. Its finite pure-action best-response inequalities define a
closed Nash graph. Every bonus parameter has a finite-game equilibrium,
so the joint feasible set in the compact bonus box is nonempty and compact.

The ORIGINAL full cap is indeed a finite maximum, not a menu cap in
disguise. Once all prescribed opponents' finite dates precede N, every
pure date at or beyond N has the same value

    original Never response + own singleton reward
                              * product opponent Never masses.

It therefore suffices to include that one late value along with the finite
menu values and Never. All are polynomial in the fixed finite profile.
Consequently the full maximum-debt objective is continuous and its stated
minimum is attained.

I checked only the delta=0 specialization of Section 2's finite-Nash
classification needed here. Its final core root is (2/7,4/7,1/7), with
dummy Never, giving continuation values (31/7,19/7,34/7,31/49). The
displayed exhaustive earlier-root support inequalities force all-Continue
against this continuation. The positive-reach argument permits backward
induction on every date. Thus the original finite-menu equilibrium is
unique and all finite action occurs at the final root. Its only omitted
full gain is the pivot's product (1-4/7)(1-1/7)=18/49. Nonpivot late values
equal their Never values because their own singletons are zero.

Now take any sequence of bonuses tending to zero and corresponding
minimizers. A convergent profile subsequence has a zero-bonus exact Nash
limit by the closed finite graph. Continuity of the ORIGINAL FULL objective
forces the limiting gap to 18/49. The zero-bonus vector remains feasible
at every delta, furnishing the reverse bound. This proves the fixed-N
limit without any uniform-in-N compactness assertion.

## Positive-bonus joint-menu limit

For N with 1/N<=delta, prescribe pivot uniform on all N finite dates and
every other player Never, with b_1=1/N and b_2=b_3=0. The pivot receives
1 and has no better original or augmented action. Player 1's finite date
t has original value (7t+8)/N, maximized at 7+1/N, exactly its augmented
Never payoff. Player 2's finite value (7t+5)/N never exceeds its Never
payoff 7. Dummy finite values are -1/N and Never is zero. These exhaust
the finite auxiliary pure actions and establish exact auxiliary Nash.

The ORIGINAL full regret is exactly 1/N, solely at player 1. Every late
nonpivot date agrees with its original Never response, and the pivot's
opponents Never, so it has no omitted late gain. Hence
0<=M_N(delta)<=1/N for arbitrarily large N, proving the second claim.

## Verdict and scope

Both displayed iterated limits follow. This evaluates the best point of
the ENTIRE auxiliary correspondence; an arbitrary bad equilibrium branch
does not falsify it. It also changes the menu jointly with bonus accuracy,
so a fixed-menu perturbation limit is not an obstruction. No universal
table producer or completeness of private-Never exactification follows.
No mathematical objection was found within this bounded claim.
