# Exact finite-clock completion tests

Reviewer: CODEX_ROOT.

Scope: bounded independent arithmetic checks of the thirteen-atom example
in Section33 and the private-recommendation examples in Section36 of the
author's notebook. This is not a review of the general source or
limit-minimizer constructions or an export gate. No Lean check is claimed.

## Law and complete response class

Use the cyclic four-player K10 reward table specified by `reward_table`
in `experiments/CODEX_NASH_BOX__FINITE_CLOCK_JOINT_APPROXIMATION.py`.
The old law puts probability1/5 on each adjacent pair and the grand
coalition quitting at date1; all nonmembers Never.

The new law retains each old atom with probability9/50. Its other
probability1/10 has player0 quitting at date0 and independent opponent
clocks quitting at date1 with probabilities(3/5,1/10,3/5), otherwise
Never. This specifies thirteen distinct atoms of total mass1.

Direct rational enumeration gives the following prescribed values and
unilateral reply values, with columns deadline0,deadline1,deadline2,Never:

| Player | Prescribed | Replies |
| --- | --- | --- |
| 0 | 113/50 | 1,1839/1250,1127/500,5599/2500 |
| 1 | 54/25 | 11/10,36/25,54/25,54/25 |
| 2 | 64/25 | 9/10,46/25,64/25,64/25 |
| 3 | 54/25 | 4/5,36/25,54/25,54/25 |

Every later finite deadline has exactly the deadline2 payoff because all
opponent clocks are date0,date1,or Never. An uninformed independent
randomized stopping law is a mixture of these pure response classes.
Thus no omitted finite deadline or Never can exceed the prescribed
value. This is full coarse obedience of a CORRELATED clock law, not
Nash obedience of its independent product marginals.

## Information comparison

Computing total correlation as the sum of marginal entropies minus joint
entropy, rational logarithm enclosures from `log_interval` and
`entropy_interval` in
`experiments/CODEX_NASH_BOX__CORRELATED_ROOT_CONTROL.py` give

    I(old)>108/100,
    I(new)<1025/1000,
    I(old)-I(new)>58/1000.

The enumeration used exact `Fraction` arithmetic. Logarithms were
bounded by the rational atanh series with24 terms and its explicit
geometric remainder, not by floating-point inequalities. The descriptive
values are1.0826087556 and1.0242678961.

## Verdict and boundary

The finite test passes. Retaining a nontrivial counterfactual opponent
team can lower information while maintaining all coarse constraints;
the absorbed-branch Never-reset obstruction does not exclude this
operation. The test supplies neither a repeatable global decrease nor
information tending to zero. Its table already has a uniform-equilibrium
payoff by a separate argument. The general source-variation theorem and
the feasibility of variations at an ordered-law limit require their own
proof and review.

## Private recommendation tests

For the same K10 table, choose J uniformly among the four players and B
uniformly in {0,1}, independently. Put the owner's clock at0, its
successor's clock at2-B, and the other clocks at1+B. Exact rational
enumeration of these eight atoms gives, for every player,

    prescribed payoff = 5/4,
    largest unconditional response payoff = 9/8,
    largest recommendation-dependent gain = 0.

The private gain was computed by partitioning atoms by the player's own
recommended clock and summing the maximum nonnegative response gain in
each part. Responses include deadlines0,1,2,3 and Never. Every later
finite deadline has the deadline3 payoff because an opponent stops by2
even after deleting the tested player. Thus this finite check covers all
complete private-recommendation replacements for this law.

For the owner/punisher family, choose J uniformly, Q uniformly in
{0,...,M-1}, and P uniformly in {M,...,2M-1}, independently. The owner
stops at Q, its successor at P, and the other players at P+1. Direct
rational enumeration gives the following bounded checks:

| M | Full private source gain | Reference-completion atoms | Tested private-map gain after completion |
| --- | --- | --- | --- |
| 4 | 5/64 | 480 | 7/64 |
| 8 | 9/256 | 6528 | 8829/117760 |

The reference completion fixes the first and second events and samples
the two remaining clocks independently from the original marginal
conditioned to exceed P. Its total mass is exactly1 in both checks.
The tested private map replaces recommendations in [M,M+M/4] by Quit0
and retains every other recommendation. Its gain exceeds1/32 for every
player in both tests.

These calculations independently confirm the stated finite values and
the distinction between coarse and private recommendation obedience.
They do not check the general all-M bound, the paper-source adapter,
information-infimum attainment, or a vanishing-information producer.
