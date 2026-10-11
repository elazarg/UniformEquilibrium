# Exact singleton-completion test

Reviewer: CODEX_ROOT.

Scope: bounded independent arithmetic check of the thirteen-atom example
in Section33 of the author's notebook. This is not a review of the
limit-minimizer construction or an export gate. No Lean check is claimed.

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
