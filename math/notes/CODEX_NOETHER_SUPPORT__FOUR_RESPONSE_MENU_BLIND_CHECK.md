# Blind check: four prescribed response rules balance on actual laws

Identity: CODEX_NOETHER_SUPPORT.

Status: independent proof completed from ROOT's statement before reading
the author proof or nearby verdicts. The claim is true by an explicit
cumulative-law recursion. This is not an equilibrium existence theorem.
Source/priority comparison remains pending in a separate follow-up section
or feedback record; no export or Lean work is authorized.

## Exact interpretation and claim

There are four players. A profile is an independent product of laws p_i on
N∪{Never}. Each player i has fixed nonnegative finite weights a_i,b_i,c_i,d_i
on, respectively: Quit at date zero; Never; independently sample all three
opponents' stopping laws and Quit one date after their minimum; independently
sample them and Quit one date after their maximum. Addition sends Never
to Never. The samples are private independent copies, not observations of
the actual opponents' future stopping times.

Claim: there is an actual independent profile p, depending only on these
weights and not on the reward table, for which each player's weighted sum
of the four complete-response payoff gains is zero for every bounded real
reward table, with zero Never payoff (and in fact with any fixed payoff
functional affine in that player's law).

## Direct construction, including zero total weights

Put λ_i=a_i+b_i+c_i+d_i. If λ_i=0, choose p_i=δ_Never and define
F_i(t)=0 for every finite t. Its weighted gain is automatically zero.

For the remaining players define finite-date cumulative probabilities
recursively, simultaneously for all four players:

    F_i(0)=a_i/λ_i,
    F_i(t)=a_i/λ_i
           +(c_i/λ_i)[1−∏_{j≠i}(1−F_j(t−1))]
           +(d_i/λ_i)∏_{j≠i}F_j(t−1)       for t≥1.   (1)

Every coordinate of this recursion is nondecreasing in each input on
[0,1]. Its output lies in [0,1], and its value at all-zero inputs is
F_i(0). Induction proves 0≤F_i(t)≤F_i(t+1)≤1 for every player and date.
Let ℓ_i=lim_t F_i(t). Define an actual probability law by

    p_i(0)=F_i(0),
    p_i(t)=F_i(t)−F_i(t−1)           for t≥1,
    p_i(Never)=1−ℓ_i.

All masses are nonnegative and their sum is exactly one. This construction
does not assume the recursive clock terminates almost surely.

Against the independent opponent copies, the distribution of one plus
their minimum has finite CDF

    1−∏_{j≠i}(1−F_j(t−1))             for t≥1,

and one plus their maximum has finite CDF

    ∏_{j≠i}F_j(t−1)                    for t≥1.

Both CDFs are zero at date zero. Therefore (1) says precisely that p_i
equals the normalized weighted mixture of the four response laws. Equality
at all finite CDF values also fixes the Never mass; no mass is lost at
infinity. This handles max responses with some sampled Never, min responses
with all samples Never, and arbitrary actual opponent Never atoms.

## Payoff conclusion and limitation

For fixed actual opponent laws, expected payoff is affine in player i's
independent replacement law. Write R_i^k(p_−i) for the four response laws.
For λ_i>0 the identity of probability laws just proved gives

    Σ_k w_i^k[U_i(R_i^k(p_−i),p_−i)−U_i(p)]
      =λ_i[U_i(p_i,p_−i)−U_i(p)]
      =0.

For λ_i=0 this equality is tautological. Since the equality precedes any
choice of payoff table, the SAME p works for every bounded reward table.
Boundedness ensures that all expectations and affine mixtures are defined.
No common randomization or correlated product-law mixture is used.

This balances weighted gains, not their maximum and not each response
gain separately. It supplies neither exact Nash nor approximate Nash nor
a uniform-equilibrium payoff. Its immediate certificate implication is
only that a fixed nonnegative weighting of these response gains cannot
be strictly positive at every actual independent law.

The construction is also the triangular version of a continuous-law-map
fixed point on compact stopping-law spaces. Whether excluding this particular
certificate is a new useful research boundary requires the promised narrow
source comparison; the blind proof by itself supplies no novelty claim.
