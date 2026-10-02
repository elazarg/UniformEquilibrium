# Construct approximate forward packets beyond bounded exact capacity

## Game, deviations, and punishment

There are four players I = {0,1,2,3}. At each date in ℕ, each player
independently chooses Continue or Quit. The first nonempty quitting coalition
S ends play and pays r(S) ∈ ℝ⁴. Infinite all-Continue pays zero. Fix M > 0
such that |r_i(S)| ≤ M for every i and nonempty S.

Before termination there is one live public history at each date. Thus a
behavioral strategy can be represented by a stopping law on ℕ ∪ {Never};
the four laws are independent. A unilateral deviation may replace one
player's complete law, including arbitrarily late finite dates and Never.

For a product law p, define

    U_i(p) = its expected terminal reward;
    B_i(p) = sup over all replacement laws μ_i of U_i(μ_i,p_{−i});
    d_i(p) = B_i(p)−U_i(p);
    E(p) = max[i ∈ I] d_i(p);
    D_* = inf over all product laws p of ∑[i ∈ I] d_i(p);
    P_i = inf over all independent opponent laws p_{−i} of B_i(p).

The definition of P_i uses unrestricted behavioral replies, not finite-menu
replies or publicly correlated opponent plans. Consider the contrary case

    D_* > 0,       P_i ≤ r_i({i}) for every i.

Every four-player game without a uniform-equilibrium payoff satisfies these
conditions. Producing terminal profiles with E tending to zero rules out
this case and yields one fixed uniform-equilibrium payoff. Here uniform means
that, at every positive accuracy, one profile and one finite horizon threshold
work for every longer horizon and every unilateral behavioral deviation;
the payoff target is fixed before the accuracy.

## Root payoffs

For q ∈ [0,1]⁴ and S ⊆ I, put

    p_q(S) = ∏[i ∈ S] q_i · ∏[i ∉ S] (1−q_i),
    c(q) = p_q(∅),       a(q) = 1−c(q),
    F(q,v) = ∑[S ≠ ∅] p_q(S)r(S)+c(q)v.

For player i and T ⊆ I\{i}, put
p_{q,−i}(T) = ∏[j ∈ T] q_j · ∏[j ∉ T, j ≠ i] (1−q_j). Its pure root
payoffs against continuation v are

    Q_i(q,v) = ∑[T ⊆ I\{i}] p_{q,−i}(T)r_i(T∪{i}),
    C_i(q,v) = ∑[∅ ≠ T ⊆ I\{i}] p_{q,−i}(T)r_i(T)
                 +p_{q,−i}(∅)v_i,
    A_i(q,v) = max(Q_i(q,v),C_i(q,v)).

Thus F_i(q,v) = q_i Q_i(q,v)+(1−q_i)C_i(q,v). The root is
support-δ Nash against v when

    q_i > 0  implies  Q_i(q,v) ≥ A_i(q,v)−δ;
    q_i < 1  implies  C_i(q,v) ≥ A_i(q,v)−δ.

These are unweighted inequalities for every used action. Ordinary mixed-root
regret at most δ is weaker when an inferior action is rarely used.

## Question

For every reward table satisfying the contrary-case assumptions, construct
one finite B ≥ M such that the following holds for the fixed compact box
K = [−B,B]⁴:

For every δ > 0 and every Q ≥ 0, there are an integer H ≥ 0, values
v_0,…,v_H in K, and roots q_0,…,q_{H−1} in [0,1]⁴ satisfying

    v_{t+1} = F(q_t,v_t)                         for 0 ≤ t < H;
    q_t is support-δ Nash against v_t            for 0 ≤ t < H;
    ∑[t=0..H−1] a(q_t) ≥ Q.

The bound B is chosen before both δ and Q. The packet length and the
individual values and roots may depend on both. The construction index runs
outward through successive prefixes: play order is q_{H−1},…,q_0, with
continuations v_{H−1},…,v_0. In particular the comparison for q_t uses v_t,
not v_{t+1}.

No individual-security floor is supplied for the annotations, and they need
not be terminal payoffs of actual profiles. Under the assumed normality,
bounded approximate words acquire the required punishment floors after
discarding a bounded number of construction rows. That number depends on
accuracy and the fixed box, not on requested charge. Requesting the extra
charge first leaves any desired charge afterward. Compact charged recurrence
and the reversed play order then yield terminal approximate Nash profiles.
The question asks for the words themselves, not verification of supplied data.

## Equivalent absorption-weighted formulation

It is equivalent to construct, in some one fixed box [−B,B]⁴ with B ≥ M,
for every δ > 0 and Q ≥ 0, a finite word satisfying

    |v_{t+1}(i)−F_i(q_t,v_t)| ≤ δ a(q_t)          for every t < H and i;
    A_i(q_t,v_t)−F_i(q_t,v_t) ≤ δ a(q_t)          for every t < H and i;
    ∑[t=0..H−1] a(q_t) ≥ Q.

There is again no punishment-floor condition. The box is chosen before both
accuracy and charge. Passing between the two formulations may enlarge that
one box; a separate box for each requested word is not permitted.

These are ordinary mixed-root regret bounds, not support inequalities. Their
errors are weighted by the absorption of the same root. Replacing them by
unweighted error δ, or by an error bound only after summing along one chosen
path, is not this equivalent formulation. At a zero-absorption row both
displayed errors must vanish exactly.

## Exact-capacity obstruction

Under the contrary-case assumptions, for every fixed finite B ≥ M there is a
finite C_B such that every positive-length exact block with values
w_0,…,w_H in [−B,B]⁴, equations

    w_t = F(x_t,w_{t+1}),

and exact root Nash at x_t against w_{t+1} satisfies

    ∑[t=0..H−1] ∑[i ∈ I] x_t(i) ≤ C_B.

The bound ranges over all such blocks in that fixed box, independently of
their lengths. Consequently every infinite exact spine whose values have
one uniform bound in time has ∑[t≥0] x_t(i) < ∞ for every i. An individual
finite block's boundedness, or a new box chosen separately for each charge
target, is not this uniform statement.

The two charges obey a(q) ≤ ∑[i]q_i ≤ 4a(q). Bounded exact capacity does
not itself produce the approximate packets, bound every positive-tolerance
packet class, or contradict the game assumptions.

## A sufficient summable-error construction

A different complete positive answer is to construct, from the same
reward-table assumptions, one infinite sequence of roots x_t, values w_t,
nonnegative errors b_t,n_t, and a fixed player k such that

    sup[t,i] |w_t(i)| < ∞;
    ∑[t≥0] b_t < ∞,       ∑[t≥0] n_t < ∞;
    |w_t(i)−F_i(x_t,w_{t+1})| ≤ b_t            for every t,i;
    A_i(x_t,w_{t+1})−F_i(x_t,w_{t+1}) ≤ n_t    for every t,i;
    ∑[t≥0] x_t(k) = ∞.

These are ordinary unweighted error sums on one sequence in play order.
The punishment-normal inequalities assumed above make one fixed persistent
player sufficient for a terminal and uniform-equilibrium conclusion.
Existence of this sequence must be proved; ruling out an unspecified class
of “compatible” sequences is not enough. Separate blocks or labels chosen
independently at successive stages do not supply it.

## Scope of a complete answer

The packet construction or the stated infinite construction is sufficient;
neither is asserted necessary for all proofs of uniform equilibrium.
A direct contradiction of the contrary-case assumptions is also sufficient.
A complete negative answer is an explicit four-player reward table and
Γ > 0 such that every behavioral product law admits a unilateral behavioral
deviation improving its terminal payoff by at least Γ.

A positive root at one fixed value, compact recurrence without the displayed
Bellman matching, or support errors growing with packet length do not answer
the producer question. Repeating the exact-capacity bound alone does not
consume its bounded branch.
