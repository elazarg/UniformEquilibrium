# Consume a mixed first collision at a debt-rigid terminal-debt minimum

## Game and unrestricted response values

There are four players I={0,1,2,3}. At each date in ℕ each player
independently chooses Continue or Quit. The first nonempty quitting
coalition S pays r(S)∈ℝ⁴; infinite all-Continue pays zero. Fix M>0 with
|r_i(S)|≤M for every reward coordinate, and write s_i=r_i({i}).

A behavioral profile p is equivalently four independent stopping laws on
ℕ∪{Never}. A deviator may replace its complete law, including arbitrarily
late finite dates and Never. No common random seed is available. Define

    U_i(p)=the prescribed expected terminal payoff,
    B_i(p)=sup over all replacement laws μ_i of U_i(μ_i,p_{−i}),
    d_i(p)=B_i(p)−U_i(p),
    D(p)=∑[i∈I] d_i(p).

Let K be the Euclidean closure of all actual pairs (U(p),B(p)). It is
compact. For w=(u,b)∈K put D(w)=∑[i∈I](b_i−u_i), and let

    δ=min[w∈K] D(w)=inf[actual p] D(p).

Assume δ>0. This is a lower bound against every actual behavioral profile,
not only finite-clock, stationary, or bounded-memory profiles.
Membership in K does not assert that the pair is realized by one profile.

Assume all own singleton rewards s_i are strictly positive, and for every
player i there is j≠i such that r_i({j})≤s_i.

Assume recipient-row genericity: for each i, the numbers r_i(S) are
pairwise distinct as S ranges over nonempty coalitions. Assume also that
there is one nonnegative vector a, with ∑[i∈I]a_i=δ, such that

    D(w)=δ ⇒ d_i(w)=a_i for every i and every w∈K.

Only the debt vector is common. Minimizing payoffs, caps, laws and
calendars need not coincide. Some a_i may be zero.

## Supplied first-row decomposition

Fix an actual carrier continuation v=(u,b)∈K and an independent product
root q∈[0,1]⁴. Player i Quits at the first date with probability q_i;
on all-Continue the continuation is v. This means the continuous semantic
limit of literal one-row prefixes over actual realizing tails, not play
followed by an unattained strategy at an infinite date.

For T⊆I\{i} put

    p_{−i}(T;q)=∏[j∈T] q_j · ∏[j∉T,j≠i](1−q_j),
    α_i(q)=∏[j≠i](1−q_j),
    A_i(q)=∑[∅≠T⊆I\{i}] p_{−i}(T;q) r_i(T),
    Q_i(q)=∑[T⊆I\{i}] p_{−i}(T;q) r_i(T∪{i}),
    C_i(q)=A_i(q)+α_i(q)b_i.

The complete first-row pair T_q(v)=(u′,b′) is

    u_i′=q_i Q_i(q)+(1−q_i)[A_i(q)+α_i(q)u_i],
    b_i′=max(Q_i(q),C_i(q)).

These caps cover every behavioral response, not just changing the first
action: Continuing permits the complete tail response valued at b_i.
Every T_x(w), x∈[0,1]⁴ and w∈K, belongs to K. Require

    D(T_q(v))=δ,
    R(q)=∑[S⊆I,|S|≥2] ∏[i∈S]q_i · ∏[j∉S](1−q_j)>0.

Thus a nonsingleton event occurs at the first root of a genuine global
minimum. The row need not be Nash against u or b. The tail need not
minimize debt; its only automatic lower bound is D(v)≥δ. Rates zero and
one are allowed. No positive Never probabilities are assumed, and no
conditioning on a zero-survival event is permitted.

## Constraint on every minimum prefix

Require the following on the ENTIRE same carrier, not just the supplied
row. For every x∈[0,1]⁴ and w∈K with

    ∑[i∈I]x_i>0,      D(T_x(w))=δ,

at least two rates x_i are positive, at least one lies strictly between
zero and one, and some player i satisfies

    Q_i(x)=A_i(x)+α_i(x)b_i(w).

Thus every nonzero minimum prefix has a random first-root coalition law
and an exact tie between Quit and the complete Continue response value.
The player realizing the tie may have zero debt and zero prescribed
root Quit probability. Sure quitters and α_i(x)=0 remain allowed.

For every such row, a tied player's positive singleton margin implies
that some nonempty opponent coalition S has p_{−i}(S;x)>0. On that
event, Quit pays r_i(S∪{i}) and Continue pays r_i(S), which are different
by row genericity. This is a genuine payoff-kernel distinction, although
the complete expected response values tie. It is not a positive gain.
No tail stopping date is assumed to attain b_i(w).

This global condition applies again after any proved same-table
minimum-preserving graft or reconstruction. A tie at one supplied row
alone would not license that reuse. A reward-table change requires
re-establishing the conditions for the changed table and carrier.

## Quantitative minimum constraints

The following all-owner inequalities are available at every minimizing
pair w=(u,b)∈K, with γ=δ²/(8M):

    b_i−s_i≥δ+γ,
    u_i−s_i≥δ−(b_i−u_i)+γ≥γ.

For the supplied decomposition put c(q)=∏[i](1−q_i) and
g_i(q)=Q_i(q)−C_i(q). Its exact total-debt identity is

    δ=c(q)D(v)+∑[i∈I][max(g_i(q),0)−q_i g_i(q)].

Every summand is nonnegative. In particular,

    0≤∑[i∈I][max(g_i(q),0)−q_i g_i(q)]≤(1−c(q))δ.

No equality D(v)=δ or root-Nash conclusion follows from this identity.
The collision also gives α_i(q)≤1−R(q) for every i; contraction of this
fixed prefix does not assert that iterating it preserves minimality.

The global variational condition is stronger than D(v)≥δ: the supplied
tail v minimizes G_q(w)=D(T_q(w)) over every w∈K, with value δ. Root
changes and whole-tail changes must both respect the same global bound;
neither optimization is restricted to one selected continuation or one
selected best response.

## Available clock-class reduction

Let K_abs be the closure of full payoff/cap pairs of actual profiles
with Pr(AllNever)=0. Let K_fin be the closure of those pairs when each
of the four marginal stopping laws assigns zero mass to Never. The caps
in these definitions still range over every behavioral replacement.

The nonnegative own singleton rewards and the row witnesses above give
the entire-carrier identity K_fin=K_abs. If a_k=0 for some player k, then
the exact bound s_k·Pr_p(AllNever)≤d_k(p), together with full-response
coupling of small Never-mass replacements, gives

    min[K_abs]D=δ,
    {w∈K_abs:D(w)=δ}={w∈K:D(w)=δ}⊆K_fin.

Consequently either every a_i is positive, or every original minimum
pair has an actual realizing sequence with all four clocks finite almost
surely. This permits choosing new realizers; it is not a claim about
every old realizing sequence. Each new approximant may have finite support;
there need not be a uniform support bound, raw-date tightness, a uniform
expected stopping-time bound, or realization of a minimum pair by one
actual profile. The supplied continuation v still need not
be minimizing or Nash; the variational constraint remains over all K.

## Question

For every reward table and every collection of data satisfying these
conditions, construct an actual behavioral product law π on the same
table such that

    D(π)<δ,

or prove directly that the supplied conditions are inconsistent.

A positive four-player terminal-gap table, if one exists, permits
reselection to a bounded table with the positive singleton rewards,
row witnesses, common-debt and universal minimum-prefix properties
above and at least one nonzero minimum
prefix. No old minimizing law is asserted to survive that table change.
Consequently an affirmative answer rules out positive terminal gaps and
gives uniform-equilibrium payoff existence. In that conclusion one fixed
payoff target must work at every accuracy: the profile and horizon
threshold may depend on the accuracy, but for that profile the payoff
and all unilateral gains must satisfy the error bound at every larger
finite-average horizon.

It is also acceptable to produce a more restrictive class from arbitrary
positive-gap game data and prove inconsistency there. Any additional
strategic or reward-table condition must be produced by that reduction,
not assumed for one convenient selected profile.

A complete negative answer is an explicit four-player table and Γ>0
such that, against every behavioral profile, some unilateral behavioral
deviation improves terminal payoff by at least Γ. A lower bound for a
restricted strategy class is not such an answer.

## Requirements on a consuming argument

All modifications must be actual independent laws on the same reward
table, or limits whose membership in K is proved. If simultaneous tail
changes or counterfactual timing comparisons are used, select actual
realizing profiles and calculate their complete response values. The
finite pair v alone is not a compositional description of those changes.

For a one-player replacement p→ρ by player i, its own cap is unchanged,
so exactly

    D(ρ)−D(p)=−[U_i(ρ)−U_i(p)]
                +∑[j≠i][d_j(ρ)−d_j(p)].

The other caps are unrestricted and may switch their maximizing stopping
times. A positive mover gain alone is therefore not a descent. Every
tied maximum must remain in the calculation; choosing favorable response
branches independently for different variations is insufficient.

A finite cycle of same-date profiles is not a temporal chronology.
A temporal argument must prove its actual continuation matching and
accumulated error control. A rank argument must give a total renewable
transition with a strict well-founded decrease, and consume every
terminal state. Neither construction is required: any rigorous
same-table proof reaching the strict-debt conclusion is acceptable.
