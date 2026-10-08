# Consume a least-Never fully paid nonsure collision at a separated debt minimum

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

Let K_abs be the closure of full payoff/cap pairs of actual profiles whose
prescribed play absorbs almost surely. For independent stopping laws this
means Pr(AllNever)=0, or equivalently at least one marginal has zero Never
mass. Caps still range over every behavioral replacement. Assume a STRICT
separation from the original full minimum:

    min[w∈K_abs]D(w)=δ+g,       g>0.

Assume all own singleton rewards s_i are strictly positive, and for every
player i there is j≠i such that r_i({j})≤s_i.

Assume recipient-row genericity: for each i, the numbers r_i(S) are
pairwise distinct as S ranges over nonempty coalitions. Assume also that
there is one STRICTLY POSITIVE vector a, with ∑[i∈I]a_i=δ, such that

    D(w)=δ ⇒ d_i(w)=a_i for every i and every w∈K.

Only the debt vector is common. Minimizing payoffs, caps, laws and
calendars need not coincide.

## Least literal Never among all full minima

For an actual profile p let ν(p)=Pr_p(AllNever). Retain this actual
coordinate together with its complete payoff/cap pair, and put

    H=closure{(U(p),B(p),ν(p)): p is an actual product-law profile},
    H_min={(u,b,ν)∈H: D(u,b)=δ},
    ν*=min{ν:(u,b,ν)∈H_min}.

The compact sets H and H_min are nonempty, and the strict absorbing
gap implies ν*>0. The selection ranges over ALL full minima, not one
fixed semantic fibre or one chosen sequence. H is not formed by freely
adjoining a probability to a semantic pair: every triple has one common
actual realizing sequence for all three coordinates.

Require the supplied first-row decomposition below to realize a triple
with literal full-profile Never probability ν*. The existence of some
other triple above the same payoff/cap pair with probability ν* is not
sufficient. Conditional suffix Never and finite clocks escaping to infinity
are not substituted for this coordinate.

## Supplied first-row decomposition

Fix an augmented carrier continuation (u,b,ν_tail)∈H, write v=(u,b),
and fix an independent product root q∈[0,1]⁴.
Player i Quits at the first date with probability q_i;
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

The literal augmented prefix is

    T̂_q(u,b,ν_tail)=(u′,b′,c(q)ν_tail),
    c(q)=∏[i∈I](1−q_i),       c(q)ν_tail=ν*.

Its witnesses prefix the same fixed row q to actual tails jointly
realizing (u,b,ν_tail). Thus the complete prefixed triple belongs to
H_min and retains the selected FULL-profile coordinate. Neither the
tail's semantic pair nor its Never probability is required to be minimal.

Thus a nonsingleton event occurs at the first root of a genuine global
minimum. The row need not be Nash against u or b. The tail need not
minimize debt; its only automatic lower bound is D(v)≥δ. Zero rates are
allowed, but no rate is one. Every positive rate is strictly mixed.
No conditioning on a zero-survival event is permitted.

## Constraint on every minimum prefix

Require the following on the ENTIRE same carrier, not just the supplied
row. For every x∈[0,1]⁴ and w∈K with

    ∑[i∈I]x_i>0,      D(T_x(w))=δ,

at least two rates x_i are positive, every rate is strictly below one,
and some player i satisfies

    Q_i(x)=A_i(x)+α_i(x)b_i(w).

Thus every nonzero minimum prefix has a random first-root coalition law
and an exact tie between Quit and the complete Continue response value.
The player realizing the tie has positive debt a_i, although its prescribed
root Quit probability may be zero. Every α_i(x) is positive.

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

## Uniform Never mass and finite response witnesses

For an actual profile put ν(p)=∏[i∈I]p_i(Never). The exact singleton
bound and complete-response coupling of a smallest Never-mass replacement give

    s_iν(p)≤d_i(p),
    δ+g≤D(p)+14Mν(p)^(1/4).

Thus every profile with D(p)≤δ+g/2 has

    ν(p)≥η=(g/(28M))⁴>0,
    p_i(Never)≥η,       d_i(p)≥s_iη       for every i.

This applies to EVERY sufficiently near-minimal actual profile and every
realizing sequence of every full minimum. It is not a tightness or actual
minimum-attainment assertion. In particular every nonzero minimum prefix
above has c(x)≥η.

For fixed opponent laws, writing h_i=∏[j≠i]p_j(Never), a delayed finite
response has limit

    V_i(t,p_{−i})→V_i(Never,p_{−i})+h_i s_i.

Near-minimizers therefore have literal Never strictly below the full cap,
and the full cap is the supremum over finite responses. At a tied minimum
prefix, Quit at its first root and finite responses strictly later in its
realizing tails approach the SAME cap. Both gains over the prescribed
profile approach the positive debt a_i. Exact cap attainment at an ordinary
finite date is not assumed.

For any nonempty opponent coalition S at that root with positive probability,
the first response pays r_i(S∪{i}), whereas the later response pays r_i(S).
Row genericity distinguishes the two payoff kernels on that positive event;
their expected response values can nevertheless tie.

## Complete periodic-replay account

Take a finite-law minimizing sequence realizing the supplied minimum prefix.
For each approximant, form a finite block ending after every finite atom
and including an empty final response date. Repeat its original hazard word
forever; each player uses its own independent draws. Write U_i,B_i for its
original full profile values, R_i for its literal Never payoff, n_i for its
marginal Never mass, ν=∏[i]n_i and h_i=∏[j≠i]n_j.

With h_i<1 for every i and ν<1, this actual absorbing periodic profile has

    prescribed payoff U_i/(1−ν),
    full behavioral cap max(B_i,R_i/(1−h_i)).

The supplied minimum prefix has at least two positive suppliers, so these
denominators stay positive along sufficiently late approximants. After a
joint subsequence of the bounded scalar data, keep the same symbols for
their limits. The absorbing debt floor gives

    ∑[i∈I](R_i/(1−h_i)−B_i)⁺
      ≥g+ν/(1−ν)·∑[i∈I]U_i>0.

Here U_i>s_i>0 by the quantitative minimum bounds. Periodic replay must
therefore create a new upper response cap. Payoff improvement under renewal
does not assert a debt decrease or a usable temporal return.

## Question

For every reward table and every collection of data satisfying these
conditions, construct an actual behavioral product law π on the same
table such that

    D(π)<δ,

or prove directly that the supplied conditions are inconsistent.

A positive four-player terminal-gap table, if one exists, permits
reselection to a bounded table with the positive singleton rewards,
row witnesses, STRICT full/absorbing gap separation, common positive debt
and universal nonsure minimum-prefix properties above. A least literal
Never triple and a nonzero minimum prefix realizing that same triple
can also be selected. No old minimizing law is asserted to survive that
table change, and no raw clock profile attaining the triple is assumed.
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
