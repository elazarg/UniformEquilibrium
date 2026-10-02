# Turn an actual quantitative paid row into debt below the global infimum

## Game and full terminal debts

There are four players I = {0,1,2,3}. At each date in ℕ, each player
independently chooses Continue or Quit. The first nonempty quitting
coalition S pays r(S) ∈ ℝ⁴; infinite all-Continue pays zero. Fix M > 0 with
|r_i(S)| ≤ M for every reward coordinate.

A behavioral profile is equivalently an independent product law p on
(ℕ ∪ {Never})⁴. A unilateral deviation replaces one complete stopping law,
including arbitrary late finite dates and Never. Define

    U_i(p) = the prescribed expected terminal reward;
    B_i(p) = sup over all replacement laws μ_i of U_i(μ_i,p_{−i});
    d_i(p) = B_i(p)−U_i(p);
    D(p) = ∑[i ∈ I] d_i(p);
    D_* = inf over all actual product laws p of D(p);
    P_i = inf over all independent opponent laws p_{−i} of B_i(p).

Punishment P_i is an infimum of unrestricted behavioral best-reply values;
the opponents do not receive a common random seed. Assume

    D_* > 0,       P_i ≤ r_i({i}) for every i.

The inequality D(p) ≥ D_* holds against every actual behavioral product law,
not only stationary, finite-clock, or bounded-memory profiles.

## A minimum and its actual realizing profiles

Let ℓ_p be the probability vector of the terminal outcome: its coordinates
are the fifteen nonempty quitting coalitions and Never, where Never means
all players choose Never. Put

    Φ(p) = (U(p),B(p),ℓ_p).

Let C be the closure, in finite-dimensional Euclidean space, of
{Φ(p) : p is an actual behavioral product law}. It is compact because
U and B lie in [−M,M]⁴ and ℓ_p lies in a finite probability simplex.
The continuous function (u,b,ℓ) ↦ ∑[i] (b_i−u_i) attains its minimum D_*
on C. This does not assert that a minimizing point equals Φ(p) for an
actual profile.

Fix one minimum z_* = (u_*,b_*,ℓ_*) in C and one sequence of actual laws
p^n with Φ(p^n) → z_*. Also retain a nonempty coalition S_* with
ℓ_*(S_*) > 0. This is a positive terminal coalition atom, not a stopping-date
atom and not a statement about independent marginal limits.

## An actual paid row with quantitative reach

The supplied data include an index n₀ and a finite chain of actual product
laws

    σ^0 = p^(n₀), σ^1, …, σ^m = p.

Each step replaces one player's complete law and leaves the other three
unchanged. These replacements are recorded as actual equalities of laws;
their order is not an order of temporal play, and no payoff monotonicity is
assumed merely from this ancestry.

The endpoint satisfies D(p) > D_*. It has a distinguished player i with
d_i(p) ≥ D_*/4 and two distinct pure stopping times s,t in ℕ ∪ {Never}.
The time s has positive mass in p_i. The ordered comparison is a profitable
switch from s to t against the same opponents p_{−i}.
Write U_i(u,p_{−i}) for the payoff when i uses the pure time u.

Order Never after every finite time and put a = min(s,t), which is finite.
Let

    A = Pr_{p_i}(T_i ≥ a);
    L = ∏[j ≠ i] Pr_{p_j}(T_j ≥ a);
    R = A L.

Thus A is own survival, L is opponent survival, and R is actual joint
survival to the start of date a. Require the quantitative floors

    A ≥ D_*/(16M),
    L ≥ D_*/(32M),
    R ≥ D_*²/(512M²).

All these probabilities refer to the actual endpoint p. Because R > 0,
conditioning each marginal on survival to a and subtracting a from its
finite times gives one well-defined actual continuation product law.

For a pure time u ≥ a, let V_i^a(u) be i's expected terminal payoff against
the opponents conditioned to survive to a, when i waits until u and quits,
or chooses Never if u = Never. Dates are shifted by a in this continuation.
Define the reached comparison

    g = V_i^a(t)−V_i^a(s).

Require

    Lg = U_i(t,p_{−i})−U_i(s,p_{−i}) ≥ D_*/16.

The equality holds because both pure plans Continue before their first
disagreement at a. The quantity Lg is an opponent-survival-weighted
pure-witness gain. It is not silently identified with the payoff improvement
from replacing the original mixed law p_i by t. The conditional continuation,
the ordered pair s,t, and the actual law p are all retained.

## Question

For every reward table and every collection of actual data satisfying the
conditions above, construct an actual behavioral product law π on the same
table such that

    D(π) < D_*.

This would contradict the defining global lower bound. Equivalently, a
complete positive solution may prove that no such collection of data exists.
The task is to convert the paid comparison and its actual continuation into
this strict terminal-debt conclusion, not to select another profitable row.

Every four-player game without a uniform-equilibrium payoff admits the
displayed punishment-normal positive-infimum setting and such minimum,
realizing, and quantitative paid-row data. Consequently a solution rules
out that case. A sequence of actual profiles with maximum debt tending to
zero would be a stronger sufficient output; compact payoff selection then
gives one fixed uniform-equilibrium payoff target.

A complete negative answer is an explicit four-player table with one Γ > 0
such that, against every behavioral product law, some unilateral behavioral
deviation improves terminal payoff by at least Γ. Failure restricted to one
strategy class is not such a certificate.

## Constraints on proposed constructions

New profiles may be introduced, but their complete terminal payoffs and
unrestricted caps must be proved on the same table. If a comparison uses the
fixed minimum z_* or a particular retained continuation, it must use those
actual data or prove the required replacement identity. The minimum is not
silently replaced by an attained profile.

The recorded finite replacement chain does not concatenate into play.
Likewise infinitely many all-Continue prefixes do not define a profile that
reaches the old continuation after an infinite date. A construction using
temporal blocks must prove its actual Bellman matching and control the
accumulated error.

No rank construction is required. If one is proposed, it must define its
state set, an initial state determined by the given data, a well-founded
order, and a total rule which at every nonterminal state produces a strictly
smaller state. Every terminal state must produce
an actual π with D(π) < the original D_*. A rank decreasing only on an
optional or empty transition relation does not suffice.

These conditions audit a construction using the supplied data; they do not
assert that every possible proof of uniform equilibrium must preserve this
replacement ancestry or follow a chronological argument.
