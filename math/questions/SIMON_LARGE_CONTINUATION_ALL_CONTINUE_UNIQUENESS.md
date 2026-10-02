# Large continuation payoffs and all Continue uniqueness

Let N be a finite nonempty set of players. For each nonempty coalition
A ⊆ N, fix an arbitrary payoff vector r(A) ∈ ℝ^N. For a continuation
vector x ∈ ℝ^N, define a one-stage game G(x) in which each player chooses
Quit or Continue. If the coalition A of quitters is nonempty, the payoff
is r(A); if every player continues, the payoff is x.

A mixed profile p ∈ [0,1]^N consists of independent Quit probabilities.
For player i and S ⊆ N \ {i}, put

    wᵢ(S,p) = ∏[j ∈ S] p_j · ∏[j ∈ N \ (S ∪ {i})] (1 − p_j).

The payoffs from the two pure actions against these opponents are

    Qᵢ(p) = ∑[S ⊆ N \ {i}] wᵢ(S,p) r(S ∪ {i})ᵢ,

    Cᵢ(x,p) = wᵢ(∅,p) xᵢ
              + ∑[∅ ≠ S ⊆ N \ {i}] wᵢ(S,p) r(S)ᵢ.

Empty products equal one. These definitions include probabilities zero
and one and the one-player case.

For η ≥ 0, say that p satisfies the support best-response inequalities
with error η if, for every i,

    pᵢ > 0  implies  Qᵢ(p) ≥ Cᵢ(x,p) − η,
    pᵢ < 1  implies  Cᵢ(x,p) ≥ Qᵢ(p) − η.

At η = 0 this is ordinary mixed Nash equilibrium. No trembling-hand
perfection condition is imposed.

## Question

Assume that there are a fixed vector m ∈ ℝ^N and a fixed η > 0 such that,
for every x with xᵢ ≥ mᵢ − η for all i, every profile satisfying the
support best-response inequalities with error η has pᵢ < 1 for every i.

Must there be B > 0 such that, for every x with xᵢ ≥ B for all i, the
set of exact mixed Nash equilibria of G(x) consists only of the profile
p = 0 in which every player continues?

The threshold B may depend on the reward table, m and η, but it must be
chosen before x. The assumption excludes a sure quitter uniformly at one
positive error; it does not assume a common positive lower bound on the
probability ∏[i ∈ N] (1 − pᵢ) that every player continues.

## Weaker assumption

Does the same conclusion follow if, for some fixed vector ℓ ∈ ℝ^N,
every exact Nash equilibrium of G(x) has pᵢ < 1 for all i whenever
xᵢ ≥ ℓᵢ for all i? This drops the positive error margin and is a separate
question. A negative answer under this weaker assumption would not
refute the first implication.
