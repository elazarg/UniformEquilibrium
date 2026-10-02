# Quantile and common-clock compression for quitting games

## Status

The proofs below are mathematical arguments, not Lean-checked declarations.
The accompanying Python script performs exact-rational regression checks.
No cardinal bound on minimal counterexamples and no parent-equilibrium
compiler from smaller games is claimed.

## Setup

There are n >= 2 players. Terminal rewards lie in [-M,M], and all-Never pays
zero. Strategies are independent probability laws on N union {Never}.
Write U_i for prescribed payoff, B_i for the supremum over every behavioral
replacement, d_i = B_i - U_i, and e = max_i d_i.

For a law mu write F_mu(t) = mu({0,...,t}), and put

    d_K(mu,nu) = sup_{t in N} |F_mu(t)-F_nu(t)|.

## 1. Uniform strategic continuity in the CDF metric

If only player j's law changes from mu to nu, then, for every payoff
coordinate i and all fixed independent laws of the other players,

    |U_i(mu,p_-j)-U_i(nu,p_-j)| <= 4 M d_K(mu,nu).

Proof. First fix every other player's pure stopping time. If their earliest
finite time is t, with quitter set S, the payoff as a function of player j's
time is A = r_i({j}) before t, B = r_i(S union {j}) at t, and C = r_i(S)
after t, including Never. Its expectation under mu is

    C + (A-B) F_mu(t-1) + (B-C) F_mu(t),

where F_mu(-1)=0. Its difference under nu is bounded by
(|A-B|+|B-C|) d_K(mu,nu) <= 4 M d_K(mu,nu).
If all other players choose Never, the expectation is
r_i({j}) lim_t F_mu(t), so the bound also holds. Integrating over the other
players proves the claim.

Consequently, when d_K(p_j,q_j) <= delta_j for every j,

    |U_i(p)-U_i(q)| <= 4 M sum_j delta_j,
    |B_i(p)-B_i(q)| <= 4 M sum_{j != i} delta_j.

The second inequality is uniform over the unchanged deviator's entire
replacement law before taking the supremum; no attainment is assumed.

## 2. Midpoint quantile approximation

For integer K >= 1 define u_k = (2k-1)/(2K). Let Q_mu(u) be the least finite
t with F_mu(t) >= u if one exists, and Never otherwise. Define

    mu^[K] = (1/K) sum_{k=1}^K delta_{Q_mu(u_k)}.

For every finite t,

    F_{mu^[K]}(t) = (1/K) # {k : u_k <= F_mu(t)}.

Thus d_K(mu,mu^[K]) <= 1/(2K). Every approximate law has at most K atoms,
including Never, and every mass is an integer multiple of 1/K.

Applying this separately to n players gives

    |U_i(p)-U_i(p^[K])| <= 2 n M/K,
    |B_i(p)-B_i(p^[K])| <= 2(n-1)M/K,
    |e(p)-e(p^[K])| <= A_n/K,

where A_n = (4n-2) M.

## 3. Exact compression of the common clock

For a finite family of finite-support profiles, let

    D = {t_1 < ... < t_L}

be the union of all finite support dates. Define

    phi(t_1) = min(t_1,1),
    phi(t_{a+1}) = phi(t_a) + min(t_{a+1}-t_a,2),
    phi(Never) = Never.

The first formula preserves whether a deviation can occur before the first
support date. The second preserves both simultaneous actions and whether an
empty date exists between consecutive support dates. It is not sound to
arbitrarily insert empty dates between originally consecutive dates.

This map preserves prescribed terminal outcomes. It also preserves every
best-response cap exactly: any pure deviation is at a support date, in an
available gap, after the last date, or Never. The corresponding class exists
on both clocks and gives exactly the same outcome against each opponent
pure tuple. The argument applies in both directions. Arbitrary mixed and
unbounded replacement laws cannot improve on the supremum of pure replies.

Every compressed finite support date is at most 2L-1. If D is empty, all
profiles are all-Never and are left unchanged.

## 4. Uniform finite rational net

Let G_K consist of all independent profiles whose laws have masses in
{0,1/K,...,1} and support in

    {0,...,2nK-1,Never}.

For every actual independent behavioral profile p, there is g in G_K with

    |U_i(p)-U_i(g)| <= 2 n M/K,
    |B_i(p)-B_i(g)| <= 2(n-1)M/K,
    |e(p)-e(g)| <= A_n/K.

Proof. Quantile-approximate the n laws, then compress their union of at most
nK finite support dates with the common clock above.

The set G_K is finite. It has

    binomial((2n+1)K,K)^n

profiles. The bound is not an efficiency claim.

## 5. Simultaneous cross-face version

Let p^1,...,p^m be any finite source family, including quiet lifts from
different faces. Quantile-approximate every law and use one common clock for
the whole family. All finite support lies before 2mnK.

For every independently chosen family of weights theta_{ia} >= 0 with
sum_a theta_{ia}=1, form

    x_i(theta) = sum_a theta_{ia} p_i^a,
    y_i(theta) = sum_a theta_{ia} compressed(p_i^a^[K]).

Then, uniformly for all such theta, the three bounds in Section 4 hold
between the product profiles x(theta) and y(theta). Indeed, convex mixtures
preserve the CDF approximation bound; the common clock preserves the caps
of every recombination exactly.

This is an independent-profile construction. The weights are not a shared
random source label. In particular, choosing different source laws at
different coordinates is explicitly covered. Quiet Never laws remain quiet,
and original date-zero deviations retain their date-zero interpretation.

For a child game with k players, its own exploitability changes by at most
(4k-2)M/K. An ambient immediate outsider gain changes by at most A_n/K.

The theorem does not say that a suitable theta yields an approximate parent
equilibrium. Choosing that theta, or some stronger cross-face construction,
remains a separate strategic problem.

## 6. Complete finite certificates for positive global gaps

Let

    eta(r) = inf_p e_r(p),
    a_K(r) = min_{g in G_K} e_r(g).

Then

    max(0, a_K(r)-A_n/K) <= eta(r) <= a_K(r).

The upper bound holds since G_K consists of actual profiles. For the lower
bound, compress any arbitrary p to g in G_K and use

a_K <= e(g) <= e(p)+A_n/K, then take the infimum over p.

For a rational reward table and rational reward bound M, a_K is an exactly
computable rational number. All prescribed opponents stop before 2nK or
Never, so a cap is the maximum over the finite dates 0,...,2nK and Never.
The last finite test, 2nK, is essential: it represents quitting after every
prescribed finite date. Expected payoffs and these finite maxima are rational.

A positive-gap certificate is therefore K and a verified rational beta such
that

    e_r(g) >= beta for every g in G_K,
    beta > A_n/K.

It certifies the unrestricted gap beta-A_n/K. Every rational table with
eta(r)>0 has such a certificate: take any K with A_n/K < eta(r) and use
beta = a_K(r). Exhaustive finite checking is a valid verifier, though very
expensive.

This proves computable approximation of eta for rational tables, and a
terminating search for a finite positive certificate whenever eta>0. It does
not provide a terminating decision procedure for eta=0.

## 7. Rationalization of a hypothetical minimal counterexample

If two tables on the same player set differ by at most delta in every
coordinate, every prescribed payoff and cap changes by at most delta.
Therefore |eta(r)-eta(s)| <= 2 delta.

Consequently any real counterexample with gap gamma has a rational
same-cardinality counterexample within gamma/4, with gap at least gamma/2.
If the original cardinality is minimal among all counterexamples, this
rational counterexample is also cardinal-minimal. Section 6 supplies a finite
certificate for it.

This establishes existence of rational, finitely certifiable minimal
counterexamples conditional on existence of a counterexample. It does not
exhibit one reward table, prove existence of a counterexample, or identify a
minimal cardinality.
