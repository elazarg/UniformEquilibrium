# Four-player quitting controller–tester sign question

## Game and compact semantic value

There are four players I = {0,1,2,3}. A reward table r assigns a real vector
r(S) to each nonempty coalition S. At each date the players independently
choose Continue or Quit. The first nonempty quitting coalition ends play
and receives r(S); infinite all-Continue pays zero.

A behavioral profile p is an independent product of stopping laws on the
nonnegative integers together with Never. Let U_i(p) be its terminal
expected payoff and let

    B_i(p) = sup over all replacement laws mu_i of U_i(mu_i,p_(-i)).

The supremum includes every privately randomized or unbounded stopping time.
Define the finite-dimensional closed carrier and its minimum exploitability:

    K_r = closure { (U(p),B(p)) : p is any behavioral product law };
    eta(r) = min { max_i(b_i-u_i) : (u,b) in K_r }.

If R = max_(S,i) |r_i(S)|, the carrier is a compact subset of
[-R,R]^4 × [-R,R]^4. Every coordinate b_i-u_i is nonnegative, so eta(r) >= 0.
The minimum need not be realized by an actual profile.

## Question

Prove or refute that eta(r) = 0 for every four-player reward table.

A positive answer proves that K_r meets the diagonal b = u. Equivalently,
the game has one fixed uniform-equilibrium payoff: at every positive error,
one behavioral profile approaches that target and bounds all unilateral
gains over every sufficiently long finite-average horizon. The profile and
horizon threshold may depend on the error, but the target may not.

A negative answer requires one explicit table with eta(r) > 0. The following
closed-invariant-set formulation is an equivalent way to give such a
negative certificate.

## Explicit invariant-set formulation

The terminal payoff and cap pair of all-Never play is

    e_Never = (0, (max(r_i({i}),0))_(i in I)).

For a new product root x in [0,1]^4, where x_i is player i's Quit
probability, define for S contained in I

    pi_x(S) = product_(j in S) x_j · product_(j not in S) (1-x_j).

For T contained in I minus {i}, similarly define the opponents' product mass

    pi_(x,-i)(T) =
        product_(j in T) x_j · product_(j not in T, j != i) (1-x_j).

The exact one-root prefix operator T_x(u,b) = (u',b') is

    u'_i = sum_(S nonempty) pi_x(S) r_i(S) + pi_x(empty) u_i;

    Q_i(x) = sum_(T contained in I minus {i})
                 pi_(x,-i)(T) r_i(T union {i});

    C_i(x,b) = sum_(T nonempty, contained in I minus {i})
                   pi_(x,-i)(T) r_i(T)
                 + pi_(x,-i)(empty) b_i;

    b'_i = max(Q_i(x),C_i(x,b)).

Thus C_i retains the unrestricted continuation cap, not merely the
prescribed continuation payoff.

Find an explicit r, a positive Gamma, and a closed set
C contained in [-R,R]^4 × [-R,R]^4 such that

    e_Never is in C;
    T_x(C) is contained in C for every x in [0,1]^4;
    max_i(b_i-u_i) >= Gamma for every (u,b) in C.

Finite root words from e_Never are dense in K_r. These conditions therefore
prove eta(r) >= Gamma. Conversely, when eta(r) > 0, K_r itself satisfies
them with Gamma = eta(r).

No finite, polyhedral, or semialgebraic representation of C is required.
Invariance only for selected roots, or a positive gap only for restricted
behavioral profiles, does not give the requested certificate.

## Polynomial formulation in the normal class

Let s_i = r_i({i}) and let

    P_i = inf over independent opponent laws p_(-i) of B_i(p).

Consider tables with P_i ≤ s_i for every player and s_j > 0 for at least
one player. Choose M > 0 bounding every absolute terminal reward, and set
L = M+2. No joint profile realizing the vector P, and no attainment of any
punishment infimum, is assumed.

For x ∈ [0,1]⁴ and v ∈ [−L,L]⁴ define

    c(x) = pi_x(empty),       a(x) = 1−c(x);
    F_i(x,v) = sum_(S nonempty) pi_x(S) r_i(S)+c(x)v_i;
    e_i(x,v) = max(Q_i(x),C_i(x,v))−F_i(x,v).

Here C_i(x,v) is the root Continue expression above, evaluated at the
annotation v_i rather than at a behavioral cap. The quantity e_i is ordinary
mixed-root regret. The annotation v need not be an actual payoff or cap.

The finite sure-root alternative is

    C_sure: there exist k and x with x_k=1 and e_i(x,P)=0 for every i.

This alternative gives terminal approximate equilibria against all behavioral
deviations by selecting an approximate punishment for the one exposed player.
It must be excluded in a negative certificate.

For a rational δ with 0 < δ ≤ 1/4, let E_δ contain EVERY triple (v,x,w)
with v,w ∈ [−L,L]⁴ and x ∈ [0,1]⁴ such that

    |w_i−F_i(x,v)| ≤ δ a(x)           for every i;
    e_i(x,v) ≤ δ a(x)                for every i.

There is no punishment-floor condition on v or w, prescribed initial state,
selected component, or positive lower bound on a(x). The direction is from
the continuation annotation v to the prefixed annotation w.

Within this normal positive-singleton class, the equivalent negative
certificate problem is to find one actual table for which C_sure is false,
together with δ as above and a rational-coefficient polynomial H in four
variables satisfying

    H(v)−H(w) ≥ a(x)                 for EVERY (v,x,w) ∈ E_δ.

Such a certificate exists exactly when eta(r)>0. The universal test ranges
over v,x,w, not just the four arguments of H. It includes zero-charge roots,
where w=v, and roots with arbitrarily small positive charge. No degree bound
on H is supplied.

Can this global inequality be ruled out for every table in this class with
no sure root, or can an explicit table, polynomial, and sure-root exclusion
be proved? The latter must establish semantic normality and the exclusion at
the exact behavioral punishment vector P as well as the all-edge inequality.
Sampling edges, exhausting a fixed polynomial degree, or proving drift on
only one chosen orbit is not a complete answer.
