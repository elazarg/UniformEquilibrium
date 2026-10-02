# Compile uniformly reached proper-face sources

## Mathematical data

Let I be a finite set of at least two players. For every nonempty coalition
S, a reward table r specifies a vector r(S). At each date the players
independently choose Continue or Quit. The first nonempty quitting coalition
ends play and receives its reward; infinite all-Continue pays zero. Allow
every behavioral strategy, including unbounded privately randomized stopping
times and Never, and no external public randomization.

For any such game G and profile p, let U_i(p) be its terminal expected payoff,
let B_i(p) be the supremum payoff from all unilateral behavioral replacements,
and define e_G(p) = max_i [B_i(p) - U_i(p)]. A terminal epsilon-Nash profile
has e_G(p) <= epsilon. Equivalently, the game has a uniform-equilibrium payoff
when inf_p e_G(p) = 0: one payoff target can then be approached with vanishing
unilateral gains over every sufficiently long finite-average horizon.

Assume r has no uniform-equilibrium payoff, while every quitting game with
fewer players has one. Fix gamma > 0 such that e_r(p) >= gamma for every
behavioral profile p, and let M >= 1 bound every reward in absolute value. Put

    rho = gamma/(2M) > 0.

For every nonempty proper block B of I, write J_B = I minus B. The induced
game on J_B uses r_i(S) for i in J_B and nonempty S contained in J_B.
The quiet lift of a profile in that game makes every player in B choose
Never and leaves the other strategies unchanged.

Assume the following simultaneously selected data are supplied:

- one outsider d_B in B;
- positive errors epsilon_n decreasing to zero;
- terminal epsilon_n-Nash profiles tau_(B,n) of the induced game on J_B,
  against all behavioral deviations;
- actual profiles of r and finite dates at which the all-Continue history
  is reached with probability at least rho and the complete live
  continuation is literally the quiet lift of tau_(B,n); and
- in the quiet lift of every tau_(B,n), player d_B gains at least gamma by
  quitting immediately rather than following its prescribed Never plan.

There are finitely many proper blocks. A common subsequence may therefore be
chosen along which their bounded payoff vectors, cap vectors, and finite
terminal-outcome probability vectors converge. In each induced game, the
limiting payoffs equal the limiting caps for its own players; this does not
eliminate the ambient outsider gain. A limit need not be attained by one
behavioral profile. Profiles selected on different faces need not extend,
restrict, or continue one another.

## Question

Use the proper-face sources to prove at least one of the following:

1. every cardinal-minimal counterexample has at most four players;
2. every cardinal-minimal counterexample has a fixed finite cardinal bound,
   together with closing base cases;
3. there are finitely many strictly smaller quitting games G_1,...,G_m,
   with m >= 1, a map of behavioral profiles

       L : X(G_1) × ... × X(G_m) → X(r),

   and a constant 0 <= C < infinity such that, for all child profiles,

       e_r(L(x_1,...,x_m)) <= C max_a e_(G_a)(x_a),

   where X(G) denotes all independent behavioral profiles in G. The output
   of L must be an independent behavioral profile in r, and every
   exploitability is taken against unrestricted behavioral deviations; or
4. an explicit cardinal-minimal reward table with a certified positive gap
   against every behavioral profile.

An equivalent constructive reduction is acceptable if it both compiles
uniform-equilibrium payoffs of the children to one for the parent and forces a
positive parent gap to be inherited by at least one child.

## Required cross-face content

The compiler must relate separately selected face sources. A positive gap on
the profiles extending one chosen child source is only a constrained-fibre
gap; it is not a gap for the child or parent game. Likewise, immediate
outsider obstructions on every face do not by themselves define a parent
strategy.

## Nonanswers

- recentering finite outsider witnesses to uniformly reached date-zero
  suffixes;
- simultaneous selection of outsider labels and compact face limits;
- a positive exploitability gap on one extension fibre;
- quiet lifting one proper-face equilibrium;
- a static solo, join-pressure, or outsider cycle with no profile compiler;
- upward passive padding; or
- cardinal descent which loses unrestricted behavioral deviations.
