# Three-cycle passive-row inheritance inside the degree-one residual

## Status

Ordinary mathematical proof developed in this response. The exact symbolic and
finite-calendar checks are in `VERIFY_THREE_CYCLE_PASSIVE_INHERITANCE.py` and
`THREE_CYCLE_PASSIVE_INHERITANCE_CHECKS.json`. This is not a Lean-checked theorem.
No repository files, branches, or commits were changed.

This is an unconditional raw-table sufficient criterion, including a full
behavioral strategy construction. It does not prove the four-player conjecture.
The bounded comparisons below establish separation from specified criteria, not
novelty relative to every theorem or a literature-wide priority claim.

The new calculation here is the raw three-by-three inverse test, its passive-row
inheritance, and its explicit rates. The cyclic mesh and terminal-to-uniform
mechanisms already have general certificate interfaces in the repository.

## 1. The raw-table theorem

Let I be any finite set containing a three-player subset S. A nonempty first
quitting coalition A pays r(A), and perpetual Never pays zero. Before absorption
there is only the all-Continue public history. Randomization is independent and
private. Deviations may replace a complete behavioral strategy without a time or
memory restriction.

Write

    s_i = r_i({i}),
    Gamma_ij = r_i({j}) - s_i,
    T = Gamma_SS.

Suppose T is invertible and

    T^(-1) >= 0,
    Gamma_kS T^(-1) >= 0       for every k outside S.       (H)

Inequalities are entrywise. Then the original game has a fixed ordinary
uniform-equilibrium payoff. There is no restriction on the signs of the own
singletons, on any nonsingleton reward, or on singleton columns indexed outside S.

If T^(-1) is strictly positive, the proof constructs the target from singleton
rewards alone and gives rational finite stopping laws for rational data. Every
outside player uses Never. The three active players use a subdivided, repeating
single-quitter cycle, then optionally censor it to obtain finite laws.

For four players the test consists of trying the four possible principal triples.
In particular, nonexistence of UE implies the additional necessary condition

    for every triple S with T^(-1) >= 0,
    the remaining row Gamma_kS T^(-1) has a negative entry.  (N)

The inequalities in (H) do not assert that an arbitrary equilibrium of a child
can be extended unchanged. We construct one particular child schedule and retain
an exact payoff identity at every stage of that schedule.

## 2. Why the inverse test produces a three-cycle

First suppose B=T^(-1)>0. Since T has zero diagonal, an off-diagonal equation
of TB=I says that a linear combination of the two off-diagonal entries in one
row of T, with strictly positive coefficients, is zero. Invertibility excludes
a zero row. Thus those two entries are nonzero and have opposite signs.
Applying the same argument to BT=I gives one positive and one negative entry in
each column as well.

The positive entries consequently form a fixed-point-free permutation on three
labels, hence a directed three-cycle. Relabel S as 0,1,2 so that

            [ 0   -b_0   a_0 ]
    T =     [ a_1   0   -b_1 ],       a_i,b_i > 0.
            [-b_2  a_2    0  ]

Its determinant is A-B0, where A=a_0 a_1 a_2 and B0=b_0 b_1 b_2.
For example, the (0,0) entry of T^(-1) is b_1 a_2/det(T)>0. Therefore

    P := (a_0/b_0)(a_1/b_1)(a_2/b_2) > 1.

Conversely, this sign pattern and P>1 make every cofactor contributing to
T^(-1) positive. Thus they characterize the strictly positive inverse case.

## 3. Explicit rates, rather than a supplied cycle

Put A_i=a_i/b_i and define positive odds

    t_0 = (P-1)/(1+A_1+A_0 A_1),
    t_1 = (P-1)/(1+A_2+A_1 A_2),
    t_2 = (P-1)/(1+A_0+A_2 A_0).

Set q_i=t_i/(1+t_i), c_i=1/(1+t_i). These are strictly between zero and
one. The four elementary identities are

    t_0 = A_2 q_1,
    t_1 = A_0 q_2,
    t_2 = A_1 q_0,
    C := c_0 c_1 c_2 = 1/P < 1.                         (1)

They follow by substitution and clearing positive denominators. They also give
a direct derivation: composing t_0=A_2 t_1/(1+t_1),
t_1=A_0 t_2/(1+t_2), t_2=A_1 t_0/(1+t_0) yields the displayed t_0,
and cyclically the others.

Phase i has only player i active, with Quit probability q_i. Phases run in
order 0,1,2. Define positive surpluses

    x_0=a_0 q_2,       x_1=a_1 q_0,       x_2=a_2 q_1,

and phase vectors on S

    z^0=(0,x_1,0),
    z^1=(0,0,x_2),
    z^2=(x_0,0,0).

Equation (1) gives the exact cyclic identities

    z^i = q_i T e_i + c_i z^(i+1),                     (2)

where phase indices are modulo three. For example the only nontrivial
cancellation in phase zero is c_0 x_2=q_0 b_2.

The active player's surplus is zero both at its phase and at the next phase.
Every other surplus is nonnegative. Adding s_S to (2) gives the prescribed
singleton-reward recursion. Since C<1, its bounded periodic solution is the
actual prescribed terminal payoff of the coarse cycle. No continuation value
is freely chosen after the calculation.

The coarse cycle is not yet claimed to be Nash for arbitrary collision rewards.
Subdividing its phases will make all individual-date joining opportunities small.

## 4. The omitted-player issue is settled at every stage

For k outside S let

    w_k = Gamma_kS T^(-1) >= 0,
    z^i_k = w_k z^i,
    v^i_k = s_k + z^i_k.

Use v^i_j=s_j+z^i_j for j in S. The identity Gamma_kS=w_k T and (2) give

    v^i_k = q_i r_k({i}) + c_i v^(i+1)_k.              (3)

Consequently these are the actual passive player's phase payoffs, and

    v^i_k >= s_k                                             (4)

at every phase. This is not an assertion about only the average payoff of the
child game. It is the full phase-by-phase continuation floor needed to prevent
profitable timing deviations by the omitted player.

Within a subdivided solo phase, the continuation value runs along the line
segment between its two coarse endpoint values. Equations (3)-(4), including
the nonnegative surplus identity, therefore hold at every intermediate stage as
well. The active player's value stays exactly at its own singleton throughout
its active block.

## 5. Executable phase subdivision and unrestricted caps

Let M>0 bound the absolute values of all rewards. Fix a micro-hazard bound
0<delta<1. For phase i choose

    N_i = max(1, ceil(t_i/delta)).

Split its unconditional Quit mass q_i into N_i equal pieces. At its local stage
l=0,...,N_i-1 use the conditional hazard

    h_i,l = q_i/(N_i-l q_i).

The denominator is positive. The product of these stage continuation factors
telescopes to c_i, and

    0 < h_i,l <= t_i/N_i <= delta.

Thus the original phase endpoint values and C are preserved exactly. With
rational table entries all these probabilities are rational.

Let V_i(t) be the resulting periodic continuation payoff, with initial target
v=V(0). The preceding construction gives V_i(t)>=s_i at every date. The
following stronger equality is crucial:

    V_i(t) = H_i(t) + beta_i(t) V_i(t+1).                (5)

Here H_i is the absorbing payoff contribution when i Continues, and beta_i is
the probability that all its opponents Continue. If i is quiet, Continue is its
prescribed action, so this is the prescribed recursion. If i is the active
owner, both adjacent values equal s_i and every opponent Continues, so (5)
holds again. Thus the displayed value is harmonic under the queried player's
Never strategy.

If i is the active owner, its Quit endpoint is s_i=V_i(t). If j!=i is the
active owner with hazard h<=delta, i's Quit endpoint is

    Q_i(t) = (1-h)s_i + h r_i({i,j})
           <= s_i+2M delta <= V_i(t)+2M delta.           (6)

For each i, opponents survive one entire cycle with probability

    rho_i = C/c_i       if i is in S,
    rho_i = C           if i is outside S.

All these numbers are below one because three distinct owners have positive
hazards. Put rho=max_i rho_i<1. Iterating (5) therefore identifies Never's
payoff with v_i, including for signed s_i.

More explicitly, let b_i(t) be opponent survival up to date t. A pure response
that quits at t has payoff

    v_i + b_i(t)[Q_i(t)-V_i(t)].                        (7)

This follows by iterating (5) until that date. Equation (6) bounds (7) by
v_i+2M delta, and Never pays v_i. Every full behavioral replacement is a
mixture of these pure finite dates and Never. Therefore

    U_i = v_i,       B_i <= v_i+2M delta,
    E <= 2M delta.                                     (8)

There is no error multiplied by the number of stages. A stopping deviation
uses the Quit endpoint once; its preceding Continue steps satisfy equality (5).
This is why fine subdivision controls full, rather than merely one-stage,
regret.

## 6. Finite independent laws and a quantitative selector

Keep K complete cycles and censor every later private clock independently to
Never. This is an actual product of finite-date-or-Never laws. Write p^K for
it and L=N_0+N_1+N_2 for the length of one subdivided cycle.

Prescribed play survives K cycles with probability C^K, and renewal gives

    U_i(p^K) = (1-C^K)v_i.                              (9)

For any fixed complete unilateral replacement, couple the infinite and
censored opponents by their original private clocks. The outcomes can differ
only if every opponent survives the cutoff. Its probability is rho_i^K,
independent of the deviator's chosen law. Bounded rewards imply the uniform
response estimate

    B_i(p^K) <= v_i+2M delta+2M rho_i^K.

Using |v_i|<=M and (9),

    E(p^K) <= 2M delta+2M rho^K+M C^K
            <= 2M delta+3M rho^K.                      (10)

This includes every deadline after the finite support and Never; neither is
removed from the response problem.

For 0<epsilon<=M, take

    delta = epsilon/(4M),
    K >= 1 with rho^K <= epsilon/(6M).

Then E(p^K)<=epsilon and |U_i(p^K)-v_i|<=epsilon/6. An explicit date bound is

    K [3+(4M/epsilon)(t_0+t_1+t_2)],

with integer rounding understood through the actual N_i. For a fixed strict
input table this is O(epsilon^(-1) log(1/epsilon)). This is a calendar-size
bound, not a bit-complexity claim. For rational data, K can be selected by exact
successive-power comparisons, so no floating-point logarithm is an algorithmic
premise.

## 7. Fixed-target uniform equilibrium, with signed singleton rewards

For an N-date finite word, prescribed H-stage average payoff differs from
terminal payoff by at most M(N+1)/H, allowing either standard convention for
the initial live stage.

Uniformly over a complete deviation, average payoff is at most

    B_i + M(N+1)/H.

For a pure deadline before the cutoff all absorption is early. For a deadline
after the cutoff, opponent absorption is early and the only later absorbing
reward is the deviator's singleton. If that singleton is nonnegative, delaying
it cannot increase its average contribution above the terminal one. If it is
negative, the Never response instead bounds the late contribution from above.
Never itself has only early opponent absorption. Mixtures preserve the same
bound. Hence full finite-horizon regret is at most

    E + 2M(N+1)/H.                                     (11)

The target v in (9) was selected before delta, K, or the desired accuracy.
Equations (9)-(11), with a sufficiently fine mesh and enough retained cycles,
give one profile for every accuracy and a single threshold after which all
horizons satisfy the equilibrium and payoff-delivery inequalities. This proves
the asserted fixed uniform-equilibrium payoff for the original game.

## 8. Nonnegative-inverse boundary

It remains to allow zeros in T^(-1). The strict approximation lemma in the
attached inverse-positive packet applies in dimension three: for
K0=J-I and sufficiently small e>0,

    T_e = T-e K0

has strictly positive inverse, retains zero diagonal, and tends to T. Here is
the relevant argument. With B=T^(-1)>=0 and e||BK0||<1,

    T_e^(-1)=B+e B K0 B+e^2 B K0 B K0 B+... .

All terms are nonnegative. If both B_ij and (B K0 B)_ij vanish, nonzero row i
and nonzero column j must both be supported on the same singleton k. There is
some positive B_uv with u,v different from k: otherwise the two rows outside k
are supported in one column, contradicting invertibility. The term
B_ik (K0)_ku B_uv (K0)_vk B_kj in the second-order coefficient is positive.
Thus the inverse is strictly positive. This argument depends on dimension at
least three.

Keep w_k=Gamma_kS B fixed and set the perturbed outside rows to

    Gamma^e_kS = w_k T_e.

Leave own singletons, singleton columns outside S, and all nonsingleton rewards
unchanged. These tables converge entrywise to the original table and satisfy
the strict theorem, because Gamma^e_kS T_e^(-1)=w_k>=0.

If two tables are within eta in reward sup norm, every prescribed and every
deviated payoff changes by at most eta. Full caps change by at most eta, and
full exploitability changes by at most 2 eta. Consequently approximate
terminal equilibria for the perturbed tables yield approximate terminal
equilibria of every accuracy for the original table. The fixed-payoff selection
theorem, or compact selection of their bounded prescribed payoff vectors
followed by (11), finishes the nonnegative-inverse case.

No arbitrary child equilibrium is lifted in this limiting step. Each
approximating child schedule was explicitly constructed above.

## 9. An exact degree-one matrix cylinder

Consider

            [ 0  -1   2  -2 ]
    Gamma = [ 2   0  -1   1 ].
            [-1   2   0   1 ]
            [-1   2   2   0 ]

Take S={0,1,2}. Then

    T^(-1) = (1/7) [2 4 1; 1 2 4; 4 1 2],
    Gamma_3S T^(-1) = (1/7)(8,2,11)>0.

Here a_i=2, b_i=1, P=8 and q_i=c_i=1/2. The three phase surpluses are

    z^0=(0,1,0,2/7),
    z^1=(0,0,1,11/7),
    z^2=(1,0,0,8/7).

For ANY own-singleton vector s and ANY assignment of the 44 nonsingleton
reward coordinates, the construction supplies the fixed uniform target

    v = s+(0,1,0,2/7).                                  (12)

The active recipients' singleton payoffs when player 3 quits are not used by
the construction either. They were fixed in the displayed matrix only to give
an exact full-matrix degree-one witness.

### Complete LCP support inventory

Use right-hand side -1. The columns below are support, determinant, positive
support candidate T_SS^(-1)1_S, and outside slack Gamma_Sc,S h-1_Sc.

| Support | Determinant | Candidate h | Outside slack |
|---|---:|---|---|
| 01 | 2 | (1/2,-1) | (-7/2,-7/2) |
| 02 | 2 | (-1,1/2) | (-7/2,1) |
| 03 | -2 | (-1,-1/2) | (-7/2,-1/2) |
| 12 | 2 | (1/2,-1) | (-7/2,-2) |
| 13 | -2 | (1/2,1) | (-7/2,1) |
| 23 | -2 | (1/2,1) | (-2,-1/2) |
| 012 | 7 | (1,1,1) | (2) |
| 013 | -7 | (1,1,-1) | (-1) |
| 023 | 2 | (-2,-1/2,-1) | (-11/2) |
| 123 | 2 | (-1/2,1,2) | (-5/2) |
| 0123 | 3 | (5/3,11/3,-7/3,-14/3) | () |

Every principal determinant of size at least two is nonzero, and each column
has a negative entry. A nonzero homogeneous complementary vector cannot have
support of size at least two by nonsingularity, or singleton support because
of the negative entry in that column. Hence Gamma is R0.

At right-hand side -1 the only complementary solution has support 012. It is
strictly complementary and its principal determinant is positive. Thus, with
the min-map degree convention of the attached integer-degree packet,

    kappa(Gamma)=+1.

This matrix lies in the residual of that degree criterion, not its excluded
class. The full determinant is +3 and

    Gamma^(-1)=(1/3)[ 2  2   2  -1;
                     5  2   8  -4;
                    -4 -1  -7   5;
                    -8 -2 -11   7 ],

which has both signs. The principal on {0,3} is [0,-2;-1,0]. It has neither a
nonzero homogeneous nonnegative complementary vector nor a solution at
right-hand side (-1,-1). Thus full projective Q-bar does not hold.

The negative graph is 0->1, 0->3, 1->2, 2->0, 3->0. Any negative cycle
visiting 3 must immediately return to 0, so there is no negative Hamiltonian
cycle. This excludes the literal once-per-owner signed-four-cycle criterion
and its relabelings.

All the relevant inequalities in the inverse, observer multiplier, R0 support
test, and degree computation are strict. A sufficiently small zero-diagonal
neighborhood remains in both the new sufficient class and the R0 degree-one
region. Allowing all own singletons and nonsingleton coordinates to vary gives
an open set of full reward tables, not a single exceptional table.

These are comparisons of named tests. The cylinder may overlap other cyclic
or reward-dependent sufficient classes; no exclusion of their entire union is
claimed.

## 10. Scope and remaining obstruction

The paired matrix from the attachments,

    [0,3,-1,-1; 3,0,-1,-1; -1,-1,0,3; -1,-1,3,0],

does not satisfy (H): each principal triple has a negative diagonal entry in
its inverse. Thus the arbitrary collision cylinder of that matrix remains
outside this result. The theorem does not imply that every degree-one residual
contains a suitable triple.

The exact gain is a constructive raw singleton-matrix producer with arbitrary
nonsingleton completions, including a nonempty open part of R0 degree +1. It
requires neither a supplied strategic source nor an assumed child-lifting
operator. It is not a proof or refutation of arbitrary Fin4 UE.

## 11. Source correspondence and verification

Repository declarations were inspected read-only at commit
`5aac30ad2553dadd5895dc79fbc4f1f5680d7570`.

- `BalancedSingletonCycleCertificate` in
  `UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`
  is the existing certificate interface for the coarse recursion, owner ties,
  all-player singleton floor, and deleted-opponent divergence. Equations
  (1)-(4) construct those fields directly from (H); the certificate interface
  and its general mesh consumer are not claimed as new mathematics.
- `QuittingAnchoredCyclicPatienceSystem` in
  `UniformEquilibrium/Quitting/Cycles/AnchoredCyclicPatience.lean`
  distinguishes the singleton floor from exact fixed-hazard joining
  inequalities. The proof above makes the same distinction and derives the
  approximation bound rather than silently identifying them.
- `SignedFourCycleSingletonData` in
  `UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`
  has the negative-successor sign requirement used in the comparison above.
- The attached `INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md`
  supplies the R0 degree convention and support-index computation used for
  the bounded comparison. Its degree-one restriction is not a premise of
  the constructive theorem.
- The attached `INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md`
  supplies the credited zero-diagonal strict approximation argument and
  reward-closedness method, re-established for this application in Section 8.
- The attached `ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO.md` rules out
  arbitrary unchanged-child lifting. Our theorem chooses a special schedule
  and verifies the extra player's complete response problem, so does not
  contradict that no-go.

The exact verifier passed four symbolic rate identities, the complete
11-support inventory, and 192 finite profiles over 48 signed reward tables.
For all four players in each profile, independent forward scans of all
retained dates, the first late date, and Never agreed with the backward full-cap
recursion: 768 complete finite cap comparisons. The largest calendar had 156
dates. These are finite regression checks, not a substitute for Sections 2-8.
No Lean compilation, axiom audit, or repository mutation was performed.
