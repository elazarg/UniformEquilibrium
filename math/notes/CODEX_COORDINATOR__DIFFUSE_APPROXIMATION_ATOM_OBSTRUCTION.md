# Diffuse approximate equilibria are impossible on the generic singleton residual

Owner: CODEX_COORDINATOR. Ordinary mathematics, not Lean checked. The exact
classification covers all21 generic residual sign orbits, with their necessary
magnitude restrictions. It excludes diffuse approximate-equilibrium sequences
for every bounded higher-coalition completion with at least one positive own
singleton payoff. It does not produce equilibria,
a positive gap against all behavior, or a new UE reward class. Fin4 remains
open. The compactness/refusal machinery has existing source predecessors;
the new content is the complete raw-matrix no-path theorem and its atom
consequence.

## 1. Exact statement

Let Gamma be a real4x4 zero-diagonal matrix, with every off-diagonal entry and
every principal determinant of sizes2,3,4 nonzero. Assume:

- every column contains a negative entry;
- some reciprocal pair is mutually negative;
- the opposition graph i->j iff Gamma_ji<0<Gamma_ij has no directed
  Hamiltonian four-cycle; and
- every principal triple S with Gamma_SS^{-1}>=0 has a negative coordinate
  in Gamma_oS Gamma_SS^{-1}, where o is its omitted player.

THEOREM. This Gamma has no complete absorption path as defined in Section2.
For every finite M>0 and m>0 there consequently exist epsilon0,c0>0 and a
neighborhood U of Gamma with the following property. For every original
four-player quitting-game reward table r with live/Never reward0,

    |r_i(D)|<=M,   kappa_i=r_i({i}),   max_i kappa_i>=m,
    Gamma(r)_ii=0,  Gamma(r)_ij=r_i({j})-kappa_i,  Gamma(r) in U,

and every actual behavioral profile sigma with independent private player
randomization,

    E(sigma)>=epsilon0 OR atom(sigma)>=c0,                 (1)

where E is full MAX terminal regret against all complete unilateral behavioral
deviations, and atom(sigma)=sup_t Pr(first nonempty coalition occurs at date t).
Thus no sequence with E tending to0 can have its maximum first-absorption date
mass tending to0. This includes changing periods, nonperiodic calendars,
and arbitrary stopping laws. The date need not be bounded: leading
Continue-only dates can postpone it. The constants are nonconstructive and
uniform over bounded collision completions, not as M diverges or m tends to0.
Other own levels may have either sign. If all own levels are nonpositive,
All-Never is already an exact terminal equilibrium, so that omitted case
needs no atom theorem.

The [singleton atlas](CODEX_COORDINATOR__JOINT_RETURN_SINGLETON_TOPOLOGY.md)
identifies exactly21 sign orbits admitted by the known generic matrix screens.
They all satisfy these hypotheses. The theorem is not a count of numerical
cells or reward-table coverage; the44 higher-coalition rewards remain arbitrary
within the stated finite bound.

## 2. A general compactness adapter

An absorption path for a matrix Gamma is an absolutely continuous map

    a:[0,1]->R_+^4, sum_i a_i(t)=1-t,
    u_i(t)=-a_i'(t)>=0, Gamma*a(t)>=0,
    u_i(t)>0 => (Gamma*a(t))_i=0 almost everywhere. (3)

The coordinates a_i are remaining UNCONDITIONAL first-singleton masses.
They are not independent marginal laws or continuation strategies.

LEMMA. Suppose r_n are uniformly bounded by M, max_i kappa_ni>=m>0,
Gamma_n->Gamma, and actual profiles have E_n->0 and atom_n->0. Then Gamma
has an absorption path (3).

### Native reduction used only as accounting

Let s_t be prescribed joint survival to t, q_i(t) the conditional hazards,
nu the joint Never probability, p_i(t) the probability that first absorption
is exactly singleton{i} at t, and c the total nonsingleton first-coalition
probability. Let a_i(t)=sum_{v>=t}p_i(v). If C_D(t) is the corresponding
unconditional tail probability for a nonsingleton D, exact payoff accounting
for the ACTUAL original conditional value v_i(t) gives

    (Gamma*a(t))_i
      =s_t(v_i(t)-kappa_i)+kappa_i*nu
         -sum_{|D|>=2}(r_i(D)-kappa_i) C_D(t).     (4)

No invariance under terminal-only row subtraction is assumed.

Changing only a player's original Never branch to a sufficiently late finite
Quit gives gain approaching kappa_i*nu: coincident late-opponent atoms have
vanishing probability. Apply this to an owner with kappa_i>=m. Therefore nu<=E/m. This is the usual joint-Never debt
bound and includes every late response, without assuming cap attainment.

Put h=atom(sigma) and rho=sqrt(h), considering h>0 sufficiently small.
On every date with s_t>=rho,

    q_i(t)<=h/rho=rho.

Indeed first-date absorption mass is s_t*alpha_t and alpha_t>=q_i(t).
For four independent hazards bounded by rho, the simultaneous-quitting
probability is at most6rho times the stage absorption probability: pair
union bound gives at most(3rho/2)sum_i q_i, whereas alpha>=sum_i q_i/4.
The total collision probability before survival falls below rho is at most
6rho, and all later outcomes have total probability at most rho. Hence

    c<=7rho,     sum_i a_i(0)=1-c-nu ->1.          (5)

### Nonnegative continuation cone

Let Q_i(t) be the original Quit-now offer. On the prefix s_t>=rho,
|Q_i(t)-kappa_i|<=6M rho. A deviation only at this live date gives
s_t(Q_i(t)-v_i(t))<=E. Consequently (4), |r_i(D)-kappa_i|<=2M and (5) give

    Gamma*a(t) >= -E-20M rho-M nu                       (6)

coordinatewise; the extra M nu allows negative own levels in other rows.
On the remaining tail, sum_i a_i(t)<=rho gives the stronger
lower bound -2M rho directly. Thus (6) holds at every calendar vertex.

### Complementarity from complete deviation agency

Write C_i(t) for Continue-now followed by the prescribed continuation, so
v_i=q_i Q_i+(1-q_i)C_i. At every date where C_i>Q_i, remove the player's own
Quit probability, but only through a finite cutoff T; then resume the old
strategy. This modification increases its reach at all affected dates. The
finite performance-difference telescope therefore gives

    sum_{t<=T} s_t q_i(t) (C_i(t)-Q_i(t))_+ <= E.

Let T increase. Since v_i-Q_i=(1-q_i)(C_i-Q_i),

    sum_t s_t q_i(t) (v_i(t)-Q_i(t))_+ <= E.        (7)

The cutoff is essential: no silent assumption about a modified infinite tail
or an attained cap is used.

On the prefix s_t>=rho, (4) implies

    (Gamma*a(t))_i^+
      <=s_t(v_i(t)-Q_i(t))_+ +6M rho+M nu+2M c.

Multiply by p_i(t)<=s_t q_i(t), sum, and use (7). On the remaining tail the
positive part is at most2M rho. Therefore

    sum_t p_i(t)(Gamma*a(t))_i^+
      <= E+20M rho+M nu+2M rho^2 ->0.              (8)

### Pass to a genuine path

Interpolate each vector decrement p(t)=(p_i(t)) linearly, parametrizing it
by its total singleton mass sum_i p_i(t). Each segment has length at most h.
Normalize both the mass vector and this clock by A=sum_i a_i(0), so the
resulting path a_n on[0,1] has sum coordinates1-t, is coordinatewise
nonincreasing, and is1-Lipschitz. By (5), A->1.

The cone inequality (6) persists under linear interpolation. The difference
between the endpoint sum in (8) and its Stieltjes integral is at most2M h,
because each segment changes a by l1-distance at most h. Normalization divides
this bound and (8) by A^2. Arzela-Ascoli gives a uniformly convergent
subsequence. The limiting path has Gamma*a>=0. Uniform convergence and
bounded variation give convergence of integrals against d(-a_ni), so (8)
yields int (Gamma*a)_i d(-a_i)=0. Nonnegativity then gives (3).
This proves the lemma, also when the reward tables vary with n.

## 3. Complete generic no-path theorem

Suppose a complete path exists, and write v(t)=Gamma*a(t).

### Motion on one facet almost everywhere

For a nonnegative absolutely continuous scalar function its derivative is
zero almost everywhere on its zero set. Apply this simultaneously to the
four coordinates of v. At almost every t let S={i:v_i(t)=0}.
Complementarity gives u outside S zero, while derivatives at the zero rows
give Gamma_SS u_S=0. If |S|>=2, principal nonsingularity forces u=0,
contrary to sum u=1. If S is empty, complementarity gives the same
contradiction. Thus almost everywhere exactly one row i is zero and
u=e_i.

The union of the four zero-row sets is closed and has full measure, hence
contains [0,1]. Let Omega_i be the open subset of (0,1) where row i alone
is zero. On each connected component of Omega_i, a'=-e_i almost everywhere,
so a and v are straight segments. These disjoint open components fill
(0,1) up to a null set. We call them arcs.

Full nonsingularity and sum a=1-t>0 imply v(t)!=0 for every t<1.
Consequently at most three rows can be zero at an interior time.

### Interior switching is locally finite

We give the details because periodic-cycle reasoning alone does not control
arbitrary paths.

First suppose exactly two rows i,j vanish at an interior time b. Other rows
remain positive in a neighborhood, so only u_i,u_j can be nonzero there.
In that neighborhood

    v_i'=-Gamma_ij u_j,    v_j'=-Gamma_ji u_i.

If both displayed matrix entries are positive, nonnegativity forbids any
right continuation from v_i=v_j=0. If both are negative it forbids any left
continuation to that point. Thus at a genuine interior double zero the
entries have opposite signs. Suppose Gamma_ij>0>Gamma_ji. Integration from
b gives u_j=0 to its right, so u_i=1; integration backwards gives u_i=0
to its left, so u_j=1. The other sign orientation is symmetric. Hence a
double-zero time has a neighborhood consisting of exactly two arcs and
one switch. Its chronological switch j->i is the reverse of a prefix
opposition edge.

Now suppose exactly three rows S vanish at b; the outside row stays positive
near b, so a_o is constant there. Write B=Gamma_SS. In that neighborhood

    v_S(t)=B(a_S(t)-a_S(b)).

The triple-zero time is unique there: B invertible fixes a_S when v_S=0,
and a_o is constant while sum a strictly decreases. At any other nearby
time there are at most two zero rows, so the preceding argument makes
switching locally finite away from b.

If infinitely many arcs accumulate at b from the left, they give an infinite
chronological word on S. Consecutive letters differ and every switch follows
the reversed opposition graph. An oriented graph on at most three vertices
can support an infinite directed walk only if it contains the directed
triangle; that triangle uses all three vertices and every transition occurs
arbitrarily close to b.

For t<b sufficiently close, set x(t)=a_S(t)-a_S(b). Then x>=0 and
v_S(t)=Bx(t)>=0. At each switch the two switching rows are zero. The third
row k is strictly positive, because a triple zero occurs only at b. Thus

    B^{-1}e_k=x(t)/v_k(t)>=0.

Every k occurs, so B^{-1}>=0. But for t>b close enough, z=a_S(b)-a_S(t)>=0
and v_S(t)=-Bz>=0. Multiplication by B^{-1}>=0 gives z<=0; hence z=0,
contradicting strict decrease of total mass. Left accumulation is impossible.

If infinitely many arcs accumulate from the right, instead z(t)>=0 and
v_S(t)=-Bz(t)>=0 give B^{-1}e_k=-z(t)/v_k(t)<=0 at each of the three
switch types. Thus B^{-1}<=0. On the left x>=0 and Bx>=0 would imply
x=B^{-1}Bx<=0, again contradicting total-mass decrease. Right accumulation
is also impossible.

An isolated triple-zero contact also follows chronological opposition:
its adjacent owners i,j must differ, since a nonzero off-diagonal slope
cannot remain nonnegative through a zero with the same owner on both sides.
The incoming arc forces Gamma_ji>0 and the
outgoing arc forces Gamma_ij<0. The third zero row does not change this test.

These arguments cover every possible interior zero set, so every compact
subinterval of (0,1) meets only finitely many arcs. In particular, after
choosing any interior arc, subsequent arcs have an ordinary chronological
sequence; its only possible accumulation endpoint is1. An arc cannot
silently end merely because its owner's remaining mass becomes zero while
that row stays the unique zero row: the local equation a'=-e_i would violate
nonnegativity immediately afterwards.

### Recurrent owners and the triple criterion

Every column has a negative entry. There cannot be a final arc ending at1 with owner i:
all other coordinates of a would be constant and tend to0, giving

    a(t)=(1-t)e_i,    v(t)=(1-t)Gamma e_i>=0,

contradicting a negative entry in column i. Thus the chronological tail word
is infinite. Let S be the owners occurring infinitely often. Owners outside
S cease moving after some time; their remaining mass is then constant and
has limit0, so a outside S is identically zero on that tail.

The recurrent vertices form a strongly connected set in the chronological
opposition graph: after the last occurrence of a nonrecurrent vertex, any
two recurrent vertices are connected by portions of the tail word in both
directions. The same holds in the reversed prefix graph. There is no loop
and no directed two-cycle, so |S| is3 or4.

If |S|=3, its graph is a directed triangle. Set B=Gamma_SS. On the tail,

    v_S=B a_S,    v_o=Gamma_oS B^{-1}v_S.

At a switch between two owners, their two rows vanish and the third row k
is positive; otherwise invertibility of B and a outside S=0 would force
a=0 at t<1. Therefore

    B^{-1}e_k=a_S/v_k>=0,
    (Gamma_oS B^{-1})_k=v_o/v_k>=0.

The three transition types recur, proving every column/coordinate required
in the excluded child criterion. This proves the theorem when exactly three owners recur.

### Four recurrent owners and the bowtie obstruction

Assume now |S|=4 and the opposition graph has no Hamiltonian cycle. A strongly connected oriented graph
on four vertices without a Hamiltonian cycle is, up to labels, the bowtie

    0->1->2->0,    0->1->3->0,

with no edge between2 and3. For completeness, take a directed triangle.
The fourth vertex needs an incoming and an outgoing connection to it. If
these insert the fourth vertex into a forward triangle edge, there is a
four-cycle. Otherwise relabeling makes those edges1->3 and3->0. Either edge
between2 and3 would create a four-cycle; any additional edge on the other
pairs reverses an existing edge and is prohibited in an oriented graph.

Since a mutually negative pair exists, the mutually negative pair must be23, since the
five bowtie edges are opposition pairs. Positive row scaling puts Gamma in

    [ 0, a,-1,-h;
     -1, 0, b, d;
      c,-1, 0,-f;
      e,-1,-g, 0],

with all eight parameters positive. Positive row scaling preserves legality
of v>=0 and zero facets.

There is a direct monotone quantity that rules out four-owner motion,
without any switching argument. Use v=Gamma*a and write

    D=v_2/c-v_3/e.

If e>=c, differentiation gives

    D'=(e-c)/(ce) u_1-(g/e) u_2+(f/c) u_3.

On {D>0}, v_2>0, so complementarity forces u_2=0 almost everywhere.
Consequently (D^+)'=1_{D>0}D'>=0 almost everywhere. The positive part is
absolutely continuous and D(1)=0, hence D<=0 everywhere. Whenever u_3>0,
v_3=0 and D<=0 imply v_2=0. This contradicts the unique zero row almost
everywhere, so u_3=0 almost everywhere and a_3 is identically zero.
If c>=e, the identical argument with -D gives u_2=0 and a_2=0.
At equality both vanish. Thus at least one branch owner never moves,
contradicting four recurrent owners. This completes the no-path proof.

## 4. Exact example and the uniform conclusion

The canonical remaining construction target has singleton matrix

    Gamma = [0,3,-1,3;
             2,0,1/2,-3;
             2,-2,0,-1;
             -1,-2,1,0].

Its pair minors, in order01,02,03,12,13,23, are -6,2,3,1,-6,1;
its triple minors, in order012,013,023,123, are7,-3,5,7; its determinant
is35/2. A short direct certificate supplements the general classification.
On an owner1 arc, rows2,3 of v increase and only row0 can become newly zero.
That endpoint would have rows0,1 zero with positive mutual coefficients3,2:
nonnegativity forbids any subsequent motion of either owner. An owner1 arc
cannot last to1 either, since its column has a negative entry. Hence a_1=0.
The exact identity

    19 Gamma_2 = 11 Gamma_0 +18 Gamma_1 +2*(1,1,1,1)-73 e_1

then forces v_2>=(2/19)(1-t)>0, so a_2=0. Rows3 and2 now force a_0=a_3=0,
a contradiction. This certificate covers every finite higher-reward completion
of this matrix, including the R=-25,t=987 construction target.

To prove(1), suppose no common neighborhood and positive constants existed.
For each n choose Gamma_n within1/n of Gamma, rewards bounded by M, maximum
own level at least m, and a profile with E_n<1/n and atom_n<1/n. Section2
produces a complete absorption path for Gamma, contradicting Section3.
Thus some neighborhood, epsilon0 and c0 exist. The proof makes no assertion
that a Nash approximation with the required atom has been constructed.

## 5. Scope, prior mechanisms, and next obligation

The generic residual's opposition-Hamiltonian cases are already removed by
known singleton criteria. With no mutually negative opposite chord, there
is no negative reciprocal pair. Exactly one negative opposite chord invokes
the negative-chord Hamiltonian theorem. With both opposite chords negative,
every principal-triple determinant is negative. Since the full determinant
is positive, every diagonal entry of the full inverse is negative. This
contradicts the residual's strictly positive inverse column; no extra Q-matrix
argument is needed for this sign exclusion.
The21-orbit atlas verifies the remaining graph types directly:13 acyclic,
seven with a single recurrent triangle, and one negative-cross bowtie.

A finite balanced singleton certificate yields an absorption path: repeat
its proper solo hazards, let a_i at a calendar cut be the unconditional
remaining probability that i is first quitter, and interpolate each solo
decrement. Opponent absorption gives a(1)=0; the native Bellman values and
moving-owner equality give Gamma*a>=0 and complementarity throughout each
segment. Consequently Section3 also excludes every such certificate at
every finite period, including repeated owner words. This is a corollary
of the stronger unrestricted diffuse obstruction, not a separate result to
count as additional UE coverage.

This is an internal strategy-selection boundary. No-UE games already lack
Nash approximations; proving that approximations would require an atom does
not itself remove any possible counterexample table. Selected positive-gap
minimizers have nonvanishing regret and cannot be inserted into the adapter.
The remaining constructive task is to produce approximate profiles with
substantial date atoms, or a different mechanism whose errors are controlled
relative to absorption. No universal finite-period producer follows.

Source declarations inspected, without running Lean:

- `prod_stoppingLaw_none_mul_singleton_le_terminalDebt` in
  `UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean` supplies
  the actual-profile Never bound, without row-shift invariance.
- `quittingFiniteRefusal_terminalValue_sub_eq_sum` and
  `delta_mul_tsum_selectedRefusalCharge_le_of_nash` in
  `UniformEquilibrium/Quitting/Classification/Existence/GlobalRefusalLedger.lean`
  provide the prior complete-deviation refusal mechanism.
- `ChronologicalLimit.singletonReward_le_absorptionPathPayoff` in
  `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalSingletonLowerBound.lean`
  and `ChronologicalLimit.isSequentiallyPerfectAbsorptionPath` in
  `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalPositiveSingletonRate.lean`
  are prior chronological path adapters. Section2 is a direct specialization,
  including varying bounded tables, not a new general compactness theory.
- `BalancedSingletonCycleCertificate` and its
  `BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` consumer in
  `UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean` define
  the finite architecture eliminated as a corollary.
- `exists_principalQAbsorptionApproximation` in
  `UniformEquilibrium/Quitting/AbsorptionPath/PrincipalQContinuousPath.lean`
  requires stronger projective-principal-Q data than the residual's one
  standard-Q condition; it does not contradict this obstruction.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  is the unchanged fixed-target semantic endpoint. It is not supplied here.
