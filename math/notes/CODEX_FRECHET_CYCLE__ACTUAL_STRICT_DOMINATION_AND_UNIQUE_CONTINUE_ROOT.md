# Actual strict domination can coexist with a unique Continue root

Author: CODEX_FRECHET_CYCLE.

Status: complete bounded ordinary-mathematical regression, not Lean-checked;
no export proposed. This is an already-solved raw class, not a new equilibrium
existence result. It answers the specific question whether actual strict
payoff feasibility forces a nontrivial Nash root at that payoff: it does not.
The stronger calculation also excludes that payoff as a uniform-equilibrium
target. Construction of some other equilibrium payoff is not obstructed.

## 1. Exact canonical table and actual one-date witness

There are four players, independent complete stopping laws on ℕ∪{Never},
zero preabsorption and Never payoff, and unrestricted behavioral deviations.
Set s=(1,0,0,0). For EVERY nonempty coalition S define

    r_i(S)=s_i if i∈S, and r_i(S)=2 if i∉S.              (1)

This is a rational table bounded by M=2, with exactly the asserted own
singletons. It satisfies weak solo-exit preference with equality. In
particular it belongs to known solved participant-capped/product-low classes.
Each pure singleton profile is an exact terminal Nash equilibrium: the
owner cannot improve on its nonnegative singleton by delaying or choosing
Never; outsiders receive their global upper reward 2.

The exact independent punishment value of player i is s_i. Quit at zero
guarantees s_i against every opponent profile. Against all-Never opponents
the full cap is max(s_i,0)=s_i. Thus both inequalities for the infimum hold.

Let every player independently quit at date zero with probability 1/2 and
otherwise choose Never. This is one product row followed by all-Continue,
not a correlated lottery. Player i receives s_i on its own Quit, and 2 if
it Continues while at least one opponent Quits. Therefore

    v_i=s_i/2+7/8,
    v=(11/8,7/8,7/8,7/8)>s.                            (2)

It strictly exceeds the punishment vector as well. The strict-domination
margin is at least 3/8. This is already an actual witness on one finite
date, stronger than the twenty-date input requirement.

## 2. Exact uniqueness at the realized payoff

In the Boolean root game G(v), fix ANY opponent root and write β_i for
its all-Continue probability. The own Quit and Continue endpoints are

    Q_i=s_i,       C_i=2(1−β_i)+β_i v_i.

Both 2 and v_i strictly exceed s_i, so C_i>s_i for every β_i∈[0,1].
Continue is strictly dominant for every player. Consequently all-Continue
is the UNIQUE Nash root at the actual payoff v. This excludes all other
roots, not merely Pareto-preserving or nearby roots.

The same proof works at EVERY continuation u with u_i>s_i for all i.
Thus staying in the strictly singleton-dominating chamber gives no exact
absorbing Nash–Bellman step, even though that chamber contains actual
prescribed payoffs. This is not an assertion about roots after leaving it.

## 3. Complete caps and the actual payoff-target obstruction

For arbitrary independent stopping laws, let

    z_i=Pr(T_i=Never),       N=∏_i z_i,
    α_i=Pr(i belongs to the first finite quitting coalition),
    c_i=2−s_i,
    e_i=α_i−(1−z_i)∏_(j≠i)z_j.

The quantity e_i is exactly the probability that i belongs to the first
finite coalition AND at least one other player's clock is finite. It is
nonnegative; it is not a same-date collision probability.

Writing O_i for the first opponent stopping date, pure Quit at t pays

    2 Pr(O_i<t)+s_i Pr(O_i≥t).

This increases with t and converges to
s_i+c_i(1−∏_(j≠i)z_j). Never pays 2(1−∏_(j≠i)z_j), which is no larger
because s_i≥0. Every complete response payoff is an average of these pure
values. Hence the unrestricted response SUPREMUM, possibly unattained, is

    B_i=s_i+c_i(1−∏_(j≠i)z_j).                         (3)

The actual prescribed payoff and debt satisfy

    U_i=2(1−N)−c_i α_i,
    d_i=B_i−U_i=c_i e_i+s_i N,
    D=Σ_i c_i e_i+N.                                  (4)

On every sample with at least two finite clocks, some first quitter is
counted among the e_i events, and c_i≥1. Since Σ_i s_i=1,

    D ≥ Pr(at least two clocks are finite)+Pr(all clocks are Never)
      = 1−Pr(exactly one clock is finite).              (5)

Consider any sequence of actual laws with D→0. The four probabilities
q_i=1−z_i lie in a compact cube. At any subsequential limit, (5) says that
the sum of four independent Bernoulli(q_i) variables is exactly one almost
surely. Its variance is Σ_i q_i(1−q_i)=0 and its mean is one. Hence exactly
one limiting q_i equals one and the other three equal zero. The probability
that this one player is the unique finite clock tends to one, so the
terminal coalition law tends to its singleton. Bounded rewards imply

    every zero-debt payoff cluster is one of r({0}),…,r({3}).   (6)

Conversely these four payoffs have the pure singleton exact equilibria
already checked. Thus the set of zero-debt payoff limits is EXACTLY these
four points. None equals (2).

The same is the uniform-equilibrium payoff set. For necessity, let the
uniform error tend to zero and then let each finite horizon tend to infinity.
Bounded convergence gives terminal prescribed payoffs approaching the fixed
target and terminal response bounds with vanishing error, hence D→0.
Equation (6) applies. Conversely the pure singleton profiles themselves
give their displayed uniform payoffs (delaying one's nonnegative singleton
cannot improve a finite average, and outsiders already get their upper bound).

This is a literal feasible and strictly individually rational payoff that
is not even a limit target of terminal approximate equilibria. It does not
refute equilibrium existence: the four easy singleton targets remain.

## 4. Source and repetition boundary checks

For the actual one-date witness (2), equation (3) gives

    B=(15/8,7/4,7/4,7/4),       D=25/8.

Player 0's cap includes a late finite Quit and exceeds its Never response;
omitting that late singleton branch would incorrectly report B_0=7/4.

Repeating the same product row forever gives prescribed payoff

    (22/15,14/15,14/15,14/15),

because one row survives jointly with probability 1/16. Every opponent
system then absorbs almost surely, so all four complete caps are 2 and
D=56/15. Repetition does not Nashify this actual strict-domination witness;
the total debt even rises. This example uses exact full responses, not a
periodic response restriction.

## 5. Narrow literature and existing-mechanism comparison

Primary sources inspected before choosing this test:

- Solan and Vieille, *Quitting Games* (2001), Theorem 1.2 and Propositions
  2.2–2.4 in the [journal paper](https://www.math.tau.ac.il/~eilons/quitting19.pdf).
  Their cycle construction requires a compact continuation set with
  nonempty absorbing approximate-perfect predecessor values. Their repair
  input is terminating play that is approximately perfect against its
  actual tails. A single feasible vector above singletons supplies neither
  input. The table (1) has a positive own singleton and three zero ones,
  so the paper's unit-solo assumption is not invoked for this table.
- Fudenberg and Yamamoto, *The Folk Theorem for Irreducible Stochastic Games
  with Imperfect Public Monitoring*, Sections 1–2 of the
  [author's March 2010 version](https://economics.mit.edu/sites/default/files/2022-09/The%20Folk%20Theorem%20for%20Irreducible%20Stochastic.pdf).
  Its return-generation argument assumes irreducibility. A quitting action
  can instead force permanent absorption; no opponent policy returns from
  that absorbed state to live play. The different singleton absorbing states
  here also have different feasible payoff sets. Feasibility and strict
  individual rationality at the live state do not remove that mismatch.

The local transcription/source audit used `Literature/SolanAndVieille2001.lean`
and `QuittingUnitSoloExit`, `QuittingCappedJointExit`, and
`QuittingWeakSoloExitPreference` in
`UniformEquilibrium/Quitting/Classification/SoloExitPreference.lean`.
The latter own-singleton predicate is met by (1); the distinct unit condition
is not. No strategic affine normalization of zero Never was used.

The bounded note check read the existing rational cap-inert cycle audit
`CODEX_RIEMANN__STRICT_INERT_RATIONAL_REALIZATION_AUDIT.md`, the supplied-source
repair in `CODEX_FRECHET_CYCLE__R_SURVIVAL_WEIGHTED_SOURCE_REPAIR.md`, the
calendar-extension test in
`CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_MINIMUM_CALENDAR_EXTENSION.md`, and the
fixed-format/periodic boundaries in
`CODEX_HILBERT__FIXED_PERIODIC_FORMAT_ALL_ACCURACY_CERTIFICATE.md` and
`CODEX_SPINOZA__PERIODIC_COMPLEMENTARITY_AND_PASSIVE_PADDING_NO_GO.md`.
Those already distinguish an actual profile, its cap, and an absorbing
root-perfect source. No novelty is claimed for that architectural warning.

The sharpened regression here uses the PRESCRIBED payoff of an explicit
finite independent profile, proves unique all-Continue roots against it,
and calculates all possible low-debt payoff limits on the same canonical
table. It neither realizes a positive global minimum nor eliminates a
counterexample class.

Mechanism decision: abandon preservation of the supplied strict-domination
payoff as a general target, and abandon extraction of a nontrivial exact
root while remaining in its strict upper chamber. Any useful global use of
the witness must permit a macroscopic move to another payoff region and
justify that move by additional table or incentive structure. This note
supplies no such new renewable producer and proposes no further gate.

Requested local check: verify that the late-finite supremum in (3), not the
Never payoff alone, is used in deriving the all-behavior debt identity (4).
