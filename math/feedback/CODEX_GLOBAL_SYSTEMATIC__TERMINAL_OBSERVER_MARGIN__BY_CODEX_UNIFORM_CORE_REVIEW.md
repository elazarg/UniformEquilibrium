# Independent audit of the terminal observer-margin theorem

Reviewer: CODEX_UNIFORM_CORE_REVIEW.

**Mathematical PASS.** No unresolved mathematical objection was found in the
quantitative actual-profile inequality, its augmented-closure consequence,
the sharp maximum formula, or the one-strict-player finite-calendar theorem
with exact original Never masses. This is an internal ordinary-mathematics review, not an export-gate
approval or a Lean check.

Reviewed artifact:
[CODEX_GLOBAL_SYSTEMATIC__TERMINAL_OBSERVER_MARGIN.md](../notes/CODEX_GLOBAL_SYSTEMATIC__TERMINAL_OBSERVER_MARGIN.md)

SHA256:
`15fdf8297c7c2dc37c47cd4183b679278afc51bd8ff4f51413a60af35913ffa6`.

## Scope checked

The game has four players, independent private complete stopping laws on
finite dates plus literal Never, arbitrary signed original terminal rewards
bounded in absolute value by M>=1, and zero AllNever payoff. With pivot p
and three observers S, the claim is

    min_(i in S)(B_i-e_i)
      <= max(0,Lambda_p)+4 sqrt(M sum_(i in S)(B_i-U_i)),

where Lambda_p is the maximum over x in[0,1] of the minimum of the three
joining-displacement lines. This applies to every actual profile, with no
absorption or observer-optimality hypothesis. Its zero-debt consequence is
sharp on both augmented semantic carriers and on actual absorbing
exact-observer profiles.

The full assembled artifact was read, including its finite-calendar theorem:
one exact player satisfying B_i>max(e_i,END_i) gives a finite-calendar
representation preserving the entire(U,B,e,N) tuple and the prescribed
terminal outcome law. The one-player condition concerns actual laws only.
The three-observer margin theorem additionally applies to nonrealized
augmented carrier points through its quantitative closure argument.

I checked the proof independently, focusing on the steps that could confuse
actual response offers with carrier coordinates, lose independence under
conditioning, or use a native own-zero convention implicitly. None does.

## Affinity, signed rewards, and the final-date lemma

For fixed opponent laws, a complete response is a bounded average of pure
finite-deadline and Never response offers. Hence U_i averages offers at most
B_i, even if the pure supremum is not attained. Exact observer optimality
forces every positive-probability prescribed response to attain B_i.
A strict cap-minus-Never gap therefore removes prescribed Never mass.

If an observer has a proper opponent, couple all responses using the same
opponent clocks. Almost surely some opponent stops at a finite date. Every
sufficiently late own deadline then has exactly its Never outcome. Bounded
convergence proves V_i(t)->e_i. This uses rewards in[-M,M], including the
zero AllNever outcome; it needs neither nonnegative rewards nor zero own
singletons.

A uniform positive margin on all used deadlines thus bounds each proper
observer's support. If two last dates were unequal, the earlier observer
would surely stop before the later one's used deadline, making that deadline
outcome-equivalent to Never. All observer last dates are consequently equal.
The pivot must have positive survival to that date for the same reason.

Conditioned on all opponents reaching the common last date, the other
observers quit there surely. Independence leaves the same pivot conditional
hazard x for each observer. The exact margin is

    a_p product_(j in S\{i}) a_j * L_i(x).

Every prefactor is positive and at most1. Crucially, the strict used margins
make every L_i(x) positive before the proof takes the minimum and drops those
prefactors. That positivity is necessary: the analogous comparison would
not be valid for arbitrary signed L_i. The proof uses it correctly.

## Conditioning and the quantitative constant

For delta>0, the deficit identity implies that the prescribed mass outside
F_i={t finite: V_i(t)>=B_i-delta} is at most d_i/delta. Never is outside
F_i in the nontrivial branch g>delta+4MD/delta. Also g<=2M gives
D/delta<1/2 there, so every conditioning event has positive probability.
No maximizing pure response is assumed to exist.

Each F_i is a deterministic set of that observer's dates, computed from the
fixed original profile. Conditioning the three laws separately preserves
the product structure and leaves the pivot unchanged. Coupling a law with
its conditional law costs precisely its removed mass in total variation.
Independent coordinate couplings and the union bound then give, uniformly
for every fixed complete response of observer i,

    |offer_new-offer_old|<=2M sum_(j in S\{i}) rho_j.

The deviator's response can be coupled identically; on the event that all
opponent clocks agree, the entire terminal outcome agrees. The estimate
also applies separately to literal Never. Comparing the two offers costs
4M D/delta, which is exactly the constant used in the note.

Every new used deadline therefore has Never margin at least

    g-delta-4MD/delta>0.

The conditioned profile is proper in every observer coordinate. It need
not be exact observer-Nash: the final-date lemma only needs properness and
the uniform strict used-action margin. It follows that the displayed lower
margin is at most Lambda_p. Combining with the trivial branch and choosing
delta=2 sqrt(MD) gives the claimed constant4. For D=0 the arbitrary-delta
bound passes to the limit. At no step is a conditioned cap substituted for
an original B_i.

## Sharpness, computation, and augmented limits

For Lambda_p>0, the common Quit0 observer profile with pivot Quit0 probability
x realizes exactly the three lines L_i(x). Each observer's entire menu has
only two payoff types: Quit0 and later-or-Never. Positive line values make
all observers exact best responders, and the minimum gap is Lambda_p.

For Lambda_p<=0, fixing the pivot at Quit0 reduces observer incentives to
a finite three-player binary game. A mixed Nash equilibrium exists; later
deadlines and Never are equivalent to Continue0. This supplies an actual
absorbing exact-observer profile. The proved upper bound makes its minimum
gap zero, so the maximum remains attained in this case as well.

The finite computation checks: three affine lines need only the two endpoints
and their at most three pair intersections. Finite minimax gives the stated
dual certificate. The support-at-most-two assertion follows from the finite
one-dimensional Helly property for the strict positivity intervals; open
endpoints do not invalidate that property.

All coordinates U,B,e are bounded, including with arbitrary signed original
levels. The quantitative inequality is continuous on the region of
nonnegative debts, so it passes to both closures. For a realizing sequence
of payoff/full-cap pairs, bounded Never offers admit a convergent subsequence
without changing the limiting pair. The observer debts still vanish.
This proves the statement for every augmented lift, without inventing an
actual profile for a nonrealized carrier point. Which observer is
Never-active may depend on the lift, as the note explicitly allows.

## One strict player and exact finite-calendar representation

For arbitrary signed own levels, the late-deadline limit is

    END_i=e_i+r_i({i}) product_(j!=i)N_j.

The additional term is essential. On outcomes with a finite opponent,
late responses agree with Never; on the all-opponent-Never event they
receive the own singleton instead of zero. Bounded convergence proves the
displayed limit without a proper-opponent premise.

Under U_i=B_i>max(e_i,END_i), exactness puts all prescribed mass on
maximizing responses. Never has a strict gap and all sufficiently late
finite dates have a strict gap, so i has proper bounded support. An early
maximizing date therefore exists; this is derived from exactness, not from
an assumption that arbitrary caps are attained.

Choose the note's cut T beyond that support and with the stated late-offer
and residual-mass gaps. Under every unilateral replacement by j!=i,
player i's unchanged clock still stops by T. Consequently all changes
strictly after T preserve every j-response payoff, including Never, and
preserve the prescribed first-coalition law. They also preserve every
i-response offer at dates at most T. Only i's late menu and Never value
need further control.

The scalar compression is valid. Conditioning on every opponent being
after T is a product event, so the conditional laws remain independent.
Their original conditional Never probabilities n_j are held fixed.
Hypothetical finite dates followed by independent finite/Never flags
generate exactly these laws. After averaging just the flags, the passive
payoff depends only on the finite dates' weak order, including ties.
There are finitely many weak orders; all are represented by ranks on the
same |I|-1 fresh dates. Thus their minimum and maximum bracket the actual
conditional Never payoff.

Interpolate each marginal independently between the two extremizing rank
vectors using the SAME deterministic scalar lambda. The resulting expected
passive payoff is polynomial in lambda. The intermediate value theorem
matches the required scalar payoff exactly. The common parameter does not
introduce shared randomness: the opponent draws themselves remain independent.
Each opponent uses at most two fresh finite atoms, and its conditional
Never mass is unchanged.

Unconditioning retains every probability at dates at most T and every
ORIGINAL Never mass. Only residual finite mass rho_j(T) moves, so the total
variation distance of each marginal is at most rho_j(T). Independent
coupling bounds every complete i-response payoff change by
2M sum rho_j(T). This is uniform over all deadlines and Never. The scalar
matching gives exact equality for Never; the strict late-offer gap keeps
all new finite offers after T below B_i, and an early maximizing offer
survives. Hence the full cap B_i is exactly preserved as well.

The edge cases are covered. Conditional n_j=1 makes its unused hypothetical
finite law irrelevant. If the all-opponents-after-T event has probability
zero, one opponent stops by T surely; arbitrary relocation of the other
residual finite masses cannot change any i-response outcome after T. No
conditioning on a null event occurs. The argument applies for any finite
number of players at least two, including a single opponent.

For native own-zero tables END_i=e_i, so one strict exact observer suffices.
If an actual native exact-observer tuple has no finite-calendar realization,
ALL its observers must therefore be Never-active. In arbitrary original
signed tables, two strict exact observers are proper and each has a proper
opponent, making END_i=e_i and recovering the two-observer consequence.
One strict Never margin alone does not establish the needed late gap when
the own singleton is positive and every opponent has positive Never mass.

The resulting finite calendar preserves(U,B,e,N), not only numerical debt
or prescribed payoff. A realized minimum remains the same minimum tuple.
No actual-law operation is asserted for a nonrealized compact-limit point.

The equality-boundary example also passes. Against j's hazard1/2, player i's
finite-deadline payoff is(1-2^(-t))+2^(-t)*1=1, and Never also pays1.
The displayed profile is exact Nash with a bounded clock for i. In any
finite-calendar representation preserving N_j=0, j's last positive atom
alpha gives i the response1+alpha. Thus the full cap cannot stay1. The
Fin4 embedding retains this contradiction because Never mass1 forces both
added zero-payoff players to remain Never. This proves that a bounded exact
clock alone cannot replace the theorem's strict gap; it is not a UE
counterexample or a claim about nonrealized carriers.

The narrow overlap search also inspected
`CODEX_SPINOZA__FINITE_MARKED_ORDER_COMPACTNESS_AND_DIFFUSE_CLOCK_NO_GO.md`
and `CALENDAR_POLYTOPE_UNIFORM_EQUILIBRIUM.md`. They retain weak-order
distributions or convex calendar relaxations; neither supplies this
independent two-atom scalar matching with fixed Never masses and protection
of every response cap. No preexisting theorem of this scope was found there.

## Source correspondence and limitations

I statically inspected the named declarations and nearby statements:

- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
  `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`;
- `quittingTerminalSemanticPair_rootThenContinuation` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.

Their arbitrary-reward, all-behavior, and actual-splicing scopes agree with
the uses described. No Lean command ran. The closure and quantitative
arguments are ordinary mathematics here, not new checked declarations.

The raw condition Lambda_p<=0 is not supplied for arbitrary games by this
proof. A Never best response need not have positive prescribed Never mass,
and the theorem supplies no observer repair or debt-descent step. The
positive-Lambda witness need not realize a global partial-Nash minimum.
The general margin argument extends to at least three players; the stated
five-candidate computation is specific to Fin4; the actual finite-calendar
theorem instead holds from two players onward. These limitations are
accurately retained, and arbitrary Fin4 remains open.
