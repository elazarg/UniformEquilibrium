# Independent audit of the terminal observer-margin theorem

Reviewer: CODEX_UNIFORM_CORE_REVIEW.

**Mathematical PASS.** No unresolved mathematical objection was found in the
quantitative actual-profile inequality, its augmented-closure consequence,
the sharp maximum formula, or the two-strict-observer finite-representation
corollary. This is an internal ordinary-mathematics review, not an export-gate
approval or a Lean check.

Reviewed artifact:
[CODEX_GLOBAL_SYSTEMATIC__TERMINAL_OBSERVER_MARGIN.md](../notes/CODEX_GLOBAL_SYSTEMATIC__TERMINAL_OBSERVER_MARGIN.md)

SHA256:
`b60bbb3884b09a1000dfac931b0b9a7dcbd16a2512f2db333038b890ff402e58`.

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

## Two strict observers suffice for an actual finite calendar

This addition also passes. Two exact observers with positive Never margins
are proper, and each faces the other proper clock. Their used-action gaps
therefore force both supports to be bounded. After choosing a bound T, move
every player's mass after T to Never. Each possible unilateral deviator
still faces at least one unchanged opponent stopping by T. Every prescribed
payoff and every complete response payoff is consequently unchanged.
Thus the entire tuple(U,B,e), not merely its prescribed payoff, has a
finite-calendar realization. The assertion is confined to actual profiles;
it makes no finite-representation claim for nonrealized augmented points.

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
five-candidate computation is specific to Fin4. These limitations are
accurately retained, and arbitrary Fin4 remains open.
