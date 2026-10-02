# CODEX_HILBERT — global better-reply security from independent pair laws

## Status and exact result

Ordinary mathematical proof draft; not independently reviewed, not Lean
implemented, and not exported. The bounded test finds a genuine positive
class-to-existence implication, rather than another counterexample to an
every-selector regularization claim.

For a finite quitting table with nonnegative own singleton rewards and at
least one strictly positive singleton, the complete compact independent
stopping-law game is better-reply secure **if and only if** the closure of
its actual prescribed-payoff image contains no vector coordinatewise above
the singleton vector. This characterizes Reny's original hypothesis without
requiring a common chronology, finite-menu approximation, or censoring.

An explicit open Fin4 table class satisfies this condition by the checked
independent disjoint-pair square-root law. It therefore has an exact terminal
Nash profile against unrestricted behavioral deviations, and a uniform
equilibrium payoff. The class lies outside the nonnegative weighted-social
chamber. It contains an explicit rational table with no pure timing Nash
profile. No claim is made that the class is disjoint from every other solved
class, or that better-reply security is necessary for UE.

The security characterization and its application are new in this bounded
source audit. The compact law representation, late-Never debt inequality,
pair-mass inequality, and global singleton-margin machinery are not new.
The question remaining after this tranche is an independent check of the
graph-defect factorization in Section 4 and the resulting class consumer.

## 1. Data, agency, and topology

Let I be finite and nonempty, r(S) in R^I for every nonempty S subset I,
and let nontermination pay zero. Write s_i = r_i({i}) and bound every reward
coordinate in absolute value by M.

Let T = N union {infinity} with its one-point compactification topology.
Player i's strategy space is X_i = P(T), with the weak topology. Every
complete law, including an arbitrary Never atom, is admissible. A profile
mu chooses the players' clocks independently; its terminal coalition is
the set attaining the first finite time, retaining all ties. The payoff is
zero if every clock is infinity. Write U(mu) for its payoff vector,

    B_i(mu) = sup over all laws nu_i of U_i(nu_i,mu_-i),
    d_i(mu) = B_i(mu) - U_i(mu),
    a_i = mu_i({infinity}),       A(mu) = product_i a_i,
    K_r = closure { U(nu) : nu in product_i X_i } in R^I.

K_r is compact because rewards are bounded. It is not replaced by its
convex hull. Mixtures between different product profiles would generally
require a public coordinating coin, which is not used here.

Each X_i is compact, metrizable, and convex in the locally convex space of
signed measures with its weak topology. Terminal payoff is bounded and
affine in the owner's law, hence quasiconcave. It need not be jointly
continuous. The first-stopping-law representation and unilateral mixture
identity make this law game exactly the terminal behavioral game, not a
restricted strategy class. A pure equilibrium in this law game means one
independent possibly mixed stopping law per player.

## 2. Original theorem actually used

I read Reny's original definitions and statements on pp. 1032–1036:

- Philip J. Reny, *On the Existence of Pure and Mixed Strategy Nash
  Equilibria in Discontinuous Games*, Econometrica 67 (1999), 1029–1056,
  [original paper scan](https://kylewoodward.com/blog-data/pdfs/references/reny-econometrica-1999A.pdf),
  [publisher DOI](https://doi.org/10.1111/1468-0262.00069).

At x, player i secures alpha if one fixed strategy gives at least alpha
against every opponent profile in some open neighborhood of x_-i.
Better-reply security requires, at every graph-closure point (x,u*) with x
not Nash, a player who can secure a value strictly exceeding u*_i.
Theorem 3.1 gives a pure Nash equilibrium for a compact, quasiconcave,
better-reply-secure game. This is the theorem applied here.

For comparison, Proposition 3.2 derives security from payoff security and
reciprocal upper semicontinuity; Corollary 3.3 then gives existence. I do
not impose those stronger sufficient conditions on the pair chamber.

The [Ewerhart–Reny 2022 corrigendum](https://ewerhart.net/files/2022%20Ewerhart%20Reny%20Etrica.pdf)
was read in full. It explicitly leaves Theorem 3.1 and Corollary 5.2
unaffected; its corrections concern the quasisymmetric statements, which
are not used here.

## 3. Full-response security and the Never debt floor

Assume s_i >= 0. For fixed opponents define F_i(t) to be player i's payoff
from the deterministic finite date t, and V_i from literal Never. The
complete one-player mixture identity gives

    B_i = max(sup_t F_i(t), V_i).

For each fixed finite t, F_i(t) is continuous in the opponents' weak laws.
Indeed it is a finite polynomial in their masses at dates at most t and
the corresponding finite-head survival probabilities. It handles collisions
at t exactly; there is no no-ties assumption.

The late-Quit identity is

    lim_(t -> infinity) F_i(t) = V_i + s_i product_(j != i) a_j.

Consequently B_i = sup_t F_i(t) when s_i >= 0. Thus whenever alpha < B_i,
one finite t has F_i(t) > alpha; continuity makes that **same** complete
response yield at least alpha against all sufficiently close opponents.
The supremum of secure values therefore equals the unrestricted cap. It
is not asserted that a cap-attaining finite t exists. In particular the
game is payoff secure in Reny's exact neighborhood-uniform sense.

There is also the pointwise floor

    d_i(mu) >= s_i A(mu).                                      (3.1)

To prove it, replace only i's Never atom a_i by an atom at t, leaving all
of i's finite masses unchanged. The change of payoff is exactly
a_i(F_i(t)-V_i), tending to s_i A(mu). Each replacement is one permissible
complete unilateral law. Taking the unrestricted supremum proves (3.1).
This proof does not divide by a_i or by any deleted survival, and still
works when either is zero.

The assumption s_i >= 0 matters for the secure-cap statement, not for
the algebraic late-Quit identity. For example a negative singleton can
make Never better than every sufficiently late finite Quit.

## 4. Exact location of every payoff-graph defect

Lemma. Suppose mu^n -> mu weakly coordinatewise and U(mu^n) -> u*. Then:

1. If A(mu)=0, u*=U(mu).
2. If A(mu)>0, there is v in K_r such that

       u* = U(mu) + A(mu) v.                                  (4.1)

Conversely, every v in K_r is a graph-limit payoff above the all-Never
profile.

Proof. For a finite cutoff H, let P_H(mu) be the unconditional reward
contribution from absorption strictly before H, and R_H(mu) the joint
probability of reaching H. These are continuous finite-head functions.
On R_H(mu)>0, condition each player's law on surviving to H and subtract
H from finite dates. Independence is preserved and this defines an actual
complete suffix law profile mu|H. The exact decomposition is

    U(mu) = P_H(mu) + R_H(mu) U(mu|H).                          (4.2)

Moreover R_H(mu) -> A(mu), while P_H(mu) -> U(mu): the missing finite
absorption events have probability R_H(mu)-A(mu), tending to zero. This
last convergence, rather than a fictitious value assigned to the joint
Never event, is essential.

If A(mu)=0, first take n -> infinity at fixed H in the bound
|U(mu^n)-P_H(mu^n)| <= M R_H(mu^n), coordinatewise. Then H -> infinity
gives assertion 1.

If A(mu)>0, choose H_k -> infinity and n_k -> infinity so that the
finite-head differences P_(H_k)(mu^(n_k))-P_(H_k)(mu) and
R_(H_k)(mu^(n_k))-R_(H_k)(mu), as well as U(mu^(n_k))-u*, all tend to zero.
For large k, R_(H_k)(mu^(n_k))>0, so (4.2) supplies an actual suffix
payoff v_k. A subsequence of the bounded v_k converges to v in K_r.
Taking limits in (4.2) gives (4.1). These H_k are used only to prove a
payoff-graph identity, not to construct compatible equilibria.

Finally choose nu^n with U(nu^n)->v and delay every finite clock in nu^n
by n, retaining its Never atom. Every marginal then converges weakly to
Never, whereas common deterministic delay leaves terminal coalitions and
U(nu^n) unchanged. This proves the converse. QED.

The normalized defect v is an actual-payoff limit from independent laws.
It is not an arbitrary convex combination of coalition rewards. This
distinction supplies the useful information in the application below.

## 5. Exact better-reply-security characterization

Theorem. Assume every s_i >= 0 and at least one s_i > 0. Then

    the complete law game is better-reply secure
        iff K_r intersect (s + R_+^I) is empty.                 (5.1)

Sufficiency. At a graph point (mu,u*) with mu not Nash, if A(mu)=0,
Section 4 gives u*=U(mu). Non-Nashness gives some B_i(mu)>u*_i;
Section 3 supplies a fixed neighborhood-safe finite response.

If A(mu)>0, write the defect as A(mu)v with v in K_r. The right side
of (5.1) gives an i with v_i<s_i. Then (3.1) gives

    B_i(mu)-u*_i = d_i(mu)-A(mu)v_i
                >= A(mu)(s_i-v_i) > 0.

Again one fixed finite response secures a value strictly above u*_i.
This verifies all graph points and the original uniform-over-neighborhood
quantifier, not just limits of equilibrium selections.

Necessity. If v in K_r and v>=s, Section 4 realizes (all-Never,v) in
the graph closure. All-Never is not Nash since some s_i>0. At its
opponents, the unrestricted cap of i is max(s_i,0)=s_i. No strategy can
secure strictly more than v_i>=s_i because the neighborhood includes the
all-Never opponent profile itself. Hence better-reply security fails. QED.

Combining (5.1), compactness, own affinity, and Reny's Theorem 3.1 yields
an **exact terminal Nash profile** whenever the right side of (5.1)
holds. The all-errors terminal/UE semantic theorem then gives one fixed
uniform-equilibrium payoff. No public correlation, extra player, enlarged
game, or chronological source structure is introduced.

This is a characterization of this precise existence theorem's hypothesis,
not a characterization of equilibrium existence. Known positive-singleton
solved tables fail it. For the old two-active collision-reward falsifier,
the escaped payoff already dominates s; no repeat derivation is needed.

## 6. A finite, open Fin4 table class satisfying the global hypothesis

Take I={0,1,2,3}, A={0,1}, B={2,3}. Define the base table r^0 by

    r^0({i}) = e_i,
    r^0(A)   = (5/2,5/2,0,0),
    r^0(B)   = (0,0,5/2,5/2),
    r^0(S)   = 0 for every other nonempty S.

Consider every table r with

    max_(S,i) |r_i(S)-r_i^0(S)| < 1/100.                       (6.1)

The numerical radius is only a convenient strict margin, not an optimized
constant. In particular all own singleton rewards are positive.

For an actual profile let a,b be the exact terminal masses of A,B and
x_i its singleton masses. Independence, including arbitrary Never atoms,
gives the checked two-pair inequality

    sqrt(a) + sqrt(b) <= 1.                                   (6.2)

Also sum_i x_i <= 1-a-b. Under r^0 the four payoffs are

    U_0=x_0+(5/2)a, U_1=x_1+(5/2)a,
    U_2=x_2+(5/2)b, U_3=x_3+(5/2)b.                          (6.3)

These relations persist under limits of actual terminal laws. Suppose an
actual limiting payoff for r^0 had every coordinate at least c=49/50.
Using the first pair of (6.3) and x_0+x_1<=1-a-b gives

    4a-b >= 2c-1 = 24/25.

The other pair gives 4b-a>=24/25. Substitution yields

    a >= 8/25 > 1/4,       b >= 8/25 > 1/4,

contradicting (6.2). Therefore K_(r^0) contains no vector >=(49/50)1.

For r satisfying (6.1), payoff vectors of the same actual profile differ
by less than 1/100 per coordinate, since total finite absorption is at
most one. If v in K_r satisfied v>=s(r), take its realizing profiles and
a convergent subsequence of their r^0 payoffs. The limit v^0 would satisfy

    v_i^0 >= v_i-1/100 >= s_i(r)-1/100 >= 49/50,

contradicting the preceding paragraph. Thus K_r contains no v>=s(r).
Section 5 proves exact terminal Nash existence for every table in (6.1).

The proof uses all actual stopping laws globally. It is not a stationary
screen, a statement that a chosen equilibrium family is tight, or a finite
menu EA hypothesis under another name.

## 7. Separation from the weighted-social chamber and pure sinks

The convex hull cannot replace K_r in Section 5. Already at the base table,
the half-and-half convex combination of the two pure-pair payoffs equals
(5/4)1, which strictly dominates s=1. That correlated pair lottery violates
(6.2) and is not an attainable independent terminal-law limit. The same
strict domination by this convex combination persists throughout (6.1).

For every nonzero theta>=0, a table in (6.1) satisfies

    theta dot (r(A)+r(B)-2s(r))
      >= (1/2-4/100) sum_i theta_i > 0.

Hence at least one of theta dot r(A), theta dot r(B) exceeds theta dot s.
There is no nonnegative weighted-social certificate of the known form
theta dot r(S)<=theta dot s for all nonempty S. In particular the new
class is not a restatement of that static chamber. Reciprocal USC is
also not the hypothesis used: at the base table, shifting pure A to
infinity creates the nonzero nonnegative graph payoff r^0(A) above zero,
which directly violates reciprocal USC. Better-reply security is weaker.

The class is not merely an open neighborhood of a strict pure sink.
Here is a table inside it with no pure timing equilibrium. Put e=1/200,
retain the base rewards on all singletons and on A,B, and define:

- On each cross pair (one member from A and one from B), every member
  receives -e and every nonmember receives 0.
- Each triple contains a unique full target pair P in {A,B}. Its two
  members receive -e, its remaining member receives +e, and the missing
  player receives 0.
- At the four-player coalition every player receives -e.

All-Never is improved by any singleton Quit. From a singleton, its partner
can join and obtain 5/2 rather than 0. From A or B, any outsider can join
and obtain +e rather than 0. From a cross pair, either member can leave
and obtain 0 rather than -e. From a triple, either member of its full
target pair can leave and obtain 0 at the resulting cross pair rather
than -e. From the grand coalition any player can leave and obtain the
nonmember value 0 rather than -e. These are literal changes at the first
finite quitting date, with Never available for the leaver. They rule out
every deterministic timing profile, not merely date-zero notation.
Nevertheless Section 6 supplies an exact independent-law terminal Nash.

No claim is made that stationary equilibria fail, or that this example
evades every existing structural sufficient condition. Such claims would
require additional source/classification work not needed for this test.

## 8. Narrow dependency and duplication audit

The following actual declarations and their immediate statements were
inspected; paths here are relative to the repository root.

- `quittingTerminalPayoff_update_compactStoppingLawProfile_finiteTime_tendsto`,
  `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`:
  fixed finite responses converge under mere weak-law convergence.
- `quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton`
  and
  `quittingCompactStoppingLawProfile_cap_le_finiteBound_add_opponentNeverProduct_mul_negPart`,
  `UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`:
  exact late-Quit limit and all-finite-response cap bound, with the Never
  boundary and negative-singleton correction explicit.
- `twoDisjointFirstStoppingPairMasses_sqrt_sum_le_one`,
  `sqrt_exactFiniteFirstStoppingCoalitionMass_add_sqrt_le_one_of_disjoint`,
  and `sqrt_exactFiniteFirstStoppingPairMass_add_sqrt_le_one`,
  `MathUE/Probability/IndependentFirstStoppingPair.lean`:
  (6.2) for arbitrary complete independent laws. Its defining summands are
  exactly P(T_0=T_1=t<T_2,T_3) and the reversed pair, so no stronger
  agency or zero-Never adapter is hidden in this use.
- `exists_actual_minimum_of_singleton_nonneg_social_nonpos`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllPlayerEscapeSocialSignAttainment.lean`:
  the older nonpositive-social attainment result, not the new pair class.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`,
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`:
  the unrestricted semantic endpoint, allowing unrelated profiles across
  errors. Exact law-space Nash supplies its antecedent directly.

The compact behavioral-law representation and pure-time mixture statement
were previously audited in
`notes/CODEX_CEDAR__STOPPING_TIME_COMPACT_GAME.md`; its universal BRS
falsifier and the one in
`notes/CODEX_RENY__FINITE_TIMING_NASH_BOUNDARY_SECURITY.md` are retained as
baseline counterexamples, not claimed as new results here. The Cedar
assertion that a repair would have to preserve escaping relative time
is not a necessary condition for a direct sufficient-class theorem.

The known social chamber was checked through
`notes/CODEX_SOCIAL__WEIGHTED_AGGREGATE_SURPLUS_CHAMBER.md`,
`notes/CODEX_WEIGHT_GLOBAL__NONNEGATIVE_WEIGHT_SOCIAL_CHAMBER.md`, and
`ideas/QUESTION_BACKLOG/POSITIVE_SOCIAL_SURPLUS_ESCAPE_CONSUMER.md`.
Their global-minimum singleton margins could also consume an independently
proved exclusion of all payoffs above s to obtain UE. I therefore do not
claim a new singleton-margin inequality. Here Reny's theorem instead
obtains exact terminal Nash, and the actual pair-law restriction supplies
a concrete open table class outside the weighted-social screen.

The older
`notes/KEPLER_CLOCKCONE__ADJACENT_PAIR_REWARD_PRODUCER_SEARCH.md` seeks a
reward-driven *negative* exploitability gap from pair/triangle/star masses;
its proposed tables are defeated by explicit Nash profiles. This note
uses an existing pair-mass constraint in the opposite direction: to verify
a global existence theorem. A narrow symbol search found no existing
game-facing use of the disjoint-pair declaration for this class consumer.
That is a bounded novelty statement, not an exhaustive priority claim.

I also read the existing export
`exports/OVERLAPPING_FIRST_QUITTER_SQUARE_ROOT_LAW_AND_FIN4_PAIR_CONSUMER.md`.
It already states the all-distinct-pair bound and its negative affine-mass
forcing consumer. Neither that pair law nor its unrestricted-law scope is
new here; the open reward class and positive existence application are the
changes being proposed.

## 9. Bounded verdict and next check

This test does identify a producer mechanism: a finite open reward-table
condition verifies the precise original better-reply-security hypothesis
on complete independent stopping laws and gives exact terminal Nash.
It uses information lost by the convex reward-moment hull, not a new
representation of a cutoff selection defect. It does not select good
equilibria for arbitrary positive-singleton tables: (5.1) states the exact
obstruction to this particular theorem, and known UE tables violate it.

The next requested check is limited: independently verify the normalized
graph-defect factorization (4.1), the iff in (5.1), and the pair-chamber
exclusion. There is no need to optimize the radius, enlarge the class, or
formalize anything before that check.
