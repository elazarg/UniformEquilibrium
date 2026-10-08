# The sufficient-state and global-invariant hypothesis

Status: research hypothesis and program design, not a mathematical result.
Recorded 2026-08-30.

## Question

The recent Fin4 program repeatedly produces strong local objects but fails to
compose them into terminal approximate Nash profiles, a positive admissible
return, or a renewable well-founded descent.

Treat the following as a weakly falsifiable working hypothesis:

> The recurring completion failures are caused primarily by an inadequate
> compositional state or by the absence of a global invariant on that state,
> rather than by a positive-gap four-player counterexample.

This has two distinct forms.

1. **Insufficient-state form.** The data retained at a node do not determine
   which legal continuations, returns, or regenerated descendants are
   available.
2. **Missing-global-theorem form.** The retained state is sufficient, but no
   local move is required to decrease. Progress exists only at the level of a
   whole orbit, occupation measure, viable set, or recurrent component.

The second form is not evidence that a field was forgotten. It predicts that
further local case refinement will continue to stall even with complete local
data.

## Evidence

The following observations support the hypothesis.

- Many independently derived local identities are exact, but their useful
  signs or charges do not survive composition automatically.
- Several apparent descents cease to be progress after rebasing: a real debt
  can decrease while another coordinate or another representation recreates
  the same obligation.
- Compact recurrence of labels, payoffs, or semantic pairs has repeatedly
  failed to imply recurrence of an executable charged chronology.
- Strengthening a packet often moves the obstruction to the seam between two
  operations rather than eliminating it.
- Exact regressions with zero global debt realize much of the troublesome
  local geometry. This shows that local geometry alone cannot characterize a
  counterexample.
- No positive-gap reward table, exact certificate, or stable numerical
  candidate has emerged. Since a fixed positive exploitability gap is robust
  under sufficiently small reward perturbations, a counterexample should not
  normally be an isolated measure-zero table in reward space.

These observations are not proof of the hypothesis. The exact counterexample
semidecision is now complete as an unbounded search: any positive-gap Fin4
table implies an eventual finite rational lower certificate. A finite run
without such a certificate still carries no decisive weight without a
useful bound on its coverage or discovery time. This distinction is literal
in `exists_finFourCounterexampleStep_iff_exists_real_infimum_pos`, in
`Research/Quitting/FinFourCounterexampleSemidecision.lean`.

### Evidence update: a restrictive strategy class versus a missing attachment

The September 5 source audit separates two different causes of failure.

First, exact Nash selection in finite timing games is itself too restrictive.
For one normalized four-player table, every such Nash law at every positive
deadline has unrestricted regret greater than 1/4, while different actual
finite-clock profiles in that same game have regret 1/L and one fixed uniform
payoff. The selection-independent lower bound is
`quarter_lt_finiteDeadlineTimingNash_exploitability` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashUniqueness.lean`;
the comparison and uniform-payoff theorems are
`comparisonProfile_exploitability` and
`comparisonTarget_isUniformEquilibriumPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashBarrier.lean`.
Thus more faithful compactification of this exact-Nash family alone cannot
make it an all-accuracy producer. This is a proved class obstruction, not
evidence of a positive-gap game. A proof by contradiction may still use that
family, but it must exploit the global no-UE hypothesis or construct profiles
outside the family.

Second, the independently reviewed final-window result in
`CODEX_RENY__FINITE_TIMING_NASH_BOUNDARY_SECURITY.md` does obtain literal
entry reach, a bounded terminal window, a positive atom, and a paid response
under no UE. Its surviving missing attachment is not an unspecified extra
state coordinate: replacing that window need not preserve the continuation
payoff used by its exact prefix, or regenerate a source to which the same
argument applies. This result is ordinary mathematics, not a new checked
declaration or a terminal consumer.

Arbitrary rational finite-clock profiles retain a different status. Their
total-variation approximation includes unrestricted response caps and keeps
Never distinct from late finite stopping. The portfolio analysis in
`CODEX_SKEPTIC__FIN4_BLINDSPOT_RESTART.md` proves uniform approximation of the
global exploitability value over the compact reward cube. Its compactness
proof gives no convergence rate for an arbitrary raw enumeration. This must
not be confused with absence of a quantitative finite approximation theorem
in the project: `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket`
in `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean` already gives
an objective bracket of width at most 24/level for every normalized Fin4
table. `quantileClockSupport_fin4` specifies the clock bound 8·level+1;
`hasEscapeAwareQuantileClockCompression_of_normalized` in
`Research/Quitting/EscapeAwareQuantileClockTransport.lean` supplies the
actual-profile compression with unrestricted cap control. These declarations
were inspected under their imports; no new build is claimed here.

The quantitative hierarchy approximates the true infimum, whether it is zero
or positive. It does not prove that the infimum vanishes, nor give a practical
runtime bound for exhaustive rational profile or lower-certificate search.
The verified finite portfolio coverage increment is evidence that search can
leave the pure-policy class, not evidence of full-cube coverage at every
accuracy. Thus the missing theorem is not merely a rate of finite-clock
approximation.

Allowing any fixed positive finite-menu Nash error also repairs the exact-Nash
class obstruction at the level of its zero set: the infimum of unrestricted
regret within that enlarged finite-clock class is zero exactly when UE exists.
The proof starts from unrestricted approximants in the existence direction,
so it is not an algorithm that improves an arbitrary finite-menu source.
The independently reviewed Sections 1–12 of
`CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH.md` additionally construct
one uniform positive entry-reach floor for a fixed final window, for every
sufficiently accurate finite-menu Nash source under no UE. The qualification
audit in `CODEX_SKEPTIC__APPROXIMATE_FINAL_WINDOW_EXPORT_QUALIFICATION.md`
records the still missing minimum-source attachment or full-regret consumer.
This separates a repaired source-class defect from the unresolved strategic
construction; neither should be used as a substitute for the other.

The ordinary-mathematics converse in
`CODEX_SKEPTIC__ROBUST_FINAL_WINDOW_EQUIVALENCE.md` makes this diagnostic
precise. If some own singleton reward is positive, the robust final-window
property is equivalent to no UE. In the converse, small unrestricted regret
forces small joint Never mass; finite-clock approximation then permits a
larger deadline with small late reach. The unrestricted-regret hypothesis
must precede that menu enlargement. Enlarging the menu of a merely
finite-menu Nash profile is not valid. This converse has been inspected here;
it has no new Lean or export claim.

Consequently early absorption within approximate finite timing games is a
clean alternative producer target, not a proof that the existing reach
restriction is contradictory. The forward-packet question now includes that
finite-game formulation without requiring an unrestricted-regret bound as
input. A successful construction there would be new; proving the equivalence
by starting from UE is not such a construction.

The operational test is consequently sharper: a proposed improvement must
either leave a demonstrably incomplete strategy class, make a specified
composition valid, or exclude an actual positive global minimum. Improving
a necessary restriction inside the same incomplete class is not, by itself,
evidence of approaching UE.

### Evidence update: normalized collapse versus chronological selection

Two later broad attempts provide weak additional evidence, independently of
the mathematical statements that survived inside them.

The first succeeds in collapsing the normalized ballistic recurrence much
further than the original route.  It gives exact contiguous-block balances,
a common asymptotic convex-hull vector for current and tail directions, and an
interior zero of the interpolated matrix.  Nevertheless, even this stronger
same-source provenance does not recover an absolute hazard scale, a cap,
terminal law, or executable Nash--Bellman chronology.

The second tests several algebraic, finite-cycle, finite-timing, and
counterexample shortcuts and again ends at a selection problem: either solve
the game separately or select one exact bounded Nash--Bellman spine carrying
two fixed persistent labels.  Once supplied, that object is already consumed
by checked chronological machinery; the unresolved work is producing it from
the game.

Taken together, these attempts weakly favor H2 or H4 over the view that one
more local inequality will finish the current atlas.  They also support the
more specific diagnosis that normalized recurrence is easier than an
absolute, source-faithful chronological lift.  This is evidence from the
shape of repeated failures, not evidence for the truth of uniform
equilibrium.  The attempts are correlated: they use the same repository,
frontier descriptions, and proof vocabulary.  They produced neither an exact
information-collision example nor a positive-gap table, so they do not
materially distinguish H1 from H2 and do not seriously weaken H3.

### Evidence update: the two-chamber seam audit

The current full-debt and reset-rigid calculations make the recurring failure
more specific.

1. In the full-debt chamber, positive debt now produces a complete legal
   stopping-law fork with a uniformly reached first disagreement and a fixed
   payoff gain.  Thus the earlier failures were not caused by inability to
   locate an actual paid event.
2. Changing that stopping law leaves the mover's cap fixed but can raise the
   other three unrestricted caps at first order.  Reusing roots selected at
   the old cap is mathematically false.  Recomputing a maximal exact root at
   the new cap is sound, but an open positive-minimum cap tube permits that
   root to be uniquely all Continue.  The two individually legal operations
   -- payoff-improving replacement and exact-root selection -- do not commute.
3. In the reset-rigid chamber, disintegrating the zero-debt owner's clock has
   an exact Jensen account.  Vanishing Jensen loss permits a minimum-carrying
   selection.  Positive Jensen loss produces a real response switch with
   owner, pair-deleted, and full counterfactual survival floors.  It need not
   yield a finite-rank cemetery factor: an exact all-proper four-player
   example has a positive moving-date switch at every rank while the desired
   Never product is zero at every rank and becomes positive only in the weak
   limit.
4. First-order reset-cube cap curvature can be de-scaled to a fixed-gain full
   endpoint.  This removes the possibility that the obstruction is merely an
   infinitesimal normalization artifact.  The remaining failure is
   attachment: the generic paid-cap port forgets the cube/source ancestry,
   and its inert output is not a replayable block.

These are theorem-level or exact-regression facts, not merely a pattern in
failed proof attempts.  They shift weight away from the weakest version of H1
(`one obvious field was omitted`).  Recursive unilateral replacement already
has a sharp sufficient order-three counterfactual state in Fin4, and the
forward controller--tester ledger is finite dimensional and complete for its
program language.  What remains is either:

- H2: a global theorem orienting the noncommuting operations or consuming the
  resulting recurrent/inert component;
- a stronger H1/H4 phenomenon: exact chronological suffixing requires a
  noncompact response tower or a program-dependent modulus, so no small
  compact state supports all operations simultaneously; or
- H3: a genuine positive-gap table exploiting precisely this cap-switching
  and moving-time discontinuity.

The evidence does not decide among these.  It does justify a stricter test for
new work: an added field counts as explanatory only if it makes one previously
false composition theorem true; a global invariant counts only if it consumes
a whole inert component; and a negative interpretation counts only with a
concrete table and an independent positive all-behavior gap certificate.

### Evidence update: gauge symmetry and re-exactification

Two later reductions eliminate two misleading explanations without closing
the residual.

First, absolute response-switch time is not strategic state.  Common exact
all-Continue padding preserves the complete terminal law and, under the hard
singleton-cap inequalities, preserves the semantic pair.  It also preserves
the Jensen rectangle, its paid row, and every counterfactual survival floor,
while shifting all marks arbitrarily far and spending zero exact-root hazard.
An exact four-player vanishing-hazard regression shows that merely banning
literal zero-hazard padding does not repair this: a growing prefix can have
positive hazard at every rank and asymptotically zero total effect.  Therefore
the frequent bounded-time/escaping-time splits were partly coordinate
artifacts.  A valid state must retain relative mark alignment or quotient this
time-translation gauge.

Second, failure of lower hemicontinuity of the exact-root correspondence is
not itself the terminal obstruction.  If a positive-absorption exact root is
born only at an off-minimum limiting cap, prefixing that fixed root to the
actual prelimit profiles has vanishing root defect and makes a strict limiting
debt drop.  Choosing one fresh exact root at each changed actual cap restores
exact ancestry.  Global positive minimum gives a uniform survival floor, so
the signed atom and paid passport retain a fixed fraction.  What remains is
only that repeated drops are real-valued and may be Zeno; it is not an
exactification failure.

The surviving local configuration is consequently sharper:

- the response endpoint is strictly off the global minimum;
- all Continue is the unique exact root at both the response limit and the
  reset selector;
- paid response and signed-law data remain source attached; and
- any nontrivial restart must either cross a macroscopic semantic seam or
  enter an infinite sequence of decreasing off-minimum levels.

This further weakens the hypothesis that the project is repeatedly forgetting
one elementary scalar datum.  The recurring obstruction is now a precise
failure of **extension-compatible relative alignment**: compactness can align
semantic endpoints, and stopping-law analysis can align paid events, but the
same selection need not align both with an exact positive-charge block.

This observation is still only weak evidence for H2/H4.  A future global
invariant may orient the Zeno levels, while a counterexample could exploit the
same gauge and cap discontinuities.  The distinguishing tests are now:

1. quotient every removable exact or asymptotically null prefix and seek an
   exact collision of the remaining translation-invariant state;
2. test whether the retained gain/debt and atom/debt ratios force accumulated
   charge along infinite re-exactified descent; and
3. search for an actual positive-gap table whose reduced, gauge-fixed source
   still realizes the double-all-Continue endpoint indefinitely.

### Evidence update: social separation reaches a correlated-law barrier

The aggregate singleton margin supplies a static family of separating
functionals which had not been used at full strength.  At an ordinary global
minimum, for every nonnegative weight vector \(\theta\),

\[
 \left(\sum_i\theta_i-\max_i\theta_i\right)D_*
 \le \theta\cdot(U-s),
 \qquad s_i=r_i(\{i\}).
\]

Thus any weight supported on at least two players closes the game whenever
every terminal outcome has weighted reward at most \(\theta\cdot s\).  This
strictly extends the equal-weight and subset-indicator screens, and it is a
finite linear test on the reward table.

The dual failure mode is equally informative.  For each chosen support
\(J\), failure of every weight positive on \(J\) produces a correlated
terminal law, supported on at most \(|J|\) outcomes, whose reward moment
weakly Pareto dominates the synthetic singleton vector on \(J\) and is
strict in at least one coordinate.  In Fin4, failure on a player pair already
has a two-outcome certificate.

This does not supply an ordinary behavioral source.  Exact finite examples
show that a sparse Pareto law can violate product-support constraints and can
fail Nash inequalities even when its terminal law is behaviorally realizable.
The result therefore exposes the same seam in a different language: convex
reward geometry naturally produces a public-correlation object, whereas the
game requires an independent-product chronology together with unrestricted
cap control.

There is a second, complementary witness which must not be conflated with the
sparse one.  At the actual positive minimum,

\[
 D_*-d_i\le U_i-s_i
\]

for every coordinate.  Hence the minimum prescribed vector itself weakly
Pareto dominates \(s\), strictly in at least one coordinate, and a joint
carrier lift gives a source-attached limiting terminal law with this moment.
That law may be diffuse.  Conic Caratheodory makes the witness sparse, but the
sparsified law need not remain in the joint carrier or retain the source
chronology.  Thus one can obtain **provenance** or **finite correlated
support** immediately, but not their co-realization.  This is another exact
instance of the recurring noncommutation phenomenon.

This is weak evidence against the idea that the missing ingredient is another
scalar welfare inequality.  The concrete next tests are sharper:

1. determine whether the family of pair-supported Pareto laws forced by
   failure of all weighted screens is compatible with the hard-residual
   singleton and punishment inequalities;
2. identify the least extra toggle or cap condition which turns one such law
   into an executable product block; and
3. construct a single table satisfying all pairwise dual certificates while
   defeating every such product/cap adapter.

Success in the third test would be a direct information-collision witness for
the convex reward-moment state.  Failure in the first or second could yield a
new global consumer rather than another chronological refinement.

The dual arm must not be counted as an additional contraction of the
positive-minimum residual.  At any positive ordinary minimum the checked
singleton margin already implies

\[
U_i-s_i\ge D_*-d_i\ge0
\]

and the vector \(U-s\) is nonzero.  Hence the full-support correlated-law
certificate, and its conic sparsification, are automatic consequences of the
same minimum data.  The real theorem-level progress is the closing costate
arm: it proves uniform-equilibrium existence for a new finite class of reward
tables.  On the surviving branch, the sparse law is a useful normal form and
search certificate, but not a new dynamic restriction.  Any claim of further
progress there must use its source support, quantitative atom floors, or
additional toggle/cap structure to produce an operation unavailable from
\(U\ge s\) alone.

### Globality cannot be replaced by local or separate-block optimality

There is an exact distinction between three optimization statements. Let K
be the full terminal semantic carrier, let T_q be actual product-root
prefixing, and put f(q,z)=D(T_q z). A genuine minimum decomposition must
satisfy

    f(q,z) ≤ f(q′,z′) for every product root q′ and every z′∈K.

Neither local optimality in the complete stopping-law space nor the two
separate global inequalities

    f(q,z) ≤ f(q′,z) for every q′,
    f(q,z) ≤ f(q,z′) for every z′∈K

implies this joint inequality. This is not merely an abstract optimization
warning. The exact quitting-game tests distinguish all three notions:

- The coupled finite-law example in
  `CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md` minimizes globally in
  each separate root/tail block at debt 1/200. A specified legal 32-date
  product law has strictly smaller unrestricted debt. Every complete cap,
  including Never and post-calendar stopping, is computed. Thus alternating
  even globally solved blocks can stop at a nonminimum of the full game.
- The asymmetric table in Section 43 of
  `CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md` has a strict local minimum
  against arbitrary independent stopping-law perturbations, not only a
  finite or stationary menu. It also has actual below-singleton blockers,
  strict escapes from every pure coalition, and an R₀ singleton matrix of
  degree one. Nevertheless an existing cyclic equilibrium producer applies,
  and an explicit distant actual product law lowers the debt. These tests
  do not establish insufficiency of every stronger source theorem; they
  establish insufficiency of these precisely listed local screens.
- The all-sure-family calculation in
  `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md` optimizes over every
  date-zero sure-owner profile and every actual conditional tail. Its
  positive class minimum is not the global minimum over all profiles.
  Releasing its last sure owner lowers debt when the prescribed tail is
  Never, but raises debt when that owner is prescribed a conditional best
  reply. The difference is an exact observer-cap effect. Optimizing the
  released player's own payoff is therefore not an objective-aligned
  choice of the new joint tail.

These are ordinary mathematical tests, with no new Lean claim. The tables
are solved games, not positive-gap examples. Their value is diagnostic:
using every local cap does not substitute for using the true global
minimum, and individually optimizing both legal operations does not make
their composition globally optimizing.

This favors testing a missing global comparison before adding another
passport field. It does not show that information never matters, that UE
is true, or that every global mechanism must be chronological. The evidence
is correlated: the examples were investigated inside the same program.
The decisive test remains a repair or exclusion derived from joint
whole-profile minimality, rather than another solved-table local trap.

### Payoff feasibility does not solve cap minimization

There is an exact source-level filter for payoff-only approaches. For any
Fin4 table put s_i=r_i({i}) and Γ_ij=r_i({j})−s_i. The tracked theorem
`exists_finFour_simplex_positive_projectiveResidual_of_no_uniformPayoff`
in `UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`
produces, from bare no UE, a nonnegative simplex vector λ with

    (Γλ)_i>0 for every i.

The matrix orientation is fixed by `quittingProjectiveLCPMatrix` in
`UniformEquilibrium/Quitting/Projective/SingletonLCP.lean`: receivers are
rows, singleton owners are columns. No reward-sign, punishment, or selected
strategy premise is needed by the source theorem.

This already implies actual prescribed-payoff feasibility above all own
singletons. Give player j stationary Quit hazard hλ_j, with 0<h<1.
One-row absorption is h+O(h²), singleton-j absorption is hλ_j+O(h²),
and collision absorption is O(h²). Repeating the row therefore gives
terminal payoff converging, as h tends to zero, to

    U_i→∑[j] λ_j r_i({j})=s_i+(Γλ)_i>s_i.

For sufficiently small fixed h, all four actual prescribed payoffs exceed
their singleton rewards. Zero coordinates of λ are allowed; at least one
positive hazard ensures eventual absorption. This is an ordinary elementary
consequence of the checked simplex source, not a new checked declaration.
Nothing in the argument controls unrestricted caps or regret.

Consequently a universal actual-payoff exclusion cannot apply to the
surviving no-UE source. For example, the sharp independent-clock inequality
t_a t_b≤e²/4 for two different triple outcomes is useful joint-law geometry,
but a raw class with every singleton social value at most −390 and
∑[i]s_i≥1 is already excluded without that inequality: every Γ column sum
is at most −391, so Γλ cannot be positive in all rows. The full product-law
proof does not provide new UE coverage for that class. The exact inequality,
its ordered-copy proof, and the overlap check are retained in
`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md` and its independent feedback.

This strengthens the diagnosis beyond the claim that linear social tests
are weak. Even nonlinear payoff-only infeasibility must first survive the
singleton source above. A successful new use of independent-law constraints
must constrain the same family's caps, counterfactual responses, or genuine
global-minimum membership, rather than merely exclude all prescribed
payoffs above s.

Concrete tests before investing in another raw class are therefore:

1. Check whether Γ admits a simplex vector with all-positive image. If not,
   the existing singleton source already excludes that class.
2. If it does, exhibit which complete response or global-minimum condition
   defeats the actual high-payoff stationary family; payoff feasibility
   alone is insufficient.
3. For a law inequality, identify the legal common-source intervention and
   compute every changed cap. A probability coupling used to prove an
   inequality is not itself shared randomization available in the game.

These tests do not establish that chronology is the only viable route, or
that a counterexample exists. They separate a genuinely cap-aware global
mechanism from a well-proved theorem on an already excluded reward class.

### Calendar compactness is not a Cartesian existence space

A complete stopping law is a strategy, but a compact topology on complete
laws need not preserve the payoff graph needed by an existence theorem.
On the one-point compactification of finite dates by Never, delay every
finite date of an independent finite-law profile by k. The prescribed
terminal law and payoff are unchanged, while all four laws converge weakly
to all Never. Thus every such payoff occurs above all Never in the closure
of the payoff graph. The shifted caps need not be unchanged.

Against literal all-Never opponents a fixed own law pays at most
max(s_i,0). Consequently a graph-limit payoff u with
u_i>max(s_i,0) for every owner cannot be secured there by any fixed
unilateral response. If some s_j>0, all Never is not Nash, so this is
an actual failure of better-reply security, rather than an equilibrium
point at which the security condition is irrelevant. Even the solved
table r_i(S)=1 when i belongs to S and zero otherwise has this failure:
delayed sure grand coalitions retain payoff (1,1,1,1).

The tracked theorem
`positive_minimum_fourPlayer_allOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`
gives u_i>s_i at every positive summed-debt minimum. With nonnegative
own singletons, such a minimum therefore supplies a failure of security
in this compact strategy space, not the premise of a security-based
existence theorem. This is ordinary mathematics about the topology;
no new Lean declaration or positive-gap table is claimed.

Marking every positive limiting atom as an isolated calendar point repairs
payoff and full-cap continuity at the resulting minimum source. It does
not repair continuity at every other profile on that calendar: other laws
can insert positive mass at an old nonisolated cut. Re-marking each such
law changes the common calendar as a function of all four strategies.
It is not a fixed Cartesian product on which an owner independently
changes one strategy. The exact local-continuity argument and its scope
are in `CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`.

This distinguishes two hypotheses that should not be confused. Full
response information at the source can be sufficient for its local cap
calculation, yet the same source compactification can be insufficient
for a global game-existence theorem. A proposed topological consumer
must verify its entire payoff-graph closure and independent unilateral
agency, not only continuity at a selected minimizing profile.

### Atomless approximation can discard an indispensable equilibrium mechanism

For the participant-indicator table, r_i(S)=1 if i∈S and zero otherwise,
the pure grand coalition is an exact equilibrium. Nevertheless every
independent profile whose finite-clock parts are atomless on a calendar
bounded below has

    ∑[i] U_i=1−∏[i] p_i(Never)≤1,
    B_i=1 for every i,
    D=3+∏[i] p_i(Never)≥3.

Independent finite ties have probability zero, so finite absorption pays
only one player. A pure test at the earliest calendar point gives payoff
one; if there is only a lower infimum, tests approaching it give the same
cap as a supremum. No density bound, common support or symmetry is used.
On the original integer calendar, instead,

    D=4−E|S_first|,
    D≤ε ⇒ P(S_first=I)≥1−ε,

with S_first empty on Never. Approaching equilibrium in this table thus
requires retaining simultaneous grand absorption, not replacing it by an
atomless ordering of the private clocks. The complete calculation and the
restricted-density and entropy comparisons are in DR1–DR6 of
`CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`. They are ordinary
mathematics, not new checked declarations.

This separates two tests of a proposed producer. A bad supplied restricted
Nash equilibrium does not exclude choosing a better one. The whole-class
bound above does exclude every atomless selector on this table. It does
not exclude a method that retains collision atoms, nor a contradiction
argument restricted to genuine positive global minima: this table has
minimum zero.

The methodological inference is limited but useful. A smooth clock space
may remove the very coalitions needed for equilibrium while making the
remaining optimization more regular. Before pursuing density or entropy
regularization as an existence route, test unrestricted regret across
the whole approximation class on collision-dependent solved tables.
Continuity of the restricted problem cannot replace that completeness
check. This is evidence of a representation failure, not evidence that
uniform equilibrium is false.

### Necessary conditions can overlap without consuming their common residual

There is an exact test for whether a singleton-reward pressure inequality
adds information to one supported-cap configuration. Suppose a marked
independent-law source has one owner m stopping surely by t₀. The other
three selected cap tests are t₀; m's selected test is strictly later.
Define

    μ_i=P(first coalition={i}),
    θ_i=P(all opponents of i stop strictly after its selected finite test),

and put θ_i=0 for a Never test. Then θ_j=0 for j≠m because opponent m
has stopped or ties at t₀. For m, every opponent surviving its later
test also survives its prescribed stop, so θ_m≤μ_m. Consequently

    ∑[i] w_i θ_i≤∑[i] w_i μ_i       for every w_i≥0.

Any necessary singleton-pressure bound of this form is automatic on
this configuration, even when the displayed source is assumed to be a
positive global minimum. Combining it with the supported-cap restriction
therefore does not exclude the remaining case. The configuration is the
surviving arm of LC1–LC5 in
`CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`; the focused independent
check of that restriction is in the corresponding NOETHER feedback. This is not a proof
that a positive-minimum table realizing the configuration exists.

The useful test is stronger than asking whether two claims are valid.
Before counting their combination as progress, evaluate the proposed
new inequality on the exact surviving branch. If it holds automatically,
retuning nonnegative weights cannot supply a consumer. One must change
the comparison or construct a legal operation whose full-cap account is
not already forced by that branch. This failure is not explained by an
omitted state field: the event laws already make the nonclosure explicit.

### Finite reward contacts and moving minimizing sources

A global reward comparison has a different logical burden from a strategic
splice. Let Δ(r) be the infimum of SUM debt over all independent behavioral
profiles, and let Ω>0 be its maximum over the bounded reward cube. Suppose a
source configuration forces Δ(r)=ℓ(r), where ℓ belongs to a finite family of
affine reward expressions. If one legal target table raises every expression
currently equal to Ω strictly above Ω, a sufficiently small interpolation
separates every expression from the new value of Δ. Finite separation treats
the noncontacts; uniform reward Lipschitz continuity bounds the new value
below, while worst-table maximality bounds it above by Ω.

This comparison does not transport an old minimizing profile, response
selector, or law through the changed game. Every new minimizer is constructed
afresh, and the forbidden equality applies to all of them. Thus changing
owners or supports is not a loophole when all their finitely many contact
values are separated simultaneously. The exact source identities and finite
comparison are developed in
[the global-obstruction notebook](CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md)
and [the compact-clock notebook](CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md).

This is not a general cure for cap leakage. A source with several maximizing
responses may have no fixed selected-response polynomial on a signed open
box. A unique nonisolated maximum can move under a perturbation without any
uniform complement gap. In those cases an identity with one of the finite
reward expressions has not been established. The finite number of contact
labels therefore does not make the entire behavioral source space finite.

The concrete test is whether the remaining active-cap configurations also
force a finite contact family with a compatible reward direction. Failure
must identify the moving complete-response term or conflicting contact
directions, not merely exhibit another paid deviation. This distinguishes a
genuinely new global mechanism from another local account with an unpaid
observer cap.

### Scalarizing one fixed attainable debt set is different from moving its sources

Let A be the compact set of complete debt vectors of one fixed game, and
minimize a positive weighted sum over A. As a function of the weights this
value is concave: it is the infimum of linear functions on one unchanged
attainable set. At weights admitting all two-sided coordinate derivatives,
the supporting inequalities force every minimizing vector to have the same
coordinates. Positive recipient reward scaling implements those weights in
the original game semantics, including the complete behavioral caps.

This argument does not convexify independent strategies and does not follow
one selected old profile through a changed game. It can make the entire new
minimum family debt-rigid while leaving its laws, payoffs, caps and response
times different. The complete source application and independent focused
check are recorded in
[the global-obstruction notebook](CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md)
and its BROUWER feedback.

The stronger actual-source conclusion, including the complete scalarization
proof, is stated in
[the first-collision bridge reduction](../exports/RANDOM_EARLIEST_COLLISION_PAYOFF_KERNEL_BRIDGE.md).
It selects one counterexample table before its minimum families. At that
table every produced minimum has a random first collision and two genuinely
different root/later response payoff kernels with equal maximal expectation.
This is a source restriction, not a temporal or paid consumer. The tied
player can have zero debt, so the distinction of kernels cannot substitute
for a positive best-response gain.

The useful completion test is whether a legal operation is proved to remain
inside that minimum family. If it is, debt rigidity controls every coordinate
at once, rather than merely their sum. If its full caps are uncontrolled or
its target is off-minimum, rigidity gives no missing return edge. Generic
weights alone therefore do not repair chronological splicing or solve UE;
the actual supported-earliest-cap exclusion separately proves the required
full-cap stability and local minimum preservation.

### Debt rigidity forces a macroscopic excursion when a positive debtor is reset

The following elementary consequence is ordinary mathematics, not a new
Lean claim or an export. Let K be a compact terminal payoff/cap carrier,
D its total debt, δ=min_K D, and assume every minimizing pair has one
common debt vector a. Fix a player i with a_i>0. The compact set

    Z_i={w∈K : d_i(w)≤a_i/2}

is disjoint from the minimum set. If it is nonempty, continuity gives
η_i=min_{Z_i} D−δ>0. Consequently every pair in Z_i has
D≥δ+η_i. Nonemptiness holds for an actual quitting-game carrier: keep
opponents fixed, take an arbitrarily accurate complete best response of i,
and make its own debt smaller than a_i/2. No exact cap attainment is needed.

Now let actual source pairs approach the minimum set, and let player i
replace its complete strategy by increasingly accurate best responses.
The source debts converge to a by compactness and minimum-family rigidity.
The replacement has d_i→0, since the mover's opponents and full cap are
unchanged. Its total debt is eventually at least δ+η_i. In the exact
one-player leakage identity, this implies

    liminf ∑[j≠i](d_j(replacement)−d_j(source)) ≥ a_i+η_i.

Thus cross-coordinate leakage strictly overcompensates the eliminated debt;
it cannot merely rotate the same debt vector inside the minimum family.
This applies even when some other coordinates of a are zero. It is a
statement about the specially selected debt-rigid table, not every original
reward table, and gives no effective lower bound on η_i.

Two different tasks must therefore not be conflated. A positive debtor's
complete reply requires consuming a uniformly off-minimum excursion. A
zero-debt player's tied response need not leave the minimum and supplies
no payment. Returning an off-minimum excursion by exact prefixing would
spend positive absorption, but the existence of one such return, let alone
extension-compatible renewal, is not proved by the compact gap above.
This sharpens the completion test without resolving the seam obstruction.

### Several cap dates need not be several strategic branches

A cap is a supremum over stopping dates, but two distinct maximizing dates
need not describe different interventions. If one opponent stops surely by a
finite cut, every pure deadline strictly after that cut has exactly the same
terminal coalition law as Never: the tested player continues until the game
has already ended. An entire plateau of maximizing deadlines can therefore
represent one outcome kernel.

This distinction matters when a minimum-preserving path reaches its first
cap tie. An interior tie can retain enough of the original product law for
the competing interventions to change absorbing outcomes. At a sure-owner
endpoint the tie can instead be only the dead-tail plateau described above.
The finite-amplitude head-concentration construction records these two
possibilities separately in
[the nonbijective-source notebook](CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md).
Its existential reselection alone is not a terminal consumer or a strict
reduction of the surviving strategic class.

The concrete progress test is to compare the complete deviation kernels of
the tied responses, not merely their dates or equal payoff values. If they
are outcome-equivalent, a new consumer must use additional supplied data;
counting the tie as a new active face does not provide a renewable rank.
This failure can occur even with all original opponent laws retained. It is
therefore not automatically repaired by enlarging the stored state.

## Competing explanations

### H1: insufficient compositional state

There exist two actual sources that agree on the packet currently used by a
producer or consumer, but have different sets of strategically valid
successors or different prospects for terminal completion. Any theorem using
only that packet must then fail.

### H2: sufficient state, missing global invariant

The state distinguishes all strategically relevant successors, but progress
is not visible one edge at a time. A proof needs a global object such as a
viability kernel, invariant occupation measure, cycle functional, recurrent
charge account, or a set-valued Lyapunov function.

### H3: positive-gap counterexample

Some finite reward table admits a closed obstruction that can be realized at
every scale while keeping exploitability uniformly positive against all
behavioral profiles. The recurring inert component is then a shadow of a real
counterexample rather than a proof artifact.

### H4: wrong proof language

Neither the present packet nor a modest enlargement is natural. The
conjecture may require a different global representation—for example a direct
controller-versus-deviator formulation or a dual occupation-flow
certificate—rather than a repaired version of the current atlas.

H4 overlaps H1 and H2, but is useful operationally: it warns against assuming
that the missing sufficient state is a small extension of the present one.

## What to seek globally

### 1. A sufficient information state

Seek a compact or finitely stratified state space \(X\) and a map from actual
behavioral sources into \(X\) with a congruence property:

> If two actual sources have the same state, then every allowed construction
> step available from one has a strategically equivalent step from the other,
> with the same terminal objective and deviation guarantees.

Exact equality may be too strong. An asymptotic version can use a metric and a
uniform continuity modulus for both prescribed payoffs and unrestricted
deviation values.

The state is useful only if it is:

- closed or sequentially compact under the limits used by the proof;
- preserved or updated by legal behavioral operations;
- rich enough to evaluate the complete unilateral-deviation class;
- small enough to support recurrence, selection, or optimization; and
- connected to literal profiles, rather than only carrier points.

This is the mathematical version of asking for a Markov-complete state.

### 2. A global progress theorem

On the state space, seek a controlled transition relation with one of the
following exhaustive conclusions:

- reach the terminal-approximate-Nash set;
- accumulate a positive admissible charge on a return to one fixed target;
- strictly decrease a genuinely renewable well-founded rank; or
- remain forever in a closed invariant set carrying a certified positive-gap
  barrier.

A scalar potential is only one possibility. Other candidates are:

- a lexicographic or set-valued Lyapunov function;
- a measure on active constraints or faces;
- an occupation measure whose cycle average has a forced sign;
- a viability kernel with a terminal or recurrent winning subset;
- a Conley-style decomposition into transient regions and invariant chain
  components; or
- a dual separating functional proving that a closed component is impossible
  under positive global minimum.

The desired theorem should consume an entire strongly connected component or
orbit, not merely orient one selected edge.

### 3. A controller-versus-tester duality

Formulate the construction as a controller choosing roots, continuations, and
resets against a tester choosing a horizon, player, and complete behavioral
deviation. Seek a theorem that replaces the tester's nonlocal strategy by a
recursive compact state or a dual flow constraint.

A successful duality would give a genuine dichotomy:

- a controller policy producing one fixed uniform payoff; or
- a barrier/occupation certificate proving a positive exploitability gap.

This would explain both positive and negative outcomes in one language.

### 4. A closed-component theorem

For every nonterminal recurrent class of the state transition system, prove
one of:

- it contains a positive admissible return;
- it contains a renewable rank exit;
- it violates a hard-residual inequality;
- it cannot be realized by actual behavioral sources; or
- it generates an exact positive-gap certificate.

This is stronger and more honest than continually replacing a residual by a
finer label.

## Concrete tests

### Test A: information-collision test

For each proposed packet \(P\), search for two actual finite-clock rational
sources \(s,t\) such that

\[
P(s)=P(t)
\]

but their sets of legal consumer outputs differ. A rigorous pair falsifies
sufficiency of \(P\). The output property should be concrete, such as
existence of a prescribed kind of return or source-preserving child.

An approximate version groups sources whose packet coordinates are within
\(\varepsilon\) and tests whether their successor sets remain uniformly
close. Persistent separation as \(\varepsilon\to0\) falsifies continuous
sufficiency.

### Test B: transition-congruence test

Choose each legal primitive operation used by the proof. Test whether the
state of every possible successor is determined, or uniformly bounded, by the
incoming state and chosen operation. A counterexample identifies a precise
noncompositional seam.

Passing this test for every primitive would be meaningful evidence for H2
over H1.

### Test C: ablation test

Begin with a candidate augmented state and systematically remove one
coordinate or certificate. Produce an exact counterexample whenever removal
breaks sound composition. This distinguishes necessary state from historical
accumulation of fields.

Conversely, if adding a proposed field does not close any previously failing
congruence test, do not enlarge the production interface with it.

### Test D: finite-model SCC realization

For bounded rational clocks and rewards, build the exact finite transition
graph induced by the proposed state and legal moves. For every nonterminal
SCC, ask whether its defining inequalities and source constraints are jointly
realizable.

- An infeasibility certificate removes that finite model of the SCC.
- A realization gives a concrete regression to test against stronger states.
- A realization with a certified positive all-behavior gap is a
  counterexample.

Finite truncation alone is not sound for the conjecture, so the model must
retain an explicit tail or boundary certificate.

### Test E: Lyapunov and occupation dual search

On an exact finite abstraction, search simultaneously for:

- a potential that strictly decreases outside terminal nodes; and
- an invariant occupation measure supported on a nonterminal SCC.

These are dual signals. Failure of a chosen potential class proves only that
the class is too weak. An invariant occupation measure becomes mathematically
important only after an actual-profile realization theorem.

### Test F: counterexample signal test

Run the exact positive-gap semidecision across normalized rational tables and
record certified regions searched, not only runtime. A lower certificate is
decisive. Nontermination is not evidence. Nevertheless, systematic absence of
lower events across expanding, nonredundant regions can guide which structural
configurations deserve exact infeasibility proofs.

### Test G: global-return stress test

Construct exact zero-minimum regressions that imitate every proposed global
return theorem except one hypothesis. This tests necessity. Then attempt to
derive that missing hypothesis from positive global minimum. A theorem that
cannot distinguish the regression from the hard residual is not yet using
the decisive global input.

## Predictions and possible falsification

### Predictions of H1

- Exact information-collision examples will exist for current packets.
- Adding a small number of principled state components will remove several
  apparently unrelated seam failures at once.
- A consumer stated on the enlarged state will compose without reselecting or
  rebasing its source.

H1 is weakened if extensive exact collision searches find none and every
primitive transition is congruent on the current state.

### Predictions of H2

- Local refinements will keep returning to a finite recurrent core.
- No scalar one-step debt quantity will orient all transitions.
- An occupation, viability, or cycle theorem will consume several residual
  branches simultaneously.

H2 is weakened by an exact example of two state-identical sources with
incompatible successor behavior, or by discovery of a simple renewable local
rank.

### Predictions of H3

- Exact search will eventually find a rational positive-gap table or a robust
  numerical region that survives increasingly strong all-behavior
  certification.
- The table will realize a closed source-attached obstruction indefinitely,
  rather than merely one local inert configuration.
- Its gap will persist under small reward perturbations.

H3 is falsified only by a proof of the conjecture. Repeated search failure is
not a falsification.

### Predictions of H4

- Attempts to make the current atlas Markov-complete will require unbounded or
  essentially path-valued memory.
- A different representation will make the complete deviation class
  recursive and yield a substantially simpler soundness theorem.

H4 is weakened if a compact finite-dimensional enlargement passes the
congruence tests and supports a global progress theorem.

## Progress rule for this hypothesis

Count an investigation as evidence-bearing only if it produces at least one
of:

1. an exact information-collision counterexample;
2. a proved transition-congruence theorem;
3. a principled state enlargement closing more than one seam;
4. a global SCC, viability, occupation, or Lyapunov consumer;
5. an exact infeasibility certificate for a recurrent component;
6. a certified positive-gap table; or
7. terminal approximate Nash profiles for the residual.

Another local trichotomy with no consumed output is neither confirmation nor
falsification of the hypothesis.

## Relative approximation when the reward table changes

This is an elementary logical limitation, not a quitting-game counterexample.
Suppose a selection at accuracy ε produces a table with positive debt gap
δ, reward bound M, and an error e≤εδ. If a consumer needs error small
compared with the margin γ=δ²/(8M), the available comparison is only

    e/γ ≤ 8εM/δ.

Sending ε to zero while also changing the table does not control M/δ.
For example, ε_k=δ_k=1/k, M_k=1 and e_k=1/k² meet the relative
estimate exactly, but e_k/γ_k=8 at every k. The same issue arises
without normalizing: a fixed positive limiting gap, growing reward bound
M_k=k, and error 1/k have a nonvanishing error-to-margin ratio.

Thus a fresh-table approximation theorem must either control this ratio,
give one fixed table before the accuracy, or feed a consumer that requires
only the relative estimate actually proved. Common normalization does not
repair the ratio: e and δ scale linearly, M scales linearly, and therefore
e divided by δ²/(8M) is unchanged. Closeness of debt vectors additionally
does not identify their underlying payoff/cap pairs or stopping laws.

## Initial priority

Run Tests A and B on the current surviving source state before proposing new
fields. In parallel, formulate Test E on a finite exact abstraction of the
known recurrent core. These tests distinguish “forgotten information” from
“missing global theorem” more directly than another producer refinement.
