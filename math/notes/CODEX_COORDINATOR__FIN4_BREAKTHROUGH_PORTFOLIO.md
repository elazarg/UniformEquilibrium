# Fin4: current results and the remaining proof obligations

Owner: CODEX_COORDINATOR.

Fin4 is OPEN. The target is uniform-equilibrium existence for every signed
four-player quitting table, with one payoff target fixed before accuracy
and all unilateral behavioral deviations allowed. The conference has
ordinary mathematical reductions and existence classes; it has not proved
an arbitrary-table producer or exhibited an unrestricted counterexample.

The checked theorem boundary is in `docs/FRONTIER.md` and the named Lean
sources. An exported mathematical proof is not a new Lean theorem.

## Constructed equilibrium classes

The [contracting-block theorem](../exports/TWO_CONTRACTING_BLOCKS_UNIFORM_EQUILIBRIUM.md)
unifies four actual reward-table producers. It retains an explicit quantitative
box, extends the construction across a signed singleton chamber with arbitrary
finite passive rewards and computed participant thresholds, and supplies a
complementary class with arbitrary nonnegative pair premiums. Every strategy
and return value is produced from the stated reward conditions.

For the fixed reference singleton matrix and additive passive completion,
the fourth theorem allows the common premium of rows1 and3 and the premium
of row2 to be independently small: under its row0 participant caps, one
positive bound works for both. Rows1 and3 share a premium in this theorem.
The proof combines a positive cone, a constructed invariant graph and a
hybrid pair/triple contraction. The target is fixed before accuracy, and
the finite periodic approximations price all behavioral deviations.

The exact calibration family defeats the checked stationary, sure-owner
punishment, protected-player, ledger and universal child-debt criteria.
The two independent artifact reviews are
[here](../feedback/CODEX_PERIODIC_CLOSURE__DEADLOCK_CONTRACTION_BLOCK_UNIFORM_EQUILIBRIUM__BY_CODEX_ZERO_CAP_ADVERSARY.md)
and [here](../feedback/CODEX_PERIODIC_CLOSURE__DEADLOCK_CONTRACTION_BLOCK_UNIFORM_EQUILIBRIUM__BY_CODEX_PERIODIC_ADVERSARY.md).
The [unequal-premium theorem](../exports/UNEQUAL_PREMIUM_CONTRACTION_UNIFORM_EQUILIBRIUM.md)
adds two regions for core premiums `(a beta,beta,c beta)` on the reference
singleton/additive-passive background:

- `a>0`, `0<c<5/9`, `8a<15(1-c)`;
- `1<c<2`, `3c/2<=a<3`, including the neutral boundary `2a=3c`.

Each compact subset has one sufficiently small scale threshold. A strict
cone produces the first region. In the second, a concave physical boundary
and a monotone contraction produce every pair/triple continuation, including
unbounded pair prefixes. One continuous macro slack parameter produces the
return without separate switch cases. The six row0 proper participant entries
remain independent under their upper bounds. The proof and both exact
separating rays include the full behavioral consumer and selector comparisons.
The final independent reviews are
[here](../feedback/UNEQUAL_PREMIUM_CONTRACTION_UNIFORM_EQUILIBRIUM__BY_CODEX_ACTUAL_MINIMUM_AUDIT.md)
and [here](../feedback/UNEQUAL_PREMIUM_CONTRACTION_UNIFORM_EQUILIBRIUM__BY_CODEX_MACRO_ADVERSARY.md).

The [three-diffuse-flow theorem](../exports/THREE_DIFFUSE_FLOWS_UNEQUAL_PREMIUM_UNIFORM_EQUILIBRIUM.md)
produces uniform equilibria whenever

    0<=a<3, 0<c<=1, Delta=21c-6+8a(19c+1)>=0,

at sufficiently small positive beta, uniformly on each compact parameter
subset. In particular one threshold works throughout the closed rectangle
`0<=a<=2, 2/7<=c<=1`. No numerical scale threshold is asserted. Beyond the
fixed singleton matrix, only seven passive entries, nine core participant
entries and seven upper bounds in row0 are required. All other nonsingleton
rewards and the four own-singleton levels are arbitrary finite numbers; the
scale threshold is independent of these free coordinates.

The proof joins a pair return and two triple-return arcs to a constructed
analytic core graph. Three singleton flows, approximated by finite meshes,
close the return. The finite periodic consumer controls every behavioral
deviation and keeps the payoff target fixed before accuracy. The final
independent reviews are
[here](../feedback/THREE_DIFFUSE_FLOWS_UNEQUAL_PREMIUM_UNIFORM_EQUILIBRIUM__BY_CODEX_COLLAR_ADVERSARY.md)
and [here](../feedback/THREE_DIFFUSE_FLOWS_UNEQUAL_PREMIUM_UNIFORM_EQUILIBRIUM__BY_CODEX_LOCAL_COLLAR_REVIEW.md).

For the reference additive calibration, combining this result with the
strict-cone theorem covers EVERY `0<a<3, 0<c<=1` at sufficiently small scale.
Indeed Delta<0 implies c<2/7 and
`a<(6-21c)/(8(19c+1))<=3/4`; hence `8a<6<15(1-c)`, within the older cone.
This union does not transfer the new theorem's free-coordinate scope to
the older cone. The former stress test `(a,c)=(1/10,1)` is now covered.

The [crossed-premium theorem](../exports/CROSSED_PREMIUM_HYBRID_DIFFUSE_FLOW_UNIFORM_EQUILIBRIUM.md)
adds the following regions with the same seven-passive-entry, nine-core-entry
and row0-cap requirements as the three-flow theorem:

    U: 0<a<3, c>1, 2a<3c;
    L: a>3, 0<c<1;
    B: a=3, 0<c<1.

On U, a contracting obstacle operator constructs a continuous switch between
triple and pair roots. On L, an invariant cone for the reversed linear map
orders finitely many physical continuation sheets; normalized forward
equations continue them to positive beta and glue their exact boundaries.
On B, an analytic graph contains an exact solo-player axis. A single
two-dimensional intermediate-value argument consumes all three continuous
cores, with the same finite-flow behavioral estimate. It requires no smooth
axis map or choice of a continuous return-root curve. The final independent
artifact reviews are
[here](../feedback/CROSSED_PREMIUM_HYBRID_DIFFUSE_FLOW_UNIFORM_EQUILIBRIUM__BY_CODEX_COLLAR_ADVERSARY.md)
and [here](../feedback/CROSSED_PREMIUM_HYBRID_DIFFUSE_FLOW_UNIFORM_EQUILIBRIUM__BY_CODEX_LOCAL_COLLAR_REVIEW.md).

Together the accepted results now cover EVERY fixed positive premium ratio
on the original homogeneous/additive calibration:

    for every a,c>0 there is beta0(a,c)>0 such that
    0<beta<beta0 implies UE for premiums(a beta,beta,c beta).

The exhaustive case split is short. For a<3,c<=1, use the lower-strip union
proved above. For a<3,c>1, use U when 2a<3c; otherwise c<2 and the earlier
closed wedge applies. For a>=3,c<1, use L or B. For a>=3,c>=1, the earlier
pair theorem applies: its two quiet-player inequalities reduce to
`beta<=a beta/3` and `beta<=c beta`, and its remaining bounds hold at small
scale. This union is asserted for the original calibration, without
transferring the freer coordinate scope of one branch to another.

The crossed theorem's threshold is uniform on compact subsets of U, L and
B separately. A single threshold across their joins, or for all three
independently small positive premiums, has not been proved. In particular,
pointwise coverage of every fixed ratio does not give a uniform three-premium
box. No explicit numerical threshold is asserted. The next concrete question
on this family is uniform control as ratios approach switching boundaries
or degenerate. Arbitrary singleton matrices and participant rewards, and the
global minimum obligations below, remain open.

The internal [cap-region invariance theorem](CODEX_UNEQUAL_GLOBAL__NONNEGATIVE_CAP_ROOT_ACTIVITY.md)
shows that, on the small-premium calibration, every full Nash root from
nonnegative continuations with player2 cap at most2 stays in that region.
No output-sign assumption is needed. Such a root can activate player0 only
alone at zero cap. Its
exact control also shows why this cannot be applied to the canonical incoming
head: that head prices observer deviations but may pay positive pivot regret.
The stronger internal
[exact-Nash nonattainment theorem](CODEX_NEGATIVE_CAPS__EXACT_NASH_NONATTAINMENT.md)
proves that the original calibration with own singleton levels1 has no
exact terminal Nash profile for all sufficiently small independent positive
premiums, even with arbitrary infinite behavioral laws and Never. It also
proves that every zero-debt point of its original semantic closure has
nonnegative native payoff. The proof rules out negative continuations along
the complete infinite root sequence, rather than assuming nonnegativity at
one end. This explains why an exact-profile search can fail on tables that
do have uniform equilibria. It does not exclude approximate equilibria or
identify observer-Nash incoming heads with full Nash roots.

## Model and the three different minimum problems

Native rewards Z have own-singleton, live and AllNever payoffs zero.
Private stopping laws are independent. U is prescribed payoff, B is the
supremum over all finite deadlines and Never, and d=B-U. Let K_abs be the
closure of actual absorbing payoff/cap pairs. A hypothetical counterexample
supplies a table with g=min_(K_abs) max_i d_i>0. Its native AllNever profile
still has zero debt; the restriction to absorbing profiles matters.

The source reductions use three distinct optimizations:

| Source | Objective and feasible set | Established conclusion |
| --- | --- | --- |
| Canonical low-cap F_p | Minimize d_p over K_abs with d_i=0 for i!=p and min B<=0 | A source exists for every pivot; after a gap-preserving generic perturbation it has a nonzero exact B-root with strictly positive successor caps. |
| Global absorbing C_p | Minimize d_p over K_abs with d_i=0 for i!=p | Every minimum has positive pivot payoff; generically every payoff is positive. AllContinue is the only exact root at U. |
| Never-penalized C_h | Minimize d_h+r nu on the augmented ALL-profile carrier with zero observer debts, 0<r<A | Every minimum has positive original Never mass, all END caps active, and a strict pivot margin. |

Here nu is the product of original Never masses and A is the infimum of
absorbing total debt. The last source uses the strict inverse column h.
Different pivots, weights and perturbations can select different points.
No inequalities are transferred between these three problems without proof.

The complete canonical result is
[Universal canonical pivot exit](../exports/UNIVERSAL_CANONICAL_PIVOT_EXIT_REDUCTION.md).
It supplies its source, finite-law returns and genericity argument without
a ledger assumption. At its positive-cap exit, if the successor debt is
c d_p and r is the first-zero pivot-return survival, minimality gives

    r c d_p+(1-r)W_p >= d_p,     W_p>d_p,
    U'_p >= (1-c)d_p/(1-r)>0.

Consuming this expensive exit remains open. The separate
[absorbing partial-Nash proof](CODEX_EXPENSIVE_EXIT__ABSORBING_PARTIAL_NASH_MINIMUM.md)
supplies C_p and its positivity; it does not identify C_p with F_p.

For the Never-penalized source, use the existing
[strict-margin proof](CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_PARTIAL_NASH_PREFIX_BARRIER.md)
and [constrained-repair proof](CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_REPAIR_AND_CONE_GRAFT_OBSTRUCTION.md).
They already prove vanishing-weight access, all-END activity at EVERY
minimum, a strict pivot Never-mass bound and separation from jointly
repaired pivot deletion. Reconstructing those facts is not a new result.

## The absorbing global-minimum frontier

The [incoming-collision theorem](CODEX_OBSERVER_PATH__GLOBAL_MINIMUM_INCOMING_COLLISION.md)
and [realization reduction](CODEX_PIVOT_REVIEW__SURE_ROOT_AND_PROPER_LIMIT_REALIZATION.md)
leave two concrete branches.

An ACTUAL global C_p minimum may still exist. Its whole-law variations
must preserve the three observers' exact full best responses. The
[fixed-pivot note](CODEX_COLLAPSED_CONSUMER__FIXED_PIVOT_FULL_LAW_TRAP.md)
excludes actual minima whose observers have pure uniformly strict best
replies, but it does not exclude general ties or infinite supports.

Every NONREALIZED minimum now admits the stronger
[zero-observer boundary reduction](CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md).
Incoming decomposition continues through higher-debt tails using words of
at most two roots. It reaches, finitely or as a semantic limit, a tail in

    F={Y in C_p: all B_i(Y)>=0, min_(i!=p) B_i(Y)=0},
    d_p(Y)>=m+kappa_F,     kappa_F=min_F d_p-m>0.

An infinite selected head has positive survival and summable hazards;
vanishing survival would actually realize the original minimum. The
boundary tail need not be an actual profile. No continuation is executed
after infinitely many dates. Observers with positive limiting caps become
inactive eventually in this head; only the pivot and zero-cap observers
can keep acting arbitrarily late.

For a boundary with exactly ONE zero-cap observer, Section 5 now replaces
the entire infinite head by a finite prefix followed by at most TWO
diluted geometric clocks, preserving every payoff and full deviation cap
and keeping the same boundary tail. This needs no genericity. A positive
pivot tail cap leaves only a solo-pivot geometric suffix; the two-clock
case has zero pivot and observer tail caps and an explicit rational pivot
debt formula. This is an exact representation reduction, not a boundary
repair. Boundary tails with two or more zero observer caps remain open.

The infinite case supplies an actual nonabsorbing head P and an explicit
limit comparison map. Write s for its joint Never mass, h_i for opponent
Never mass, and e_i for its Never response payoff. Then

    Phi(Z).U_i=U_i(P)+s U_i(Z),
    Phi(Z).B_i=max(B_i(P),e_i+h_i B_i(Z)),
    Phi(Y)=the original global minimum.

The boundary tail minimizes the pulled-back pivot objective on its fixed
observer-cap slice. It does NOT minimize d_p on F. The old strict incoming
tail-gap theorem remains valid, but a tail above m no longer stops
decomposition. Incoming and outgoing budgets still have different cap
annotations, and an unrelated lower-debt tail need not preserve observer
optimality.

If EVERY boundary cap is zero, Section 6 identifies an exact link to the
penalized problem: with lambda=d_p(Y), the actual positive-Never head P
globally minimizes d_p+lambda nu over the augmented partial-Nash carrier.
Its minimum first reaches the absorbing value m at lambda and stays there
for all larger penalties. The left derivative is at least nu(P)>0 and the
right derivative is zero. Thus every such endpoint has the same debt and
forces a finite plateau corner with both positive- and zero-Never minima.
Excluding that coexistence remains open; generic envelope calculus does
not exclude it.

The reviewed [weighted cap bound](CODEX_COORDINATOR__WEIGHTED_CAP_ABSORPTION_COERCIVITY.md)
excludes specified zero-cap faces under two finite reward-table tests.
If a nonnegative weight vector has strictly positive singleton column
drift and strictly positive weighted forced-Quit rewards on every nonempty
coalition, its weighted full cap bounds absorption probability from below.
This applies to every actual profile and its semantic closure. Sparse
weights exclude the entire face on which their supported caps vanish.
The arbitrary-counterexample source does not supply those reward tests;
the theorem therefore remains internal and does not close the boundary
branch as a whole.

The [local cap-collar theorem](CODEX_GLOBAL_SYSTEMATIC__LOCAL_CAP_COLLAR.md)
replaces the global forced-Quit positivity test with positive supported pair
premiums and an isolated common nonpositive forced-Quit root. Together with
strictly positive weighted singleton drift, these raw tests produce
`max_(i in S) B_i >= delta*(1-nu)` for every actual profile and its augmented
semantic closure. On the small-premium calibration, S={0,1,3} passes these
tests although EVERY weight fails the older global forced-Quit test.
Consequently the entire face `B0=B1=B3=0`, including the all-zero endpoint,
is absent from its absorbing native closure. The note proves the exact
translation for original own singleton levels1. Other zero-observer faces,
the actual-minimum branch and arbitrary tables remain open; this restricted
boundary exclusion is retained internally rather than counted as a global
source theorem.

Section 4 gives an exact warning for the new endpoint: even a zero-cap
observer whose Never action is optimal can lose by at least 1-nu-2epsilon
under EVERY epsilon-Nash repair of the other three players with joint
Never mass nu. That control has equilibria elsewhere and lacks the global
minimum ancestry; it refutes the unguarded repair, not Fin4.

On this global-minimum route, the next two proof questions are: exclude an
actual global minimum using complete-law best-response variations; or repair the boundary
tail while respecting its inherited comparison map and observer caps.

## Global reductions worth keeping in view

These retained packets concern broad source constraints rather than one
chosen calendar or controller:

- [Strict inverse column and all-END minima](../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md): the native source and fixed positive weight box; includes the older determinant/inverse-column argument.
- [Three-owner dispersion](../exports/UNIFORM_THREE_OWNER_TAIL_DISPERSION.md): a uniform actual-law mass bound, including limits in the augmented carrier.
- [Collision floor](../exports/NATIVE_COLLISION_FLOOR_AND_GLOBAL_MASS_DICHOTOMY.md): a quantitative actual-law collision/mass dichotomy and its conditional-tail consequences.
- [Every-cut late-tail debt](../exports/GENERAL_LATE_TAIL_DEBT_AND_END_CAP_MINIMUM_REDUCTION.md): bounds without a fixed future-owner count or calendar, with the additional END-active comparison stated separately.
- [Zero-active-payoff renewal](../exports/ZERO_ACTIVE_PAYOFF_SEMANTIC_RENEWAL_AND_SOURCE_INTERSECTION.md): absorbing approximation from the stated zero-debt closure source without assuming actual realization.

The existence-class packets in `math/exports/` have independent raw reward
criteria and complete producers. They are partial classes, not a coverage
proof for arbitrary tables. Earlier review evidence is consolidated in
[the export review record](../feedback/FIN4_EXPORT_REVIEWS.md).

## Proven obstructions to recurring shortcuts

Use these canonical arguments before opening another variation of the same
method. Their exact hypotheses matter.

- [Full-law component and local traps](CODEX_EXPENSIVE_EXIT__FULL_LAW_OBSERVER_COMPONENT_TRAP.md): an entire absorbing observer-equilibrium component can have a positive debt floor; a stronger local control also has negative singleton columns, a positive inverse column and generic joining determinants. Both games have equilibria elsewhere. Local or component minimality cannot replace global minimality.
- [Fixed-pivot pinning](CODEX_COLLAPSED_CONSUMER__FIXED_PIVOT_FULL_LAW_TRAP.md): unrestricted observer-law changes may be globally pinned when the pivot is fixed. This differs from a joint-law global minimum.
- [Full-cap thinning and continuation](CODEX_FIXED_COLUMN_VARIATION__FULL_CAP_THINNING_RENT.md): exact variation formulas and a spanning observer-equilibrium continuum do not select a branch through an arbitrary initial equilibrium.
- [Singleton-graft dual barrier](CODEX_COORDINATOR__SINGLETON_GRAFT_DUAL_BARRIER.md): singleton-only appended tails, including signed/switching drift, cannot bypass the stated global minimum while retaining the old cap menu.
- [Penalty transition boundary](CODEX_SOURCE_ESCAPE__CONSTRAINED_PENALTY_TRANSITION_BOUNDARY.md): scalar penalty and own-containing reward deformations need their real global consumer; a monotonicity assertion can already be conjecture-equivalent.
- [Finite exact-Nash incompleteness](CODEX_GLOBAL_CREATIVE__FINITE_EXACT_NASH_INCOMPLETENESS.md): an exact finite-calendar strategy grammar misses a genuine infinite absorbing equilibrium, even under its displayed generic singleton restrictions.
- [Analytic barrier draft](CODEX_JOINT_CAP_PROBE__GENERIC_ANALYTIC_GLOBAL_BARRIER_NOGO.md): an UNREVIEWED no-go for functions monotone under every root on the FULL annotation box. It does not rule out a potential restricted to the actual source carrier.

The accepted source constructions and these obstructions are the active
research record. New work should change one of the remaining implications,
produce an independent existence class, or give a genuine positive-gap
example. A renamed source, another solved local control, or a repeated
proof of an existing source does not count as an additional advance.
