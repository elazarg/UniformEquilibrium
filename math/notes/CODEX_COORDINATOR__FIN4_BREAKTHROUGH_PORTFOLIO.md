# Fin4: current results and the remaining proof obligations

Owner: CODEX_COORDINATOR.

Fin4 is OPEN. The target is uniform-equilibrium existence for every signed
four-player quitting table, with one payoff target fixed before accuracy
and all unilateral behavioral deviations allowed. The conference has
ordinary mathematical reductions and existence classes; it has not proved
an arbitrary-table producer or exhibited an unrestricted counterexample.

The checked theorem boundary is in `docs/FRONTIER.md` and the named Lean
sources. An exported mathematical proof is not a new Lean theorem.

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

Every NONREALIZED minimum reaches, through finitely many nonzero incoming
minimum-to-minimum steps, a nonrealized minimum X_* for which EVERY
nonzero exact factorization satisfies

    X_*=prefix_q(Y),     0<c(q)<1,
    Y in C_p,           d_p(Y)>=m+kappa,

with one kappa>0. All such roots have activity bounded away from zero
and continuation probability bounded away from zero. A sure incoming
root would actually realize its pair. Infinite exact decompositions with
vanishing joint survival also realize an initial global minimum: finite
response bounds, observer zero debt and global minimality recover its
complete caps.

The exact budget at X_* is

    R_p(q;B(Y)) <= m(1-c)-kappa c.

The outgoing minimum bound has the opposite inequality at B(X_*).
Those are DIFFERENT cap annotations. Active observers pin exact tail
caps; an unrelated lower-debt tail need not preserve their optimality.
The fixed-pivot note's Section 9 gives the exact compatibility conditions
and the necessary increase in pivot root regret. The incoming note's
Section 9 records the corresponding global fixed-observer-cap slice
minimum. Neither result produces the required substitution.

The next two proof questions are therefore: exclude an actual global
minimum using complete-law best-response variations; or consume the
strict incoming tail-debt gap with a valid joint observer repair.

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
proof for arbitrary tables. Their final review evidence is consolidated in
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
