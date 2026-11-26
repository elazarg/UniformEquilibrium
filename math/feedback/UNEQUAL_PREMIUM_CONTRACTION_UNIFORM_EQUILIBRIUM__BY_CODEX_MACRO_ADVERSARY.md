# Unequal-premium contraction theorem: full adversarial review

Reviewer: CODEX_MACRO_ADVERSARY. Ordinary mathematical review, not a Lean
check. Mathematical verdict: PASS. Export-gate verdict: PASS.

The reviewed artifact is
[Unequal participant premiums](../exports/UNEQUAL_PREMIUM_CONTRACTION_UNIFORM_EQUILIBRIUM.md),
with SHA256
`740bed96fd5791f39d4c1cc65314ecffbfe8b4bfb5beb4e759a6251282379b54`.
This verdict concerns that complete artifact, including its two raw regions,
uniformity, unrestricted consumer, calibration comparisons and source appendix.
There is no unresolved mathematical objection.

## Independence and exact scope

I first independently checked the earlier macroscopic pair/triple contact
and then the closed-wedge hybrid construction. During the latter check I
suggested the equivalent maximum form of the Bellman operator now used in
(W14). The author and other reviewer checked that small equivalence lemma
independently. I do not represent my review of that contributed formulation
as an independent check of its authorship. I subsequently read and checked
the complete assembled artifact afresh, including the strict-cone theorem,
all original-game guards, finite-word consumer and coverage calculations.

The claims checked are existence for the displayed raw rewards on

    a>0, 0<c<5/9, 8a<15(1-c),

or

    1<c<2, 3c/2<=a<3,

at every sufficiently small positive scale, with a common scale threshold
on each compact parameter subset. The threshold is independent of the
freely lowered row0 entries, original own-singleton levels, and three
unqueried grand rewards. The payoff target is fixed before accuracy.
Fin4 itself remains open; no global premium-ratio or arbitrary-table
coverage is asserted.

## Core mathematics and attempted falsification

The exact triple indifference input and output give the displayed cap map
and its derivative. The negative eigenvalue is simple: Descartes' rule
counts exactly one negative root with multiplicity, and the two endpoint
evaluations place its magnitude between c and a. The complementary plane
is separated from that eigenvalue even at its own double eigenvalue.

The C2 graph construction has the necessary regularity. In its stated
complete C2 metric, the normal remainder contributes O(radius) to the
difference estimate. Two derivatives of the composed unknown graph carry
two factors of beta, leaving O(beta) after normal division. The common
Lipschitz bound on its second derivative controls changes of evaluation
point. The stated order of choosing the derivative bounds, radius and
scale closes preservation and contraction. The analytic maps supply the
bounded higher derivatives used in these estimates. This produces the
graph; it is not a hidden strategic assumption.

I specifically tried to break the critical-line argument by letting
2a-3c vanish and by considering arbitrarily small positive states. The
argument does not discard its quadratic margin. The boundary relation
(W11) is exact, and its limiting curvature is strictly negative. The
pair map in odds is exactly diagonal, with rho3<=rho1 equivalent to
2a>=3c. Strict concavity therefore gives a strictly inward boundary even
at equality. Interior invariance follows separately from the positive
derivative of the projective boundary defect. Its denominator stays
positive and its derivative has a compact-parameter lower bound. Thus
boundary inwardness is not being mistaken for whole-region invariance.

The Bellman construction has the correct Nash sign. At the virtual
owner2-indifference input, graph factorization gives

    d-T(Pi x)=K(tcrit-T), K<0.

Outside the physical graph region this implies T(Pi x)>d, while
H T-b<d. Inside, the inequalities reverse and Pi preserves the whole
region. Picard iteration from T consequently stays T inside and increases
outside. Its fixed point supplies a legal pair root outside and the legal
triple graph inside. The weighted contraction is at most max(rho1,rho3)
divided by min H, below one half. The operator preserves continuity and
finite weighted norm, including at the origin. Exact agreement at the
switching boundary gives continuous hazards and passive values.

Unbounded pair-prefix counts do not invalidate this proof. Infinite pair
chains are allowed in the backward construction, their cap norms still
contract geometrically, and only finite truncations are later executed.
Uniform Picard convergence gives parameter continuity across 2a=3c.
The odds-to-cap pullback is explicitly made before (W16) and (W21).
The small-scale tangent is the stated maximum: the physical branch has
linear part Au+Bv, while the pair pullback has linear part u/3+v; they
agree on the limiting physical boundary.

The slack macro chart supplies actual data rather than an assumed return.
The two arms agree exactly at zero slack/hazard. The spectator guard on
the pair arm is beta times its nonnegative slack. The endpoint shooting
signs are strict, and projection changes only the auxiliary spectator
annotation. At a simultaneous zero that projection is the identity.
The passive-axis estimate is uniform, so the opposite return signs on
the transverse tube faces survive. Poincare-Miranda therefore produces
the required actual return without presupposing differentiable switching.

The strict-cone alternative is independent of that graph argument. I
recomputed (C3), both boundary evaluations in (C4), and the exact macro
elimination. The tightened cone has strict lower, upper and coordinate
margins on its normalized compact section. Its macro output has both
strict entrance margins in (C7). Analytic perturbation then preserves the
cone, and the one-variable return argument produces the return.

For additional exact checks, symbolic rational algebra reproduced (C3),
(C4), (W19), and the displayed factor relating the return residual to P.
It also reproduced all thirteen displayed response-partition determinants.
The Bernstein derivative bounds and endpoint signs supply a finite exact
return certificate; floating-point trajectories are not used as proof.

## Full-game and original-payoff audit

The macro rectangle has strictly positive u, v, a0, r and 1-r margins.
The owner0 endpoint bound uses only its specified upper reward bounds;
arbitrarily negative entries improve that inequality. Small core roots
retain a positive passive0 value because their total hazard is summable.
Solo0 has the three required inactive-player guards for small beta. The
solo2 recursion uses alpha_plus and has the claimed explicit limit for
all finite alpha<=1, including alpha<0.

The finite chronological word contains exactly the two stated annotation
mismatches. Bellman telescoping weights each seam by survival under the
actual profile or unilateral replacement. The designated solo0 and solo2
coins give a positive opponent-absorption probability in every period,
independent of the deviator's complete strategy. Consequently each seam
has total survival weight at most 1/delta_abs. The prescribed payoff and
deviation bounds, and therefore the factor-two regret estimate, follow
without a bounded-memory or finite-deadline restriction.

No continuation is scheduled after infinitely many dates. For each
accuracy the selected word is finite and periodic. Its opponents absorb
surely under every unilateral replacement, so shifting terminal rewards
by ell is exact there despite literal Never remaining zero. The finite
expected opponent-absorption time bounds the difference between terminal
and long-horizon average payoffs uniformly over deviations. The final
artifact correctly defines tau as the number of stages before the first
absorbed-reward stage. The target ell+V is chosen before approximation
lengths and horizon thresholds.

The reward-query audit is complete: grand coordinates of owners1,2,3 are
never queried by their own deviation because player0 is quiet during
the core/macro and the solo roots cannot involve all four players.
Row0 lower bounds never enter a threshold estimate. Horizon thresholds
may depend on the finite reward magnitude, as the statement allows.

## Coverage audit

Both calibration rays satisfy the stated raw regions at every sufficiently
small positive scale. Choosing a rational scale below a produced positive
threshold is legitimate; the packet does not claim a numerical lower
bound for that threshold. The prior quantitative and signed-chamber
relative-premium inequalities, pair-contraction inequalities and
equal-premium equality all fail as stated. The singleton sign pattern
permits only the identity role assignment. Normalizing positive row
scales does not restore the failed inequalities, including the analyzed
row2 rescaling of kappa times the minimum premium.

I checked the sure-owner census as a complete face partition, not only
one selected root. Its sole continuation bound, native v2>=-3, holds
for every feasible original continuation and punishment value. The
stationary proof separately excludes AllContinue, sure hazards, omitted
supports and the fully mixed support. Its endpoint equations and the
upper and lower bounds in (E5) have the stated incompatible signs.

The protected-set and nonnegative-weight comparisons cover their entire
selection sets. The proper-child controls cover all fourteen children.
In particular, the subdivided 023 cycle has the displayed Bellman values,
vanishing full child debts and a fixed outsider gain. The sole-owner
child controls remain valid with original Never zero: their active owner
obtains original payoff one, and its Never replacement cannot improve it.
The three-owner cycle itself has opponent absorption under every relevant
replacement, so its normalization is exact.

The exact finite support-at-most-two periodic exclusion respects reachability:
the sure-root census first removes any reachable first sure root, making
all phases reachable. Conditional Nash then gives nonnegative native
continuations. Positive proper participant premiums eliminate the other
pair supports and any solo phase followed by a different owner. The
remaining pair13 calendar is defeated by quiet owner2. This says nothing
against the approximate finite profiles constructed by the theorem.

I independently enumerated the displayed principal determinants and
active LCP solutions. Their signs establish the claimed R0 and offset
degree comparison. The inverse-child and exterior-row calculations reject
every selected triple. The response-partition determinant table is exact.
These comparisons establish an increment over the indicated implemented
and accepted mechanisms; they do not claim a census of every conceivable
equilibrium certificate or an unrestricted counterexample.

## Source and export gate

I inspected the exact target declaration
`quittingUniformEquilibriumPayoffConjecture`
(`UniformEquilibrium/Quitting/Conjecture/Basic.lean`) and the checked
semantic endpoint
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
Their quantifiers agree with the stated original-game target and complete
behavioral consumer. The target remains a proposition, not a proved
arbitrary-table theorem.

I also inspected the cited sure-punishment definition, protected-player
and leaver definitions, withdrawal/future-joining certificate and full-law
consumer, and literal raw inverse-child criterion in their named source
files. The universal child-profile consumer is genuinely rejected by the
vanishing-child-debt controls; it is not confused with a consumer selecting
a favorable child equilibrium. The inverse criterion uses exactly the
native singleton-difference matrix and exterior inverse row tested here.
All seven cited Lean files are tracked. No Lean build or new formalization
is claimed by this review.

The artifact is self-contained and has no dependency on a conference note,
another export, temporary program or generated output. Every strategic
witness used in the proof is produced from the displayed reward data.
There are no unproduced strategic inputs and no conditional exception is
being invoked. Its exact positive calibration rays and negative selector
tests demonstrate new raw coverage. Its source appendix states a viable
formalization boundary and does not encode the desired result as an input.
The mathematical and export gates therefore pass for the pinned artifact.
