# Independent review of capped-clock domination

The pathwise criterion, regret transfer, paired raw-table family, and strict
inverse-row sharpness are valid ordinary mathematics under the stated exact
balance and independent private-law hypotheses. The script provides exact
finite evidence consistent with these arguments. This review does not confer
Lean verification, unrestricted strategy-class completeness, or an export seal.

Reviewed objects: [the packet](../gpt/CAPPED_CLOCK_DEVIATION_DOMINATION.md) and
[its checker](../gpt/VERIFY_CAPPED_CLOCK_DEVIATION_DOMINATION.py). The owned
[source notebook](../notes/CODEX_SCHUR_CLOCK__CAPPED_CLOCK_CLASS_REVIEW.md)
records the bounded source comparison. No mathematical objection to the core
compiler or the accepted family arises from this review. The first-block
qualification below makes the infinite-spine strengthening precise.

## Raw criterion and its exact scope

Fix a finite player set, a nonempty proper child set S, an outside player k,
arbitrary signed rewards on nonempty coalitions, and independent private laws
on natural dates together with Never. All outsiders prescribe Never. For one
fixed nonnegative weight vector λ, the packet's (N), (F), and (J) are exactly
equivalent to its terminal pathwise gain comparison for the particular
unilateral child replacements T_i ↦ min(T_i,t), for every deterministic tuple
and every deadline. The four finite temporal cases identify the inequalities
without averaging; pure tuples also establish necessity. This exactness
concerns that compiler, not necessity for equilibrium existence.

The weighted-evaluation calculation is sound: with d ≤ 0 and ψ(A) ≥ d, the
residual is [f(t)−f(τ)]d + f(τ)[d−ψ(A)] ≤ 0. Allowing each raw row to fail by
η gives a residual at most η because the nonnegative coefficients sum to
f(t) ≤ 1. No terminal-to-finite-horizon interchange is needed for this step.

The min-pushforward law is a legal independent unilateral replacement. A common
deadline in the proof coupling preserves each required marginal experiment;
it supplies no common random signal to the game. Taking response suprema then
gives d_k ≤ Σ_i λ_i d_i. The bounds do not require cap attainment, absorption,
or suffix Nash. The terminal Never correction is valid, including signed
rewards. Its inequality s_j Pr(all Never) ≤ d_j is already the declaration
`prod_stoppingLaw_none_mul_singleton_le_terminalDebt`
(`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`), rather
than additional new mathematics. The packet's late-capping proof independently
explains this dependency.

For the LP written Vλ ≥ b, λ ≥ 0, infeasibility has the correct dual orientation:
y ≥ 0, Vᵀy ≤ 0, and b·y > 0. The finitely generated cone with columns V and
negative coordinate vectors proves necessity of this obstruction by separation.
For rational data both a feasible point and a strict dual obstruction can be
chosen rationally. The table class is conditional on this finite feasibility
test; the three-player capstone removes a child-equilibrium premise only when
the actual child has three players.

## Genuine separation from two existing sufficient classes

With λ = 0, the three raw conditions reduce to

    s_k ≤ 0,
    s_k ≤ r_k(A) for every nonempty A ⊆ S,
    r_k(A ∪ {k}) ≤ r_k(A) for every such A.

These are exactly `QuittingBlockDispensable` for the block complementary to S.
Indeed `quittingBlockContinueFloor` is the minimum of zero and those survivor
coalition rewards, and `QuittingBlockJoinAntitone` is the last displayed
condition (`UniformEquilibrium/Quitting/Classification/BlockDeletion.lean`).
Thus the new feasible-weight class contains that exact deletion class.

The inclusion is strict. At the complete rational fixture, every single-player
deletion has own singleton 1, continue floor 0, and join cap 2. Nevertheless
deletion of player 3 admits λ = 2e₂, with minimum raw slack 1. This is a
strict extension of the named exact deletion gate, not a claim to supersede
every quantitative deletion or punishment theorem. In particular,
`quittingGame_exists_uniformEquilibriumPayoff_of_vanishingAbsorption`
(`UniformEquilibrium/Quitting/Classification/BlockDeletionInequality.lean`)
still needs an applicable singleton/continue-floor premise, which this fixture
fails for every deletion.

The paired fixed singleton matrix has no escort edge: within each pair both
reciprocal entries are positive, and across pairs both are negative. The exact
definition `IsQuittingSingletonEscortEdge` requires opposite weak signs.
Consequently `BalancedSingletonCycleCertificate.exists_escortCycle`
(`UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`) excludes every
balanced singleton certificate on the parent and every child restriction. The
theorem includes arbitrary finite periods and eliminates zero-hazard phases
internally. This is a separation for the entire accepted paired family,
independent of its nonsingleton completion.

The family dimensions are correct: four child nonsingletons contribute twelve
freely chosen child coordinates, while seven nonsingletons containing player 3
contribute twenty-one. Four passive coordinates of player 3 can then be chosen
above their bounds, followed by seven joining coordinates below their bounds.
The three fixed singleton (F) slacks are 1, 1, and 3. Thus all thirty-three
free nonsingleton coordinates can be chosen first, with no hidden child-profile
or child-equilibrium premise. All forty-four nonsingleton coordinates are
accounted for. The new family guarantee is stronger evidence than the isolated
fixture, whose convenient mixed equilibrium is only a calibration example.

The inverse, perturbation, and simple obstruction comparisons also check out.
The stated inverse multiplies Γ to the identity and has infinity norm 1.
The inverse perturbation estimate 3/47 < 2/15 preserves strict positivity in
the proposed radius-1/100 reward ball. The radius-1/6 raw-slack estimate is
valid. The three-player principal's last row excludes an LCP solution at −1;
its homogeneous nonnegative solution must be zero. These comparisons are
separate from the compiler's proof. No priority claim about LCP degree follows
from this bounded review.

## Exact infinite-spine sharpness

Here the intended infinite object must retain all of the conditions actually
used: one positive-hazard owner per effective row, exact owner indifference,
all-player singleton floors at every row, actual continuation payoffs, and
joint absorption. They are stronger than approximate child equilibrium.

For the displayed strict triple T, let B = T⁻¹ > 0 and h_j = Σ_i B_ij.
At every continuation z = Tμ lies in the simplex z ≥ 0, h·z = 1. A zero-hazard
row leaves the continuation unchanged. Through a positive owner-i row the
owner tie persists at its successor because its survival probability is
positive. A sure owner row is itself excluded by the negative coordinate in
that owner's singleton vector and the all-player floors.

There cannot be only finitely many effective rows: their positive survival
product would contradict joint absorption. There cannot be an infinite final
block of one owner either: absorption of its suffix would make its actual
continuation that owner's singleton vector, violating another player's strict
negative singleton comparison. Thus each positive owner block ends at a finite
date, even when zero-hazard delays or block lengths have no uniform bound.
Every owner change is an escort edge, hence follows 0 → 1 → 2 → 0. The shared
boundary has both adjacent owner coordinates zero, so it is the remaining
vertex e_j/h_j. All three vertices recur.

For additional quantitative detail, use indices modulo three. A complete
owner-i block starts at e_(i+1)/h_(i+1) and ends at e_(i−1)/h_(i−1). If its
absorption probability is p_i and survival is c_i, its exact arc gives

    p_i = 1 / [a_(i+1) h_(i+1)],
    c_i = b_(i−1) h_(i−1) / [a_(i+1) h_(i+1)].

Therefore the product of the three complete-block survivals is exactly
C = (b₀b₁b₂)/(a₀a₁a₂). Splitting blocks cannot change this product.

One qualification to the wording “the merged hazards uniquely” is necessary
for an arbitrary initial date: its initial owner block may be a partial block,
so its merged hazard need not equal p_i. This does not invalidate (12). Its
initial z lies on the owner-i simplex edge between the two boundary vertices;
the arc relation then gives a remaining absorption probability at most p_i,
and remaining survival at least c_i. From any initial phase, every specified
vertex is reached through at most one partial and two complete blocks, with
survival at least C. The dates involved are finite; no uniform calendar bound
is claimed.

At a vertex with outside deficit Δ, the pure outside deadline has conditional
gain at least Δ−2Mδ because only its simultaneous collision, of probability
at most δ, can change the own-singleton Quit payoff. Earlier absorption is
unchanged. Multiplying by the survival lower bound proves (12), using the
nonnegativity of regret when Δ−2Mδ ≤ 0. This validates the inverse-row
sharpness for these exact spines; it supplies no completeness result for
arbitrary child equilibria or approximate balanced spines.

## Exact computation and source boundary

The complete checker was inspected before execution. Its main function writes
JSON; this review instead loaded it with `runpy.run_path` under a non-main
name and called its test functions, producing no checker output file. All
25,600 pathwise comparisons, 80 full-cap transfers, 80 randomized-response
comparisons, 15 necessity recoveries, 20 positive-singleton relaxations, and
four one-row no-go duals passed. The fixture has minimum raw slack 1, all
fifteen nonempty pure-coalition gaps at least 1, and complete terminal caps
equal to (13/9, 2, 2/3, 4/3) at the displayed one-date profile. The supplied
cap routine includes every natural date through the first post-calendar date,
so it covers intervening deadlines as well as Never.

Actual consumers are present as named declarations under their imports:

- `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`)
  has an arbitrary `Fin 3` reward table as its only game input.
- `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  and `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
  provide the target-selection consumer and its converse.
- `exists_finiteDeadlineTimingProfile_approximation` and
  `isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation`
  (`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`)
  provide simultaneous finite-law payoff and unrestricted-cap approximation.

These source declarations were statically inspected; no Lean build or axiom
audit was run. The packet's new raw-certificate-to-regret adapter remains
ordinary mathematics. A narrow phrase search in the cited deletion/terminal
neighborhood and the literature transcription lane did not identify an existing
copy of that weighted compiler; this is a local overlap check, not a worldwide
novelty certification.
