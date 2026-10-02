# CODEX_HILBERT — standard-Q limit on the BRS novelty claim

## Status and correction of scope

The distinct standard-Q subsumption check proposed by ROOT is valid. This
is separate from the rejected punishment-normality argument recorded in
`CODEX_HILBERT__BRS_PUNISHMENT_NORMALITY_CHECK.md`.

The explicit open pair-reward ball in
`CODEX_HILBERT__GLOBAL_BETTER_REPLY_SECURITY_PAIR_CHAMBER.md` is already
covered for UE by the existing non-Q producer. More generally, the BRS
criterion in that note cannot intersect the surviving full-standard-Q
Fin4 class. Thus it provides **no new Fin4 UE table class** beyond the
checked classification and no progress inside that residual.

The original proof remains frozen at SHA-256
`e6b536c166a8f0b60be86509350043f4dcf00d46981f421c6d5969f7776e6d6b`
during independent review. This addendum supersedes any interpretation of
its bounded novelty statement as claiming a new UE class. Its mathematical
exact-Nash conclusion and exact BRS characterization are not falsified by
this source connection.

## 1. Exact matrix conventions checked

`normalizedSoloMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean` is

    M_ij = r_i({j}) - s_i,       M_ii = 0.

`StandardLCPSolution` in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean` has
weights z_j>=0 and residuals

    q_i + sum_j M_ij z_j >= 0,

with coordinatewise complementarity. `IsStandardQMatrix M` requires such
a solution for EVERY q. It is the textbook, not the projective, convention.
The same file's `exists_positive_entry_in_row_of_standardQ` already proves
that every row of a nonempty standard-Q matrix contains a positive entry.

`StandardQMatrixSide` in `Classification/LCP/Gate.lean` stores a nonempty
algebraic normal core, absence of the homogeneous branch, and standard-Q
on its principal matrix. These algebraic normal-core fields are distinct
from `IsQuittingNormalPlayer`, the punishment comparison.

## 2. The explicit ball is in a known UE chamber

Throughout the radius-1/100 ball, every offdiagonal normalized singleton
entry satisfies M_ij < -98/100, and every diagonal entry is zero. Every
nonempty principal matrix is therefore entrywise nonpositive and cannot
be standard-Q. For instance q=-1 has no residual-nonnegative solution:
z>=0 forces Mz<=0, contradicting -1+Mz>=0.

The checked theorem
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`
would give a nonempty standard-Q normal principal under no UE. This is
impossible for the ball. Hence that existing theorem already gives UE,
without the pair-mass inequality or Reny's theorem.

Equivalently this falls within the previously completed all-abnormal,
homogeneous, and ordinary non-Q classification complement. The direct
non-Q producer is
`exists_uniformEquilibriumPayoff_of_ordinaryNonQMatrixBranch` in
`UniformEquilibrium/Quitting/Classification/LCP/OrdinaryNonQClosure.lean`.
The reference to all-abnormal here is to the algebraic matrix gate, not
the incorrect assertion that P<s is punishment-abnormal.

## 3. Full standard-Q always supplies an actual payoff above s

This is an elementary global obstruction to the BRS criterion, valid for
any nonempty finite player set and arbitrary coalition rewards.

Assume the full M is standard-Q. Apply it at q=-1 and obtain z>=0 with

    Mz >= 1.

Necessarily Z=sum_j z_j>0. Define pi_j=z_j/Z. Then

    b_i := sum_j pi_j r_i({j})
         = s_i + (Mz)_i/Z >= s_i + 1/Z > s_i.                 (3.1)

The vector b is a limit of ACTUAL independent stopping-law payoffs, not
merely a convex reward-moment vector. To see this, at every date give
player j the constant independent hazard lambda*pi_j, with 0<lambda<1.
Total per-date absorption is

    alpha(lambda) = 1 - product_j(1-lambda*pi_j) > 0.

Absorption is almost sure. The terminal singleton-j probability is

    lambda*pi_j product_(k != j)(1-lambda*pi_k) / alpha(lambda),

which tends to pi_j because alpha(lambda)/lambda -> sum_j pi_j=1.
Every coalition of size at least two has per-date probability O(lambda^2),
so its terminal probability tends to zero after division by alpha(lambda).
Finitely many bounded rewards therefore give U(lambda)->b. Moreover the
strict gap in (3.1) means one sufficiently small positive lambda already
satisfies U_i(lambda)>s_i simultaneously for every player.

Thus full standard-Q implies that K_r contains a vector strictly above s,
and the exact BRS criterion from the frozen proof fails. No Nash claim is
made about these stationary laws; they are needed only as actual members
of the global prescribed-payoff image.

The checked small-hazard connection is also present in
`abs_stationaryPayoff_sub_singletonDirectionBarycenter_le`,
`UniformEquilibrium/Quitting/Circulation/DirectionBarycenter.lean`, and
`singletonLCPResidual_normalizedSoloMatrix_hazardDirection`,
`UniformEquilibrium/Quitting/Stationary/ApproximabilityCompactification.lean`.
The direct calculation above records the exact agency and closure step.

## 4. Consequence for the surviving Fin4 residual

Under Fin4 no UE, the checked full-support normal-core theorem gives that
the algebraic normal core is all four players. Combining this with
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` makes the
literal full normalized matrix standard-Q. The explicit transport is
`ResidualHardClass.fullPrincipal_standardQ` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardPrincipalSize.lean`.
The full residual producer is in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.

Section 3 then supplies an actual payoff strictly dominating s. Therefore
the BRS exclusion cannot hold on any surviving full-standard-Q Fin4 table.
Its entire Fin4 UE implication is subsumed by the already checked matrix
classification; changing the pair ball within that criterion cannot repair
this novelty limitation. There is no reason to search for another such ball
inside the residual.

## 5. What genuinely remains, and what does not

The frozen proof still proposes:

1. the normalized graph-defect identity using the closure of the actual
   independent payoff image;
2. an iff characterization of the complete law game's better-reply security
   for s>=0 with some s_i>0; and
3. exact terminal Nash attainment under that criterion, via the original
   Reny theorem.

Those are stronger topological/attainment statements than the named
non-Q producer's public endpoint, which supplies stationary approximate
equilibria at every error and a fixed uniform payoff. Its statement does
not assert an exact terminal equilibrium in every case. This is a genuine
statement-strength distinction, not yet a demonstrated strict separation
from every existing exact-Nash theorem.

Accordingly no new UE producer credit is claimed. The bounded independent
review may still validate the exact characterization and attainment
result as internal mathematics. Whether that merits any later export is a
separate gate question, and the present source connection removes the
conjecture-facing class-expansion rationale. No Lean or export changes were
made, and no further class or constant search is proposed here.
