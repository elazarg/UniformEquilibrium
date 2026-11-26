# Independent whole-proof review of the signed collision parameter theorem

Reviewer: CODEX_CLOSURE_ADVERSARY. Verdict: PASS for the complete raw family,
every real parameter p, unrestricted unilateral behavioral deviations, and
the export gate. This is ordinary mathematics; no Lean check is claimed.

The reviewed [packet](../exports/SIGNED_COLLISION_PARAMETER_UNIFORM_EQUILIBRIUM.md)
has SHA-256
`481d74f614dcc52d93eee540330898c099a0e362d984a2040f37b7d8fd636fdc`.
Review was completed on the byte-identical pre-promotion artifact
`/tmp/FIN4_PARAMETER_UNIFIED_PROOF.md`. This review does not transfer to a
substantively changed artifact. It supersedes my preliminary positive-branch
review for the scope of this complete packet.

The executable certificates inspected are:

- [Positive branch](../experiments/SIGNED_COLLISION_PARAMETER_POSITIVE_CHECK.py),
  SHA-256 `52ab71b79794c823c790cf4e871375344f347f9ab50ea8d06314625723bd49c8`.
- [One-triple branch](../experiments/SIGNED_COLLISION_PARAMETER_ONE_TRIPLE_CHECK.py),
  SHA-256 `6ea84975e6cc21bde2e9d3d46aa38435f98209cfbdf47b7febeec1b3d93c6499`.
- [Negative covers and switches](../experiments/SIGNED_COLLISION_PARAMETER_NEGATIVE_COVER_CHECK.py),
  SHA-256 `229d3a618bcdb409f3619b23d72a6d9f6859940e92360e3982fa339f3c938aa7`.
- [Stationary/sure-root separation](../experiments/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py),
  SHA-256 `0f3009952202bd9e86768b43730faf9922d3fb339069cf312415d489bd68f147`.

I independently executed all three existence checks successfully. The
positive execution used hash
`94ce11b859d2ec5b5e9c1a2820782421cdd4323046aab1cad0bbd4767b1287f8`.
The final version only corrects the reproduction-command filename in its
module docstring. I reconstructed the old bytes and verified their hash,
and verified identical executable ASTs after removing that docstring.
The one-triple execution used the pre-promotion hash
`c049fcd8405eb2b9d6a1467f3d7e98fce6628a519cb91460568580e6c594d0dd`;
I verified that only its module docstring differs from the pinned canonical
version. The other executed files are byte-identical to the pinned versions.
I also executed the separating checker at p=0,1,-10,-100. No generated
numeric root or external center list is assumed by any certificate.

## Whole input-to-conclusion audit

All rewards and strategic quantifiers are specified. The 31 fixed native
coordinates, real p, seven upper-bounded coordinates, 21 arbitrary
coordinates, and four arbitrary original own levels account for the whole
table. Every strategic object is produced: roots, annotations, finite core,
outer blocks, target, accuracy-dependent refinements, and horizon threshold.
No strategic input remains assumed, so no conditional-export exception is
needed.

I independently derived the pair and triple root equations from the raw
coalitions. The positive pair survivals telescope, and its finite collision
formula follows from both active payoff identities and
`S_n(2+X)(1+L)=(2+p c_n)(1+100d_n)`. These are actual nonnegative outcome
probabilities. The finite entrance values converge for each finite p>0;
`p c_n<=X[p/(p+2)]^n` controls the delicate large-p limit. No uniform rate
over unbounded p is required. Near p=0, c_0 is only an auxiliary number;
every used hazard c_k, k>=1, remains in (0,1).

The two return equations reduce to F1,F2 exactly. Their specified linear
combination cancels the quadratic dependence on E and determines E0.
The positive-branch Bernstein and denominator certificates give a return
root on the entire parameter rectangle. Every finite pair suffix satisfies
the quiet-player inequalities, with the stated positive rational margins.

For nonpositive p, the one-triple formulas enforce entrance row2 and exit
row3 identically. Its polynomial factor is generated from the actual return
system. The root-set guard calculation correctly discards boxes containing
no polynomial root and requires nonzero same-sign numerator/denominator
bounds on every retained box. The independent run obtained five accepted
boxes, seven discarded boxes, and depth six. The derivative tests use the
original partial derivatives P_k,P_y before substituting y=q/(k+3/10).
They therefore justify the implicit y derivative and the unique wash
crossing. Both exact crossing brackets passed. At p=0 the third core hazard
is zero, and that now-quiet owner's Quit offer still equals its annotation;
the endpoint is included without importing the older zero-premium proof.

## Interval existence and exact support changes

I inspected the interval arithmetic and automatic derivatives, including
negative denominators, outward rounding, and parameter dependence. Every
acceptance test uses integer bounds; rational Newton estimates only propose
centers. Centers are dyadic at precision 2^-60, exactly representable on
the 2^-80 interval grid. Radius rounding enlarges the domain and tightens
the accepted image bound. The weighted matrix bounds prove contraction
and Jacobian nonsingularity throughout each outer box. The parameter
mean-value expression encloses the fixed-point map for every parameter
in a cell, not just its midpoint.

The independent full run passed all 1000 three-root cells on [0,1/10], all
1000 two-root cells on [101/1000,13/40], and both entire switch intervals.
The endpoint s=0 is used only in the regular algebraic proof; every actual
negative-p game uses s>0. Direct cells need no cross-cell branch matching.

I checked both insertion maps separately. At old wash equality, appending
solo3 with q=x/100 matches both previously active rows, preserves row3,
and transforms E0,x,E2 as stated. The wash endpoint and both return
equations are unchanged. Whole-box containment puts this inserted root
in the new uniqueness box. The certified positive old-wash derivative and
negative new-Y derivative select the physical branch on opposite sides.
When Y=0, the last two quiet owners are indifferent; no omitted inequality
appears. The five closed parameter regions have no gap and include p=0.

## Finite strategies and all deviations

The common solo0 subdivision allows arbitrary real joining rewards: every
observer reference value there is nonnegative and each Quit surplus is
bounded by delta times its positive joining reward. The negative wash is
finite even at wash equality, and the final solo3 aggregate is finite.
The seven row0 restrictions protect all its queried joining coalitions;
the other arbitrary coordinates cause no unpriced response.

For the positive branch, finite truncation creates exactly one Continue
residual, at solo2. Its exceptional owner2 coefficient is correct. The
entire growing core has exact identities, and fixed solo0/solo2 aggregates
keep deleted survival below 1-rho independently of truncation and period
length. The reference cap difference need not be nonnegative; the proof
correctly handles that case separately before using the survival bound.
Consequently `e+2eta/rho` bounds the full debt, with no accumulated factor
equal to the number of dates. For p<=0, eta=0 and the prescribed terminal
target is exact.

The full-cap recursion includes every finite deadline, Never, and their
mixtures. Proper opponents justify original row translations, including
negative own levels. Their expected absorption time gives the stated
uniform finite-horizon error against every replacement. One target is
chosen before accuracy. No public correlation, bounded deviation class,
continuation after infinitely many dates, or common horizon over unbounded
reward tables is hidden in the proof.

## Coverage, sources, and handoff

I independently verified all 80 stationary and all 65 sure-root exclusions
at p=1,-10,-100, obtaining respectively (978,371), (1028,353), and (962,331)
nodes. For negative p the solo-owner1 comparison correctly uses observer3,
not the old zero-premium observer2 comparison. The packet now includes the
finite polynomial, origin-collar, and Bernstein calculation rather than
relying on reported counts alone. It also gives complete-choice anchor,
child, attached-pair, invariant-cone, signed-inverse, and signed-cycle
obstructions. I checked those selections, including the unique attached
labeling (3,1,0,2) and all three pair partitions. The upper-face charge uses
the correct coalition123. No all-parameter stationary exclusion or census
of every conceivable UE theorem is asserted.

The exact declarations inspected are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`,
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`,
and `PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
with its matrix and inverse-weight definitions in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
The semantic attribution and receiver-first convention agree with them.

The final packet is self-contained under the conference export rules and
has an explicit formalization handoff. The arbitrary signed parameter
extension is a new raw existence class with exact separating witnesses;
it is not merely stronger profile regularity on the former p=0 class.
All objections raised during this review were resolved before the pinned
version. No mathematical or export-gate objection remains. Arbitrary Fin4
is still open.
