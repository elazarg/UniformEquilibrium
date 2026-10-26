# Independent full review of the central positive wedge

Reviewer: POSITIVE_WEDGE_FULL_ADVERSARY.

## Artifact and verdict

The reviewed manuscript is `CENTRAL_POSITIVE_WEDGE_UNIFORM_EQUILIBRIUM.md`,
assembled for review at [CENTRAL_POSITIVE_WEDGE_UNIFORM_EQUILIBRIUM](../exports/CENTRAL_POSITIVE_WEDGE_UNIFORM_EQUILIBRIUM.md).
Its exact SHA256 is

    afa63bbe45f0c5560123e7d92e0f3dca54488aef1ffe498a73bad297597d5a41

Verdict: PASS for the complete ordinary-mathematical theorem and export gate.
No mathematical objection remains. This review covers the entire artifact,
including the raw-data producer, all parameter and boundary arguments, every
behavioral and finite-horizon comparison, and the separating-ray certificate.
It is not a Lean compilation, a formalization claim, or a solution of Fin4.
Approval applies to these exact bytes; changed proofs require renewed review.

## Exact claim checked

For the complete raw family in Section1 there are constants C>=100 and
beta0>0 such that every K>=C and 0<=p<=beta0 K has a uniform-equilibrium
payoff. One target is fixed for each game before the accuracy. All unilateral
behavioral replacements are covered. The constants are independent of the21
free joining coordinates and the four original own-singleton rewards.
The seven row0 participant bounds remain hypotheses. The other displayed
native coefficients remain fixed. No numerical threshold or coefficient
neighborhood is asserted.

This is a producer from raw reward data. Its core, outer return, repair,
finite pair approximations and actual periodic profiles are all supplied
by the proof. No equilibrium continuation or admissible return is assumed.

## Core identities and singular dynamics

I checked the three root formulas by separating forced-Quit and passive
opponent outcomes. At alpha=0 the backward equations reduce to

    Z+97u=L, beta Y+4u=X, 2Y-101Z=-100Znext,

where u=w/(1-w). Their determinant factor is4-9797beta/2, so the displayed
backward map remains analytic at beta=0. No inverse of the singular forward
map is being used.

The fixed line is exactly(J,J/2,0). The displayed normal matrix has a simple
positive eigenvalue near3/4 and a second eigenvalue near0. Its determinant
is negative for beta>0 small, so the fast mode really can alternate. The
proof explicitly handles this rather than assuming both modes positive.
At beta=0, the invariant projection and theta recurrence agree with the
exact rational map. The positive derivative of the projection with respect
to terminal Z supplies the stated terminal section by the ordinary IFT.

## Uniform long-core argument

The proof of the invariant projection uses summable normal contraction;
parameter derivatives introduce polynomial factors in the iteration index,
which preserve summability. Coordinates with the projection as center
coordinate fix that coordinate exactly at alpha=0. The required finite
smoothness follows on a smaller compact tube. The finite terminal collar
enters that tube uniformly; this avoids assuming the terminal section was
already infinitesimally close to the fixed line.

The choice max(delta)<q<1 with q^2<min(delta) and max|kappa|<q^2 is available
near beta=0. It makes the leading stable-amplitude series and its parameter
derivatives converge. Its remainder is O(poly(n)q^(2n)), so dividing by
(delta(J,beta))^n is justified. The scale uses the unknown J, not its
limiting outer solution. This is essential for the claimed C1 convergence.

I checked the first-variation recurrence: center variation grows at most
linearly, while its effect on the normal component carries the exponentially
decaying unperturbed normal coordinate. Thus the normal variation has a
phase-independent limit. At beta=0 its physical w component is-J. Stable
summation also gives polynomial bounds on the second alpha derivative,
which justify the Taylor remainder before division by t. Derivatives of t
cost polynomial factors only. This proves the scaled entrance limit.

The aggregate error estimate is also adequate: the omitted alpha=0 orbit
has total activity O(poly(n)t), and finite perturbed-coordinate errors sum
to O(poly(n)alpha). Products and affine recursions remain in a bounded
compact neighborhood. The same estimate holds after parameter differentiation.
This justifies the stronger O(poly(n)t) outer-return estimate even though
the divided entrance error has its own geometric rate.

For physical signs, the exact entrance w_first=0 cancels the common negative
alpha shift. At every later chronological index the positive leading term
is larger by a uniform factor at least1/delta_max. The fast alternating term
is uniformly smaller; the finite terminal collar is handled separately by
compact continuity. This supplies positivity for arbitrarily large N,
which a fixed-N continuity argument would not establish. Nonterminal Y,Z
have uniform positive margins, and terminal Y vanishes exactly with Z.
The first-root transverse estimate gives Y_first/Z_first=1/2+O(alpha).

## Return selection and all large K

The limiting core passive recursions eliminate its survival factor from
the outer equations. Their selected J and T0 are independent of terminal
phase. I independently checked the root (3/4,5/4), the Jacobian

    [[5/2,-45/14],[0,-10/7]],

and the beta derivative(-183/160,-57/64), by exact symbolic arithmetic.
The entrance derivative in Lambda is negative and bounded away from zero,
so the full three-equation selection is nonsingular uniformly on the
compact phase/beta rectangle.

The phase derivative of J_N is O(poly(N)t). Therefore the extra derivative
of delta(beta,J_N)^(N-1) tends to zero, and physical alpha increases strictly
with phase. This checks the potentially dangerous neutral-center dependence.
Both terminal boundaries are transverse. At the upper boundary the final
root is literally solo3; its deletion produces exact wash equality and
preserves the raw alpha,beta and all outer returns. The invariant projection
and stable amplitude place the shortened sequence in the unique preceding
branch neighborhood. Thus the neighboring K intervals join exactly.
Compactness in beta and geometric growth of their endpoints give one finite
C covering every large K, rather than a sequence of isolated parameters.

## Pair prefixes and complete consumer

I independently checked by exact symbolic calculation the finite pair
survival and first-coalition identities at one step, all four bilinear row0
corner formulas, and the complete row3 surplus recurrence. Their limits
are the stated fixed entrance C. The ratio estimate follows uniformly as
beta tends to zero because its denominator is beta+2alpha; the argument
never divides by beta in this limit. Subsequent ratios decrease. The
p=0 solo2 case is treated separately with its correct nonnegative initial
surplus. Every finite pair prefix therefore has legal quiet comparisons.

The finite calendar assigns exact annotations to its pair word. Only the
solo2 boundary has a vanishing identity residual because C_n differs from
C. The outer target and selected triple core stay fixed before the pair
length and solo0 mesh are chosen. All immediate Quit inequalities are
priced, including the unrestricted joining rewards in the solo0 mesh.
The43-step repair, final solo3 split and support-boundary equalities are
valid at the permitted endpoint cases.

Every unilateral replacement faces proper opponents with per-period
absorption probability at least min(a,b)>0. The full cap recursion therefore
bounds its gain by e+2eta/rho; no bounded-memory restriction is used.
The same opponents-only clock bounds expected absorption time uniformly
over replacements, giving the finite-horizon comparison. Native translation
adds each kappa_i to every terminal payoff because opponents are proper.
These arguments establish one fixed uniform target, not accuracy-dependent
targets or only stationary-deviation inequalities.

## Coverage, source audit and reproducible checks

The p=1,K→infinity ray is outside the scalar K=100 family, the negative
regions and the outer positive cone. The displayed singleton matrix fixes
relabelings and positive row units as stated. The complete selectors
compared in Section8 fail on this ray: ordered anchors and upper-average
weights, mixed-trap sign, passive-child selection, attached-pair templates,
all three invariant-cone partitions, signed inverse-column and signed-cycle
criteria. The participant and singleton obstructions are explicit.

I inspected the exact baseline polynomial certificate and ran

    python math/experiments/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py --uniform-k 1

It passed all80 nonzero stationary supports in862 nodes and all65 sure-root
patterns in371 nodes. The retained checker SHA256 was

    e256a0015f98f8aa3a46b9333624991bcaee78ce53da1fd19bcc30560636e026

I checked the monotone K relaxation, direct F2 exclusion at p=1, principal
inverse combinations, uniform origin bound and exact Bernstein rejection
rules. The packet provides complete table data and certificate rules and
does not use the command or an external payload as a mathematical premise.

I inspected `quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
Both cited source files are tracked. Their scope agrees with the stated
consumer; the manuscript independently supplies its mathematical adapter
and behavioral proof. No Lean commands were run. The documentation checker
passed. The manuscript has no math/ or temporary-file dependencies.

## Attempted falsifiers and remaining scope

The adverse checks targeted loss of C1 convergence from a J-dependent
exponential scale, negative fast eigenvalues, accumulated center drift,
phase dependence of the leading outer solution, gaps between adjacent
length intervals, loss of the pair guard when p approaches0, and target
variation with the pair approximation. The arguments above resolve each
within the stated small-beta/large-K region. No counterexample or unpriced
behavioral deviation was found.

The theorem adds a genuine nonstationary existence region. It does not
close either arbitrary-game global-minimum case, cover all positive ratios,
remove its fixed core coefficients, or solve Fin4. Those limitations are
stated accurately. The full export gate is satisfied at the pinned bytes.
