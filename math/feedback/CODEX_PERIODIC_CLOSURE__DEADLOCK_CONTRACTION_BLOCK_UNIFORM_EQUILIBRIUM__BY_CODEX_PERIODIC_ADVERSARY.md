# Independent review: two contracting Nash blocks

Reviewed artifact: [TWO_CONTRACTING_BLOCKS_UNIFORM_EQUILIBRIUM.md](../exports/TWO_CONTRACTING_BLOCKS_UNIFORM_EQUILIBRIUM.md), reviewed as the consolidated manuscript before verbatim placement.
SHA-256: `e8a81b27e567c021bba87ddc45574a0ddf117f38739269938e3eed2a26dabd63`.

**Mathematical verdict: PASS. Export gate: PASS.** No unresolved objection.
The four raw classes cover the quantitative box, a complete signed singleton
chamber with computed small-premium thresholds, and a complementary regime
with arbitrary nonnegative pair premiums, together with one uniform rectangle
of independent positive premium scales and independent row0 upper bounds.
They neither settle Fin4 nor assert
exact finite-period Nash in the contraction branches. This reviewer did not
construct these producers, their matrix source, scalar returns, contraction
arguments, or stationary/sure-root classification. I contributed earlier
coverage exclusions; that portion is disclosed as a contribution rather than
counted as an independent discovery. I independently checked the complete
consolidated proof, including all new signed-source and pair-return joins;
approval of the former quantitative artifact was not inherited. No Lean
command was run.

For the fourth theorem I independently audited the complete assembled proof
and its quantifiers, including portions not in my earlier component reviews.
I did not construct its low cone, C^{1,1} graph, contact charts, obstacle
operator, finite cover or macroscopic joins. My role in the obstacle argument
was adversarial review and requesting explanatory sign/continuity bridges.

## Mathematical and semantic audit

I re-derived the two fractional indifference formulas, their derivative
numerators, the odds identity for F, the strict scalar-root brackets, and
the cone estimates. The ratio bounds preserve the first coordinate, and
the player0 grand-collision term is retained in its forced-Quit bound.
I also re-derived the independent-coordinate formula for the macroscopic
Y, the endpoint quadratic and its exact positive endpoint values. The
continuous-limit intermediate value argument selects one target before
accuracy is chosen.

The second block remains valid for arbitrarily negative alpha: replacing
alpha by max(alpha,0) in its hazard makes player0's Continue value at least
its actual Quit value. Its recurrence, limiting annotation, and designated
hazard lower bound remain exact. The boundary eta=0, alpha=0 and the upper
endpoints b=1/4, alpha=3 introduce no division by zero. The t=0 root and
continuity there are handled explicitly; b=0 is correctly excluded.

Only the two seams incur error. Deleted-player absorption bounds their
expected total visits by7, giving payoff error7E and unrestricted regret14E.
This applies to complete behavioral replacements, including Never and all
private mixtures, without a public randomizer. For each chosen finite word,
uniformly bounded expected absorption time supplies the finite-horizon
average-payoff conclusion. The original own-level translation is valid for
arbitrary signed ell because every unilateral replacement absorbs surely.
I checked the complete entry inventory, including the final clarification
that an unlisted coordinate in row i is unqueried in i's own deviation payoff.
No bound on an irrelevant other player's payoff under i's deviation is used.

The error estimate E <= (3/4)^M+(187/800)(1/5)^N and its period bound follow
from the displayed recurrences. The negative control is exact: changing all
proper participant rewards in row0 to4 makes the proposed pair13 root fail
by Y+W-4YW>=W>0. The control's separately displayed sure stationary root
does satisfy all four endpoint inequalities. Thus the guard test concerns
this producer and is not incorrectly claimed as a necessary UE condition.

## Coverage and export decision

### Signed chamber, matrix source, and complementary pair mechanism

The full matrix reduction is valid with either sign of g1 and h1. I checked
every proper support in the large-y0 argument, the positive adjugate of023,
the exterior-row inequalities, the R0 limiting argument, and the final
N=0 child exit. The cofactor and determinant identities were independently
expanded exactly. The source declarations apply to the original game's
literal singleton differences after identifying the full normal core; the
proof does not silently transfer nonexistence to a different game.

The zero-premium macroscopic return has the claimed positive derivative
and a negative value before its stopping point, even with signed g1,h1.
Its rational bracket search therefore terminates. The Bmac and Taylor-box
searches have strict slack at their stated limiting compact boxes. In
particular the fixed-tail derivative is Dcore, not the derivative obtained
by incorrectly holding xi fixed. I independently differentiated the actual
fraction and verified this distinction. The cone substitution stays inside
the finite box, and the constants in (G17)--(G20) imply t'<=t/5, the signed
core bounds, the summed passive drift bound, and the player0 Quit bound.
The macro cone entry, scalar crossing and solo2 return satisfy all required
joins. Arbitrarily large fixed passive rewards only shrink the constructed
positive threshold; no uniform bound on those inputs is hidden.

I re-derived the pair mechanism's Phi/Psi identities, product-survival
formula, scalar iterates and limiting S. They remain valid when h1 and
intermediate t values are negative, or either pair premium is zero. The
four-vertex spectator test is the entire bilinear response inequality.
Nonnegative g1,K0 justify the passive player's induction, while the separate
immediate-pair exit correctly needs neither sign. The global v(u) return
satisfies A*a=Psi exactly, has positive initial return derivative, and meets
the r=1 barrier while a<1. The Lambda bound follows directly from v/a and
a>=u*Cs/(c*D). I also checked the pair-premium-independent sufficient cap
and the sharper fixed-matrix endpoint bounds97/560 and -6/11.

Both new finite-word consumers have exactly two seams and a designated
opponent absorption probability bounded below independently of word length.
Their signed annotations cause no change in Bellman telescoping. Every
unilateral replacement absorbs, which justifies native-to-original translation
for arbitrary signed own levels and the fixed-target uniform-horizon limit.
All queried entries, including those in a deviator's own row, are accounted
for. No exact infinite calendar or strategic compactness assertion is used.

### Exact counterexample-class narrowing

The uniform rectangle's five covering regimes are valid with their stated
closed endpoints. I checked the SAME c=9/5 cone on[0,27/50], its margins
7/2000 and7/250, and its strict macro-entry numerator. Exact rational
Bernstein recomputation reproduced both derivative ranges for the extended
return polynomial and both right-endpoint shooting bounds. The positive
v argument using its cubic and the strict owner0 macro slack also check.

The C^{1,1} graph transform has a complete weighted-C1 domain and the stated
small contraction bounds; no third derivative of the unknown graph is used.
Its parameter-stability estimate controls the vanishing physical boundary
as lambda approaches1 from below. In particular the errors are proportional
to (1-lambda)y+w, so pointwise positivity is not being substituted for a
uniform endpoint bound. The off-graph C1 return and shooting IVT use a
produced graph and intersect it exactly.

I independently expanded the finite-prefix contact identity and the exact
transverse derivative (F4). The normalized terminal equations divide by
beta^(m+1), with nonzero normal derivative; adjacent sheets have the claimed
opposite physical orientations and identical boundary values. At lambda_c,
the two macroscopic arms also have opposite strict return endpoints. This
last orientation is necessary and is actually proved, rather than inferred
from sheet incidence.

The obstacle band uses exact axis divisibility and positive critical-height
factorization. Its Lipschitz graph operator contracts in the weighted norm;
the stopped sector never evaluates a leading graph outside its wedge. The
clipped homogeneous candidate establishes the uniform shrinking-radius
tangent comparison. The local t_z sign supplies the stopped pair guard,
whose exact recurrence remains nonnegative, including the solo1 endpoint.
Initializing passive truncations with the invariant rational pair limit
makes the active/stopped boundaries join exactly. The simultaneous return
and shooting residuals then satisfy the required rectangle face signs.

The compact-cover argument does yield ONE positive threshold. Away from1,
finite phase counts and all normalized contact charts are locally uniform.
The lambda_c two-arm argument supplies a neighborhood of that contact.
For direct-pair returns away from it, the strictly positive first-order
guard gives a strict initial ratio margin; subsequent ratios increase. This
also handles a neighborhood of3, where a bound proportional to1-lambda/3
alone would not be uniform. The lambda>=3 branch instead uses eta<=1/2
and the independent pair corollary, without any lambda-dependent beta bound.
These regimes overlap and cover every positive ratio.

All freely lowered row0 coordinates are absent from prescribed payoffs and
enter their own replacement only through the fixed upper bounds. The solo2
control uses max(alpha,0)<=1. Thus the scale threshold is independent of
those negative magnitudes, all free grand coordinates and signed own levels.
The horizon threshold may depend on the full finite reward magnitudes, as
the statement explicitly permits. The actual finite words have exactly two
seams and deleted-player absorption; the full-cap and fixed-target arguments
apply to every branch. No uniform finite period or uniform horizon across
the entire raw reward class is inadvertently asserted.

The rational calibration e=1/100, h=1/25000 is inside the raw class and
separates it from the applicable broad existing producers. I checked the
complete sure-face census, including the sole-sure2 continuation term and
the original row2 lower bound. I independently expanded its N2 and N3
polynomials and checked their interval signs. The stationary proof exhausts
proper supports and its fully mixed inequality contradiction is valid.
Thus the full stationary and sure-root/punishment-tail selections fail,
not merely a selected root or tail.

The protected-player obstruction excludes every protected selection:
only0 is globally protected and trap13 misses it. The full premium core
is all four players. Both lower-ledger and support-filtered ledger arguments
exclude every admissible nonnegative weight, not one normalization. This
avoids the older h=0, positive-grand2 family that was already covered by
`exists_uniformEquilibriumPayoff_of_supportSpecific_strictLeave`.

I checked all fourteen child cases in the final universal child-debt
obstruction. The child123 indifference identities and outsider gain are
exact. In child023 the three value rows satisfy the Bellman equalities;
subdivision leaves the terminal singleton law (1/4,1/4,1/2) unchanged.
Adding max(e,h)*delta gives a full-cap supersolution. The prepended empty
date preserves vanishing child debts and gives outsider1 a gain at least3/4.
Consequently no proper child or finite choice of debt weights repairs the
universal lift. This is appropriately distinguished from a hypothetical
method selecting a specially favorable child profile.

The additional source comparisons also survive complete selections.
Positive proper participant premiums defeat weighted participant-upper,
forced-Quit-upper, product-low and ordered marked-block conditions under
every allowed support or ordering. Trap13 defeats weighted trap leavers;
the mixed joining-sign test fails on02. All three pair matchings fail a
required joining gap. Exact finite pair-only cycles are excluded: every
pair except13 has an active owner's Continue payoff strictly above its
positive Quit premium, every solo phase admits a later profitable joining
deviation, and a cycle using only13 gives player2 a negative payoff.
The sole nonnegative-inverse triple023 fails its exterior exit row.
The literal matching-sign neighborhoods have incompatible singleton signs.
These comparisons concern their proved raw regions, not an unspecified
extension of a qualitative neighborhood theorem.

For completeness, every nondiscrete response-invariant quotient fails at
linear coefficients, even allowing positive constant row scales. For
partitions 01|2|3, 1|02|3, 1|2|03, 0|12|3, 012|3, 12|03,
0|2|13, 02|13, 2|013, 0|1|23, 01|23, 1|023, 0|123, the first
merged pair and first two block coordinates have row-sum minors respectively
5,4,1,-6,-15,-1,3,-9,-5,-6,-10,7,-2. The full-block row sums
(5,0,-1,-2) are not positive rescalings. The discrete Gamma is R0: its
principal minors of size at least two are nonzero and every singleton
column has a negative outsider. At offset -(1,2,3,5), its complete
complementary-support census has the unique strict solution
x=(3,0,8,3), slack=(0,3,0,0), with support023 determinant5.
Its degree is therefore +1, excluding the negative-degree selector too.

No strategic input is assumed: the scalar root, limit annotations, finite
profiles and fixed payoff target are all produced from the raw table.
The source correspondence distinguishes existing exact block interfaces
from the new two-seam argument and identifies the actual terminal-Nash
convergence consumer. The finite predicates and stated Lean handoff are
faithful and do not place the conclusion in an assumed field.

The new counterexample exclusion is therefore a raw existence class
containing a concrete table outside these complete existing selections.
That is a substantive increment beyond the already covered predecessor,
and it passes the export boundary. It is not a universal classification of
all conceivable equilibrium certificates or a claim that any remaining
Fin4 table is a counterexample.

The new pair calibration e=1/100000,h=3/100000 satisfies all pair bounds
and the full earlier exclusion proofs, while h/e=3 violates both triple
mechanisms' bounds. The signed-chamber calibration bridge is also valid:
its specified constants do not change with small e,h, because the fixed
grand0 reward10 remains Mquit and the other relevant background data are
fixed. Thus its positive choice of e,h is not circular. The attached-pair
singleton template does fit Gamma under roles(3,1,0,2), but every required
nonpositive proper participant cap fails on these calibrations. The broader
one/both-joint-premium results retain those caps. The old deadlock block
also fails its zero joint row and weighted nonpositive row2 condition.
These checks exclude complete role and parameter selections, not merely
the examples printed in older packets.

The final handoff explicitly names the four raw predicates, UE-existence
theorem shape, matrix/search/root/return/seam lemmas, and actual terminal
convergence consumer. No strategic witness is an assumed field. The source
audit, exact boundary tests, fixed payoff target, and explicit overlap
calibrations satisfy the self-contained export gate for this consolidated
artifact. There is no remaining mathematical or handoff objection.

The new lambda=1 calibration with e=h<delta satisfies all existing complete
coverage exclusions recorded above but violates the quantitative ratio cap,
the general signed-background kappa=3/11200 cap, and the pair condition
beta<=eta/3. It supplies a literal additional exclusion. The first three
theorems remain useful because their independent-coordinate, signed-chamber
or unbounded-premium scopes are not subsumed by the homogeneous rectangle.
The consolidated packet passes the export gate as four related raw
producers sharing one semantic consumer; the unrestricted Fin4 problem
remains open.
