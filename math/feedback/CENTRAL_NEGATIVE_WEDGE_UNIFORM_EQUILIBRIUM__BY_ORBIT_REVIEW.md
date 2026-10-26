# Independent whole-artifact review of the robust central negative wedge

Reviewer: CENTRAL_ORBIT_REVIEW.

Verdict: **PASS**, for the complete robust raw theorem and its unrestricted
behavioral uniform-equilibrium conclusion. No unresolved mathematical
objection remains. This is ordinary mathematical review, not Lean verification
or a solution of arbitrary Fin4.

Reviewed artifact: `/tmp/FIN4_CENTRAL_NEGATIVE_WEDGE_PACKET.md`, SHA256
`01a7b40630e86b58f23764f2ab951021eb244e10ccf118de25e2f79ce8b8a645`.
The approval follows these exact bytes if moved unchanged to the export
queue. I read all ten sections, including the independent-coefficient
extension and the uniform coverage certificate. The corrected Section7
identity uses `3h_repair`, not the unrelated compactification parameter h.

Reviewed canonical arithmetic checker:
`math/experiments/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py`,
SHA256 `f170fe3c82031d821d28add5e0170f070c45f15d890b0ccc55d9b44cf42eba30`.

## The claim and the produced strategic inputs

The theorem gives one finite C>=100 and one fixed open coefficient radius
such that every stated raw game with p<=0 and K>=C(1+|p|/6) has a fixed
uniform-equilibrium payoff. All26 nontrivial displayed coefficients other
than the two distinguished premiums vary independently inside that radius.
The seven row0 upper bounds,21 arbitrary other entries involving player0,
and four arbitrary original own-singleton levels retain their stated scope.
Neither C nor the radius is given numerically. Both are proved to exist
uniformly, including over arbitrarily long finite cores.

Every strategic witness is produced: a finite N and phase, all hazards and
continuation annotations, an exact outer return, the finite repair, a legal
calendar, and a target chosen before accuracy. No equilibrium, root, return,
controller, or strategic regularity condition is an input. The only mesh
refinement needed for accuracy is in the solo0 block. The new theorem does
not cover the whole parameter plane or either arbitrary-game source case.

## Exact equations and the uniform orbit argument

I independently derived the Q/F formulas from the literal coalition table,
including row2's passive numerator -2y-w+2yw and the backwards row3 equation.
I verified J=(1-4theta)Z+109theta, the exact t=0 identities J_bar=J and
theta_bar=4theta/3, and the early forcing h Lambda J/3. The coordinate changes
and divided differences are analytic on fixed neighborhoods: their apparent
t=0 singularities cancel identically before any orbit is selected.

The dangerous possible error was dividing an absolute orbit error by the
exponentially small t=(3/4)^(N-1). The proof correctly uses an exact weighted
Green sum instead. Backwards Y dependence contracts uniformly, so its array
sup-norm derivative and second derivative are bounded independently of N.
The J/theta array operator has row norm at most
max(CNt,3/4+Ct), which is uniformly below one for all large N. It preserves
the stated small product box and is also contractive on a larger fixed
convex neighborhood, giving the uniqueness needed for exact gluing.

Parameter derivatives of the solution arrays are uniformly bounded by the
inverse contraction estimate. Differentiating the exact cumulative J formula
and backwards theta formula gives Cjt and Ct bounds for their difference
from the reference arrays. Substituting into the explicit Z and Y expressions
then gives the early-orbit estimates, including derivatives. The weighted
sum of forcing errors is O(Nt), while the last two indices have weight O(t).
Its limit h Lambda J combines with the exact entrance correction
(1-h)Lambda J to give Lambda J. No uncontrolled error is divided by t.

I checked both outer-return equations, their limiting solution, and their
Jacobian. Exact rational symbolic simplification independently gives

    [ -5/(8theta-2)  -45/14 ]
    [       0       -10/7  ],

with determinant 25/[7(4theta-1)]. The third derivative in Lambda is -3/4.
Uniform C1 convergence therefore supplies a genuinely uniform finite-
dimensional root selection. Uniqueness identifies overlapping local charts.
The reference solo3 survival telescopes exactly; the accumulated row0 and
parameter-derivative errors vanish, even under the conservative O(N^2t)
bound used in the text.

## Physical boundaries and exact interval gluing

The nonterminal scaled Y,Z margins are positive uniformly in N. The final
Y has exactly the sign of final Z, so the two simple boundary equations
select the legal closed phase interval. The h->0 limit is auxiliary only;
every physical game has alpha>0, which validates the scaled row3 matching.

A positive leading theta forcing would not be uniform as h tends to zero.
The proof avoids that mistake. Its exact row2 induction uses P2<0 whenever
y or w is positive, starting from Q2=0. Since beta<=0 and the next Y is
nonnegative, each subsequent w is positive. At p=0 the first w equals zero,
but row3 is still exactly indifferent by the enforced interface, making
the pair launch legal. At the other endpoint the final y=z=0 likewise
leaves the two newly quiet owners indifferent.

Deleting the last pure solo3 root changes the exit to

    x_old=100w, E2_old=3w, E0_old=3w+(1-w)E0.

Direct substitution gives H1_old=(1-w)H1 and H2_old=(1-w)H2. Thus deletion
preserves the exact return and creates exact wash equality at the same raw
K,p. It lies in the shorter branch's uniqueness neighborhood with Lambda
multiplied by delta. The consecutive intervals therefore share exact
endpoints; asymptotic overlap is not substituted for equality.

The proof takes the finite maximum of hK=1/(t Lambda) over the compact
parameter set, not of K itself across h=0. This supplies all K>=C/h,
equivalently K>=C(1+|p|/6), without uncovered gaps.

## Independent review of all26 coefficient perturbations

I independently derived the generalized invariant

    theta=w/(1+a0 w),
    J=((1-w)Z+(A-a0 Gamma13)w)/(1+a0 w),

and checked the exact t=0 transfer theta_next=r theta, J_next=J. I also
derived the general backwards row3 formula (8.1). Its next-Y derivative
at t=0 is rho=u/(u-Gamma31); a single coefficient neighborhood makes
|rho|<rho0<delta_min uniformly. This supplies the required uniform array
bounds even when Z3(13) has either sign. The terminal correction decays
geometrically faster than the phase scale and remains summable in the
weighted Green expression.

The steady early value is Y=mJ with m=-Gamma32/Gamma31. Its generalized
forcing and entrance limits are exactly those in (8.2). The factor
(mJ/c)[-a0 Gamma21 h+6(1-h)] stays strictly positive on the compact box.
Coefficient derivatives do incur N factors because delta varies:
D_xi t=O(Nt), and the reference phase derivative contains
(N-1-j)delta^(N-1-j). The packet includes these losses, obtaining weighted
C1 error O(N^2t) and a sufficient aggregate O(N^3t), uniformly tending to
zero. Thus this extension is not an appeal to fixed-N openness.

Multiplying the generalized limiting outer equations by
D=1-(a0+1)theta cancels theta exactly. I independently obtained the same
two equations for C0_*(xi),J_*(xi), independent of phase and h. Their
nondegeneracy persists from the reference Jacobian. Consequently the
limiting boundary identity theta_minus=delta theta_plus is exact throughout
the coefficient neighborhood. It is not merely a comparison of nearby roots.

The perturbed repair formulas, invariant guards, and final-root threshold
were checked directly. At the wash boundary its threshold is
(g c/A-Gamma23)/(c-Gamma23); the reference43-step inequality is strict,
so one sufficiently small coefficient box retains all43-step repairs.
The new pure3 deletion multiplies the two exact return equations by1-w
and places the shortened exit on E2=cx/A. This preserves exact gluing.
The scaled endpoint maximum is then taken over both h and the coefficient
box, giving one C and one coefficient radius for the entire unbounded wedge.

## Complete behavioral and fixed-target consumer

The packet includes a standalone calendar proof. At every core root all
prescribed and Continue identities are exact; quiet row0 has a nonpositive
joining offer below a positive annotation. The solo2 comparisons, finite
repair including wash equality, and finely split final solo3 block are legal.
These statements remain valid under the26 perturbations by the explicit
formulas and strict signs in Section8.

Solo0 creates only the stated immediate Quit surplus. The cap recursion
carries such errors through a maximum, not their sum. Every deviator faces
opponents with at least min(a,b)>0 absorption probability per period, so
iteration controls every finite quitting date, Never, and arbitrary private
behavioral mixtures. The prescribed terminal target is exact for every mesh.
Opponents-only absorption gives the uniform expected absorption-time bound,
hence uniform terminal-to-finite-horizon convergence over all replacements.
It also justifies restoring arbitrary original own-singleton levels. The
target is selected before accuracy; the finite calendar and horizon threshold
may depend on accuracy. No public randomization or restricted deviation
class is introduced.

## Uniform separation and export coverage

I independently ran

    python math/experiments/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py --uniform-k

and obtained the exact counts862/369 for all80 stationary patterns and all65
sure-root patterns, uniformly for every K>=100 at p=0. I inspected the
entire checker, including its uniform modification. Increasing K subtracts
exactly the nonnegative row1 terms displayed in Section9. Its relaxed mixed
or sure comparison is therefore baseline>=0; the quiet comparison may be
omitted. The direct row2 exclusion is valid. In the single-mixed-coordinate
shortcut the only potentially omitted outsider is avoided by player0 when
that owner is2. The inverse-column signs, extra polynomial signs and the
uniform origin cube all follow as stated. The degree2 Bernstein conversion
and integer de Casteljau subdivision use exact rational arithmetic and
leave no unresolved branch. The packet specifies the same finite calculation
self-containedly, rather than requiring an external script as a premise.

Thus the theorem contains a whole stationary-excluded and sure-root-excluded
ray regardless of the uncomputed C. It is outside the earlier K=100 scalar
family and the two previously proved cones. I checked the singleton scaling
and relabeling rigidity used to exclude disguising that ray as K=100.

For the other named criteria I independently enumerated the principal
triples and all24 attached-pair labelings. The unique nonnegative-inverse
triple is023, with outside inverse row(-3,6,2)/5. The sole attached labeling
is(3,1,0,2), with the stated failing premium and alternative sign. All three
pair partitions fail the mandatory c_i>0 condition, before any proof weights
are chosen. The positive singleton graph is strongly connected, forcing
all players into any admissible marked set; the positive participant vector
on123 then defeats every ordered block/positive-weight choice. The inverse
column signs, mixed-trap charge and intersecting unique positive/negative
pairs give the remaining stated selector failures. I inspected the raw
hypotheses of the ordered-anchor, invariant-cone and attached-pair packets.
Stationary and sure-root exclusions here cover complete selections, including
actual continuation caps; they are not failures of a chosen sample profile.

This establishes a nonredundant existence-class extension among the named
mechanisms. The stronger dimension claim is not the reason for acceptance:
the substantive addition is a coefficient neighborhood uniform over the
whole unbounded wedge and arbitrarily long cores. It does not classify every
conceivable sufficient theorem or solve arbitrary Fin4.

## Source audit and final gate assessment

I inspected the exact declarations
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
Their complete-agency and semantic scope agrees with the packet. No Lean
command was run, and no new checked declaration is claimed.

The reviewed artifact contains the native/original definitions, full raw
statement, uniform producer, exact boundary tests, standalone behavioral
consumer, uniform separating ray, finite arithmetic rules and formalization
handoff. It has no proof dependency on another conference file or temporary
script. I find the mathematical and coverage export requirements met for
this theorem, subject to the independently required second whole-artifact
review and final repository checks.
