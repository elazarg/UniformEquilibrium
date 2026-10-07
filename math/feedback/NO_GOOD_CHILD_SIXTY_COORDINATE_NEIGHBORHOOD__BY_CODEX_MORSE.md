# No-good cyclic-child neighborhood: independent review

Reviewer: CODEX_MORSE.

Review surface: “A genuine full sixty-coordinate neighborhood at the
low-ε interior” through EOF in
`../notes/CODEX_NOETHER__NONLINEAR_PHASE_ESCAPE_AND_BOUNDARY_GLUING.md`,
whole-note SHA256
`90a73608bcf3a2a1cda7317becbc4b3df6376dd6d8bacc8d231e0cd1017bcd08`.
The required canonical equations and complete source comparisons were
checked against the frozen negative-premium cyclic-child theorem. No
counterpart review was read. This is ordinary mathematical review, not
a Lean check or a final standalone-artifact seal.

Verdict: PASS on the raw full-neighborhood producer and its stated bounded
coverage claim. No unresolved mathematical objection or unproduced strategic
input was found. The result is not merely another choice of ε in the
fixed-row family: it covers unrestricted perturbations of all sixty reward
coordinates, including points outside every relabeling and positive
playerwise affine image of that family. The exclusions below concern
actual raw criteria and complete carrier selection sets, not every possible
supplied-root verifier or an unspecified neighborhood around some other
example.

## Exact scope

Put e=100/729, P=1−e, E=1+e. The complete center r* is

| S | r*(S), in player order0,1,2,3 |
|---|---|
| 0 | (1,0,0,0) |
| 1 | (2,1,4,0) |
| 2 | (2,0,1,4) |
| 3 | (0,4,0,1) |
| 01 | (E,P,3,−1) |
| 02 | (1,−1,P,3) |
| 03 | (P,3,−1,P) |
| 12 | (3,1,E,3) |
| 13 | (1,E,3,1) |
| 23 | (1,3,1,E) |
| 012 | (E,P,1,2) |
| 013 | (1,1,2,P) |
| 023 | (P,2,P,1) |
| 123 | (2,E,E,E) |
| 0123 | (1,1,1,1) |

For ANY fixed η>0, lower only r₁(12), r₂(23), r₃(13) from1 to1−η,
obtaining r^η. The theorem produces a full open reward neighborhood of
r^η on which a proper joint03/solo1/solo2 periodic profile is exact
terminal Nash against unrestricted behavioral deviations. The profile and
its actual original-game target are chosen once per table, before horizon
accuracy. They give same-profile uniform-payoff witnesses with a geometric
tail estimate. No reward equalities constrain nearby tables.

The additional source-separation assertion uses sufficiently small η>0
and then a sufficiently small neighborhood. It does not assert that every
large-η center still defeats the old raw criteria. No explicit common
radius over all η, and no optimal radius, is claimed.

## Independent algebra and the actual Jacobian

I recomputed the four derivative intervals and all six rational endpoint
evaluations in (O2). They agree exactly. In particular F_p>14, F_y>9,
G_p<−1, G_y>5 on the given positive rectangle. The displayed corner
signs bracket one F-root p(y) for every y in the interval. At the left
end F(41/200,y)<0 forces p(y)>41/200, and G_p<0 makes G at the
selected root negative. The right-end argument reverses these inequalities
and gives positive G. Thus the root is actually produced, not supplied.

On F=0 the derivative of the reduced G is

    (F_p G_y−F_y G_p)/F_p,

strictly positive. D=F_p G_y−F_y G_p>79. The crossing is unique in
this rectangle and lies strictly inside every proper-rate constraint.
The canonical formulas for z,w have positive denominators and produce
values in(0,1); the rectangle is strictly below the z=1 cap.

I checked the actual endpoint identity independently from the policy
recursion, rather than identifying four nominal equalities with Nash.
Let a=(1−p)(1−y), b=1−z, c=1−w and ρ=abc. With the original
four-vector rewards, write

    A=p(1−y)r(0)+y(1−p)r(3)+py r(03),
    B=z r(1),     C=w r(2).

Then V_A=(A+aB+abC)/(1−ρ), V_C=C+cV_A and V_B=B+bV_C.
The literal active gaps are

    K₀=(1−y)r₀(0)+y r₀(03)−y r₀(3)−(1−y)V_B,0,
    K₁=1−V_C,1,       K₂=1−V_A,2,
    K₃=(1−p)r₃(3)+p r₃(03)−p r₃(0)−(1−p)V_B,3.

Exact substitution gives (O4), for every proper rate vector, not only
at a zero. Eliminating H₁,H₂ gives precisely f=F/N and k=G/N,
with N=3(1−p)(1−y)(1+3y−p). Block elimination therefore gives
det ∂(H₁,H₂,f,k)/∂(p,y,z,w)=D/N. The reordering and negative
H₁ factor in (O4) give exactly

    det ∂K/∂(p,y,z,w)
       =−(1−p)(1−y)D/[N(1−ρ)⁴]≠0.

Terms differentiating the denominator disappear at the root because all
four numerators vanish there. This check would detect the common error of
using a nominal continuation annotation instead of the actual policy value.

The three modified coordinates appear in neither A,B,C nor any active
Quit endpoint. Thus the same root and Jacobian work at every r^η. The
policy values and actual K are smooth in all sixty rewards near this
proper root. The ordinary implicit-function theorem applies with those
sixty coordinates as unconstrained parameters and the four hazards as
unknowns. It supplies the required local root branch internally.

## Strict passive inequalities and the unrestricted consumer

At the center the only potentially binding low-ε passive comparison is
player1 at C. Lowering r₁(12) gives it strict margin ηw. The changes
at r₂(23) and r₃(13) improve already strict comparisons A2 and B3.
All other passive inequalities are strict: p,y,z,w are proper, e<1,
and H=(3−e)y−p>0. In particular the negative active joint values
are retained; no singleton floor is substituted for their Continue values.
All eight passive inequalities persist together with the four actual
active equalities. These are all twenty-four row/action tests.

Every player has positive-hazard opponents in the fixed three-row period.
After deleting any deviator, the period survival ρ_i stays below1 in a
sufficiently small neighborhood. Policy iteration therefore handles every
late pure time and Never. An arbitrary behavioral reply on the sole live
history is a law over those times, so the same bound covers it. No public
signal, restricted deviation set, terminal-only cap, or horizon-dependent
root is used.

With |r_i(S)|≤M, the direct bound C=3M max_i(1−ρ_i)⁻¹ gives
delivery C/N and unilateral finite-horizon gain2C/N. The initial live
date pays zero, as required by the literal quitting game. The target is
the actual phase-A payoff and does not change with accuracy. This is
consistent with the actual-value/profile requirements of
`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`; source presence
is not a Lean certification of these new identities.

## All65 concrete-base selection sets remain excluded

This is a complete carrier argument, not a continuation of one selected
finite Nash point. The literal definitions rechecked were
`quittingPersistentLargeBaseComponent`,
`quittingPersistentLargeBaseExcess_nonpos_iff`,
`quittingSingletonBaseOwnerFloorExcess`, and
`quittingSingletonBaseExcess_nonpos_iff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
The actual consumers are `exists_uniformPayoff_or_singletonBase_pos_gap`
and `exists_uniformPayoff_or_persistentLargeBase_pos_gap` there.

At r*, punishment is P in every coordinate: immediate Quit guarantees P,
and the adverse sure opponent gives at most P. The complete auxiliary cube
at continuation P has exactly the proper root(1/10,1/10,1/10,1/10),
as established by the full boundary census in the canonical proof. In
particular it has no sure coordinate. An accepted base/free point with
nonempty base would extend to a full root at P with that base sure:
free optimality comes from its finite Nash conditions, base signs from
the concrete excess, and every omitted nonfree player's Continue sign
is ALSO in that excess. The singleton owner is priced at actual
punishment, not a stationary-Never approximation. Thus this excludes
every disjoint nonempty base/free choice, including empty free sets.
There are3⁴−2⁴=65 choices.

Each induced finite Nash set is nonempty and compact. At r* its continuous
concrete excess is strictly positive everywhere, hence has a positive
minimum. For varying rewards its Nash graph is closed, because every
finite-game best-response inequality is continuous. If a sequence of
nearby rewards admitted excess tending to0, compactness of the free cube
would supply a subsequence with a limiting Nash point at r* and nonpositive
excess, contradiction. This argument needs upper closed-graph compactness,
not persistence or lower semicontinuity of any particular Nash point.

Actual punishment is1-Lipschitz in the reward sup norm. Every complete
profile/deviation payoff changes by at most that norm, uniformly; taking
the reply supremum and then opponent infimum preserves the bound. This
includes empty/Never events, whose payoff remains0. Therefore singleton
excess is jointly continuous in reward and free point too. Taking a finite
intersection handles all65 carriers. For sufficiently small η, a smaller
ball around r^η stays in this exclusion neighborhood. No supplied
punishment value or favorable Nash selector remains.

## All fourteen universal quiet-lift systems remain excluded

For thirteen proper child carriers the canonical sure-singleton or sure03
profiles have strict outsider joining inequalities, and positive rewards
for their sure owners. These finite strict signs persist. Delaying a
sole sure owner still earns its own singleton, while Never earns0;
this harmless equality does not break the exact child Nash assertion.

For child123, the active rates are exactly2/3 at r^η because the modified
entries occur only in passive tests. In active order3,1,2 and rate order
y,z,w, the three cycle-residual derivative matrix is

    ((0,3,−1), (−1,0,3), (3,−1,0)),

with determinant26. The actual active-gap Jacobian differs at the zero
by the positive common factor(1−1/27)⁻¹ in each row, so it too is
invertible. The three formerly binding low passive comparisons acquire
strict margins2η/3; the high comparisons were already strict. An actual
child root is therefore PRODUCED for every sufficiently nearby child
table by IFT, not supplied as a premise. Its deleted-player contraction
proves full-behavior child Nash and zero child joint-Never probability.

The omitted pivot's original gain at r^η remains

    (15−26e)/39 = 8335/28431 >0,

and it stays positive nearby. The other thirteen outside gains and child
strict signs also persist. Hence every child still has an actual zero-debt,
zero-Never witness with positive omitted-player debt.

The exact universal consumer is
`quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`.
It applies to EVERY child profile and every one of patient, deadline,
evaluated-security, terminal-security and cancellation certificates.
The witness makes both the weighted child-debt term and Never term zero.
Thus all five actual certificate kinds fail on each of the fourteen
carriers, regardless of coefficient magnitudes. This is stronger than
testing a fixed set of LP weights and is robust for the stated reason.

## Remaining raw-source scope and the affine-partition subtlety

I checked the source of the claimed persistence, rather than relying only
on the phrase “finite screens.” The strict center obstructions to favorite
matching graphs, signed-column inverse signs, pair partitions, positive
scheduled-pair premiums, proper premium cores and boxed trap sums all
persist after choosing η small enough. The trap123 has positive cyclic
participant witnesses; the greatest premium core remains all four players.
All players retain a strictly negative participant premium, so no protected
player exists. The global weighted-floor test at background0 forces all
three child weights to vanish, and the negative pivot premium at background3
then forces the pivot weight to vanish. These are strict finite witnesses,
not an appeal to compactness of an unbounded weight cone.

The actual conditional-range producer remains excluded uniformly over ALL
blockers and boxes: each child has passive singleton4 and every participant
reward at most1+e at r^η. The strict gap persists nearby. This violates
`IsQuittingConditionalFaceGapRange` in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`.
It also excludes the literal odd interval-blocker-core producer in
`UniformEquilibrium/Quitting/Classification/Existence/FiniteOddIntervalBlockerCoreRowAdapter.lean`:
every embedded odd core in Fin4 contains a child, and its required
C_i^+<H_i^- contradicts the same global extrema gap. The influence from0
to1 is−e at empty background and1−e+η at background2. Its opposite
strict signs and the nonzero affine-membership defect persist. Thus the
raw fixed-sign influence and componentwise affine-potential prerequisites
remain false, under all relabelings.

Response-quotient scaling requires an additional argument because positive
playerwise affine factors are not a priori bounded. Let Γ(r) be the
singleton-gap matrix and g_i=Σ_j Γ_ij. At r*, every g_i=1; these stay
positive nearby. The necessary block-row identities from
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`
imply that c_i g_i is common within each proposed block, where c_i>0
are its player factors. Rescale each block by this common positive
number. Then c_i=1/g_i for every player. Thus the normalized factors
converge to1, even if the original factors were unbounded.

There are only fifteen partitions. At the center the necessary identities
allow only the discrete partition, 0|123 and the indiscrete partition;
every other partition has a fixed nonzero identity defect. No new such
partition can appear along a convergent sequence of nearby tables.
The three surviving normalized quotient limits are respectively

    Γ*,    ((0,1),(−1,2)),    (1).

All are R₀ of degree1 with positive determinant, so the same is true
in a sufficiently small neighborhood whenever the response invariance
itself survives. Positive quotient-row scaling does not change these
tests. Consequently neither
`exists_uniformEquilibriumPayoff_of_responseInvariant_singletonSign`
in `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientStrategic.lean`
nor `finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`
can admit a nearby table through a degenerating affine scale. This supplies
the boundedness detail behind the notebook's brief persistence statement.

Finally, changing only r₀(1) to2+ζ with small ζ≠0 remains in the
produced open set. The singleton-gap sign pattern identifies row0 as
the unique row having two positive comparisons. Their ratio is1+ζ,
rather than1, and positive playerwise affine transformations preserve
that ratio. No relabeling removes the obstruction. Thus this table is
outside the entire affine/relabeling fixed-row completion family.
The new theorem excludes a genuine full-dimensional raw neighborhood,
not merely the old equality stratum.

## Scope of the verdict

No stationary-root nonexistence is claimed or needed. An existing theorem
that accepts a supplied root or supplied phase certificate does not produce
the four roots proved here. Conversely, no unspecified neighborhood from
another example is declared disjoint merely from differing center tables.
The result has been checked against the actual bounded raw criteria and
whole selection carriers named above and in its canonical source comparison.
The exact algebra, complete cap inequalities, all65 compact screens and all14
universal quiet-lift exclusions give a substantive PASS on this frozen
candidate. A subsequent standalone assembly still requires its own
byte-bound fidelity check; no exported or Lean-checked status is implied here.

## Final standalone-artifact check

Final artifact reviewed in full:
`../exports/FULL_DIMENSIONAL_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM.md`,
984 lines, SHA256
`a29f782168f49fd10519dd4148ff8fc300e5023497a8d4bd0c713a773c78ebb6`.
Verdict: PASS. No unresolved objection, dropped premise, unproduced strategic
input or mathematical dependency on another conference document was found.
No counterpart review was read. The earlier notebook verdict and this
stronger exact-center artifact verdict have distinct scopes.

The substantive assembly delta is the exact all-base argument for EVERY
0≤η<e, giving a specified rational center η=e/2. I checked it directly
against all fifteen literal reward rows, not from a continuity assertion
or an author's report. In hazards(h,x,y,z), the child gaps are exactly

    g₁=e(1−h)(1−y)(1−z)+(1−e)h+y−(3−e)z
                                              −η(1−h)y(1−z),

and its two cyclic rotations. The pivot gap is exactly

    −(1−e)x−y+(1−e)z+e(1−x)(1−y)(1−z).

These identities were recomputed by summing all eight opponent products
for each player with the empty event priced at P. All participant entries
are≥P when η<e; the same adverse sure opponent supplies the matching
punishment upper bound. Thus actual punishment really stays P.

The complete root census is valid. A quiet child x=0 forces z>0.
Its successor's nonnegative gap then forces (3−e)y<1, while the other
child's gap is strictly positive and forces y=1. This contradicts quietness.
A sure child x=1 makes the positive successor's gap at most−1. These
arguments use the η terms with their correct signs and eliminate EVERY
boundary child pattern, including several simultaneous quiet/sure hazards.

For proper children the common one-variable successor map has denominator
≥3−e−η>0 and derivative

    [1−(e+η)(1−h)+(e+η)(1−h)φ]/denominator >0.

Its numerator is positive, and denominator minus numerator is at least1.
A strictly increasing real map cannot have a nonconstant three-cycle,
so all three hazards equal r(h). The fixed-point equation has r derivative
at most−(2−e)+η<0 and h derivative at least1−2e>0. Its endpoint
signs give one proper r(h), strictly increasing. The pivot equation
e(1−r)³−r=0 then forces r=1/10. Substitution gives exactly

    h_η=(274/3645+9η/100)/(548/729+9η/100),

strictly between0 and1. Strict monotonicity also excludes the two pivot
boundaries, not only additional interior roots. At η=50/729 this is
h_η=593/5525. The resulting cube root has no sure coordinate, proving
the all65 base/free exclusion at this explicit center and, by the complete
compact-carrier argument, throughout a neighborhood of it.

The all14 universal quiet-child exclusions hold at every0<η<e too.
The thirteen sure child profiles are unchanged. Some indicated omitted
gains decrease from1 to1−η, but remain strictly positive; the other gains
are unchanged. Their child Nash inequalities remain valid. For child123,
the actual policy and active root are unchanged, and all three previously
binding passive margins become2η/3. The artifact includes the complete
active numerators and invertible actual Jacobian, so the perturbed child
profile is produced. The continued child and omitted gain therefore give
the universal debt/Never contradiction on a full reward neighborhood.

I also checked the finite raw comparisons at these explicit η centers.
The altered reverse pair joins are1−η>0, while all harmful/favorite
join signs remain strict. The boxed trap singleton sum is e−η>0.
The influence signs become−e and1−e+η and its affine defect becomes
1+η. The normalized quotient argument included in the artifact rules
out an escape through unbounded affine factors. R₀/degree1 and positive
determinants persist; it correctly does NOT claim that response invariance
itself is absent.

For an additional direct check against the implemented product-low raw
criterion, set q₀=0 and all three child hazards to any fixed t∈(0,1).
Each active child's expected participant premium is

    t[e−η+ηt] >0    for0<η<e.

Thus `hasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`
also fails strictly and locally. This is an exact full-product test,
not an inference from the existence of one positive participant entry.

The entire standalone includes the complete center table, IVT isolation,
actual four-gap determinant, all twenty-four action tests, Bellman
realization, unrestricted deviations and the initial-zero horizon estimate.
Its source comparisons are intrinsic and its external paths name production
sources rather than conference notes. The ζ perturbation and subball retain
the unique two-positive singleton row and a strict inequality between its
two positive comparisons; all affine/relabeling fixed-row copies remain
excluded on that subball. No common target for distinct tables, exact
finite-horizon Nash, radius uniform in η, arbitrary stationary census or
full Fin4 conclusion has been introduced by assembly. This is a genuine
full-dimensional raw producer and significant bounded counterexample-class
narrowing, as ordinary mathematics. It is not a Lean verification claim.
