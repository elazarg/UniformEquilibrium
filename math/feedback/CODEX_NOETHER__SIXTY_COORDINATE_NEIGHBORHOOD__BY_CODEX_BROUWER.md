# Independent review: full-coordinate negative-premium neighborhood

Reviewer: CODEX_BROUWER. Ordinary mathematics, not a Lean check.

## Surface, scope and verdict

I reviewed the subsection “A genuine full sixty-coordinate neighborhood
at the low-ε interior” through EOF in
[the author notebook](../notes/CODEX_NOETHER__NONLINEAR_PHASE_ESCAPE_AND_BOUNDARY_GLUING.md),
whole-file SHA256
`90a73608bcf3a2a1cda7317becbc4b3df6376dd6d8bacc8d231e0cd1017bcd08`.
I used the already independently checked canonical definitions and
corrected periodic consumer. No counterpart review was read.

**Soundness: PASS.** The reduced Jacobian really is connected to the four
actual active Bellman differences by the displayed exact identity. The
root is produced by exact rational isolation, not supplied. All eight
passive comparisons become strict, and all strategic inputs survive a
full sixty-coordinate perturbation. There is no remaining strategic gap.

**Significance: PASS for the stated bounded source comparison.** The
neighborhood contains tables outside the preceding fixed-row locus,
including all its relabelings and positive recipient-affine transports.
The actual persistent-base and universal quiet-child exclusions persist;
this is not a new name for an assumed regular policy. The assertion does
not exclude every unspecified neighborhood attached to another producer.

Keep the two parameter scopes distinct: the UE neighborhood exists for
EVERY fixed η>0, whereas the manuscript's simultaneous source-separation
argument uses sufficiently small η. Below I give an exact stronger
punishment-root calculation valid for 0<η<ε, supplying the concrete
choice η=ε/2=50/729 without a continuity argument for that center.
This is a coverage-proof strengthening, not a condition on the main IFT.

## Exact isolation and actual four-equation Jacobian

At e=100/729 I recomputed all four rational derivative enclosure
intervals in (O2) directly from the expanded polynomial coefficients.
They agree with the manuscript. I also checked all six displayed
endpoint evaluations of F and G. Since the rectangle lies strictly
before the z=1 cap, these signs select the canonical F crossing there.
The derivative bounds imply

    F_p G_y−F_y G_p>14·5+9·1=79.

Consequently G is strictly increasing along that local F branch, and
the opposite endpoint signs produce a unique root in the rectangle's
interior. This establishes regularity for that produced root; it need
not assert that every possible canonical root is regular.

Here is an independent check using actual policy values. Write r_j for
the full reward vector of singleton j, and r_03 for the joint vector.
For arbitrary nearby hazards define

    A₀=p(1−y)r₀+(1−p)y r₃+py r_03,
    ρ=(1−p)(1−y)(1−z)(1−w),
    V_A=[A₀+(1−p)(1−y)(z r₁+(1−z)w r₂)]/(1−ρ),
    V_C=w r₂+(1−w)V_A,
    V_B=z r₁+(1−z)V_C.

These are the unique ACTUAL policy values. The four active differences
are, in player order,

    K₀=(1−y)r₀,₀+y r_03,₀−y r₃,₀−(1−y)V_B,₀,
    K₁=r₁,₁−V_C,₁,
    K₂=r₂,₂−V_A,₂,
    K₃=(1−p)r₃,₃+p r_03,₃−p r₀,₃−(1−p)V_B,₃.

Substituting the canonical rows gives exactly (O4), for EVERY proper
hazard vector, not only at its zero. I checked the four rational
identities independently. The factor 1/(1−ρ) is necessary: inserting
the forced-Quit value at the active phase gives a discrepancy d_i;
the scalar policy-cycle correction changes the actual active gap to
d_i/(1−ρ), rather than leaving it equal to the annotated discrepancy.

For rows ordered (H₁,H₂,f,k), the (z,w) derivative block of the first
two equations is diag(u,d), with u=3(1−p)(1−y) and d=1+3y−p.
Its Schur complement is the derivative of the reduced pair (F/N,G/N),
where N=ud. At the root its determinant is D/N², giving the full
numerator determinant D/N. Reordering the four rows in (O4), retaining
the minus sign on H₁, therefore gives exactly

    det D_(p,y,z,w)K
      =−(1−p)(1−y)D/[N(1−ρ)⁴] ≠ 0.

This last determinant formula is used AT THE ROOT; derivatives of the
nonconstant prefactors vanish there because the numerators are zero.
Thus the reduced nonsingularity has not been mistaken for an unproved
nonsingularity of the strategic equations.

## Off-path changes and every passive test

The three lowered coordinates r₁(12), r₂(23), r₃(13) never appear in
the prescribed outcomes 0,3,03,1,2. They also never appear in an ACTIVE
player's forced-Quit endpoint: the two joint owners quit only with the
other scheduled joint owner, and each solo owner quits alone. Hence
the policy values, all four active equations and their Jacobian are
literally independent of the three lowerings.

Let H=(3−e)y−p and d=1+3y−p. At the full r^η table the eight
Continue-minus-Quit passive margins are exactly

| Phase/player | Margin |
|---|---|
| A/1 | (3−e)y−(1−e)p |
| A/2 | ep+η(1−p)y |
| B/0 | (1−e)z+(1−z)H/d |
| B/2 | (3−e)z |
| B/3 | p(1−e)/(1−p)+ηz |
| C/0 | H/d |
| C/1 | ηw |
| C/3 | 3H/d |

Every entry is strictly positive for each fixed η>0 at the produced
proper root. In particular C1 was the only previously binding full-game
comparison; it is now strict. This list also shows why the off-path
lowerings cannot hurt the full profile even for large η.

The actual value solution and every pure endpoint are smooth functions
of the four hazards and all sixty rewards while ρ<1. The four-equation
IFT therefore permits arbitrary small changes in all sixty coordinates,
not just changes tangent to the five canonical row equalities. Shrinking
the neighborhood retains proper hazards and all eight strict margins.
The twenty-four action tests then hold for each original nearby table.

## Original-game strategic consumer and quantifiers

The four actual policy recursions and active indifferences, together with
the passive inequalities, supply zero root Nash at every phase. Deleting
any player leaves at least two proper opponent hazards per period.
Therefore opponent survival contracts uniformly over every unilateral
behavioral replacement, including Never and unbounded delayed stopping.
The Bellman annotations are realized payoffs and the full terminal cap
comparison follows by iteration. No off-path strategy is silently fixed
on behalf of a deviator.

For each nearby reward table the resulting hazards and target are fixed
before accuracy or horizon is chosen. The same C/N delivery and 2C/N
Nash-error bounds follow from opponent absorption and the selecting-live-
date zero payoff, with C=3M max_i1/(1−ρ_i). No horizon-dependent IFT
root, common random phase, or exact finite-horizon Nash is claimed.

I checked the literal product and solo endpoint interfaces
`PairedCycle.rootSuccessor_eq_bellman` in
`UniformEquilibrium/Quitting/Root/PairedProductRoot.lean`, and
`quittingRootQuitPayoff_soloStationaryRoot_owner`,
`quittingRootContinuePayoff_soloStationaryRoot_owner`,
`quittingRootQuitPayoff_soloStationaryRoot_other` and
`quittingRootContinuePayoff_soloStationaryRoot_other` in
`UniformEquilibrium/Quitting/Root/SingletonRootEndpoints.lean`.
The exact strategic consumers remain
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
They consume the produced policy/root-Nash/contraction inputs; they do
not produce the missing scalar root, which this manuscript supplies.

## Child witnesses and whole-source stability

In child123 the actual active-gap NUMERATORS, in variables (q₁,q₂,q₃),
are

    q₂−3(1−q₂)q₃,
    q₃−3(1−q₃)q₁,
    q₁−3(1−q₁)q₂.

At q₁=q₂=q₃=2/3 their derivative is exactly the displayed matrix
with determinant26. Actual gaps divide these numerators by the nonzero
child-period factor 1−(1−q₁)(1−q₂)(1−q₃). The derivative at the zero
is therefore nonsingular as well. The three low-value passive margins
are 2η/3, and the other three are 2−2e/3. Thus this separate exact
child Nash, including opponent-only absorption, genuinely persists under
arbitrary nearby reward perturbations. Its pivot gain stays positive by
continuity; no profile from the full four-player IFT is substituted for
the child certificate.

The other thirteen child witnesses have strict joining comparisons and
positive sure owners. For a sole sure owner, delayed own Quit still gives
the same singleton, while Never gives zero; for a sure pair, deviating
faces the other sure owner. These exact behavioral comparisons persist.
The changed outsiders' gains become 1−η, so the coverage neighborhood
uses η<1. The joint03 witnesses and the child123 positive pivot gain do
not change at the r^η centers. The zero-debt/zero-Never contradictions
to the universal withdrawal consumer are therefore robust, not merely
approximate witnesses with possibly growing amplification weights.

For the full and partial persistent-base sources, compactness and the
closed graph of induced finite Nash are the correct directions of
continuity. The minimum excess cannot jump DOWN through zero near a
center with a strictly positive attained gap. Punishment is 1-Lipschitz
under the maximum reward norm: every full strategy payoff changes by at
most that norm, and taking response suprema and punishment infima retains
the bound. The component excesses therefore vary continuously in reward
data. I checked the actual floor and outsider components in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`,
in particular `quittingSingletonBaseOwnerFloorExcess`,
`quittingSingletonBaseExcess_nonpos_iff`, and
`quittingPersistentLargeBaseExcess_nonpos_iff`. Thus the argument retains
all induced Nash laws and all partial free carriers.

The other exclusions used in the canonical comparison have the claimed
robust defects. In the response-quotient test, positive affine row scales
do not create a hidden noncompact loophole: near the center every Γ row
sum stays positive, and a block identity forces row scales within that
block to be proportional to the reciprocal row sums. Dividing each row
by its row sum makes the necessary partition tests continuous. Finitely
many failed partitions stay failed; the three surviving candidate matrix
types retain degree1 and positive determinants. The remaining strict
pair-join, inverse-sign, premium-trap and influence failures persist too.

Changing only r₀(1) by a small nonzero ζ gives positive comparisons
1+ζ and1 in the unique two-positive row. Their equality is invariant
under positive recipient scaling, recipient translation and relabeling.
It is mandatory in the preceding canonical family, so the nearby table
is outside that entire fixed-row producer, not just its printed labels.
The open construction supplies the policy on such tables automatically.

## Exact optional coverage strengthening: a specified lowered center

The following independent calculation removes an unnecessary unspecified
smallness choice for the r^η CENTER, while leaving the nearby radius
existential. Fix 0<η<e=100/729. All participant rewards still exceed or
equal P=1−e, and each adverse sure opponent still gives passive0 and
joining P. Hence every punishment value remains exactly P.

With h,x,y,z denoting the cube hazards (not the phase rates), the modified
child difference is

    g₁=e(1−h)(1−y)(1−z)+(1−e)h+y−(3−e)z
                                −η(1−h)y(1−z),

with cyclic rotations for g₂,g₃. The pivot difference is unchanged.
If x=0, g₁≤0 forces z>0, since at z=0 its value is positive for η<1.
Then g₃≥0 gives (3−e)y≤max(e,1−e)<1, while g₂>0 forces y=1,
a contradiction. A sure child x=1 again makes g₂≤−1. Thus all
children are proper.

Put C=e(1−h), L=η(1−h), A=1−e and B=3−e. The common fractional
map is

    φ_h(r)=[C+Ah+(1−C−L)r]/[B+C−(C+L)r].

It maps [0,1] into(0,1) and has derivative
[1−(C+L)(1−φ_h(r))]/[B+C−(C+L)r]>0, because e+η<1.
The children therefore share a common hazard r(h), characterized by

    e(1−h)(1−r)²+Ah−(B−1)r−η(1−h)r(1−r)=0.

The left side is strictly decreasing in r and strictly increasing in h.
The unchanged pivot gap is e(1−r)³−r, which vanishes precisely at
r=1/10. Substitution yields the unique proper pivot hazard

    h_η=[274/3645+9η/100]/[548/729+9η/100] ∈(0,1).

Thus every root at the punishment vector is proper, explicitly excluding
ALL accepted persistent bases without selecting a convenient induced law.
For the concrete rational lowering η=e/2=50/729, that unique root is

    (593/5525, 1/10, 1/10, 1/10).

The other strict canonical exclusions and all fourteen child witnesses
still hold at this specified lowered table. Their persistence, followed
by the small nonzero ζ perturbation above, gives a fully specified center
for the source-separating neighborhood. No bound on its radius and no
blanket exclusion of other unspecified neighborhoods is asserted.

No repair to the frozen mathematical statement is required. A final
self-contained assembled artifact still needs its own exact-byte check;
this verdict does not cover future edits automatically.

## Final entire-artifact check

**PASS — ordinary mathematics, including original-game strategy production
and the explicitly bounded source-separating open region.** I read all984
lines of the standalone
[FULL_DIMENSIONAL_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM.md](../exports/FULL_DIMENSIONAL_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM.md),
SHA256
`a29f782168f49fd10519dd4148ff8fc300e5023497a8d4bd0c713a773c78ebb6`.
This is a bounded assembly/delta check against the independent substantive
review above; no counterpart review was read. No mathematical repair is
requested for these bytes.

The artifact retains the complete sixty-coordinate center, the literal
four actual Bellman-gap identity and its nonzero determinant, all twelve
policy equalities and all twelve alternative-action comparisons. The
three lowered rewards remain absent from the policy and active equations.
Their strict passive margins, especially the full-profile C1 margin ηw
and the child's three margins2η/3, are present. Thus the local theorem
still covers every η>0, even where a lowered participant reward is signed;
the narrower source-comparison interval0<η<e is kept separate.

The original reward table and original Never0 are retained throughout.
The four opponent-only period survival factors are strictly below1.
Their bounds are uniform over complete behavioral replacements, including
Never. The realized initial target, terminal Nash comparison, and the
initial-live-zero finite-horizon delivery C/N and Nash error2C/N are all
carried into the final statement. The named `PeriodicCompiler` consumers
are not being used to supply the local root or any missing raw data.

The assembly correctly incorporates the exact all-base proof for every
0≤η<e, not merely continuity from η=0. In particular the rational center
η=50/729 has the unique punishment-priced cube root
(593/5525,1/10,1/10,1/10), all proper. The no-sure-root consequence applies
to all65 disjoint nonempty-base/free-carrier choices, not only the fifteen
full complementary games. Its stability uses compact induced Nash sets,
their closed graph and the actual punishment value's sup-norm Lipschitz
bound. This does not replace punishment by stationary Never.

All fourteen deleted-child counterprofiles are still actual zero-debt,
zero-Never witnesses. The thirteen pure witnesses retain the appropriate
strict signs. The mixed child uses its own nonsingular actual active-gap
map, all six strict passive tests and opponent absorption. Consequently
the universal weighted-child-debt-plus-Never consumer cannot be repaired
by changing withdrawal kind, weights, floors or child carrier nearby.

I also checked the two expanded whole-source comparisons. For arbitrary
positive row scales the quotient identities force c_i g_i to be constant
within each recipient block, where g_i is the full singleton row sum.
Blockwise normalization therefore reduces them to the single bounded
choice c_i=1/g_i. This justifies continuity of the finite partition census;
it is not an assumption that unknown scales stay bounded. The surviving
normalized quotient matrices remain near Γ, [[0,1],[−1,2]] and[1];
R0 openness, local degree constancy and positive determinants exclude
the stated two raw quotient exits. Supplied nonzero quotient roots are
expressly not excluded.

For the added literal odd-interval screen I opened
`UniformEquilibrium/Quitting/Classification/Existence/FiniteOddIntervalBlockerCoreRowAdapter.lean`:
`finiteOddCoreContinuationUpper` takes the maximum over ALL nonempty
coalitions omitting the owner, while
`finiteOddCoreBlockerAbsentQuitLower` includes the empty background.
`IsLiteralStrictFiniteOddIntervalBlockerCore` requires the strict upper/
lower sandwich. Every embedded odd core in Fin4 has a child owner with
C_i⁺≥4 and H_i⁻≤1, so that exact raw premise is impossible, robustly.
The exclusion is correctly limited to this row-extrema adapter, not every
possible supplied stationary face certificate.

Finally, the ζ perturbation and radius inequalities really give a nonempty
open subball: its unique two-positive singleton row has unequal positive
entries, an invariant obstruction to the compared fixed-row family under
positive recipient affine changes and relabeling. The packet does not
claim to exclude unspecified neighborhoods of unrelated IFT theorems or
all stationary equilibria. Its full producer, finite source comparisons,
qualitative-radius quantifiers and strategic handoff are self-contained;
no mathematical proof depends on another conference note or an untracked
helper. No Lean verification, export promotion or arbitrary-Fin4 solution
is asserted by this verdict.
