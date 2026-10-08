# Independent review of FE1–FE4 and GF1–GF6

Reviewer: CODEX_MORSE. Ordinary mathematics, not Lean checking.

Reviewed [author notebook](../notes/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md),
from “FE: exact free-coordinate extension and complete-carrier preflight”
through EOF. Frozen FULL notebook SHA256:
`fce1fc790c3ee43a86f25b70737eaf1b78ac8f3bd711d3cc8e99515d7426d62e`.

Verdict: **mathematical PASS for FE and the unconditional global GF theorem;
new-counterexample-class/export coverage UNRESOLVED.** GF genuinely produces
both hazards from actual reward coefficients; it does not merely verify a
supplied root. Its original-game Q argument legitimately removes the two
additional direct-branch hypotheses. Neither this mathematical verdict nor
the complete FE2 carrier exclusions establish disjointness from the full
union of implemented and accepted existence producers. The author's current
internal, no-export disposition is appropriate.

## 1. Exact claims and inherited review

I reuse the independent mathematical PASS in
[my MP review](CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE__MP__BY_CODEX_MORSE.md),
including the full FOUR-variable Jacobian, exact rational intervals,
arbitrary signed absorbing-row translations, deleted-opponent contraction,
and fixed-profile uniform quantifiers. There is no need to replace that
Jacobian by a symmetric two-variable derivative or repeat its IFT calculation.

FE changes the raw class: sixteen singleton cells and eight scheduled pair
cells remain prescribed, twelve recipient-specific joining cells can only
decrease, and the other twenty-four cells are arbitrary finite reals. It
claims the already produced MP profile for every such completion and an open
used-coordinate extension with fresh rates.

GF is different. Its nine numerical parameters are seven strictly positive
numbers A,B,C,D,H,α,β and two arbitrary real numbers E,F, subject to
F<β+2√(Dβ). Four own levels s_i are arbitrary signed reals and four row units
λ_i are strictly positive. The raw singleton equalities, complete scheduled
rows, and twelve inequalities define the reward class independently of a
strategy. The direct conclusion under C>H and
Δ=(B+H)(C−H)−AD>0 is an exact proper period-two terminal Nash profile and one
fixed-target, same-profile horizon witness. The unconditional conclusion is
UE existence, not an asserted direct profile outside that branch.

In both cases the game has independent private coins, deterministic public
all-Continue live histories, first-nonempty-coalition absorption, live and
Never reward zero, and unrestricted unilateral behavioral replacements.
No public correlation or finite-deviation restriction is introduced.

## 2. FE: the free-coordinate inventory and ordinary open extension

For each recipient i, the actual prescribed payoff and unilateral cap use
exactly these nine cells:

- all four singleton rewards in that recipient row;
- its scheduled mate-pair reward;
- the opposite scheduled pair's passive reward;
- its two own-plus-one-opposite-owner pair rewards;
- its own-plus-the-opposite-pair triple reward.

These are nine distinct cells per recipient, hence thirty-six raw cells.
The complementary twenty-four are eight outsider entries on nonscheduled
pairs, twelve triple entries, and all four grand entries. UNUSED is therefore
a recipient-by-recipient statement, not a claim that no triple coalition
can occur after a deviation. For example, a triple formed by recipient0
does not expose recipient1's own cap to that triple reward.

On-policy coalitions are only singletons,03,12. A deviator can add at most
one quitter to at most two unchanged scheduled owners. The grand coalition
is consequently unreachable under EVERY unilateral replacement. At a
passive phase the four possible opponent subsets are empty, the two
singletons, and their pair; the listed three nonempty joining rewards are
the entire passive Quit endpoint. Lowering them can only lower that endpoint.
All policy identities are unchanged and all four strict MP cap margins
survive. Thus arbitrary finite completions really are harmless to this
particular profile and all its unilateral caps.

The IFT extension also follows. The four genuine hazard equations and four
passive margins depend only on this finite raw coordinate projection, or
on its centered version. Apply the already verified four-variable IFT there
and shrink for properness and the four strict margins. The other twenty-four
coordinates do not appear in either condition, so one common used-coordinate
radius works for all their finite completions. Large unused rewards can make
the reward bound and horizon threshold large; no uniform horizon threshold
over all completions is claimed. Arbitrary own offsets are handled by the
same actual absorption argument as MP, not by general UE affine invariance.

## 3. FE2–FE3: complete finite carriers, with their exact scope

I checked the fifteen-row FE2 table, its singleton differences and pair
joining gaps, and ran FE4's standard-library rational verifier. Its inventory,
sole grand trap, fourteen child witnesses, four base-gap polynomials, and
explicit stationary caveat all pass. These computations are evidence for
the displayed finite identities, not substitutes for the proofs below.

Every proper nonsingleton participant premium is negative, but all grand
participant premiums are +1. Thus the entire trap family is {I} and the
premium core is I. There is no protected participant, AllNever is not Nash,
and grand Quit is defeated by owner0's withdrawal to123, which pays3 rather
than2. The signed empty-core composition that invalidated MP's significance
does NOT apply to this table.

The trap exclusions quantify over the relevant COMPLETE weight sets. At the
grand row every nonzero nonnegative support-upper weight gives a strictly
positive sum. At T=023 the omitted player's grand premium is +1, so every
strictly positive trap weight has positive weighted leave charge there.
The unweighted larger-trap leave coefficient also has that sign. This rules
out the listed support-upper/weighted-floor/boxed-charge certificates; it is
not a universal impossibility theorem for all equilibrium constructions.

The host-to-unique-positive-joiner map h is the four-cycle
0↦3↦1↦2↦0, with joining gain1/2. Every proper nonempty child contains a host
whose positive joiner lies outside. Sure Quit by that host and Never by the
other child owners is exact child Nash with zero child debts and zero joint
Never, but its quiet parent lift gives that outsider gain1/2. This refutes
every finite-coefficient universal child-debt-plus-Never estimate on EACH
proper child. It does not exclude all selected safe child equilibria.

I also checked the singleton-base census against the actual floor screen in
`exists_uniformPayoff_or_singletonBase_pos_gap`, in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
The owner screen prices its empty-opponent Continue branch at the actual
`quittingPunishmentValue`. The other screens are precisely the free-player
Nash and outside-joining signs used in FE3.

For base0 the entire three-player free Nash set consists of the two printed
pure points and the printed proper point. The boundary reduction is valid;
the exceptional smaller quadratic root gives y>1 and is not a missing root.
At the mixed point t<2/3 implies y>4/5. Every original reward to recipient0,
including Never0, is at least−1; hence its actual punishment floor is at
least−1. The empty-event Quit-minus-floor gap is at most2. All nonempty
events containing3 have joining gap at most−1/2; all other nonempty events
have gap at most2. Therefore the exact floor-priced gap is at most
2−5y/2<0, as asserted. This uses the correct LOWER punishment bound.

For bases1 and3 the forced zero hazards and resulting unique sure quitter
follow from strictly negative free gaps. For base2 the exceptional w=1/5
indeed gives both remaining gaps−3/5; the proper-w case and w=1 case exclude
every other boundary or interior point. At every remaining pure point the
base owner strictly prefers withdrawing, with the stated gains.

Restricted free sets introduce no hidden accepted points: the outside join
screen supplies the omitted owners' Continue inequalities, so acceptance
would give a Nash point of the already classified full nonbase game. For a
base of size at least two, opponent survival is zero for each base member;
the floor is irrelevant. An accepted point is a full one-stage Nash point
with at least two sure quitters. Selecting one sure quitter as a singleton
base contradicts the same census. This matches the actual large-base
component definition and
`exists_uniformPayoff_or_persistentLargeBase_pos_gap` in that file.

Crucially, these are exclusions of semantically ACCEPTED points in the
induced finite carriers, not contradictions of the disjunctive declarations
themselves. Nor do they exclude FE2's exact contracting stationary profile
q=(0,0,1/2,1/2), whose actual target is (0,0,1/2,1/2). The author correctly
retains that caveat. Raising a free cap can defeat this selected stationary
profile without defeating all stationary profiles or every actual producer.

## 4. GF global crossing: endpoints, denominators, and signs

The strict hypotheses of the DIRECT branch are enough for every step. Put
h=H−β, T(a)=C−h(1−a), and ψ(a)=(1−a)T(a)−β. Both endpoint values of T are
positive. Moreover ψ(0)=C−H>0 and ψ(1)=−β<0. The polynomial is nonzero and
has a least zero a₀ in (0,1), with ψ>0 on [0,a₀). This least-zero choice is
legitimate even if the quadratic has two roots or h=0 makes it linear.

For den(a)=(1−a)[aT(a)+D(1−a)−Fa], direct subtraction gives

    den−aψ = D(1−a)²−Fa(1−a)+βa.

For 0<a<1, x=a/(1−a) is strictly positive and this is

    a(1−a)[D/x+β(1+x)−F]
      ≥ a(1−a)[β+2√(Dβ)−F] > 0.

The AM–GM calculation uses positive D and β and is valid for EVERY real F
under the stated strict threshold, including positive F. At a=0 the
difference is D>0. At a=a₀<1 the same strict interior calculation applies.
Since aψ≥0 throughout [0,a₀], den is positive throughout that closed
interval. Therefore b=aψ/den is continuous, vanishes at both endpoints,
and is strictly between0 and1 in its interior. There is no pole, hidden
denominator sign assumption, or unsafe endpoint limit.

I independently checked the continued good equation and the cleared bad
linearization; GF5's exact polynomial verifier also passes. The identity

    (1−a)(C_good−W_good)=aψ−b·den

holds without a reward-sign assumption on E or F. On the constructed branch
it vanishes. For g=C_bad−W_bad, b′(0)=(C−H)/D and

    g′(0)=A−(B+H)(C−H)/D=−Δ/D<0.

The α terms cancel in the derivative; omitting α here is correct. Since
b<1 even at the endpoints, W_bad has no pole on [0,a₀]. Thus g is continuous
on that compact interval, negative at some interior η near0, and strictly
positive at a₀ because b(a₀)=0 and g(a₀)=Aa₀. IVT gives a proper root strictly
between η and a₀. No uniqueness, smooth global selection, numerical search,
or externally supplied hazard is required. Both hazards are PRODUCED from
the nine raw coefficients for every direct-branch table.

## 5. GF all behavioral caps and fixed-target semantics

The active indifferences follow by substituting the actual scheduled joint
participant rewards and mate singleton rewards. In particular

    −Hb+(1−b)[−αb/(1−b)] = −(H+α)b,
    −Ha+(1−a)[βa/(1−a)] = (β−H)a.

All four passive Continue identities then hold by symmetry and the two
produced equations. For each good owner the THREE nonempty passive joining
cells are bounded by0, hence Q_good≤0<W_good. For each bad owner the actual
favorable singleton event, harmful singleton event, and double event are
priced separately using the three stated raw caps. At the selected root,

    Q_bad ≤ C_bad−(H+α)b²(1−a) < C_bad=W_bad.

The harmful bound is genuinely stronger than the old MP cap and is used
essentially. Positive favorable joins and unrestricted E are permitted;
they are not replaced by a minimum of rewards or a lower payoff ledger.
All twelve cap cells are accounted for.

These equalities and inequalities match the complete inputs of
`GameTheory.PairedCycle.twoPair_exact_terminal_and_fixedProfile`, in
`UniformEquilibrium/Quitting/Cycles/TwoPairExactCertificate.lean`. That is a
supplied-endpoint consumer, whereas GF supplies its proper hazards and ALL
endpoints from raw data. It is not evidence that GF was already a raw class
producer in the implementation.

Each player's unchanged opponents survive a two-date block with factor
κ_i=∏_{j≠i}(1−q_j)<1. The bound persists against every complete unilateral
behavioral replacement, including arbitrary private memory and Never. The
bounded Bellman remainder vanishes on iteration. Consequently the displayed
values are actual terminal payoffs and every unilateral payoff is at most
that value. This proves unrestricted terminal Nash, not merely a rootwise
or stationary-deviation statement.

Actual deleted-opponent absorption also makes row affine transport valid:
for prescribed play AND every unilateral replacement the terminal law has
total mass1. Thus original terminal payoffs are s_i+λ_i times the normalized
payoffs, and positive λ_i preserves gains. The zero Never payoff has not
silently been translated. The fixed original target is

    u_i=s_i+λ_i v_i,
    v=(X_bad,W_bad,W_good,X_good).

With κ=max κ_i<1, the opponent live-time sum is at most2/(1−κ), sufficient
for the author's K. Under the project's zero quitting-date reward convention,
delivery error is at most MK/N and finite-horizon regret at most2MK/N. Fix
the table, chosen hazards, profile and target BEFORE ε, and choose only the
horizon threshold after ε. Unbounded free cells affect finite M, not the
existence or these quantifier orders.

## 6. GF unconditional conclusion: original Q, not a normalized-game assumption

I read the actual declaration
`isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff` in
`UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`, together
with its receiver-row singleton convention and standard-LCP definitions.
It assumes only no UE in the ORIGINAL raw Fin4 game. There is no hidden
nonnegative-own, normality, supplied-punishment, or normalized-noUE premise.
The actual matrix is diag(λ)G because its off-diagonal entries are
r_i({j})−r_i({i}); the diagonal is zero.

Positive LEFT row scaling transports textbook Q exactly as stated. Given
an arbitrary offset q for G, apply Q of diag(λ)G to offset diag(λ)q. Its
residual is diag(λ)(Gx+q), preserving nonnegativity and coordinatewise
complementarity. This is the correct direction and convention.

If C≤H, offset (−1,−1,−1,−1) cannot even be feasible: the sum of the two
leaf images is (C−H)(x₀+x₁)−D(x₂+x₃)≤0 but feasibility requires at least2.
So Q forces C>H. If Δ≤0, take t>(C−H)/A and offset (−1,−1,−t,−t).
Core feasibility individually forces x₁>0 and x₀>0, since A>0 and all
other core entries are negative. Complementarity therefore gives the TWO
core equalities, whose sum is

    A(x₀+x₁)=2+(B+H)(x₂+x₃).

Substitution makes the sum of the leaf images

    2(C−H)/A+(Δ/A)(x₂+x₃) ≤ 2(C−H)/A < 2t,

contradicting leaf feasibility. Equality Δ=0 is also excluded. This uses
complementarity rather than mistakenly treating a positive-image simplex
point as a homogeneous LCP root.

Bare original noUE thus forces the direct branch on the SAME raw table.
The global producer then contradicts that assumption. This proves the
unconditional GF raw class theorem, including arbitrary signed own levels,
without assuming general affine UE preservation. Off the direct branch it
proves existence by contradiction; it does not furnish the direct rates or
a predetermined direct-branch target there.

## 7. Coverage: valid exclusions, actual overlaps, and the remaining gate

The original MP empty-core objection is accepted and correctly retired.
FE2's grand trap means that objection alone no longer dismisses FE. GF
likewise permits positive participant premiums and arbitrary grand data.
This is a real correction of scope, not yet a complete novelty proof.

The FE2 complete trap, child, and persistent-base exclusions above are sound.
The matching-favorite raw families have a bijective favorite graph, whereas
FE and GF have the nonbijective graph 0↔1 with leaves2↦0 and3↦1. All relabels
and positive row affine changes preserve that distinction. The FE2 mixed
inverse columns and all printed principal-triple inverses agree with MP's
singleton matrix; selected inverse-column and positive-principal-inverse
criteria therefore do not rescue that FE2 witness.

I additionally checked the MATRIX-FREE weak-unit raw producer, not merely
its inverse-based predecessor. Its declaration is
`exists_uniformPayoff_of_oneSidedWeakUnitRawGuards`, in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`;
its exact lower ranking is `QuittingCrossedWeakLowerRanking` in
`GuardedCrossedResponseWeakHalfLower.lean`. A recipient's unique positive
singleton outsider forces its selected passive partner to be that favorite;
otherwise the empty-own subset violates the lower ranking. At the only
remaining partner choices, FE2 violates the lower ranking as follows, using
centered values (row offsets cancel):

| recipient | required partner | outsider event | joining event | violated comparison |
| --- | --- | --- | --- | --- |
| 0 | 1 | 23 | 02 | 0≤−3/2 |
| 1 | 0 | 23 | 13 | 0≤−3/2 |
| 2 | 0 | 13 | 23 | 0≤−1 |
| 3 | 1 | 02 | 23 | 0≤−1 |

Thus EVERY ordered pair fails this raw test at FE2. The two-sided weak
lower-ranking variants also fail. This is an actual sixteen-comparison
producer exclusion, not an inference from Γ inverse alone.

There are nevertheless known covered subfamilies, which must be retained:

- Every FE completion or GF parameter table with empty premium core is
  already covered by the signed noUE single-pivot normalization followed by
  `exists_uniformEquilibriumPayoff_of_empty_quittingPremiumCore`, as detailed
  in the original MP review. Removing grand restrictions does not exclude
  this whole subset from the new class.
- GF allows equality in its favorable-pair caps. Some parameters and
  completions can therefore satisfy the already accepted two-pair
  nonnegative-mate-joining criterion on partition01/23. Failure on the chosen
  mixed partition03/12 alone would not exclude that alternative partition.
- FE2 itself has an exact contracting stationary equilibrium. A generic
  supplied-stationary consumer applies to that equilibrium, although that
  does not produce one throughout the raw FE completion family. No
  stationary NONEXISTENCE or complete stationary-architecture separation
  follows from the negative finite-carrier screens.
- General response-invariant quotient producers must use all actual
  reward rows, not just Γ's possible block sums. FE2's nonsingleton
  modification excludes the sole potential nondiscrete partition by the
  printed full-response witness. This finite FE2 exclusion is not uniform
  over all GF free completions.

The remaining obstacle is precisely the COMPLETE coverage gate. The
accepted raw circuit and cyclic-child producers, actual stationary guarded
producers, and existing full-reward/affine/free-coordinate neighborhood
producers must be compared at a concrete surviving table or subfamily.
For example, the implemented
`BelowSingletonJointPhaseFixture.exists_reward_supnorm_radius` in
`UniformEquilibrium/Quitting/Examples/BelowSingletonJointPhaseLocalPersistence.lean`
and `PairedCubicStationaryExample.exists_local_stationary_branch` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`
are genuine fresh-profile neighborhood producers, not raw-equality screens.
The accepted `TWO_JOINT_PHASES_FULL_TABLE_NEIGHBORHOOD` and
`FULL_DIMENSIONAL_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM` also include such scope.
Different singleton signs at their centers alone do not identify their full
existential input domains. Conversely, an unspecified local IFT radius does
not license asserting that it covers this arbitrary finite-distance table.
Their actual retained conditions or available explicit domains must be used.

I have not proved that this entire family lies in the old union, nor supplied
an exact member outside that complete union. The mathematical construction
should therefore be retained, but it presently has NO new-class export
endorsement from this review. That is a coverage question, not a missing
root, cap, sign-scaling, or behavioral lemma in GF.

Concrete next check: produce ONE explicit GF direct-branch table and complete
the old-producer selection-set/neighborhood comparison for that table,
including already accepted packets. A raw witness whose selected quiet
stationary profile fails is insufficient; the relevant producers' COMPLETE
inputs or carriers must fail. Until then, do not count FE or GF as an
additional counterexample exclusion.
