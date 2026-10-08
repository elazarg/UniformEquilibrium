# Independent review of the mixed-sign paired producer MP1–MP6

Reviewer: CODEX_MORSE. Ordinary mathematical review, not Lean checking.

Reviewed section: “A mixed-sign paired producer on the nonbijective
two-cycle-plus-leaves branch” through EOF in
[the author notebook](../notes/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md).
Frozen section SHA256:
`a59c1f3a57e4ba35c4dee353d257766dd9ab4cc544496c67b0d908bff0448aa7`.

Verdict: **mathematical PASS; counterexample-class/export significance FAIL
as presently demonstrated.** The exact absorbing profile and arbitrary-table
local persistence are sound. But an existing-production composition covers
the whole sufficiently small MP region, including arbitrary signed own
levels, not merely its positive-own subregion. A stronger exact-profile
conclusion on this already covered UE region does not pass the export gate.

## 1. Claim checked

The author gives all sixty coordinates of a native own-zero table z. A root
a of the explicit polynomial P in (1/3,3/8), and b=(a−a²−a³)/(1−a³),
produce an alternating schedule: pair03 uses hazards a,b at even dates and
pair12 uses hazards a,b at odd dates. The claim is an exact absorbing terminal
Nash equilibrium against every unilateral behavioral deviation, with one
fixed profile and target meeting the uniform finite-horizon contract.

The claim also includes every absorbing-row translation z_i(S)+s_i, for
arbitrary signed s, and one full centered reward-space neighborhood with all
four hazards produced anew. No public coin, bounded deviation class, assumed
root, or given continuation vector is used.

## 2. Exact table and endpoint check

I independently entered all fifteen rows, including all passive coordinates,
and formed each endpoint from its actual opponent-coalition product law.
The two active pairs are 03 and12. Every mate singleton is −1. Their joint
participant rewards are −3/2 for owners0/1 and −1/2 for owners2/3. Therefore
the active endpoints agree at

    X_bad=−3b/2,       X_good=−a/2,

with post-active continuations

    W_bad=−b/[2(1−b)],       W_good=a/[2(1−a)].

For every passive owner, the empty opposite-pair event uses its next active
value, the two singleton events use the displayed raw singleton rewards,
and the opposite-pair event pays zero. This gives exactly

    C_bad=a(1−b)−2b(1−a)−(3/2)b(1−a)(1−b),
    C_good=(3/2)a(1−b)−(1/2)b(1−a)
                                −(1/2)a(1−a)(1−b).

Writing F_bad=(1−b)(C_bad−W_bad) and
F_good=(1−a)(C_good−W_good), direct substitution gives

    F_bad(a,N/D)=a(a−1)P(a)/(2D³),
    F_good(a,N/D)=0.

These are literal policy identities, not singleton-only approximations.
The two corresponding passive Quit endpoints are

    Q_bad=−a−3b/2+3ab/2,
    Q_good=−a/2−b+ab/2.

In particular the triple rewards, which a passive deviator can create,
are included. The stated strict margins follow from a>1/3 and
3/16<b<1/5: W_bad>−1/8 while Q_bad<−1/3, and W_good>1/4 while
Q_good<0. No omitted coalition raises a passive Quit cap.

The exact IVT endpoint values are correct:

    P(1/3)=37/243,
    P(3/8)=−451543/2097152.

Both arguments for the rational b interval are valid. Convexity bounds the
lower-bound cubic above by its negative endpoint chord. The expanded
upper-bound polynomial is bounded below by 5/216. Root uniqueness is not
needed anywhere.

## 3. Full four-variable Jacobian, not a symmetric surrogate

For arbitrary proper q and raw r, I independently differentiated the four
polynomials in MP.5 before imposing q=(a,a,b,b). The resulting matrix is
exactly the stated four-by-four J. Each diagonal entry is zero, since the
passive identity for owner i depends on the other three hazards only.
The six printed expressions A,F,B+C,D+E,B−C,D−E all agree with that
actual differentiation.

The simultaneous-swap symmetry at the center splits J into the invariant
symmetric and antisymmetric two-coordinate spaces. The first block is
[[A,B+C],[D+E,F]]. The second has diagonal entries −A,−F and off-diagonal
entries B−C,D−E. Hence its determinant is indeed

    det J=[AF−(B+C)(D+E)]·[AF−(B−C)(D−E)].

There is no substitution of a two-variable derivative for the required
four-variable derivative.

I rechecked the interval calculation by exact rational monomial bounds.
The independently obtained intervals, all inside the manuscript's bounds,
are:

| Expression | Lower bound | Upper bound |
| --- | ---: | ---: |
| A | 231657/204800 | 9371/8000 |
| F | −13/27 | −485/1024 |
| B+C | −17309/12800 | −13161/12800 |
| D+E | −7/128 | 27/640 |
| B−C | −46679/38400 | −14177/12800 |
| D−E | 2107/1152 | 1233/640 |

The manuscript's looser bounds consequently imply
Δ_plus≤−281/640 and Δ_minus≥69/50. Thus J is nonsingular at every
chosen root in the rational rectangle.

Parameterized IFT legitimately applies to the four hazards and the
56-dimensional centered reward space. The active endpoint identities are
algebraic for every proper nearby hazard vector; IFT solves the four passive
policy identities. Properness and the four strictly positive passive Quit
margins persist after shrinking. Rewards absent from the identity equations
but present in Quit endpoints are covered by that same finite margin
shrinkage. No symmetry is imposed on the perturbed table.

## 4. Unrestricted terminal and uniform semantics

The four phasewise policy equalities and endpoint inequalities prove the
terminal Nash claim. Against any complete unilateral behavioral replacement,
the other three scheduled clocks still have independent geometric survival.
For the center their two-date survival factors are bounded by

    (1−a)(1−b)² < 169/384,
    (1−a)²(1−b) < 169/384.

These bounds do not depend on the deviator's memory, private randomization,
or choice to Never. Iterated conditional endpoint inequalities therefore
have a vanishing bounded continuation remainder. They bound every full
behavioral deviation, not just one-stage responses or finite deadlines.
The same contraction identifies the policy templates with the actual
prescribed terminal payoffs.

The bound E(τ+1)≤768/215 is sufficient for the stated finite-average error
MC/H under the project's convention that the live quitting date pays zero.
Thus terminal Nash gives finite-horizon regret at most2MC/H, with a fixed
profile and fixed target. Nearby profiles have a possibly different finite
geometric bound, which suffices for their own thresholds.

Absorbing-row translation is justified only after this deleted-opponent
contraction. Every prescribed and unilateral terminal outcome absorbs
almost surely, so translation adds exactly s_i to every such payoff. Never
does not create an exception. This establishes all signed translations
without appealing to a false general affine invariance of nonabsorbing
profiles.

The tracked consumer
`GameTheory.PairedCycle.twoPair_exact_terminal_and_fixedProfile` in
`UniformEquilibrium/Quitting/Cycles/TwoPairExactCertificate.lean` has exactly
the required properness, passive Continue identities, and passive Quit
bounds. Its declarations and imports were inspected. MP supplies its
strategic inputs rather than assuming them.

## 5. Decisive complete coverage check, including signed own levels

Every nonsingleton participant coordinate of the native table is at most
−1/2, while its own singletons are zero. Consequently, for every row
translation and every centered perturbation satisfying

    max_(i,S≠∅)|r_i(S)−r_i({i})−z_i(S)| < 1/2,

we have

    r_i(S)−r_i({i})<0       for every i∈S, |S|≥2.       (1)

There is no positive-premium trap. This is robust across ALL sixty raw
coordinates and ALL signed own levels. It is stronger than checking
one selected paired producer or one inverse-sign screen.

For nonnegative own levels, the checked declaration
`exists_uniformEquilibriumPayoff_of_empty_quittingPremiumCore` in
`UniformEquilibrium/Quitting/Classification/Existence/SignedPairCoreUniformPayoff.lean`
already gives UE. Its wrapper
`exists_uniformEquilibriumPayoff_of_empty_or_signed_pair_core_weakSameSign`
in `UniformEquilibrium/Quitting/Classification/Existence/SignedPairCoreRewardClosure.lean`
also includes this empty-core branch. The accepted mixed-premium-traps
criterion is vacuously satisfied as well; its complete trap family is empty.

The own-sign restriction does NOT leave a new MP region. Here is the exact
composition closing that apparent gap for any signed Fin4 empty-core table.

Suppose such a table r has no UE. Since the reward data are finite, choose
their finite absolute bound and apply
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`.
It produces a pivot p with s_p=r_p({p})>0 and the actual normalized table

    r'_i(S)=[r_i(S)−o_i]/s_p,
    o_p=0,       o_i=r_i({i}) for i≠p,

which still has no UE. Its own singleton vector is the nonnegative pivot
unit vector. The formula is the actual definition
`quittingSinglePivotNormalizedReward` in
`UniformEquilibrium/Quitting/Root/SinglePivotNormalization.lean`, and the
singleton identity is `quittingSoloReward_singlePivotNormalized` there.
For every participant coordinate,

    r'_i(S)−r'_i({i})=[r_i(S)−r_i({i})]/s_p.        (2)

Because s_p>0, every positive-premium relation, and therefore every trap,
is unchanged. The normalized table still has empty premium core. The
checked empty-core theorem now supplies its UE, contradicting the source's
`no_uniformPayoff` field. The contradiction proves UE for the original
SIGNED empty-core table.

This composition does not assume arbitrary row-shift invariance, transport
an unreviewed law, or infer proper absorption from an AllNever equilibrium.
It uses the actual bare-noUE normalization producer and its own checked
noUE preservation. For the strict MP region one can alternatively derive
empty core directly from(1) after normalization, without any general
core-invariance lemma.

Thus a whole centered open region of radius1/2 around every translated
MP center is already within the project's UE capabilities. MP's qualitative
IFT radius can of course be shrunk below1/2. No table outside that existing
region, nor any persistence radius reaching outside it, is demonstrated.
The arbitrary signed-own form therefore does not repair the significance
failure. Narrow failures of RawRegion, crossed matching, quotient degree,
or other named paired interfaces remain correct but insufficient for a
new existence-class claim. This stronger containment makes additional
screens of their complete selection sets unnecessary for this verdict.

## 6. Disposition and next question

Retain MP as a sound exact absorbing-profile/local-persistence construction
in the owned notebook. Do not export it as a new UE class or new
counterexample exclusion. Its genuine additional conclusion is an exact
absorbing period-two profile on an already UE-covered open region.

A future raw mixed-sign producer would need an explicit input table outside
the complete existing existence capabilities, in particular outside the
signed empty-core composition above, and a produced neighborhood or other
independent raw criterion around that table. Adding a positive participant
premium somewhere is necessary to escape the present simplest coverage
obstruction, but not sufficient for passing the full gate.

No Lean files, author text, exports, Git state, or shared index were changed.
