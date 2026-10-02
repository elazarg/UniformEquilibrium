# Signed-opposite four-cycle producer beyond the matrix-class union

Author: `CODEX_RENY`.

## Status and exact novelty boundary

Ordinary proof draft, not independently reviewed as a whole or Lean-checked.
This is a separate extension of the frozen positive-opposite prototype
`CODEX_RENY__HETEROGENEOUS_SINGLETON_PERRON_CYCLE_PRODUCER.md`; that file
remains unchanged. The prototype was subsumed by solved matrix chambers.
Here negative opposite comparisons are permitted, and an exact heterogeneous
example has full standard-Q, no homogeneous solution, and a non-projective-Q
proper principal. An explicit strict algebraic condition produces balanced
cycles on an open neighborhood of that example from the table alone.

The existing balanced-singleton and cyclic-tail semantic compilers are NOT
new. The circulant example by itself is already admitted by the existing
raw equal-hazard criterion once its literal tail is checked. The proposed
new coverage is the NONCIRCULANT raw-data class and its open neighborhood;
Section 7 records the bounded source comparison and its limits.

All rewards on nonsingleton coalitions and all own singleton levels are
arbitrary. No punishment value, preselected equilibrium, supplied balanced
cycle, public correlation, or detected deviation is an input.

## 1. Complete class statement

Players are Fin4 in cyclic order 0,1,2,3. For an arbitrary quitting reward
table, with zero payoff on infinite all-Continue, put

    sᵢ=rᵢ({i}),       Γᵢⱼ=rᵢ({j})−sᵢ.

Assume

    Γᵢ,ᵢ₊₁=−bᵢ<0,     Γᵢ,ᵢ₊₂=gᵢ∈ℝ,
    Γᵢ,ᵢ₊₃=hᵢ>0.                                  (1.1)

Unlike the prototype, gᵢ may be negative. Set aᵢ=gᵢ/bᵢ, dᵢ=hᵢ/bᵢ>0,
and calculate from these twelve raw coefficients

    X=a₀d₁+(a₀a₁+d₀)a₂,      Y=(a₀a₁+d₀)d₂,

    K = [ a₃X+d₃(d₁+a₁a₂)    a₃Y+d₃a₁d₂ ]
        [ X                   Y             ],

    Δ=(K₀₀−K₁₁)²+4K₀₁K₁₀,
    λ=(K₀₀+K₁₁−√Δ)/2.                             (1.2)

The minus sign in this root is intentional. K need NOT be a positive matrix
and no Perron theorem is used here. Require the following strict finite
inequalities, in the displayed order so all expressions are defined:

    Δ>0,       λ>1,       K₀₁<0,       K₀₀−λ>0;

    A=1/λ,     W₀=−K₀₁,       W₁=K₀₀−λ,
    W₃=A(a₂W₀+d₂W₁)>0,
    W₂=A d₁W₀+a₁W₃>0.                             (1.3)

These are table-computable conditions, not an existence quantifier over a
strategy or balanced cycle. They hold at the explicit tables in Section 5.

### Theorem draft

For every table satisfying (1.1)–(1.3), the following construction gives a
fixed uniform-equilibrium payoff v⁰. Moreover, for every e>0, integer H≥1,
ρ>0, and integer N₀≥0, it gives N≥max(H,N₀) and a product stopping law p
on {0,…,N−1,Never} with FULL terminal exploitability E_r(p)<e and

    R_p(N−H)<ρ.                                    (1.4)

In particular p is e-Nash against every deviation in its actual finite
menu. A positive own singleton is not needed for this direct producer;
the exact test tables below may be completed with sᵢ=1 for every i.

## 2. The signed spectral construction really produces positive hazards

The characteristic equation gives

    K(W₀,W₁)ᵀ=λ(W₀,W₁)ᵀ.

This is the usual 2×2 eigenvector (K₀₁,λ−K₀₀) multiplied by −1. Both
coordinates are positive by (1.3), and W₂,W₃ are positive by the remaining
two explicit inequalities. Algebraic substitution gives

    W₁=a₀W₂+d₀W₃,       W₀=a₃W₁+d₃W₂,
    W₂=A d₁W₀+a₁W₃,     W₃=A(a₂W₀+d₂W₁).        (2.1)

For example, eliminating W₂,W₃ in the first equation gives
W₁=A(XW₀+YW₁), the second row of the K-eigenvector equation; substituting
that relation in the second equation gives the first K-eigenvector row.
The signs of individual aᵢ do not affect these identities.

Normalize and define

    wᵢ=(1−A)Wᵢ/ΣⱼWⱼ,
    t_k=1−Σ[j<k]wⱼ,        q_k=w_k/t_k,
    c_k=1−q_k=t_(k+1)/t_k.                         (2.2)

Since λ>1 and all four Wᵢ>0, we have 0<A<1, Σwᵢ=1−A, t₀=1,
t₄=A, and 0<qᵢ,cᵢ<1. Repeating the four singleton roots with only owner
i active at phase i with hazard qᵢ has cycle survival ∏cᵢ=A, and its
first-absorption probabilities during one cycle are exactly wᵢ.

The four identities (2.1) are precisely

    Σ[j>i]wⱼΓᵢⱼ+AΣ[j<i]wⱼΓᵢⱼ=0.                 (2.3)

For i=3 the common factor A is canceled; A>0 justifies this step. Thus
the construction uses neither a nonnegative-matrix eigenvector selection
nor an invalid zero-survival boundary argument.

## 3. Actual values and the signed-opposite floor repair

Let vᵏ be the actual terminal payoff of this almost-surely absorbing cycle
when started at phase k. Then

    vᵏ=q_k r({k})+c_k v^(k+1),
    v⁰=Σⱼwⱼr({j})/(1−A).                          (3.1)

Starting just after phase i, the rotated cycle weights are wⱼ/t_(i+1)
for j>i and Awⱼ/t_(i+1) for j≤i. Equation (2.3), divided by
(1−A)t_(i+1), therefore gives v^(i+1)_i=sᵢ. Bellman at the owner's
own phase also gives vⁱ_i=sᵢ.

There are exactly two other phases. They satisfy explicit positive floors:

    v^(i+2)_i−sᵢ = q_(i+1)bᵢ/c_(i+1)>0,
    v^(i+3)_i−sᵢ = q_(i+3)hᵢ>0.                  (3.2)

The first identity comes from solving Bellman at the disliked next phase,
whose value is sᵢ; the second comes from Bellman at the previous phase,
whose continuation is the own phase with value sᵢ. Thus the middle
comparison gᵢ can be negative without violating ANY phase floor. The
prototype's backward-positivity argument is not incorrectly reused here.

All fields of `BalancedSingletonCycleCertificate` are now produced:
literal Bellman arcs, exact active-owner indifference, all-player singleton
floors, and positive opponent hazard for every player. No coarse exact-Nash
claim is made when collision rewards are arbitrary.

## 4. Full behavioral semantics and literal finite EA construction

Choose M>0 bounding the absolute value of every reward, including every
nonsingleton reward. Subdivide each coarse phase i into L dates with only
i active, each with hazard θᵢ=1−cᵢ^(1/L). Coarse values remain unchanged.
Within a phase each value is a convex combination of its coarse endpoints,
so every fine-date value is ≥sᵢ, and the active owner's value is exactly
sᵢ throughout its phase.

At a passive player's fine date, quitting yields

    (1−θᵢ)sⱼ+θᵢrⱼ({i,j})≤sⱼ+2Mθᵢ.

Continue equals its prescribed value and is ≥sⱼ. At its own dates both
endpoints agree. Therefore forcing any player to Continue through a finite
prefix preserves its payoff if the prescribed continuation is then restored.
Quitting at its last date can improve by at most 2M maxᵢθᵢ times the
opponent-deleted reach, hence by at most 2M maxᵢθᵢ.

The Never deviation has the same payoff as the prescription: opponents'
survival per full cycle is ∏[i≠j]cᵢ<1, so the bounded continuation term
vanishes after arbitrarily many forced-Continue cycles. All behavioral
deviations along the unique all-Continue history are mixtures of finite
stopping times and Never. Consequently full terminal regret is ≤2M maxθᵢ.
The target v⁰ is independent of L, and the checked balanced-singleton
uniform-payoff compiler therefore gives the fixed UE payoff v⁰.

For the direct finite claim, given e,H,ρ,N₀, choose L so 2M maxθᵢ<e/2,
then K≥1 so 4MΣcᵢ^K<e/2 and A^K<ρ. Censor each player's finite
stopping atoms at dates ≥T=4LK to Never. This moves marginal mass cᵢ^K.
A single product coupling changes prescribed values and full pure-deviation
caps by at most 2MΣcᵢ^K each; thus the censored law has E_r(p)<e. Its
joint Never mass is A^K. Choose N≥max(T+H,N₀). All its finite atoms lie
before N−H, so R_p(N−H)=A^K<ρ. Full regret was controlled BEFORE menu
enlargement; this is not false padding of a finite-menu Nash source.

## 5. Exact base and noncirculant example

The circulant base comparison matrix has offsets (−1,−1,6):

    Γ* = [ 0  −1  −1   6 ]
         [ 6   0  −1  −1 ]
         [−1   6   0  −1 ]
         [−1  −1   6   0 ].                        (5.1)

Here aᵢ=−1,dᵢ=6 and

    K=[55 −78; −13 42],      eigenvalues 16 and 81.

The selected λ is 16, not the larger eigenvalue. Conditions (1.3) give
W=(78,39,39/2,39/4), hence A=1/16, w=(1/2,1/4,1/8,1/16), and
qᵢ=1/2 for every i. With sᵢ=1, the exact coarse values are

    v⁰=(1,4,2,1),   v¹=(1,1,4,2),
    v²=(2,1,1,4),   v³=(4,2,1,1).

An exact NONCIRCULANT comparison matrix changes only two entries in row0:

    Γ† = [ 0  −1  −9/10  29/5 ]
         [ 6   0  −1     −1   ]
         [−1   6   0     −1   ]
         [−1  −1   6      0   ].                  (5.2)

Now

    K=[541/10 −381/5; −121/10 201/5],
    eigenvalues 16 and 783/10.

All (1.3) inequalities remain strict. Again qᵢ=1/2, the first three coarse
values are unchanged, and v³=(39/10,2,1,1). Exact rational arithmetic checks
all sixteen Bellman entries, all owner equalities, and every phase floor.
No relabeling can make Γ† cyclically invariant, since its rows have
different multisets of off-diagonal entries. Nor can positive playerwise
rescaling repair the unequal within-row ratios.

An additional exact test genuinely uses UNEQUAL hazards:

    Γ‡ = [ 0 −1 −1  6 ]
         [ 9  0 −1 −1 ]
         [−1  4  0 −1 ]
         [−1 −1  4  0 ].                          (5.3)

Here K=[56 −44; −16 28] has eigenvalues12 and72; the construction gives
A=1/12 and q=(1/3,1/2,1/2,1/2). With sᵢ=1 the exact coarse values are

    v⁰=(1,4,2,1),       v¹=(1,1,3,3/2),
    v²=(2,1,1,3),       v³=(4,2,1,1).

All sixteen Bellman entries and all floors again pass direct rational
substitution. Thus the algebraic producer's unequal-hazard freedom is
exercised by an exact example, not only inferred from continuity.

## 6. Full standard-Q, no homogeneous solution, and failure of Q-bar

The following check is essential: being outside the old cyclic open-sign
input does not alone establish new matrix-chamber coverage.

All three matrices in Section 5 have STRICTLY POSITIVE inverses. For Γ* the
inverse is 1/1200 times the circulant matrix with first row (37,209,13,41).
For Γ†, exact arithmetic gives detΓ†=−2319/2 and

    (Γ†)⁻¹ = (1/11595) [370   2019   127    392 ]
                       [410    357  2021    121 ]
                       [130    396   358   2018 ]
                       [2090   123   404    334 ]. (6.1)

For the unequal-hazard Γ‡, detΓ‡=−781 and

    (Γ‡)⁻¹ = (1/781) [ 17  91   11   27 ]
                     [ 39  25  209   16 ]
                     [ 14  29   55  206 ]
                     [139   9   44   37 ].        (6.2)

Let B=Γ⁻¹ for any of these tables. Positivity makes B strictly copositive: for
nonzero x≥0, xᵀBx>0. Thus B has no nonzero homogeneous complementary
solution and is standard Q by the checked copositive-R₀ theorem.
The standard-Q property transfers back through inversion: for an arbitrary
right-hand side q, solve the B-LCP at −Bq. If its variable is w≥0 and
its residual is z=−Bq+Bw≥0 with zᵢwᵢ=0, multiplying by Γ gives
w=q+Γz. Hence z solves the Γ-LCP. This is an exact all-q proof, not a
finite numerical screen.

There is also no homogeneous simplex solution for Γ. If w=Γz≥0,
z≥0, and zᵀw=0, then z=Bw and wᵀBw=0. Strict copositivity gives
w=0 and hence z=0, contradicting simplex mass one.

For Γ* and Γ‡ the opposite principal on {0,2} is [0 −1; −1 0]. For Γ† it is
[0 −9/10; −1 0]. Both fail projective Q at q=(−1,−1): writing cemetery
mass α≥0 and singleton weights x,y≥0 with α+x+y=1, both residual
coordinates are nonpositive and include −α and a strictly negative
multiple of the OTHER singleton weight. Nonnegative residuals force
α=x=y=0, a contradiction. Thus the full matrix is NOT projective Q-bar.
The recursive normal core is all four players, since each player's
successor is a strict negative blocker retained at every layer.

The three examples therefore inhabit the exact full-normal-core,
standard-Q, nonhomogeneous, non-projective-Q-bar matrix regime. This is
a matrix placement statement, not an assertion of the stronger actual
terminal-gap/paid-port hard-source hypotheses.

Moreover all the conditions are strict and persist on an open neighborhood
in the twelve off-diagonal singleton comparison coordinates. Invertibility
and strict inverse positivity persist by continuity; the negative opposite
pair persists; the selected simple eigenvalue and every inequality in
(1.3) persist. Hence the new raw-data producer covers an actual open set
of heterogeneous matrices in this matrix regime, not only an isolated
circulant example. Own singleton levels and all 44 nonsingleton reward
coordinates remain free.

## 7. Bounded source audit and what is actually new

The matrix definitions and convention were read in
`Quitting/Classification/LCP/MatrixClasses.lean`, `Normalization.lean`,
and `QuittingRewardAdapter.lean`. `CopositiveQBridge.lean` supplies
`isStandardQMatrix_of_copositive_of_isR0Matrix` in exactly the row/sign
convention used above. The inversion step was proved explicitly; a narrow
inverse/Q search did not locate a preexisting named inversion lemma.

`CyclicSingletonOpenSignProducer.lean` has TWO distinct relevant interfaces:

- `QuittingCyclicSingletonOpenSignData` requires only its first forward
  comparison negative and all later ones nonnegative. Both tables fail
  that sign hypothesis.
- `hasQuittingCanonicalEqualHazardTailData_iff` only requires cyclic
  invariance, a supplied scalar survival, polynomial balance, and
  nonnegative closed tails. The circulant table Γ* DOES satisfy this
  existing exact criterion at survival1/2. Thus Γ* alone is an explicit
  certificate in an already-covered example, not novel UE coverage.

`CyclicSingletonTailData` in `CyclicSingletonTailProducer.lean` supplies
one tail function of the relative cyclic offset, with one survival factor
and a recurrence for every player and phase. That recurrence forces Γ
itself to depend only on the relative offset. Γ†, and general matrices
in the neighborhood just constructed, do not satisfy this input.

`CyclicSingletonEscort.lean` was checked at its definitions and theorem
list: it extracts a necessary escort cycle from supplied balanced-cycle
certificates; it is not a heterogeneous table-to-certificate producer.
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` remains the
existing semantic consumer for the object produced here. The direct
finite construction in Section 4 also makes every requested EA quantifier
explicit. The positive-opposite prototype's whole-class subsumption proof
fails here exactly because a proper opposite principal is non-projective Q.

The neighboring `CyclicKofNPlayerPhaseHazards.lean` was also checked:
`isUniformEquilibriumPayoff_of_finitePlayerPhaseNashCertificate` consumes
supplied hazards and exact root-Nash conditions at every phase. It does
not construct hazards from the singleton table, and arbitrary collision
rewards in the present theorem do not give those exact coarse conditions.
The earlier notebook `CLAUDE_BANACH__CYCLIC_SINGLETON_BALANCE.md`, Sections
D and its final review disposition, explicitly restricts its raw producer's
openness to the cyclic coefficient stratum; it does not supply the present
heterogeneous open neighborhood. This history is not substituted for a
checked declaration when assessing theorem truth.

Therefore the candidate novelty is an explicit finite algebraic producer
on a noncirculant open neighborhood that intersects the surviving matrix
regime. It is not a new supplied-cycle consumer, not an arbitrary-Fin4
producer, and not a literature-priority claim. A broader existing-producer
comparison and independent proof review remain necessary before export.

## Research corrections retained

During exploratory screening, two proposed proper-principal index tests
were corrected before being used in any theorem. A claimed failed LCP
direction for Γ* was also false: at q=(−1,1,−1,1), z=(0,1,0,1) is a
valid solution. These errors were communicated immediately; no finite
direction screen is used in the final all-q argument above. The positive
inverse calculation and exact LCP inversion replace that screening.

## Next independent check

Verify the signed eigenvalue branch and reconstruction, the two identities
(3.2), inverse positivity and Q inversion, the proper-principal obstruction,
and the claimed genuinely heterogeneous source scope. Then compare narrowly
against any additional raw-data cycle producer not already named here.
