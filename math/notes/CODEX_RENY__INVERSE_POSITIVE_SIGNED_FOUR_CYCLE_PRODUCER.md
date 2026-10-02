# Inverse-positive singleton matrices and a positive cycle construction

Author: CODEX_RENY.

## Current status and question

Ordinary mathematics, not independently reviewed or Lean-checked. The
inverse-positive sufficient theorem in Sections 1–3 has a complete direct
proof. It answers the first falsification test positively: in the same
signed successor/predecessor cell, strict positivity of the full inverse
does produce all four positive hazards and all passive floors.

The coverage comparison is now proved in Section 6: negative determinant
forces the already exported small-root conditions; positive determinant
forces full projective Q-bar. Thus this is a clean matrix-based construction
but adds NO UE table coverage beyond that already available union. Section 7
also shows that inverse positivity is not necessary for the exported raw
spectral class. This bounded replacement mechanism is complete and stopped
as a new-class attempt. No new export or arbitrary-Fin4 claim is made.

The self-contained question is whether a matrix property can replace the
strict spectral tests in the frozen
`CODEX_RENY__SIGNED_OPPOSITE_FOUR_CYCLE_PRODUCER.md`. Its existing export
and all other authors' files remain unchanged.

## 1. Exact raw-table statement

There are four players in order 0,1,2,3. Each nonempty quitting coalition S
has an arbitrary real reward vector r(S); infinite all-Continue pays zero.
Players use independent private randomization and may deviate with any
complete behavioral strategy. Before absorption the public history at a
date is uniquely all-Continue; stopping laws on ℕ∪{Never} therefore encode
the full unilateral behavioral response space.

Let sᵢ=rᵢ({i}) and Γᵢⱼ=rᵢ({j})−sᵢ. Assume

    Γᵢ,ᵢ₊₁=−bᵢ<0,       Γᵢ,ᵢ₊₂=gᵢ∈ℝ,       Γᵢ,ᵢ₊₃=hᵢ>0.

Assume Γ is invertible and every entry of Γ⁻¹ is strictly positive.
The theorem asserts that these table hypotheses produce a period-four
balanced singleton cycle with every owner hazard in (0,1), and hence a
fixed uniform-equilibrium payoff. All own singleton levels and all
nonsingleton rewards are arbitrary signed real numbers.

In addition, for every e>0, H≥1, ρ>0, and N₀≥0, with H,N₀ integers,
they produce an integer N≥max(H,N₀) and an actual product law p on
{0,…,N−1,Never} with unrestricted terminal exploitability E_r(p)<e and
reach R_p(N−H)<ρ. This is not only a supplied-cycle or supplied-source
claim.

Normalize rows for the algebra only: let Gᵢⱼ=Γᵢⱼ/bᵢ,
aᵢ=gᵢ/bᵢ, dᵢ=hᵢ/bᵢ>0. Thus

    G = [ 0  −1   a₀   d₀ ]
        [ d₁  0  −1    a₁ ]
        [ a₂ d₂   0   −1  ]
        [−1  a₃  d₃    0  ].

Its inverse B=G⁻¹=Γ⁻¹ diag(b) is strictly positive. This normalization
does not change the actual reward table or any strategy; it only rescales
the balance equations by positive factors.

## 2. A positive two-dimensional crossing from the inverse

For 0<A<1 define the positive matrix

    P(A)=(1−A) [ d₁B₀₁    B₀₂/A ]
                [ d₁B₃₁    B₃₂/A ].

Let its Perron root be given explicitly by

    p(A)=(P₀₀+P₁₁+√((P₀₀−P₁₁)²+4P₀₁P₁₀))/2.

This continuous positive function is strictly greater than each diagonal
entry. As A↑1 every entry tends to zero, so p(A)→0. As A↓0,
P₁₁=(1−A)B₃₂/A→∞, so p(A)→∞. The intermediate value theorem produces
some A∈(0,1) with p(A)=1. This scalar is extracted from the actual finite
matrix; no cycle or continuation is supplied.

Set x₀=P₀₁>0 and x₁=1−P₀₀>0 at the crossing. The characteristic
identity gives P(A)x=x. Define a four-vector by

    W=(1−A) B (d₁x₀e₁+(x₁/A)e₂),

where e₁,e₂ are the coordinate vectors for players 1 and 2. Every entry
of W is strictly positive. The two selected coordinate equations P(A)x=x
give W₀=x₀ and W₃=x₁. Therefore

    GW=(1−A)(d₁W₀e₁+(W₃/A)e₂).

Its four rows read

    W₁=a₀W₂+d₀W₃,
    W₂=A d₁W₀+a₁W₃,
    W₃=A(a₂W₀+d₂W₁),
    W₀=a₃W₁+d₃W₂.                                  (2.1)

For the third equation, subtracting the W₃ term on the left gives
a₂W₀+d₂W₁=W₃+(1−A)W₃/A=W₃/A. All signs are literal. This is the
desired positive four-coordinate reconstruction without choosing a signed
eigenvector or presupposing its positivity.

The crossing is in fact unique, although uniqueness is unnecessary. Every
entry of P(A) strictly decreases with A. If A<A′ and y>0 is a Perron
vector of P(A′), then P(A)y>P(A′)y. The elementary positive-matrix
comparison gives p(A)>p(A′). Equivalently this follows by substituting
positive two-coordinate eigenvectors into the explicit Perron formula:
if ℓ>0 is a left Perron vector of P(A), multiplication of
P(A)y>P(A′)y by ℓᵀ gives p(A)ℓᵀy>p(A′)ℓᵀy. A positive left vector
is obtained from the same formula applied to the transpose.

## 3. Actual cycle, full deviations, and the finite output

Normalize wᵢ=(1−A)Wᵢ/ΣW, define t_k=1−Σ[j<k]wⱼ, and put
q_k=w_k/t_k, c_k=t_(k+1)/t_k. Then all q,c lie in (0,1), Σw=1−A,
and ∏c=A. A period with only owner k active at phase k has precisely
these first-absorption weights w. The equations (2.1), multiplied back by
bᵢ, give

    Σ[j>i]wⱼΓᵢⱼ+AΣ[j<i]wⱼΓᵢⱼ=0.

The actual absorbing-cycle value vᵏ satisfies

    vᵏ=q_k r({k})+c_k v^(k+1),
    v⁰=Σwⱼr({j})/(1−A).

Rotating its first-absorption weights and using the balance gives
vⁱᵢ=vⁱ⁺¹ᵢ=sᵢ. The other two phase surpluses are exactly

    vⁱ⁺²ᵢ−sᵢ=qᵢ₊₁bᵢ/cᵢ₊₁>0,
    vⁱ⁺³ᵢ−sᵢ=qᵢ₊₃hᵢ>0.

Thus every passive floor holds, even for negative gᵢ. Every player also
faces three positive opponent hazards per period. These are exactly the
fields of `BalancedSingletonCycleCertificate`; its existing checked
`isUniformEquilibriumPayoff` consumer gives the fixed target v⁰ for the
actual table, including arbitrary nonsingleton rewards.

For completeness the direct finite-output bound is the same literal
construction, not finite-menu padding. Fix M>0 bounding every reward.
Subdivide each owner phase into L dates of hazard θᵢ=1−cᵢ^(1/L).
Own fine-date endpoints remain equal; all passive Continue values are at
least sᵢ and Quit can exceed sᵢ by at most 2M maxθ. Forcing Continue
through a prefix and then restoring the prescribed tail preserves payoff.
Only the final pure Quit incurs this one endpoint error. Never is the
limit of these restorations because every deleted-opponent period product
is strictly below one. Consequently the full behavioral regret is at most
2M maxθ and the payoff is the fixed vector v⁰.

Choose L with 2M maxθ<e/2, then K with 4MΣcᵢᴷ<e/2 and Aᴷ<ρ.
Censor each marginal's dates at or after T=4LK to Never. This moves exactly
cᵢᴷ mass in marginal i. Product coupling changes each prescribed payoff
and every pure unilateral cap by at most 2MΣcᵢᴷ each, uniformly in all
later dates and Never. Hence the censored law has full regret <e and joint
Never mass Aᴷ. Taking N=max(T+H,N₀) proves the stated reach and menu
conclusion after full regret has already been controlled.

## 4. Exact early test: inverse positivity need not select the small root

Consider the actual comparison matrix

    Γ = [ 0 −4  0  1 ]
        [ 5  0 −2 −2 ]
        [ 1  9  0 −3 ]
        [−3  6  1  0 ].

It has determinant 1 and exact inverse

    Γ⁻¹ = [18 3 4 6]
          [ 5 1 1 2]
          [24 3 6 7]
          [21 4 4 8].

With b=(4,2,3,3), the old signed transfer matrix is
K=[8/9 1/2; 1/12 3/4], with eigenvalues

    (59−√241)/72<1,        (59+√241)/72>1.

Thus this table fails the old small-root strict tests. The inverse-based
construction instead selects

    A=(59−√241)/45∈(0,1),

and one exact positive vector is

    W=((√241−13)/6, (17−√241)/12,
       √241−15, (17−√241)/3).

Positivity uses 15<√241<17. Direct substitution checks all four balances.
Normalization therefore gives four strictly positive hazards, and the two
floor identities above check all sixteen phase values without ignoring any
player. All own levels can be set to 1 and every nonsingleton reward left
free. This is not being called new UE coverage before the matrix audit.

An exact random-integer screen of 100000 signed-cell matrices found 1485
with strictly positive inverses. Every one admitted a positive eigenvector
with eigenvalue >1 in at least one of the two transfer branches. Of those,
1438 had a mutually negative opposite pair. This is experimental support
only; Sections 1–3 prove the theorem independently of the screen.

## 5. Bounded source audit and next check

The route starts from `docs/TOOLKIT.md`'s balanced-singleton compiler and
matrix-class entries. The actual definitions and semantic consumer are in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean` and
`Quitting/Classification/LCP/QuittingRewardAdapter.lean`. A narrow inverse,
positive-matrix, and eigenvector search in the cyclic modules and
`CopositiveQBridge.lean` did not locate this inverse-column construction.
The explicit positive 2×2 crossing above needs only its displayed quadratic
formula and the intermediate value theorem; no literature theorem has been
silently imported.

The coverage comparison additionally uses the literal
`isProjectiveQMatrix_iff_standard_or_homogeneous` and
`IsProjectiveQBarMatrix` definitions in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`, and
`isStandardQMatrix_of_copositive_of_isR0Matrix` in `CopositiveQBridge.lean`.
These declarations were checked under their imports. The full projective
Q-bar consumer is
`exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` in
`UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`.
That semantic consumer also assumes punishment normality; the raw table here
has arbitrary signed own levels, so the hypothesis must not be dropped.
For the claim of already available Fin4 existence coverage, argue by
contradiction: no UE gives all-player punishment normality on the SAME table
via `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
The now-supplied normality and the established projective Q-bar property feed
the Snell consumer and contradict no UE. The direct cycle construction in
Sections 1–3 does not use this contraposition or any normality hypothesis.

## 6. Exact coverage split: no new class beyond the existing union

Write δ=detG≠0 and D=d₀d₁d₂d₃>0. Use the signed transfer matrix K
from the frozen producer, whose entries are

    X=a₀d₁+(a₀a₁+d₀)a₂,        Y=(a₀a₁+d₀)d₂,
    K₀₀=a₃X+d₃(d₁+a₁a₂),      K₀₁=a₃Y+d₃a₁d₂,
    K₁₀=X,                     K₁₁=Y.

Direct determinant/cofactor expansion gives

    detK=D,             δ=trK−D−1,
    K₁₀=δB₁₃,          K₀₁=d₂δB₀₂,
    K₁₁=1−δB₀₃.                                      (6.1)

For example detK=d₃d₂[(d₁+a₁a₂)(a₀a₁+d₀)−a₁X]=D. The relevant
cofactors are adj(G)₁₃=X, adj(G)₀₂=K₀₁/d₂, and adj(G)₀₃=1−Y.

### Negative determinant implies every old small-root test

If δ<0, strict inverse positivity makes K₀₁,K₁₀<0 and K₁₁>1.
Its discriminant is strictly positive. Also
K₀₀=(D+K₀₁K₁₀)/K₁₁>0, so both eigenvalues are positive. The larger
eigenvalue exceeds K₁₁>1, while

    det(I−K)=1−trK+D=−δ>0.

It follows that the smaller eigenvalue λ is also strictly above 1.
Because K₀₁K₁₀>0, λ is strictly less than both diagonal entries, in
particular K₀₀−λ>0.

The actual positive W constructed in Section 2 satisfies the old transfer
equation K(W₀,W₁)ᵀ=A⁻¹(W₀,W₁)ᵀ. A positive eigenvector with K₀₁<0
has eigenvalue less than K₀₀; therefore its eigenvalue is precisely λ,
not the larger root. The eigenspace is one-dimensional. Thus its first two
coordinates are a positive multiple of the old choice
(−K₀₁,K₀₀−λ), and reconstructing W₂,W₃ by (2.1) shows that the old
two remaining positivity tests hold as well. This is exactly the already
exported strict spectral producer, not a newly excluded matrix chamber.

### Positive determinant implies full projective Q-bar

If δ>0, B>0 makes all four principal 3×3 determinants positive, since
det(G with row/column j deleted)=δBⱼⱼ>0. Every cyclically consecutive
three-player principal, after positive row normalization, has the form

    T = [0  −1   a]
        [d   0  −1]
        [g   e   0],           d,e>0,

with detT=a d e+g>0. This covers every three-player principal after a cyclic
rotation of the four labels. If g≥0, its first unit vector is a homogeneous
simplex solution. If g<0, determinant positivity gives a>0, and

    T⁻¹ = (1/detT) [ e     a e    1  ]
                    [−g    −a g   a d]
                    [d e   −g     d  ]

is strictly positive. Hence T is standard Q: a strictly positive inverse is
strictly copositive and R₀, its standard-Q property follows from the checked
copositive bridge, and the inversion argument transfers Q back to T.
Explicitly, for any ξ, a B-LCP solution at −Bξ with variable w and residual
z=B(w−ξ) gives w=ξ+Tz, a T-LCP solution. The same argument gives standard
Q for the full G because its inverse is positive.

Every adjacent two-player principal has a nonnegative column and therefore
a homogeneous unit-vector solution. Neither opposite pair can have both
comparisons negative: a₀,a₂<0 would make

    adj(G)₁₁=a₀+a₂d₀d₃<0,

contrary to δB₁₁>0; likewise a₁,a₃<0 would make
adj(G)₀₀=a₁d₂d₃+a₃<0. Thus each opposite pair has a nonnegative
off-diagonal entry and a homogeneous unit-vector solution too. Every
one-player zero matrix has such a solution.

We have checked all nonempty principal sizes: full G is standard Q;
each three-player principal is standard Q or homogeneous; each smaller
principal is homogeneous. By the literal standard-or-homogeneous
projective equivalence, G is projective Q-bar. Positive row normalization
preserves these properties: replace an LCP right-hand side by its inverse
row scaling, leaving the nonnegative/complementary weights unchanged.
Therefore the actual Γ is projective Q-bar as well.

This proves the exact whole-family subsumption

    inverse-positive signed cell
      ⊆ old signed spectral class ∪ full projective-Q-bar class.

No negative-principal or Q-bar conclusion was inferred from a finite
direction screen. In the exact positive-determinant example of Section 4,
the four principal 3×3 determinants are 18,1,6,8. Three have a nonnegative
column; the remaining principal on {0,1,3} has a strictly positive inverse.
Its failure of the old small-root test therefore does not add UE coverage.

## 7. Inverse positivity is not necessary for the old spectral class

For completeness, even within negative determinant the proposed matrix
replacement is not an equivalent or weaker description of the whole old
class. The exact matrix

    Γ₀ = [ 0 −1  0  5 ]
         [10  0 −2 −7 ]
         [−5 11  0 −5 ]
         [−5  3  6  0 ]

has determinant −2440 and (Γ₀⁻¹)₂₂=−23/488<0. Nevertheless its normalized
transfer matrix is K=[36/5 −66/25; −5 11], with eigenvalues 5 and 66/5.
The old construction gives

    W=(66/25,11/5,11/10,11/25)>0,
    A=1/5,              q=(48/145,40/97,20/57,8/37).

These are exact substitutions in all four reconstruction equations; all
hazards are in (0,1) and the general b,h identities give every passive
floor. Thus inverse positivity is a sufficient matrix test and a useful
new direct construction, but not a strict weakening of the exported raw
tests and not an additional UE class after the coverage split.

## Disposition

The proposed full-inverse replacement passes as ordinary mathematics and
fails as a new-coverage mechanism. It is retained as a tool, not an export
candidate. No unresolved existence hypothesis has been repackaged as a
certificate field. A materially different extension would need to weaken
the inverse positivity used to produce the actual positive four-vector or
leave the present four-owner calendar; that is not asserted here.
