# Full-floor obstruction for the word (0,1,2,0,1,3)

Author: CODEX_RENY.

## Status and exact scope

Ordinary mathematics, not independently reviewed or Lean-checked. The
natural strict singleton-sign cell of this six-phase word cannot supply a
new open raw-data existence class. Positive hazards and all literal floors
force both comparisons between its once-used owners to vanish and force
their remaining rows to be positive multiples. Every resulting matrix is
then homogeneous or projective Q-bar. The complete calculation is below.

This is a falsification of one proposed raw-data extension, not a general
impossibility theorem for repeated-owner cycles. Boundary cells where one
of the ten specified nonzero comparisons vanishes are not classified here.
No export or new UE class is claimed. All frozen exports remain unchanged.

## 1. Actual data and the tested producer

Four players independently choose Continue/Quit, with arbitrary real vector
r(S) on every nonempty absorbing coalition and payoff zero on all-Never.
Let sᵢ=rᵢ({i}), Γᵢⱼ=rᵢ({j})−sᵢ. All own levels and all nonsingleton
coordinates are arbitrary; behavioral deviations are unrestricted.

The tested deterministic owner word is

    phase:   0   1   2   3   4   5
    owner:   0   1   2   0   1   3
    hazard:  α   β   γ   δ   ε   ζ,

with every hazard strictly between zero and one. Only its indicated owner
may quit at a phase. Let c_α=1−α, and similarly for the other hazards.
Its actual period survival is A=c_αc_βc_γc_δc_εc_ζ∈(0,1).

We require actual cycle values satisfying Bellman, owner equality vᵗᵢ=sᵢ
when owner(t)=i, and every passive floor vᵗᵢ≥sᵢ at every phase. These
are the literal `BalancedSingletonCycleCertificate` fields, not just the
owner balance equations. Exact coarse root Nash is not assumed for
arbitrary collision rewards; a valid balanced cycle would feed its existing
fine-mesh/full-behavior UE consumer.

Consider the natural strict cell

    Γ = [ 0  −b   h   k ]
        [ d   0  −e  −f ]
        [−u   v   0   x ]
        [−z   t   y   0 ],

where b,h,k,d,e,f,u,v,z,t>0, and x,y are initially arbitrary real numbers.
These are exactly the strict signs required at the immediate next and
previous distinct owners by the floor conditions. A producer based on
strict reward inequalities in this sign configuration would have to handle
an open part of this cell.

## 2. Four floor comparisons force an exact collapse

Subtract s from every cycle value. Owner indifference and Bellman imply
zero surplus immediately after an owner's phase as well as at that phase.
For owner 2, therefore, the surplus is zero at phases 2 and 3. For owner 3
it is zero at phases 5 and 0.

Define the two positive block ratios

    X=α/(c_αβ),                  Y=δ/(c_δε).

Consider a generic coordinate with singleton comparisons (−u,v) at the
two-player block (0,1). Its absorbing surplus in the first block is

    −uα+c_αβv = u c_αβ(v/u−X),

and in the second block it is u c_δε(v/u−Y).

For player 2, the first block ends at its own phase 2, whose surplus is
zero. Thus its phase-0 floor gives v/u≥X. The second block begins at
phase 3, whose surplus is zero, and ends at phase 5 with nonnegative
surplus. Bellman across the block gives v/u≤Y. Consequently

    X≤v/u≤Y.

For player 3, the first block begins at phase 0 with zero surplus and ends
at phase 2 with nonnegative surplus, so t/z≤X. The second block ends at
its own phase 5 with zero surplus, so its phase-3 floor gives t/z≥Y.
Therefore

    Y≤t/z≤X.

All four inequalities must be equalities:

    X=Y=v/u=t/z=:R>0.                              (2.1)

Both blocks have zero absorbing surplus for both once-used owners. Their
surpluses at phases 0,2,3,5 are consequently all zero. Bellman for player 2
at phase 5 reads 0=ζx+c_ζ·0, forcing x=0. Bellman for player 3 at phase 2
similarly forces y=0.

Thus ANY certificate in this strict cell necessarily has

    Γ₂₃=Γ₃₂=0,          (Γ₂₀,Γ₂₁)=u(−1,R),
                         (Γ₃₀,Γ₃₁)=z(−1,R).       (2.2)

In particular a mutually negative opposite pair is impossible, as is a
generic perturbation of either cross comparison. Solving the six owner
equalities alone would miss this obstruction completely.

## 3. The remaining matrices are already covered

The repeated owners' exact equalities give four scalar relations:

    bβ=c_βhγ,       bε=c_εkζ,
    eγ=c_γdδ,       fζ=c_ζdα.                       (3.1)

Define the two positive thresholds

    r=be/(hd),                   s=bf/(kd).

Using (3.1),

    r=δ c_βc_γ/β,                s=α c_εc_ζ/ε.

Multiplying and using X=Y=R yields the exact identity

    rs=A R².                                       (3.2)

Since A<1, R>√(rs)≥min(r,s).

If R≤max(r,s), choose λ∈[0,1] with R=λr+(1−λ)s. The positive/nonnegative
vector

    Z=(R,1,bλ/h,b(1−λ)/k)

satisfies ΓZ=0 by direct substitution in all four rows. Normalizing its
strictly positive total gives a homogeneous simplex solution.

If R>max(r,s), both principal 3×3 matrices on {0,1,2} and {0,1,3} have
strictly positive determinants:

    detΓ₀₁₂=h d v−b e u=u h d(R−r)>0,
    detΓ₀₁₃=k d t−b f z=z k d(R−s)>0.

Each has a strictly positive inverse. For the first, for example, the
adjugate is

    [ e v   h v   b e ]
    [ e u   h u   h d ]
    [ d v   b u   b d ],

whose entries are all positive; the second is the same expression with
(h,e,u,v) replaced by (k,f,z,t). A strictly positive inverse implies
standard Q by the checked copositive-R₀ theorem and the explicit LCP
inversion argument: solve the inverse matrix at right-hand side −Bξ,
then interchange its nonnegative variable and residual.

The full 4×4 matrix is standard Q as well, despite its two proportional
rows. Scale rows 2 and 3 by 1/u and 1/z so both become (−1,R,0,0).
For any right-hand side ξ, if ξ₂/u≤ξ₃/z solve the standard LCP on
{0,1,2} and set the weight of player 3 to zero. Its omitted residual is
the residual in normalized row 2 plus ξ₃/z−ξ₂/u≥0. If the reverse
inequality holds, use {0,1,3} instead. Complementarity is unchanged in the
omitted zero-weight coordinate. This covers every ξ, not a finite screen.

The other two 3×3 principals have homogeneous unit vectors: on {0,2,3},
the column of player 2 is (h,0,0)≥0; on {1,2,3}, the column of player 1
is (0,v,t)≥0. Every two-player principal has a nonnegative column, including
the zero opposite principal {2,3}; so does every one-player principal.
Thus the full matrix is projective Q-bar.

Together the cases prove

    positive six-phase certificate in the strict cell
      ⇒ homogeneous simplex solution OR full projective Q-bar.

The recursive algebraic normal core is all four players: each row has a
strict negative witness retained at every layer (0→1→2→0 and 3→0).
Hence the homogeneous alternative is already covered by the complete
homogeneous normal-core producer. For the Q-bar alternative and arbitrary
signed own levels, the old semantic coverage uses the no-UE contradiction
adapter to same-table punishment normality, then the projective-Q-bar Snell
consumer; its normality hypothesis is not silently dropped.

No comparison with more specialized odd-core reward identities is needed
to prove this whole-cell subsumption: the matrix union already covers it.

## 4. Two exact rational full-floor checks

Take

    Γ_Q = [ 0 −1  2  2 ]
          [ 2  0 −1 −1 ]
          [−1  2  0  0 ]
          [−1  2  0  0 ]

and all six hazards equal to 1/2. The exact phase surpluses vᵗ−s are

    (0,1,0,0), (0,0,1,1), (1,0,0,0),
    (0,1,0,0), (0,0,1,1), (1,0,0,0).

All twenty-four Bellman entries, all owner equalities, and every floor
hold. Here A=1/64, R=2, r=s=1/4, so R²A=rs=1/16. Both relevant
3×3 determinants are 7 and this is the Q-bar alternative.

For the homogeneous alternative, take

    Γ_H = [ 0 −1  2/17   2    ]
          [ 1  0 −1/2   −1/10 ]
          [−1  2  0      0    ]
          [−1  2  0      0    ],

with hazards (1/10,1/18,1/2,1/2,1/2,1/2). Its phase surpluses are

    (0,1/10,0,0), (0,0,1/9,1/9), (1/17,0,0,0),
    (0,1/2,0,0),  (0,0,1,1),     (1,0,0,0).

Again all owner, Bellman, and floor identities hold exactly. Now A=17/320,
R=2, r=17/4, s=1/20, and the homogeneous simplex weights are

    (112,56,221,15)/404.

The two relevant 3×3 determinants are −9/34 and 39/10. Thus one bad
principal alone would not establish new coverage: the full matrix is on
the already covered homogeneous branch. Both fixture computations were
checked with exact rational arithmetic; the general obstruction does not
depend on numerical evidence.

## 5. Source audit and disposition

The actual certificate fields and their arbitrary-collision semantic
consumer were read in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`.
A narrow repeated-owner/six-phase search in the cycle and existence
subtrees did not locate the block-ratio obstruction above. No raw table
producer is inferred merely from the generic certificate interface.

The matrix conventions and standard-or-homogeneous projective equivalence
are those in `Quitting/Classification/LCP/MatrixClasses.lean`.
`isStandardQMatrix_of_copositive_of_isR0Matrix` in `CopositiveQBridge.lean`
supplies the pure matrix bridge. `HomogeneousProducer.lean` closes the
homogeneous normal-core branch without a punishment-floor hypothesis;
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` in
`CounterexampleNecessary.lean` records the corresponding counterexample
restriction. For the full Q-bar semantic branch use
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`
and `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` in
`UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`.

The six-phase strict-cell proposal is stopped as a new-coverage mechanism.
The exact failure is not an inability to solve the owner equations: full
passive floors force two return ratios to agree and collapse the two
once-used owners into proportional rows with zero mutual comparison.
Neither the thin boundary certificate nor its small-mesh consumer should be
renamed a new strict raw-data producer.
