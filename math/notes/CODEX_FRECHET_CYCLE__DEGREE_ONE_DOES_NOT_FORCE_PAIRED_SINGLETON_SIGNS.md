# Degree one does not force the paired singleton sign chamber

Author: CODEX_FRECHET_CYCLE.

Status: completed bounded normalization falsifier, ordinary mathematics,
not independently reviewed or Lean-checked. The full-matrix necessary
conditions R0 and integer LCP degree +1, together with exclusion from the
named matrix/singleton consumers below, do not force paired symmetric
signs. No nonexistence of equilibrium, exhaustive classification, or new
export is claimed.

## 1. Proposed reduction and exact rational counterexample

There are four players, arbitrary signed first-quitting rewards, zero
live/Never rewards, independent behavioral play and unrestricted behavioral
deviations. Write s_i=r_i({i}) and Γ_ij=r_i({j})−s_i. The question is
purely about the full zero-diagonal singleton matrix, not a selected
equilibrium root or a continuation annotation.

The proposed sign reduction would put every surviving strict-sign matrix,
up to simultaneous player relabeling and independent positive row/column
scaling, in the paired chamber: positive comparisons within two pairs and
negative comparisons across pairs, with every reciprocal pair having the
same sign.

Take instead

    Γ=[ 0   3   1/10  −1 ]
      [ 3   0    −1   −1 ]
      [−1  −1     0    3 ]
      [−1  −1     3    0 ].                             (1)

Its exact determinant and inverse are

    det Γ=549/10>0,

    B=Γ⁻¹=(1/549)[ 60 243 101  79 ]
                  [210  27  79   2 ]
                  [ 90  90  60 210 ]
                  [ 90  90 243  27 ].                   (2)

Every inverse entry is strictly positive. Nevertheless Γ_02>0 and
Γ_20<0. Positive row/column scalings preserve each entry's sign,
and relabeling only moves this asymmetric reciprocal pair. Thus (1)
cannot have the paired symmetric-sign pattern under the allowed changes.
All twelve off-diagonal entries are nonzero; this is not a zero-entry
boundary objection.

## 2. R0 first, then the exact degree computation

Suppose x≥0 and w=Γx≥0 satisfy x_iw_i=0. If x≠0 then w≠0 by
invertibility. Strict positivity of B gives x=Bw>0, so complementarity
forces w=0, contradiction. Therefore Γ is R0.

This argument is essential: uniqueness for one inhomogeneous LCP alone
would not prove R0.

For the test right-hand side b=−1, the unique complementary solution is

    h=B1=(161/183,106/183,50/61,50/61)>0,
    Γh−1=0.                                             (3)

Indeed any solution has w=Γx−1≥0 and x=B(1+w)≥B1>0, so w=0
and x=h. The ambient min map f_−1(x)=min(x,Γx−1) agrees with
Γx−1 near h. Hence its local integer degree is sign det Γ=+1.
R0 supplies boundedness and right-hand-side independence of total LCP
degree, giving

    κ(Γ)=+1.

The required degree facts are those in the reviewed
[integer LCP degree packet](INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md).
That packet is ordinary mathematics, not a claimed existing Lean degree
declaration. The nonzero degree also makes Γ standard Q by the existence
property of degree for every right-hand side.

## 3. Exact named-consumer comparison

This is a bounded comparison of literal hypotheses, not an assertion that
every reward completion avoids every sufficient theorem.

- Full normal core: choose blockers next=(3,2,0,0). They are distinct
  from their owners and Γ_i,next(i)=−1. Thus the exact fixed-blocker
  criterion gives normalCore Γ=all four players. No empty-core or
  smaller-core exit applies to this matrix.
- Full homogeneous and non-Q exits: R0 excludes the full homogeneous
  simplex witness, while κ=1 implies full standard Q. Since the normal
  core is full, the same statements hold for its reindexed normal matrix.
- Principal projective-Q-bar: the principal on {0,3} is [0,−1;−1,0].
  It has no nonzero nonnegative homogeneous complementary vector, and
  its image of a nonnegative vector cannot dominate (1,1). Thus it is
  neither homogeneous nor standard Q and is not projective Q. The FULL
  matrix fails projective Q-bar and does not meet the current unconditional
  principal-Q-bar Snell consumer. The same negative pair rules out full
  copositivity.
- Inverse-negative-determinant and integer-degree exits: the inverse is
  positive but the determinant is positive; κ is exactly the surviving
  value +1. Neither reviewed index sufficient criterion applies.
- Once-per-owner signed four-cycle: only the unordered pair {0,2} has
  opposite signs in its two orientations. A negative-successor,
  positive-predecessor Hamiltonian cycle would require four distinct
  such asymmetric reciprocal pairs. No relabeling can supply it.
- Literal cyclic open-sign producer: it requires exactly one negative
  off-diagonal comparison in every row (later offsets nonnegative).
  The negative row counts here are (1,2,2,2), so it cannot apply after
  relabeling or positive row/column scaling.
- Named paired raw region: its own/partner/quiet singleton bounds require
  exactly one negative singleton gap per recipient. The same row-count
  obstruction excludes it. This comparison is to its literal raw region,
  not every possible paired equilibrium or collision-dependent repair.
- The checked two-block singleton fiber requires the first owner to be
  indifferent between its own singleton and the second owner's singleton.
  All off-diagonal entries in (1) are nonzero, so that particular equality
  cannot be obtained by the allowed transformations.

Principal scopes must not be silently strengthened. The full standard-Q
matrix here contains the non-Q principal {0,3}. Full R0 is not hereditary
either: the principal {0,1}=[0,3;3,0] has homogeneous witness (1,0).
Extending that witness by zero to four players gives negative residual
coordinates at players 2 and 3, so it is NOT a full-matrix homogeneous
witness. Applying the full supported-normal consumer to that principal
witness would drop its actual outsider hypotheses.

Consequently a reward table with normalized singleton matrix (1) satisfies
the literal algebraic ResidualHardClass predicate: full nonempty normal
core, no homogeneous witness on that core, standard Q on that core,
and failure of projective Q-bar on the full matrix. This is not a theorem
that the table is a quitting counterexample.

## 4. Reproducible exact check

The following test contains the exact source matrix, inverse, degree-test
root, and finite sign checks. No floating-point evidence is needed.

```python
import itertools
import sympy as S
G=S.Matrix([[0,3,S.Rational(1,10),-1],[3,0,-1,-1],
            [-1,-1,0,3],[-1,-1,3,0]])
B=S.Matrix([[60,243,101,79],[210,27,79,2],
            [90,90,60,210],[90,90,243,27]])/549
assert G*B==S.eye(4) and B*G==S.eye(4)
assert G.det()==S.Rational(549,10) and all(x>0 for x in B)
h=S.Matrix([S.Rational(161,183),S.Rational(106,183),
            S.Rational(50,61),S.Rational(50,61)])
assert B*S.ones(4,1)==h and G*h==S.ones(4,1)
assert G[0,2]*G[2,0]<0
assert [(i,j) for i,j in itertools.combinations(range(4),2)
        if S.sign(G[i,j])!=S.sign(G[j,i])]==[(0,2)]
assert not any(all(G[p[k],p[(k+1)%4]]<0 and
                   G[p[(k+1)%4],p[k]]>0 for k in range(4))
               for p in itertools.permutations(range(4)))
assert [sum(int(bool(G[i,j]<0)) for j in range(4))
        for i in range(4)]==[1,2,2,2]
assert all(G[i,j]!=0 for i in range(4) for j in range(4) if i!=j)
assert G.extract([0,3],[0,3])==S.Matrix([[0,-1],[-1,0]])
assert G.extract([0,1],[0,1])*S.Matrix([1,0])==S.Matrix([0,3])
assert all(G[i,j]==-1 for i,j in enumerate([3,2,0,0]))
```

## 5. Declarations inspected and stopping point

Paths are relative to the repository root. The exact current declarations,
not stale module prose about whether a consumer is open, determine scope.

- `ResidualHardClass`, `StandardQMatrixSide`,
  `UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`;
  `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`, in the
  neighboring `CounterexampleNecessary.lean`: normal-core versus full
  matrix hypotheses.
- `IsProjectiveQBarMatrix`, `principalMatrix`,
  `isProjectiveQMatrix_iff_standard_or_homogeneous`,
  `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`.
- `normalCore_eq_univ_of_fixed_blocker`,
  `negativePairMatrix_not_projectiveQ`, in the neighboring
  `ElementaryMatrixObstructions.lean`.
- `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell`,
  `UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`:
  the CURRENT unconditional consumer requires full projective Q-bar.
- `pairedSingletonMatrix_not_projectiveQBar` and the literal residual-hard
  adapter in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`:
  the paired benchmark is a calibration, not a classification theorem.
- `SignedFourCycleSingletonData`,
  `UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`;
  `QuittingCyclicSingletonOpenSignData`, in
  `CyclicSingletonOpenSignProducer.lean`: the exact signs used above.
- `RawRegion` and its own/quiet singleton bounds in
  `UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`, and the
  named consumer `exists_exact_allSuffix_uniformPayoff_of_rawRegion` in
  `PairedCycleEquilibrium.lean`.
- `TwoBlockTargetSingletonConditions`, `firstOwnerSingletonRow`,
  `targetPayoff`,
  `UniformEquilibrium/Quitting/Examples/Cyclic/FinFourTwoBlockSingletonFiber.lean`:
  the required off-diagonal equality, not a generic two-owner criterion.

The failed implication is precisely the proposed paired-sign normalization
from these matrix conditions and named exits. No actual no-UE table was
constructed. The singleton cylinder allows arbitrary own levels and
nonsingleton completions, and some completions can satisfy other
reward-dependent consumers. No worldwide priority or exhaustive theorem
survey is claimed. This witness test is complete and stopped; the next
research mechanism must not assume reciprocal sign symmetry of the
remaining degree-one class.
