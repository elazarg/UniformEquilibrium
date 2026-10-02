# Inverse-class transformations and the boundary of reward transport

Author: CODEX_NOETHER_SUPPORT.

Status: completed bounded transformation test; no additional UE class
obtained. The actual single-pivot backward consumer does not enlarge the
matrix criterion. Its reward-limit closure adds only an already solved
homogeneous class. Membership stretching has different quantifiers and
does not supply the proposed fixed-table backward implication.

## 1. Question and semantic domain

For an arbitrary signed Fin4 quitting table r, let s_i=r_i({i}) and
Γ_ij=r_i({j})−s_i, so Γ_ii=0. Never and the live stage pay zero. Profiles
are independent complete behavioral strategies; deviations replace one
entire strategy. Write U_i for terminal payoff, B_i for the supremum
over every such response, E_r=max_i(B_i−U_i), and η(r)=inf_p E_r(p).
No response supremum or profile infimum is assumed attained.

The new criterion is the matrix class

    C={Γ : diagonal Γ=0, det Γ<0, Γ⁻¹≥0}.

The frozen [discounted-index theorem](../exports/INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md)
gives one fixed ordinary uniform-equilibrium payoff for every table with
Γ∈C, without restrictions on own singletons or nonsingleton rewards.
This note asks whether current literal reward transformations and their
actual backward consumers add tables outside this class AND outside the
already solved homogeneous branch. It does not presume that an affine
terminal shift preserves zero-Never play.

## 2. A genuine backward consumer whose matrix test is invariant

The current single-pivot normalization assumes s_k>0 and defines

    o_i=0 if i=k, and o_i=s_i otherwise,
    r̂_i(S)=(r_i(S)−o_i)/s_k.

It divides EVERY player's absorbing payoff by the same s_k. Never is
still zero. Under original all-player punishment normality P_i≤s_i,
`isUniformEquilibriumPayoff_original_of_singlePivotNormalized` produces
an original uniform payoff o+s_k v̂ from a normalized uniform payoff v̂.
This is an actual same-prefix punishment-tail lift, not an unchanged-law
affine identity. Its quantitative terminal error includes the normalized
source's joint Never mass and its square root. The positive canonical
pivot forces that mass to vanish along approximate equilibria.

The exact matrix identity, however, is

    Γ̂=Γ/s_k,      Γ̂⁻¹=s_k Γ⁻¹,
    det Γ̂=(s_k)^(−4) det Γ.

Thus Γ̂∈C if and only if Γ∈C. Applying the new theorem after this
normalization adds no table coverage, even when the genuine backward
consumer's normality and positive-pivot hypotheses hold.

More generally, a playerwise terminal affine change
r̂_i(S)=a_i r_i(S)+b_i with a_i>0 has Γ̂=DΓ, where D=diag(a_i).
Consequently Γ̂⁻¹=Γ⁻¹D⁻¹ and det Γ̂=(∏a_i)det Γ; C is invariant.
This is only a matrix statement for arbitrary b. No general zero-Never
strategic equivalence is inferred. The punishment-normal auxiliary shift
has a_i=1 and leaves Γ exactly unchanged. Relabeling players also
preserves C by simultaneous permutation of rows and columns.

Changing ONLY the own-singleton levels is different. If their increments
are h_i and every off-own coordinate remains fixed, then

    Γ̂=Γ−diag(h_i)(J−I).

It is not a rowwise terminal affine change, and neither of the cited
backward semantic consumers applies just from this identity.

## 3. Singular boundary limits are already homogeneous

**Matrix fact.** If Γ_n∈C and Γ_n→Γ entrywise, then either Γ∈C or
there exists x≥0, x≠0 with Γx=0.

Proof. Determinant continuity gives det Γ≤0. If Γ is invertible, then
det Γ<0 and inverse continuity gives Γ⁻¹≥0, hence Γ∈C.

Otherwise put B_n=Γ_n⁻¹≥0 and h_n=Σ_ij(B_n)_ij. Then h_n→∞.
Indeed a bounded subsequence of h_n would bound every entry of B_n;
after subselection B_n→B and ΓB=I, contradicting singularity of Γ.
The normalized matrices C_n=B_n/h_n are nonnegative with entry sum one.
By compactness a subsequence converges to C≥0 with entry sum one, and

    Γ_n C_n=I/h_n →0,        therefore ΓC=0.

Choose a nonzero column x of C. It is nonnegative and Γx=0, as claimed.
This argument needs neither a rank-three assumption nor a bounded inverse.

**Existing Fin4 consumer for the singular arm.** Normalize x to have
sum one. It is a literal homogeneous singleton witness: its residual
Γx is zero, hence is nonnegative and complementary. Suppose for
contradiction the incoming table had no UE. The SAME-table declaration
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
then supplies P_i≤s_i for every owner. Thus this x satisfies every
premise of `exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal`,
including a possible vertex support. That declaration gives an original
full-behavior uniform payoff, a contradiction.

One must not silently feed the full-space x to a consumer requiring a
witness on a reselected normal-core principal. The supported-normal
consumer just named takes the literal full matrix and the supplied
punishment floors, so it provides the exact bridge needed here.

Thus reward-limit closure of C gives no additional Fin4 coverage beyond
C and a CURRENT homogeneous consumer. This conclusion does not assert
that every matrix with a nonnegative kernel belongs to the closure of C.

The actual reward-limit implication itself is valid: if r_n→r uniformly,
then every prescribed or deviated clock profile has the same stopping
outcome law at r_n and r, and |E_(r_n)(p)−E_r(p)|≤2||r_n−r||∞.
UE at every r_n therefore gives terminal Nash profiles for r at all
errors, and the existing all-errors consumer selects one fixed UE target.
But the preceding matrix fact already classifies every possible new
singular endpoint of this operation as homogeneous. Degenerating positive
scalings to zero does not reverse this implication: the solved limiting
zero table does not supply solved approximating tables or vanishing
errors after division by the scaling factor.

## 4. Why the membership-stretch/fiber source is not a new backward map

The frozen [membership-stretch reduction](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md)
starts from the EXISTENCE of a counterexample in the normalized reward
cube. It chooses a global worst table r*, then a small common membership
stretch r*_α, then a maximum over the four own-singleton coordinates of
that stretched table. It may change the incoming counterexample table.
It does not state UE(r(s))⇒UE(r*) for an arbitrary selected s.

The exact construction leaves own singletons fixed before the fiber
reselection and has ||r_α−r||∞≤2α. Accordingly

    |η(r_α)−η(r)|≤4α.

At a fixed α>0, solving r_α by the inverse criterion gives only
η(r)≤4α. It does not give η(r)=0. If arbitrarily small stretches enter
C, their matrices converge to Γ(r), and Section 3 puts r in C or the
already solved homogeneous class. This infinitesimal variant therefore
also adds no new matrix coverage.

The final own-singleton reselection has no displacement bound 2α.
For every frozen 56-coordinate vector b, its own-singleton fiber even
contains s=(−1,−1,−1,−1), where all Never is an exact equilibrium.
The existence of a solved point in that fiber plainly does not estimate
max_s η(r(s)); the frozen reduction deliberately chooses the maximum.
To use the new theorem at that maximizer, one would have to prove that
the selected maximizing matrix is in C (or otherwise solve every
remaining maximizing possibility). The source theorem supplies no such
inverse sign or determinant condition.

Nor does the current membership debt comparison fill the gap. Its
declaration concerns the SAME unpadded one-date root, requires a sure
opponent for each queried owner and pointwise coherent supported
membership gaps, and only then orders full debts. The minimum-equality
declaration additionally requires actual final minimum attainment and
the original/final infimum ordering. None of these is produced by a UE
of a stretched table. No arbitrary profile or all-errors backward
consumer follows from those conditional root comparisons.

This is a conclusive stop for these specified compositions, not a
counterexample to a general backward UE statement: refuting existence
transport by producing a no-UE input would itself require a genuine
quitting counterexample. No such counterexample is claimed.

## 5. Exact tests and inspected sources

The singular boundary is inhabited. For t>0 set

    Γ_t=[0 1 0 0; 0 0 1 0; 0 0 0 1; t 0 0 0].

Its determinant is −t and its inverse is a nonnegative weighted
permutation matrix. At t=0 its rank is three and Γ_0 e_0=0. Thus the
singular arm of Section 3 is real, but it has exactly the existing
homogeneous witness; it is not a new index class.

The following source declarations and their hypotheses/proofs were
inspected under their imports, without a Lean build. Paths are relative
to the repository root.

- `quittingSinglePivotNormalizedReward`,
  `UniformEquilibrium/Quitting/Root/SinglePivotNormalization.lean`;
  `quittingProjectiveLCPMatrix_singlePivotNormalized`,
  `UniformEquilibrium/Quitting/Classification/LCP/SinglePivotNormalizationTransport.lean`.
- `exists_singlePivot_samePrefix_terminal_lift`,
  `UniformEquilibrium/Quitting/Punishment/SinglePivotTailLift.lean`;
  `isUniformEquilibriumPayoff_original_of_singlePivotNormalized` and
  `uniformEquilibriumPayoffSet_singlePivotNormalized`,
  `UniformEquilibrium/Quitting/Punishment/SinglePivotUniformPayoff.lean`.
- `exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal`,
  `UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProductionNormalDispatch.lean`;
  `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`,
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
- `quittingMembershipStretchedReward`,
  `abs_quittingMembershipStretchedReward_sub_le`, and
  `QuittingAgreesWithMembershipStretch`,
  `UniformEquilibrium/Diagnostics/Quitting/MembershipStretch.lean`;
  `quittingTerminalDeviationDebt_original_le_final_of_membershipStretch`,
  `UniformEquilibrium/Diagnostics/Quitting/MembershipStretchDebtComparison.lean`;
  `membershipStretch_sameRoot_minimumEquality_and_supportedSaturation`,
  `UniformEquilibrium/Diagnostics/Quitting/MembershipStretchMinimumEquality.lean`.
- The fixed-target/all-errors declarations in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`,
  already inspected in the preceding inverse-class review, provide the
  actual reward-closedness endpoint, not a profile-attainment theorem.

Next question, if this route is reopened: identify a NON-affine,
non-vanishing reward operation with a proved original full-regret/backward
consumer whose hypotheses are supplied independently of the desired UE.
The current normalization, small-stretch, and fiber-existence compositions
do not provide one. No export or additional conditional compiler is
proposed here.
