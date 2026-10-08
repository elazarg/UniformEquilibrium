# CODEX_NOETHER review of FE1–FE4 and GF1–GF6

Status: mathematical soundness PASS; additional existential coverage
UNRESOLVED. No export approval on significance. The ordinary Fin4 conjecture
and the canonical positive-full-floor consumer remain open.

Reviewed object: the FE and GF sections of
`notes/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`, frozen full-file SHA
`fce1fc790c3ee43a86f25b70737eaf1b78ac8f3bd711d3cc8e99515d7426d62e`.
That SHA was verified before and after the review. This review is independent
of the counterpart FE/GF feedback, which I have not read. It reuses my earlier
MP soundness PASS, not its failed significance conclusion. No author file or
export has been edited.

## Claim and semantics checked

The game is the original four-player quitting game, with independent private
randomization, publicly observed all-Continue live history, first nonempty
coalition absorbing, and zero live and Never rewards. All unilateral
behavioral replacements are allowed. The conclusions are exact terminal Nash
and fixed-target uniform equilibrium, not merely a root action test or a
bounded-controller equilibrium.

FE claims a complete raw completion family: sixteen prescribed singleton
coordinates, eight coordinates in the two COMPLETE scheduled pair rows,
twelve upper-bounded passive joining coordinates, and twenty-four arbitrary
finite coordinates. It also claims an open used-coordinate extension, with
an IFT radius independent of the free coordinates.

GF claims a nine-parameter raw reward criterion, allowing arbitrary signed
own values and positive row units. In its direct branch C>H and Δ>0 it
produces proper two-phase rates from actual coefficients. Outside that branch
it asserts UE existence using original-game singleton standard-Q necessity;
it does not assert an explicit two-phase profile there.

## FE soundness

1. The inventory 24 fixed + 12 bounded + 24 free = 60 is exact. On-policy
   absorption uses only singletons and the two scheduled pairs. A passive
   owner's Quit cap uses precisely its singleton and three listed joining
   entries. Lowering those three entries only improves its inequality. Thus
   the original four active equalities and four passive inequalities remain
   valid on the entire stated completion family, not just at FE2.

2. The twenty-four free cells really are irrelevant to the recipient's OWN
   payoff and cap. A triple can occur when a different owner deviates, so a
   claim about its whole vector being unreachable would be false; the author
   makes the correct coordinatewise claim. The grand coalition is genuinely
   unreachable under one unilateral replacement because at most two unchanged
   owners are active in a phase. Arbitrarily large finite grand rewards do
   not invalidate this reasoning.

3. Deleting any one owner leaves positive periodic absorption. The uniform
   deleted-opponent survival bound from MP is unchanged. Consequently every
   unilateral replacement, including Never, absorbs almost surely. Ordinary
   row translation with Never fixed at zero is legitimate HERE because this
   absorption was proved for every deviation. It is not a general affine
   invariance theorem for quitting games.

4. The IFT field and passive cap inequalities depend only on the thirty-six
   used coordinates. The MP four-variable Jacobian is nonsingular and all
   four passive margins are strict. IFT on that coordinate projection gives
   a common sufficiently small used-coordinate neighborhood, independent of
   all free cells. The horizon threshold may depend on the particular full
   table through its finite reward bound M. No common threshold across
   unbounded free rewards is claimed or proved. I read the open extension as
   a neighborhood of the retained MP used-coordinate center, not a uniform
   radius around every arbitrary downward passive completion.

5. The geometric bound controls the initial absorption delay under both the
   policy and every deviation. It gives delivery error MC/H and regret
   2MC/H with C=768/215 as stated. Rates, target, and the table precede the
   requested accuracy. These are the fixed-target uniform quantifiers.

I ran the supplied exact Fraction verifier: inventory, sole-grand trap,
all fourteen proper-child witnesses, base-gap polynomials, and the displayed
stationary caveat passed. This is supporting arithmetic evidence, not a
substitute for the preceding all-behavior argument.

## FE2–FE3 complete-selection checks

The complete FE2 table has positive own values 1, entire trap family {I},
and core I. Every proper participant premium is negative and every grand
premium is +1. Owner 0 can withdraw from grand absorption for 3 instead of 2.
Thus empty-core existence, pure-grand equilibrium, and a protected-player
criterion do not cover this table.

The trap checks quantify over ALL weights: a nonzero nonnegative support
upper average fails at I; a strictly positive weighted leave test fails at
023 through λ₁>0; the unweighted leave charge fails there through 1>0. This
is materially stronger than testing one chosen weight.

The proper-child obstruction is also complete for the stated universal
certificate families. The unique positive singleton joining map is the
four-cycle h: 0→3→1→2→0. Every proper nonempty S has some j∈S with h(j)
outside S. The child pure-solo-j profile is exact terminal Nash, has all
debts zero and joint Never zero, while outsider h(j) gains exactly 1/2 in
the parent quiet lift. This falsifies ANY universal bound of the displayed
debt/Never form on each child. It does not falsify a selected safe child
profile. This distinction is essential: the explicit selected q₂=q₃=1/2
profile really is stationary Nash in FE2.

I independently checked the exhaustive singleton-base boundary arguments,
not just the displayed roots. Base 0 has precisely the two stated pure
points and the symmetric proper point t=(3+√2)/7. At the proper point,
y=(2−t)/(1+t)>4/5 and the actual floor-priced owner-0 gap is at most
2(1−y)−y/2<0. The bound uses the ORIGINAL table minimum −1, rather than
an arbitrary centered punishment level. Bases 1, 2, and 3 have only their
listed induced free Nash points, and the base-owner withdrawal gains are
strict. Acceptance with only a subset of the other owners free still
requires the missing ambient joining inequalities, hence yields one of
these same full induced Nash points. A full one-stage Nash point with two
or more sure owners would also appear in a singleton-base census; when
another owner is sure, the owner's floor replacement has zero survival
coefficient. Therefore the persistent-base obstruction is not just a
failure at one convenient supplied product row.

The mate-cap vectors, nonbijective favorite map, triple inverse signs,
positive-row-unit response quotient exclusions, and standard-Q versus
non-Q distinction in FE3 are consistent with the actual singleton matrix.
In particular, this is not an example escaping via non-Q singleton data.
I checked the author's R0/degree reasoning: all principal nonsingleton
submatrices are nonsingular, singleton homogeneous candidates have a
negative residual coordinate, and offset −1 has its unique full-support
solution with positive full determinant 2.

Additional narrow producer checks: `IsQuittingBlockerSwitch` requires all
outsider values in each row to equal one baseline. FE2 row 0 has outsider
singleton values 2, −1, and 0, so no baseline works. The complete literal
range predicate `IsQuittingConditionalFaceGapRange` also fails for EVERY
blocker: row 0 has a Continue value 3 but every participant reward at most
2, making its strict lower mixture comparison impossible. These are raw
producer failures, unlike merely not supplying a face-box certificate.

## GF soundness, including an explicit falsification attempt

The GF singleton matrix uses receiver rows. The actual original projective
matrix is diag(λ)G, because subtracting rᵢ({i}) removes the own level exactly.
Positive left row scaling preserves standard-Q: multiply an arbitrary
normalized offset by diag(λ), obtain an original-matrix LCP solution, and
divide each residual and complementarity equality by its positive λᵢ.
No transposition or signed-own assumption is being inserted.

I checked the global scalar construction on the whole interval, especially
the possible mixed sign h=H−β. T is positive because BOTH endpoint values
C−H+β and C are positive. The least zero a₀ of ψ is interior and ψ is
positive before it. The exact identity

    den−aψ = D(1−a)²−Fa(1−a)+βa

is positive on the closed branch: interior positivity follows from
D/x+β(1+x)−F ≥ β+2√(Dβ)−F>0, and at a=0 it equals D. Thus den>0 and
0<b<1 wherever 0<a<a₀. At a₀, b=0, not an inadmissible singular endpoint.
This directly tests the most plausible failure of the actual-data producer.

Substituting the branch makes the good passive Continue identity exact.
The bad residual g has g(0)=0, g′(0)=−Δ/D<0, and g(a₀)=Aa₀>0. IVT
therefore supplies an interior a, and hence an interior b, from the actual
reward coefficients. No externally supplied root, limiting rate, or IFT
neighborhood is needed. E is unrestricted; it changes the middle of the
crossing but neither the initial derivative nor the positive endpoint.

All passive cap coordinates were checked. For a good owner, EVERY one of
the three nonempty passive joining entries is nonpositive, so Q≤0<Wgood.
For a bad owner the three bounds give

    Q ≤ Aa(1−b)−(B+H+α)b(1−a)+Eab
      = Cbad−(H+α)b²(1−a) < Wbad.

Together with the exact active indifferences and passive Continue
equalities, these are all four owners' action inequalities in both phases.
Proper rates give deleted-opponent geometric absorption, so their Bellman
iteration bounds full behavioral replacements and Never. The resulting
target is sᵢ+λᵢvᵢ, fixed before accuracy, with the same legitimate
absorption-based row-translation argument as FE. I ran the supplied exact
polynomial verifier; the denominator, good identity, initial derivative,
bad cap subtraction, and Q-elimination identities passed.

The unconditional GF exit is also valid. The named original-game theorem
below has no own-sign, normality, or supplied genericity premise. If C≤H,
offset (−1,−1,−1,−1) has no LCP solution: the sum of the two leaf matrix
rows is (C−H)(x₀+x₁)−D(x₂+x₃)≤0, whereas feasibility needs at least 2.
If C>H and Δ≤0, use offset (−1,−1,−t,−t) with t>(C−H)/A. Core feasibility
forces x₀,x₁>0, hence complementarity yields

    A(x₀+x₁)=2+(B+H)(x₂+x₃).

The leaf-row sum becomes 2(C−H)/A+(Δ/A)(x₂+x₃)<2t, contradicting
feasibility. Thus a genuine bare noUE table would have to be in the direct
branch, where the produced fixed-target UE contradicts it. This is a
complete existential proof on the WHOLE stated raw class.

## Significance: what passed, what remains unresolved

The original MP neighborhood is fully covered by signed empty-core
existence, as both original reviews established. FE removes that particular
objection: FE2 has full premium core, and its complete trap, child, and
persistent-base tests above genuinely exclude the named producer classes.
This is evidence of new scope, not a proof of coverage against every
accepted existential producer. The explicit stationary FE2 point must not
be erased or turned into a stationary nonexistence claim.

The rational and centered stationary face-box declarations are supplied
continuous-field/zero-transport certificates. Their source headers expressly
do not produce the field or its signs from arbitrary rewards. They cannot
be cited as an automatic raw FE-family producer merely because FE2 has a
stationary Nash point. Conversely, absence of a supplied box does not prove
that no older actual-data stationary producer applies. Fixed-fixture IFT
packets require comparison of their COMPLETE existential neighborhoods,
not just comparison with the finitely many printed centers. The current
frozen text appropriately does not assert that complete comparison.

There is a further concrete obstacle to transferring FE2's preflight to
GF. FE2 is NOT a GF table: at its numerical coefficients

    A=1, B=2, C=3/2, D=1/2, H=1,
    α=β=1/2, E=F=0,

GF requires z₀(02),z₁(13)≤−7/2, but FE2 has both equal to −3/2.
Lowering just those two entries does put it into GF, with Δ=1>0.
However that modified positive-own table has pure-solo-2 and pure-solo-3
exact equilibria. At solo 2 every joining gap is negative; the same is true
at solo 3. The host prefers own payoff 1 to Never 0. Thus this immediate
GF specialization is ALREADY covered by a pure-solo producer. This is an
exact falsification of a tempting coverage transfer, not a counterexample
to GF's sound theorem. Different coefficients or free cells may give a
genuinely new GF witness; that has not been supplied in the frozen section.

Verdict: FE and GF are complete ordinary sound producers. A packet claiming
additional existential UE coverage still needs a serious, explicit coverage
clause, compared with complete implemented/accepted producers. The separate
proposed GS witness can serve that purpose if its actual data and complete
carrier exclusions check out. Only that new significance clause needs a
targeted follow-up review; the sound FE/GF algebra should not be rerun.
No strengthening of constants or weaker local fixture is requested.

## Exact source declarations inspected

- `twoPair_exact_terminal_and_fixedProfile`,
  `twoPair_policy_and_nash`, and `twoPair_isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Quitting/Cycles/TwoPairExactCertificate.lean`.
- `isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff` in
  `UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`;
  `quittingProjectiveLCPMatrix` in
  `UniformEquilibrium/Quitting/Projective/SingletonLCP.lean`; standard-Q
  definitions in `MathUE/LinearProgramming/CopositiveQ.lean`.
- `exists_uniformEquilibriumPayoff_of_empty_quittingPremiumCore` in
  `UniformEquilibrium/Quitting/Classification/Existence/SignedPairCoreUniformPayoff.lean`;
  `exists_uniformEquilibriumPayoff_of_empty_or_signed_pair_core_weakSameSign`
  in `UniformEquilibrium/Quitting/Classification/Existence/SignedPairCoreRewardClosure.lean`;
  `nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`.
- `quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_slack`
  in `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockChildDeletionAdapter.lean`;
  `withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
- Singleton/large-base excess definitions and the corresponding ordered
  concrete-gap alternatives in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
- `SignedFourCycleSingletonData` in
  `UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`;
  its larger-region adapters and classification existence wrappers.
- `IsQuittingBlockerSwitch` and
  `isUniformEquilibriumPayoff_of_blockerSwitch` in
  `UniformEquilibrium/Quitting/Classification/Existence/BlockerSwitch.lean`;
  `IsQuittingConditionalFaceGapRange` and
  `exists_uniformEquilibriumPayoff_of_conditionalFaceGapRange` in
  `UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`.
- `QuittingRationalStationaryFaceBox.exists_uniformEquilibriumPayoff` and
  `QuittingCenteredStationaryFaceCertificate.exists_uniformEquilibriumPayoff`
  in their same-named classification existence files, with the underlying
  `ConditionalFaceGap.lean` definitions.

Next requested check: only the prospective serious GS coverage clause,
against the complete existential selection sets. My own research resumes
the canonical global-floor coupled-law problem; this review is not a
consumer of that source.
