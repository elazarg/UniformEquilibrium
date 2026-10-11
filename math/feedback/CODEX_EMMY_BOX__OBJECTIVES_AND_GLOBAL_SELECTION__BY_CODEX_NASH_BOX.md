# Independent review of the two-ledger cap-chamber producer

Reviewer: CODEX_NASH_BOX.

Scope: Sections17.1--17.8 of
`notes/CODEX_EMMY_BOX__OBJECTIVES_AND_GLOBAL_SELECTION.md`, frozen whole-file
SHA256 `068b7b33a4be29cfe6d1249da30caaad18c94e6a2373ccd291f9d0a2ec1e8bb9`.
I did not read the other review before forming this assessment.

Verdict: PASS for the stated ordinary mathematical theorem and the exact
four-player test. No unresolved mathematical objection found. This is not
Lean verification, an arbitrary-game theorem, an exhaustive novelty census,
or a claim excluding unspecified qualitative neighborhoods.

## 1. Claim and source semantics checked

There are finitely many players, at least two; bounded real terminal rows,
zero nonabsorption payoff, independent private randomization and arbitrary
complete behavioral replacements. Own singleton rewards s_i are nonnegative.
For one nonzero a>=0 the two proper-coalition ledgers obey H_a>=0 and J_a<=0,
with one strict singleton H. Every proper support contains a participant
whose own coalition rewards are all at most its singleton. The strict
singleton-insertion graph has no cycle on a proper vertex subset. The
conclusion is an original uniform-equilibrium payoff, with no strategic
witness supplied as an input.

I opened the actual declarations:

* `quittingTerminalSemanticCarrier`,
  `exists_terminalProfile_sequence_tendsto_semanticPair`,
  `quittingTerminalSemanticCarrier_isCompact`,
  `continuous_quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
* `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
* `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
  and `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
  in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`;
* `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier` in
  `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`;
* `exists_successor_le_singleton_of_exactRoot_nontrap_support` in
  `UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`;
* `IsFiniteCoalitionPremiumTrap` and its negation equivalence in
  `MathUE/FiniteCoalitionPremiumCore.lean`, together with the reward adapter
  in `Classification/QuittingPremiumSupportPeelingOrder.lean`.

These support the used actual-pair closure, fixed-root invariance, cap
identities and full-behavior diagonal consumer. The proof never replaces
the actual carrier by a convexified payoff box. A root chosen only at a
limiting pair remains legal because its fixed prefix map is continuous;
it need not be Nash on the approximating profiles.

## 2. Produced seed and every-root preservation

The sole-j-Quit0 seed has exactly B_j=s_j and
B_i=max(r_i(j),r_i(ij)) for i!=j. The owner's alternative Never gives0,
so the nonnegative own singleton hypothesis is genuinely used. For every
other player the complete response classes are Quit0 and all positive
deadlines/Never. Thus no late response has been omitted.

Nonnegative weights give L_a(B)>=H_a(j)>0. The seed either is already
diagonal or defines a positive finite lambda=L_a(B)/E. Its low-cap member
j makes the closed constrained carrier nonempty and hence compact.

For ANY exact cap-Nash root, B' is the root successor of B and every
debt coordinate, hence its maximum E, scales by the same joint Continue
mass c. A sure root gives a diagonal outright; it need not preserve a
grand-row inequality afterward. For an interior full-support root,
indifference yields

    B_i-s_i = sum_(empty!=A subset I\{i}) z_A
                              [r_i(A+i)-r_i(A)].

Reversing these finite sums gives precisely sum z_S J_a(S), with S proper
and nonempty. Thus L_a(B)<=0, contradicting its strict positivity at a
positive-E chamber point. There is no missing cardinality sign or grand
term in this identity.

Every remaining nonzero root has proper support. Its flat supported
player has Q_i<=s_i and supported Nash optimality transfers this to
B'_i. Every root terminal coalition is proper, so H_a>=0 gives
L_a(B')>=c L_a(B)>=lambda E'. All Continue fixes the pair. These are
every-root statements, not a favorable-selector assumption.

## 3. Minimum-specific escape and weak boundaries

At a positive minimum, if some B_i<s_i, all Continue is not Nash. Finite
Nash existence therefore supplies a nonzero root, already covered above.
Otherwise the set L={i:B_i=s_i} is nonempty and proper: low-cap membership
gives nonemptiness, and L_a(B)>0 with a>=0 prevents L from being all players.

A sink i in the induced insertion graph on L has no profitable joining
edge to another member of L. With only i quitting at probability p, its
own two endpoints coincide. For j!=i the literal Continue-minus-Quit
difference is

    (1-p)(B_j-s_j)+p[r_j(i)-r_j(ij)].

This is nonnegative for every j in L, including equality edges. Outside L
the first coefficient is strictly positive, so one sufficiently small
p>0 handles all remaining players simultaneously. This supplies a full
nonzero Nash root and strict E contraction, contradicting the minimum.

Zero coordinates of a cause no problem: only nonnegativity is used in
the seed and ledgers, and L_a(B)>0 still proves L proper. Weak H or J
inequalities and flat participant equalities are retained without any
hidden strictness. No uniform positive absorption bound is required.
An attained zero maximum debt is a diagonal because all carrier debts
are nonnegative. The inspected consumer then gives one fixed uniform
target against unrestricted behavioral deviations.

## 4. Independent exact four-player checks

I reconstructed the literal table rather than relying on the author's
labels. Fraction enumeration over every proper coalition independently
gave (H,J,P), where P is the unweighted inserted outsider premium:

    singleton       (1,-3,-2)
    adjacent pair   (0,-5,-4)
    opposite pair   (0,-6,-4)
    triple          (3,-1,8).

The same enumeration checked every proper support for both a flat
participant and an insertion sink. The positive participant-premium
cycle forces the sole premium trap to be all four. The sole-owner0
seed has U=(1,0,4,0), B=(1,2,4,0), E=2, L=3 and lambda=3/2.

The arbitrary-continuation sure-root exclusion is correct: the opposite
player's joining differences are -4,-5/2,-1; after it Continues the
predecessor's are -1,-5/2; the successor then joins and the owner withdraws.
No continuation is consulted once some other player quits surely.

I independently expanded the three-active-support equations for (a,b,c,0):

    Q0=1-2b-c+bc,
    b0=c(4-(5/2)b),
    Q0-b0=1-2b-5c+(7/2)bc.

Stationary exact indifference and B0>=0 imply b<1/2 and c<=1/5.
Then Q1=1-2c+a(1-c)>=3/5, while its exact stationary Never value is
2ac/(a+c-ac)<=2/5, a contradiction. The support-one and support-two
cases also have the stated strict joining/Never deviations. Full support
has strictly positive terminal H expectation, whereas the indifference
J identity gives a negative cap surplus. Thus the entire stationary
exact-Nash strategy class is excluded, not merely numerical roots or a
chosen scale. This independently excludes every sound producer whose
conclusion is an exact stationary product equilibrium, without guessing
its unquantified parameter thresholds.

## 5. Bounded raw-source comparisons and remaining coverage scope

I opened `HasGlobalQuittingWeightedFloor` and
`HasWeightedQuittingTrapLeavers` in `WeightedQuittingTrapLeavers.lean`.
Summing its four singleton inserted-premium tests gives -2 sum w, so no
nonzero nonnegative weight satisfies the global floor. The stated
upper-average raw comparison also fails on the grand row by 8 sum w.
I am affirming this explicit inequality, not identifying an additional
unnamed producer solely from the phrase "upper-average".

I opened `QuittingTrapChargeCoefficients` in `BoxedQuittingNashCharges.lean`,
its `threshold` in `BoxedQuittingNashChargeOdds.lean`, and
`HasBoxedQuittingNashCharges` in `BoxedQuittingNashChargeReturn.lean`.
The table forces delta<=2, tau>=8, gap<=3, loss<=1, so every admissible
threshold is <=13/2. The actual whole predicate requires
sum s+4M<threshold for a coordinate bound M>=10, hence requires >44.
Thus no coefficient selection rescues that predicate.

The new test is not literally in the exported passive-triple chamber
family because its pair outsiders are3/2 and2 instead of that theorem's
fixed1. This is not by itself an exclusion of all other nonstationary
raw producers or unquantified neighborhoods. Those further comparisons
must be made against their complete hypotheses or complete consumers.
The author's Section17 already limits its inventory to the named bounded
comparisons and makes no exhaustive census claim; this review preserves
that scope.

## 6. Reusable content and unresolved generalization

The proved raw class genuinely supplies its seed, preserved chamber and
positive-minimum escape, not just a verifier taking any of these objects
as inputs. Arbitrary Fin4 data do not automatically satisfy H>=0, J<=0,
proper premium peeling or proper-subset insertion acyclicity. The theorem
does not establish a globally selected analogue of those guards, and
does not supply a single chronologically convergent exact-root spine.
None is needed for this stated class theorem.
