# Independent review: curvature prefix renewal through a cap-inert branch

Reviewer: `CODEX_MINER`

Date: 2026-08-26

Note reviewed:
[`CHATGPT_EXTERNAL__CURVATURE_PREFIX_RENEWAL.md`](../notes/CHATGPT_EXTERNAL__CURVATURE_PREFIX_RENEWAL.md)

## Verdict

**REVISE; the one-prefix algebra passes, including the corrected
opponents-Continue/joint-Continue normalization, but the claimed renewable
passport is not yet established as an iterated interface or a frontier
contraction.**

Equations (3)--(8) are exact under the intended hypotheses.  Equation (9) is
also correct for one prefix after adding the hypotheses which its conclusion
uses: the square has positive curvature, its receiving endpoint is actual,
the global actual-profile debt infimum is positive, and the common root is an
exact cap--Nash root at that endpoint with positive joint Continue mass.

There are three mandatory scope repairs.

1. The quantity called `Theta` is not the repository's named
   `quittingStoppingLawNormalizedDebtDirection` or cluster `curvature`; the
   square cap curvature `C` equals `lambda` times the former curvature gap.
   `C/D_T` is a new debt-normalized ratio and should be named accordingly.
2. The factor-two lower bound in (9) is only one-step renewable.  Repeating
   the transported arm gives at best `Theta_n >= Theta_0/2^n`, so it supplies
   no fixed positive passport or well-founded progress measure.  Literal
   all-Continue prefixes preserve the square exactly, but also preserve the
   entire state; this is lossless retention, not renewal progress.
3. “No positive-charge exact path can begin at the port” is valid only for
   the cap-annotated, forward prefix choice whose tail annotation is the cap
   vector `B`.  It says nothing about exact roots at the prescribed payoff
   `U`, and it does not rule out a backward Bellman edge having `B` as its
   head and a different tail.

The note is useful as an exact algebraic proposal for a richer stored source
object, but current `QuittingPaidCapLiftedSource`/`InertStall` data do not store
the three source/mixed/receiving corners.  No maintained consumer accepts the
new proposed passport, and no result here consumes the inert arm.  Keep this
internal; it is not export-ready.

## 1. Exact shifted-witness identities

Let `p_o^C` denote the observer's Continue probability and let

\[
 c=c_{-o}(q)=\prod_{i\ne o}p_i^C.
\]

When the observer uses `shift tau`, it Continues surely at the new prefix.
If an opponent exits there, the unnormalized absorbing contribution is `A`;
if all opponents Continue, the game reaches the suffix and pays `V_X(tau)`.
This proves (1):

\[
 V_{q*X}(\operatorname{shift}\tau)=A+cV_X(\tau).
\]

Against the prefixed opponents, an unrestricted behavioral deviation by `o`
can Quit immediately for `Q`, or Continue and then use any unrestricted
suffix deviation.  Therefore

\[
 B_{q*X}=\max\{Q,A+cB_X\}.
\]

Writing

\[
 h_X=[Q-A-cB_X]_+
\]

turns the maximum into `A+cB_X+h_X`, and subtraction proves (3).  Subtracting
two copies of (1) proves (4); the wall cancels because it is independent of
the shifted witness.  No optimal-strategy attainment is used.

These calculations correspond closely to checked declarations:

- `quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
  `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean` is (2);
- `quittingPureTimeDeviationPayoff_sub_rootThenContinuation_shift_one` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`
  is exactly (4); and
- `QuittingPaidCapLiftedSource.pureTimePayoff_sub_shift` iterates (4) through
  the already checked cap-prefix sequence.

I found no named declaration for the single-witness regret form (3), but it is
an immediate corollary of the checked max and shifted-payoff formulas rather
than an independent strategic theorem.

## 2. Curvature identity and the support implication

For a common root, `Q`, `A`, and `c` depend on the root, reward table, and
observer, not on which of `S,M,T` is used as suffix.  Thus

\[
 B'_Z=A+cB_Z+h_Z
\]

at every corner `Z`.  Affinely combining the three equations gives exactly

\[
 C'=cC+(1-\lambda)h_S+\lambda h_T-h_M.
\]

Equation (5) passes with no missing coefficient.

Assume `q` is exact Nash against `B_T`.  Positive **joint** Continue mass
implies that every player, in particular `o`, assigns positive probability
to Continue.  A played action of an exact product Nash root cannot be
strictly below the other pure action.  Hence the observer's Continue endpoint
dominates immediate Quit:

\[
 Q\le A+cB_T,
\]

so `h_T=0`.  This proves (6).  The note should state explicitly that exact
Nash is against the receiving cap vector `B_T`, not against `U_T` and not
against the mixed cap `B_M`.

With `h_T=0` and `h_S>=0`,

\[
 C'\ge cC-h_M.
\]

Consequently failure of `C'>=cC/2` forces `h_M>cC/2`, and the weak alternative
in (7) follows.  For the alternative to be a positive quantitative split,
the hypotheses should include `C>0`; positive joint Continue then also gives
`c>0`.

The `h_M` arm has a precise checked interpretation which the note should
record.  It is not the cap/prescribed continuation-option surcharge.  It is
the positive part of the immediate-Quit-minus-Continue endpoint difference
of the **common root against the mixed cap tail `B_M`**.  Since the observer's
Continue probability is positive,
`quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart` in
`UniformEquilibrium/Quitting/Root/NashDefect.lean` shows that it contributes

\[
 p_o^C h_M
\]

to the common root's coordinate Nash defect at `B_M`.  Thus the wall says
that a root exact at `B_T` is quantitatively non-Nash at `B_M`; it is not an
exact edge, an absorbing charge, or a unilateral deviation at a prescribed
tail.

By contrast,
`quittingRootContinuationOptionSurcharge` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`
compares best endpoints at `B_M` and `U_M` for one semantic pair.  The two
objects must not be identified.

## 3. Literal all-Continue preservation

At the all-Continue root, opponents Continue surely, so `c=1`, and there is
no absorbing contribution, so `A=0`.  Immediate Quit against all-Continue
opponents pays the singleton reward.  For every actual suffix `Z`, its
unrestricted cap dominates that singleton deviation, hence

\[
 h_Z=[r_o(\{o\})-B_Z]_+=0.
\]

Therefore `C'=C`.  Equation (8) is correct, provided `S`, `M`, and `T` are
literal actual profiles.  A stopping-law mixture is actual, so this condition
is met in the intended curvature square.

Common all-Continue prefixing also preserves more than just `C`: (3) has
`c=1` and `h_Z=0`, so all shifted-witness regrets at all three corners are
unchanged.  Thus, if the original `QuittingStoppingLawCurvaturePaidWitness`
and all three profiles are retained externally, its source and receiving
approximation budgets can be shifted losslessly as well.

This observation is mathematically sound, but its present frontier content is
limited.  The checked `QuittingPaidCapLiftedSource.InertStall` already gives:

- every selected cap root is literally all-Continue;
- every selected actual prefix has the same semantic pair and debt;
- shifted pure-time payoff differences are unchanged; and
- the original paid row is transported losslessly at every finite depth.

The new datum would be retention of the discarded source and mixed corners,
not a new state or a new consumer.  Repeating an all-Continue delay produces
the same cap square again.  It permits the same curvature decoder to be
invoked again, but that invocation returns the same kind of paid witness and
does not create descent, charge, or a new source.

## 4. Opponent versus joint Continue mass in (9)

The correction in the note is right.  Curvature transport at observer `o`
uses the opponents-only coefficient

\[
 c=\prod_{i\ne o}p_i^C,
\]

because a deviating observer forces its own prefix action to Continue.  Exact
cap--Nash debt transport uses the full prescribed product root and hence the
joint coefficient

\[
 c_{\rm all}=p_o^C c.
\]

The notation `q_o(C)` in the note is ambiguous because `C` already denotes
curvature.  It should be replaced by `p_o^C`, or in repository notation by
`(q o false).toReal`.

For the receiving actual profile `T`, the checked declarations

- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`, and
- `quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash`

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`
give

\[
 D'_T=c_{\rm all}D_T.
\]

Assuming positive joint Continue and `C>0`, `D_T>0`, division is legal and

\[
 {C'\over D'_T}
 \ge {cC/2\over p_o^C cD_T}
 ={1\over2p_o^C}{C\over D_T}
 \ge {1\over2}{C\over D_T}.
\]

Thus (9) is correct.  If `D_*>0` is the global actual-profile infimum and the
prefixed `T'` is actual, then `D'_T>=D_*`; because `Theta=C/D_T>0`, this yields

\[
 C'\ge (\Theta/2)D'_T\ge \Theta D_*/2.
\]

The positivity of `Theta` is essential.  Without `C>0`, multiplying
`D'_T>=D_*` by `Theta/2` can reverse the useful comparison, so the claimed
absolute floor does not follow.

Positive joint Continue is automatic for an exact cap root in the maintained
positive-infimum regime by
`capNash_continueMass_pos_of_debtSumInf_pos`.  Also, positive absorption is
not outside the division argument: a root may have both positive absorption
and positive joint Continue.  Only **sure absorption** (`c_all=0`) prevents
division.  The note's phrase “a zero-Continue or positive-charge endpoint
must be handled ... not by division” should be repaired to:

> Sure absorption is outside (9).  Any positive absorption may instead be
> dispatched by the existing charge/debt-descent theorem, even though (9)
> remains algebraically valid when joint Continue is positive.

## 5. Why (9) is not yet an iterated passport

For one transported step, the ratio loses at most a factor two.  If the same
argument is applied at `n` successive non-inert transported steps, it proves
only

\[
 \Theta_n\ge 2^{-n}\Theta_0.
\]

The corresponding absolute lower bound also decays like `2^{-n}`.  This does
not preclude Zeno decay, does not force a finite rank change, and does not
give a fixed source-independent curvature floor for arbitrarily many
renewals.  To obtain a genuine maintained invariant one would need, for
example, a loss charged to absorption or debt decrease, or a parameterized
alternative whose cumulative loss is summable.  No such estimate is present.

There is a second interface gap.  The common-prefix calculation uses all
three literal profiles `S`, `M`, and `T`, their common mover and observer, the
mixture weight, and the equality saying `M` is the stopping-law mixture of
the other corners.  Common prefixing does preserve that equality, because the
same prefix law occurs in both mover endpoints.  But the current
`QuittingPaidCapLiftedSource` stores only:

- the receiving actual profile;
- one observer and paid first-disagreement row; and
- the positive global minimum.

Its `SummablePort` does not store `S`, `M`, `lambda`, or the original source
and endpoint approximation inequalities.  The adapter from
`QuittingStoppingLawCurvaturePaidWitness` deliberately drops those data when
it constructs the cap-lifted source.  Consequently (5)--(9) cannot currently
be applied by unpacking an `InertStall`; a new typed carrier and a common-
prefix mixture lemma would be required.

The result is therefore best described as:

> an exact one-step transport identity and a proposal for a richer retained
> square, lossless on literal all-Continue prefixes and factor-two-degrading
> on the general transported arm.

It is not yet a renewable well-founded passport.

## 6. Maximal-root split and the meaning of “no path can begin”

The pointwise maximal-root split is valid ordinary mathematics.  At a fixed
cap vector `B`, the product-root space is compact, the exact Nash
correspondence is nonempty and closed, and absorption is continuous.  Hence
absorption attains a maximum.  If the maximum is zero, every exact root has
zero absorption.  Zero absorption means joint Continue mass one, which forces
every marginal to Continue surely, so the only exact root is all-Continue.

This is not the selector currently used by
`quittingCapLiftedPrefixRoot`: the checked implementation chooses an arbitrary
exact cap root.  `InertStall.root_eq_allContinue` proves only that all roots
selected along that particular zero-total-absorption port are all-Continue;
it does not prove uniqueness among all exact roots.  The maximal selector
would remove that selection artifact, but it is not currently a named checked
part of the cap-lifted port.

The conclusion about exact paths must retain two qualifications.

First, uniqueness is at the **cap vector `B`**.  In the forward prefix
convention of `QuittingPunishmentFloorInfiniteOrbit`, selecting a root exact
at the current tail value `B` and prefixing it can only select all-Continue,
so the next cap value is again `B` and the one-step charge is zero.  This is
the precise true meaning of “no positive-charge exact path can begin at the
cap port.”

Second, it says nothing about roots exact at the literal prescribed vector
`U`.  When the semantic debt is positive, `U != B`, and the checked
`capNash_isZeroNash_at_prescribed_iff_surcharge_eq_liveDebt` shows exactly why
cap exactness does not transport automatically to prescribed exactness.  A
positive-charge exact prescribed-payoff path may still exist.  Nor does cap
root uniqueness rule out a backward Bellman edge whose **head** is `B` but
whose different tail annotation selects another root; it only classifies
roots whose tail annotation is `B`.

## 7. Novelty and recommendation

The constituent algebra substantially overlaps checked interfaces:

- cap max/prefix identities: `TerminalDebtPrefix.lean`;
- exact cap debt scaling and absorption descent:
  `TerminalCapNashEndpointTransport.lean` and
  `TerminalCapNashChronology.lean`;
- pure-time difference scaling, observer reach, and inert losslessness:
  `PaidCapLiftedSummablePort.lean` and
  `PaidCapPortExactTrichotomy.lean`;
- normalized stopping-law curvature and its paid-row decoder:
  `NormalizedCurvaturePaidRow.lean` and
  `NormalizedCurvatureStrategicDispatch.lean`; and
- cap/prescribed surcharge separation:
  `TerminalSemanticOwnStrategyTransport.lean` and
  `PairBasePaidResetEndpointSeam.lean`.

The genuinely new candidate is narrow: retain the complete literal
source/mixed/receiving cap square through the cap lift, rather than retaining
only its receiving paid row.  The note correctly identifies the algebra this
carrier would satisfy.  It does not yet show that this extra field contracts
the maintained inert residual.  On an inert port it is a static self-copy; on
a non-inert port the existing charge/debt descent is already available and
the new normalized estimate degrades under repetition.

Recommended status after revision: **internal algebraic lemma/proposed
interface, not export and not a conjecture-facing closure.**  A next result
would need either a consumer of the mixed-cap defect `p_o^C h_M`, or a
cumulative transport estimate whose loss is paid by the summable absorption
budget rather than a fixed factor two at every step.
