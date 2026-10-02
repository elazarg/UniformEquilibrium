# Signed source retraction and near-minimum contraction of a Fin4 response cycle

Authors: CODEX_DESCENDANT

Independent review:
[PAIRED_HULL_REVIEW](../feedback/CODEX_DESCENDANT__PAID_CYCLE_FINITE_MEMORY_AND_SOURCE_REPROJECTION_OBSTRUCTION__BY_PAIRED_HULL_REVIEW.md)

## Exact statement

Let \(I=\operatorname{Fin}4\), and let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting-game reward table. At each live date, players independently
randomize between Continue and Quit. A unilateral response may replace one
player's entire behavioral strategy, including by Never, an unbounded pure
stopping time, or an arbitrary randomized clock.

Fix \(M>0\) such that

\[
|r_i(S)|\le M
\qquad(i<4,\ S\ne\varnothing).
\]

For an actual behavioral profile \(\sigma\), write

\[
U_i(\sigma)
\]

for its terminal payoff and

\[
B_i(\sigma)=\sup_{\tau_i}U_i(\tau_i,\sigma_{-i}),\qquad
d_i(\sigma)=B_i(\sigma)-U_i(\sigma),\qquad
D(\sigma)=\sum_{i<4}d_i(\sigma).
\]

Let \(\mathcal C^{\rm law}\) be the joint closure of prescribed payoff,
unrestricted cap, and complete terminal law on the fifteen nonempty
coalitions and Never. Put

\[
D_*=\min_{z\in\mathcal C^{\rm law}}D(z.1)>0.
\tag{1}
\]

Assume a supplied FinFourMinimumAtomProducer. Thus one fixed Fin4 hard
residual and one literal causal family \(S_n\) are supplied, with

\[
\operatorname{SemLaw}(S_n)\longrightarrow z_*,
\qquad
D(z_*.1)=D_*.
\tag{2}
\]

For each tail starting at \(N\), apply the checked actual-source pure-time
response alternative. If its retained source index inside that tail is
\(k_N\), its global index is

\[
m_N=N+k_N\ge N.
\]

Suppose the off-minimum cycle branch occurs for a cofinal sequence of tail
starts. Pass to a strict refinement of the resulting global indices \(m_N\)
and choose one result from each retained tail. This gives:

* a cofinal sequence of retained actual sources, still denoted \(S_n\);
* a finite literal pure-clock response cycle \(C_n\) of length at most
  \(1296\);
* literal finite complete-strategy-replacement ancestry from \(S_n\) to every
  vertex of \(C_n\); and
* on every cycle edge, one exact unrestricted cap-attaining response whose
  mover gains at least \(D_*/4\), has zero debt at the target, and whose target
  is literally the next source.

Every cycle vertex is strictly off the minimum fibre. Define

\[
E_n=\max_{X\in C_n}\bigl(D(X)-D_*\bigr).
\tag{3}
\]

After one composed strict subsequence, exactly one of the following two
reductions applies.

### A. Uniformly off-minimum source-attached paid retraction

If \(\limsup E_n>0\), then there are a fixed player \(i\), a fixed
\(\varepsilon>0\), and actual profiles \(A_n,B_n\), such that:

* \(A_n\to B_n\) replaces only player \(i\)'s complete strategy;
* \(A_n,B_n\) are literal coordinatewise hybrids of \(S_n\) and one selected
  cycle vertex;
* the edge is oriented from that vertex toward the retained source; and
* at least one fixed alternative holds cofinally.

The first alternative is a literal source-oriented paid replacement:

\[
U_i(B_n)-U_i(A_n)\ge\varepsilon/16,
\tag{4}
\]

and the checked actual-reach theorem at \(A_n\), with observer \(i\), supplies
a source-supported paid first-disagreement row with

\[
\operatorname{gain}\ge\varepsilon/64
\tag{4a}
\]

and

\[
\frac{\varepsilon}{16}
\le4M\,\operatorname{OwnSurvival},\qquad
\frac{\varepsilon}{16}
\le8M\,\operatorname{OppReach},\qquad
\left(\frac{\varepsilon}{16}\right)^2
\le32M^2\,\operatorname{JointReach}.
\tag{4b}
\]

The second alternative is a source-supported paid first-disagreement row at
the literal hybrid \(A_n\), with one fixed observer \(j\ne i\), declared gain

\[
\operatorname{gain}\ge\varepsilon/192,
\tag{5}
\]

\[
\frac{\varepsilon}{48}
\le4M\,\operatorname{OwnSurvival},\qquad
\frac{\varepsilon}{48}
\le8M\,\operatorname{OppReach},
\tag{6a}
\]

and

\[
\left(\frac{\varepsilon}{48}\right)^2
\le32M^2\,\operatorname{JointReach}.
\tag{6b}
\]

The row in the second alternative is a profitable unilateral
first-disagreement edge by \(j\), not merely an externality caused by \(i\).

### B. Near-minimum response chord and source-regenerated support child

If \(E_n\to0\), one composed strict subsequence fixes one cycle edge, its
mover \(i\), its target coalition \(K\ne\varnothing\), and all later
compactification choices. Write that edge

\[
X_n\longrightarrow Y_n.
\tag{7}
\]

Then \(Y_n\) differs from \(X_n\) only in \(i\)'s complete strategy,
attains \(i\)'s unrestricted cap, and

\[
U_i(Y_n)-U_i(X_n)=d_i(X_n)\ge D_*/4,
\qquad d_i(Y_n)=0.
\tag{8}
\]

Both endpoint debts tend to \(D_*\). Each \(Y_n\) terminates surely in the
fixed coalition \(K\) at its literal earliest finite date \(t_n\).

Fix \(s\in(0,1)\). Mix only player \(i\)'s complete stopping law:

\[
H_n^s=(1-s)X_n+_i sY_n.
\tag{9}
\]

After the same composed subsequence,

\[
\operatorname{SemLaw}(X_n)\to x,\qquad
\operatorname{SemLaw}(Y_n)\to y,\qquad
\operatorname{SemLaw}(H_n^s)\to h^s,
\tag{10}
\]

and

\[
D(x)=D(y)=D(h^s)=D_*.
\tag{11}
\]

For every player \(k\),

\[
d_k(h^s)=(1-s)d_k(x)+s\,d_k(y).
\tag{12}
\]

In particular,

\[
d_i(y)=0,\qquad d_i(x)\ge D_*/4,\qquad
d_i(h^s)=(1-s)d_i(x)>0,
\tag{13}
\]

so

\[
\varnothing\ne\operatorname{supp}^+(y)
\subsetneq\operatorname{supp}^+(h^s),
\qquad
|\operatorname{supp}^+(y)|\le3.
\tag{14}
\]

The literal target family \(Y_n\) retains \(K\)-mass one at \(t_n\), while
\(H_n^s\) retains \(K\)-mass at least \(s\) there. Apply source-faithful
causalization first to the literal \(H_n^s\) family and its moving marks.
This constructs the source at \(h^s\) and chooses exact prefix words \(W_n\).
Put

\[
A_n=W_n\star H_n^s,\qquad P_n=W_n\star Y_n.
\]

Opponent-deleted survival proves \(\operatorname{SemLaw}(P_n)\to y\), and
the shifted \(K\)-atom in \(P_n\) stays uniformly positive. Causalize this
literal \(P_n\) family at its shifted marks to construct the source at \(y\).
The thin paired wrapper stores the actual edge \(A_n\to P_n\) and the
\(P_n\)-based child chronology. Both sources copy the original hard residual.

Hence the near-minimum response-cycle arm has a one-use source-faithful
transition to a minimum child of strictly smaller nonempty positive-debt
support. That child may enter the existing renewable tangent trace; the
present theorem does not consume the later tangent exits.

## Conjecture-facing change

This strictly narrows the maintained quantitative paid-port question.
The checked cycle theorem left every entirely off-minimum horizontal response
cycle as one residual. The present theorem separates that residual into:

\[
\boxed{
\begin{array}{c}
\text{a fixed paid reverse source edge},\\
\text{a fixed actual paid row at a literal retraction hybrid},\\
\text{or a source-regenerated strict-support minimum child}.
\end{array}}
\tag{15}
\]

In particular, an asymptotically minimum cycle is not a new terminal strongly
connected component: it enters the already maintained finite support lane.
The live response-cycle obstruction is reduced to the already isolated
paid-cap waist and the renewable support lane. Neither downstream lane is
declared to produce a uniform-equilibrium payoff here.

## Definitions and assumptions

A pure-clock profile assigns each player one time in
\(\overline{\mathbb N}=\mathbb N\cup\{\infty\}\). Against fixed opponents,
every behavioral strategy induces a stopping-time law on this space, every
such law has a behavioral hazard realization, and terminal payoff is affine
in that law. Thus the mixture in (9) is ordinary independent private
randomization by one player, not a public correlation of whole profiles.

The complete terminal law includes Never. All compactifications in this
packet are joint compactifications of payoff, unrestricted behavioral caps,
and that complete law. A marked stage mass is the unconditional probability
of reaching the displayed date and terminating there in the displayed
coalition.

The coordinatewise hybrid from \(S\) to \(X\) is formed by choosing an order
of the four players and successively replacing each complete strategy of
\(S\) by the corresponding strategy of \(X\). Its reverse is a literal
four-step retraction from \(X\) to \(S\).

## Source correspondence

The finite response cycle, exact cap attainment, gain floor, zero target
debt, finite alphabet, literal return, and source ancestry are checked in:

* QuittingPureTimeMaxDebtExactResponseStep,
  QuittingPureTimeExactResponseCycle, and
  exists_quittingPureTimeExactResponseCycle_finFour in
  [PureTimeSelectedExactResponseOrbit.lean](../../UniformEquilibrium/Diagnostics/Quitting/PureTimeSelectedExactResponseOrbit.lean);
* QuittingActualSourcePureTimeResponseAlternative and
  minimumRealizingSequence_exists_actualSourcePureTimeResponseAlternative in
  [ActualSourcePureTimeResponseAlternative.lean](../../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualSourcePureTimeResponseAlternative.lean); and
* the reviewed declaration record
  [Fin4 finite pure-clock exact response cycle](../formalized/FIN4_FINITE_PURE_CLOCK_EXACT_RESPONSE_CYCLE.md).

The incoming source is FinFourMinimumAtomProducer in
[Source.lean](../../Research/Quitting/FinFourProducerAtlas/Source.lean).
The positive-debt localization used in arm A is
positiveDebt_exists_actualJointReach_paidRow_mem_support in
[ActualReachPaidFirstDisagreement.lean](../../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualReachPaidFirstDisagreement.lean).
The response-chord inequality is
quittingTerminalSemanticDebt_responseChord_le in
[MinimumResponseChordLaw.lean](../../Research/Quitting/MinimumResponseChordLaw.lean).
The literal moving-family source reconstruction is
nonempty_sourceFaithfulMinimumCausalization in
[SourceFaithfulMinimumLawCausalization.lean](../../Research/Quitting/SourceFaithfulMinimumLawCausalization.lean).
The all-Never exclusion is
not_allNever_positiveMinimumTerminalSemanticDebt in
[PureTimePositiveMinimumAllNever.lean](../../UniformEquilibrium/Diagnostics/Quitting/PureTimePositiveMinimumAllNever.lean).

The common-prefix complete-cap estimate is proved as ordinary mathematics in
[Common prescribed-prefix backward edge](../notes/SOCIAL_WEIGHT_REVIEW__COMMON_PRESCRIBED_PREFIX_BACKWARD_EDGE.md).
It covers early Quit, arbitrary late stopping, mixed clocks, and Never.

The new mathematics is the four-coordinate paid retraction, its uniform
source-oriented dichotomy, and the application of the minimum response chord
to a cofinal near-minimum response-cycle family with literal marked target
atoms. Existing cycle declarations did not orient any edge back toward the
retained source or contract the near-minimum cycle into the support lane.

## Proof

### 1. Four-coordinate signed retraction

Take arbitrary actual profiles \(S,X\) with

\[
D(X)-D(S)=\delta>0.
\tag{16}
\]

Replace the four coordinates of \(S\) by those of \(X\), in any fixed order:

\[
S=Z^0,Z^1,Z^2,Z^3,Z^4=X.
\tag{17}
\]

For some \(r<4\),

\[
D(Z^{r+1})-D(Z^r)\ge\delta/4.
\tag{18}
\]

Put \(A=Z^{r+1}\), \(B=Z^r\), and let \(i\) be the changed player. Set

\[
g=U_i(B)-U_i(A),\qquad
\Delta=D(A)-D(B)\ge\delta/4.
\]

Player \(i\)'s opponents are identical at \(A,B\), so
\(B_i(A)=B_i(B)\). Therefore

\[
\Delta
=g+\sum_{j\ne i}\bigl(d_j(A)-d_j(B)\bigr).
\tag{19}
\]

If \(g\ge\Delta/2\), then \(g\ge\delta/8\). Since \(B\) is a legal
unilateral target for \(i\),

\[
d_i(A)\ge U_i(B)-U_i(A)=g.
\]

The checked actual-reach theorem at \(A\), observer \(i\), and debt floor
\(\delta/8\) therefore supplies a paid row of declared gain
\(\delta/32\), with its three reach floors. Otherwise the three nonmovers
contribute more than \(\delta/8\), so some \(j\ne i\) satisfies

\[
d_j(A)-d_j(B)\ge\delta/24.
\tag{20}
\]

Since every debt is nonnegative,

\[
d_j(A)\ge\delta/24.
\tag{21}
\]

Apply
positiveDebt_exists_actualJointReach_paidRow_mem_support
to the actual profile \(A\), observer \(j\), and debt floor
\(\rho=\delta/24\). It supplies a source-supported paid first-disagreement
row of declared gain \(\rho/4=\delta/96\), along with

\[
\rho\le4M\,\operatorname{OwnSurvival},\qquad
\rho\le8M\,\operatorname{OppReach},\qquad
\rho^2\le32M^2\,\operatorname{JointReach}.
\tag{21a}
\]

This proves the pointwise paid-retraction alternative.

If \(\limsup E_n>0\), pass to \(E_n\ge\varepsilon>0\). Choose a maximizing
cycle vertex \(X_n\). Eventually

\[
D(X_n)-D(S_n)\ge\varepsilon/2.
\]

Apply the pointwise theorem with \(\delta\ge\varepsilon/2\), then make one
finite-label subsequence selection fixing the retraction coordinate, the
observer, and the output type. The reverse-edge gain is at least
\(\varepsilon/16\), and its associated actual paid row has gain at least
\(\varepsilon/64\). In the second arm take
\(\rho=\varepsilon/48\), which is below the observer debt; its paid-row gain
is \(\varepsilon/192\), and the checked theorem gives (6a)--(6b).

### 2. Exact-response chord at the minimum

Assume \(E_n\to0\). The cycles have uniformly bounded finite length and use
finite role labels. On one composed strict subsequence, fix a cycle edge and
its mover \(i\), then fix every later finite label and compactification
choice. Let \(X_n\to Y_n\) be that edge.

Exact cap attainment and unchanged opponents give

\[
B_i(Y_n)=B_i(X_n),\qquad
U_i(Y_n)=B_i(X_n),\qquad
d_i(Y_n)=0.
\tag{22}
\]

Every cycle vertex satisfies

\[
D_*\le D(\cdot)\le D_*+E_n,
\]

so both endpoint debts tend to \(D_*\).

For fixed \(s\in(0,1)\), form (9). Prescribed payoff and terminal law are
affine in this one-player stopping-law mixture. For a nonmover \(k\), the
payoff of each fixed unrestricted response is affine in the same mixture, so
the supremum over all such responses is convex. The mover cap is constant.
Consequently

\[
d_k(H_n^s)\le(1-s)d_k(X_n)+s\,d_k(Y_n)
\qquad(k<4).
\tag{23}
\]

After common compactification, global minimality and the endpoint limits give

\[
D_*\le D(h^s)
\le(1-s)D(x)+sD(y)=D_*.
\tag{24}
\]

Thus equality holds. The four coordinate slacks in (23) are nonnegative and
sum to zero, so every one vanishes. This proves (11)--(12). Equation (22)
and the gain floor give (13). Since \(D_*>0\), the support of \(y\) is
nonempty; equation (12) then gives the strict inclusion (14).

### 3. The target supplies the marked atom

A pure-clock profile is either all Never or terminates surely in its earliest
finite coalition. The target \(Y_n\) cannot be all Never cofinally. Otherwise
its semantic pair would be the fixed all-Never pair and would attain the
positive global minimum, contradicting
not_allNever_positiveMinimumTerminalSemanticDebt.

After a further finite-label selection, one fixed \(K\ne\varnothing\)
terminates each \(Y_n\) with mass one at its earliest finite date \(t_n\).
The mixture \(H_n^s\) chooses \(i\)'s target stopping law with probability
\(s\), while opponents remain unchanged, so the same \(K\)-event has mass at
least \(s\) at \(t_n\).

### 4. Literal source regeneration and copied prefix

Apply nonempty_sourceFaithfulMinimumCausalization to the literal family
\(H_n^s\), its exact moving marks \(t_n\), and its positive
\(K\)-stage-mass floor. This constructs the minimum source at \(h^s\) and
selects exact cap--Nash words \(W_n\). Their joint survival and every
opponent-deleted survival tend to one. Copy the incoming table-level hard
residual to the regenerated source and put

\[
A_n=W_n\star H_n^s,\qquad P_n=W_n\star Y_n.
\tag{25}
\]

The word is prescribed identically at both endpoints, so \(A_n\to P_n\)
remains a literal complete \(i\)-strategy replacement. It is not claimed
that \(W_n\) is cap--Nash against \(Y_n\).

For any prescribed word \(W\), tail \(T\), and player \(k\), coupling a pure
response through the word gives

\[
\left|B_k(W\star T)
-\max\{r_k(\{k\}),B_k(T)\}\right|
\le2M\bigl(1-H_k(W)\bigr),
\tag{26}
\]

where \(H_k(W)\) is survival through \(W\) of all opponents of \(k\).
Pure stopping-time extremality makes this estimate uniform over every
behavioral response, including Never and arbitrarily late stopping.

At a positive global minimum, the singleton moat gives

\[
B_k-r_k(\{k\})\ge D_*>0.
\tag{27}
\]

Thus the maximum in (26) selects the tail-cap branch asymptotically at both
minimum limits. Prescribed-payoff and law coupling through the common word
then gives

\[
\operatorname{SemLaw}(A_n)\to h^s,\qquad
\operatorname{SemLaw}(P_n)\to y.
\tag{28}
\]

The shifted marked atom in the literal \(P_n\) family remains uniformly
positive. Apply nonempty_sourceFaithfulMinimumCausalization to \(P_n\) at
those shifted marks, and copy the same incoming hard residual. This completes
the source at \(y\). The paired wrapper stores \(A_n\to P_n\), the source
causalization at \(h^s\), and the \(P_n\)-based child chronology. This proves
the source-faithful support transition (14).

## Boundary tests

1. **No positive excess.** If \(D(X)=D(S)\), the coordinate telescope need
   not contain any oriented signed edge. Strict endpoint excess is essential
   in arm A.
2. **The observer row is selected at the hybrid.** The nonmover debt
   inequality is not itself a deviation. The paid row follows only after
   applying the actual-reach theorem at the literal profile \(A\); its source
   and receiver are those selected by that theorem.
3. **Approximate cap attainment.** If the response in (7) is only
   \(\eta_n\)-optimal, then \(d_i(Y_n)\le\eta_n\), not zero. A nonvanishing
   error can destroy the strict support exclusion of \(i\).
4. **One minimum endpoint is insufficient.** If only \(Y_n\) approaches the
   minimum while \(X_n\) stays off minimum, (24) does not force coordinatewise
   equality and no support contraction follows.
5. **All Never.** A pure-clock target with no finite deadline has no positive
   finite stage atom. The positive-minimum all-Never exclusion is exactly what
   supplies a nonempty marked coalition in arm B.
6. **Time-forgetting law is insufficient.** Source regeneration uses the
   literal moving dates and unconditional stage masses, not merely a positive
   coordinate in the compact terminal law.
7. **Unbounded deviations.** Estimate (26) is stated for the unrestricted cap.
   A finite-horizon cap would not control Never or late stopping and would not
   justify (28).
8. **Horizontal versus temporal.** Neither the response cycle nor the copied
   prefix edge is asserted to be a Nash--Bellman chronology within one play.

## Adapter and consumer

For every tail of the incoming minimum producer's literal realizing family,
minimumRealizingSequence_exists_actualSourcePureTimeResponseAlternative gives
an actual-source minimum-hit or off-minimum-cycle alternative. If minimum hits
occur cofinally, they belong to the separate minimum-return lane. If cycles
occur cofinally, the source selected inside the tail beginning at \(N\) has
global index \(m_N=N+k_N\ge N\). A strict refinement of these global indices
therefore supplies the cofinal family used in this theorem.

Arm A supplies either a literal paid complete-strategy retraction toward the
retained source or an actual source-supported paid first-disagreement row at a
literal retraction hybrid. Both enter the paid-cap waist, whose downstream
trichotomy is not consumed here.

Arm B constructs complete same-residual minimum sources at both chord limits
and a one-use strict-support transition. Its target enters the existing
renewable positive-debt-support tangent trace. This consumes the
near-minimum-cycle arm as an independent response-cycle residual; it does not
consume the later positive-slope, support-entry, or off-minimum tangent exits.

## Lean handoff

Suggested declarations:

    QuittingFourCoordinateSignedRetraction
    QuittingFourCoordinateSignedRetraction.paid_or_hybridPaidRow
    QuittingResponseCycleExcessAlternative
    QuittingNearMinimumExactResponseChord
    QuittingNearMinimumExactResponseChord.debt_affine
    QuittingNearMinimumExactResponseChord.support_strict
    FinFourNearMinimumResponseCycleSourceRegeneration
    FinFourNearMinimumResponseCycleSourceRegeneration.commonPrefix

The signed retraction should be stated first for two arbitrary actual
profiles; its proof needs only four-step coordinate replacement and
quittingContinuationBestResponseValue_update_self.

The chord theorem should accept supplied actual profile families and expose
one common refinement for all three joint limits. Do not encode cap attainment
or minimum equality as fields manufactured by a constructor. The source
adapter should take the incoming FinFourMinimumAtomProducer and copy its hard
residual explicitly. Reuse nonempty_sourceFaithfulMinimumCausalization and
the common-prefix cap estimate rather than choosing new minimum realizers.

Useful formalization regressions are: a nonmover debt change before applying
the actual-reach selector; an approximate response whose target debt stays positive;
an all-Never pure-clock target; and a copied prefix at which an unrestricted
deviator Quits before the tail.

## Scope and nonclaims

* This is ordinary mathematics, not yet a Lean theorem.
* It is conditional on the cofinal off-minimum-cycle branch of the checked
  source alternative; cofinal minimum hits are not reclassified here.
* It does not temporalize the horizontal response cycle.
* It does not consume the downstream paid-cap trichotomy or tangent exits.
* It does not give a rank on arbitrary outer-atlas returns. The support
  transition is a one-use entry into the existing tangent phase.
* It does not construct a uniform-equilibrium payoff or a counterexample.

## Lean formalization record

Pre-formalization packet SHA-256:
`1b4ba8577b1f39f64d02b4ccaee99217a99530c03ecfce45130b664ca8115398`.

The checked production and Research surfaces were integrated in commit
`1733c4b8e388c3ec587a16d3d3cbeda42ac92063`.  The final audited signed scratch
used manifest SHA-256
`b3f5efffc364192c88e33a98076285117ea9ccaac9c60cc01320639d7a111275`;
the final high module had SHA-256
`1b2523061750a45b19ca710f20d5cbd1e7313eb33e4f6568e72b0039e1fab27b`.

The production owners are
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FinFourSignedRetraction.lean`
and
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticNearMinimumExactResponseChordCompactification.lean`.
They expose `QuittingFinFourSignedRetraction`,
`QuittingFinFourSignedRetractionPaidAlternative`,
`QuittingFinFourUniformExcessPaidAlternative`,
`QuittingNearMinimumExactResponseFamily`, and
`QuittingNearMinimumExactResponseChordCompactification`, including the affine
minimum-fibre chord and strict support contraction.

The Research owner
`Research/Quitting/FinFourProducerAtlas/FinFourSignedCycleContraction.lean`
contains the supplied-source compiler.  Its principal declarations are
`FinFourCofinalOffMinimumResponseCycles`,
`FinFourUniformCycleFixedPaidRetraction`,
`FinFourUniformCycleFixedMoverPaidRow`,
`FinFourUniformCycleFixedNonmoverPaidRow`,
`FinFourNearMinimumCycleSourceRegeneration`,
`FinFourSelectedCycleContractionBranch`, and
`nonempty_finFourSelectedCycleContractionResult`.  The checked finite-label
selector makes the retained mover or nonmover label uniform on a cofinal
subsequence and preserves the packet's paid-row and reach constants.

Evidence seals:

- **M:** PASS.  The signed four-coordinate telescope, paid alternatives,
  exact-response chord compactification, common-prefix regeneration, and
  finite-label cofinal selection match the reviewed mathematics.
- **L:** PASS.  The generic leaves are reachable from the production umbrellas
  and generated axiom audit; the Research source compiler is checked with
  warnings as errors and representative axiom prints.
- **A:** conditional and Research-only.  The high compiler consumes a supplied
  minimum producer, literal source chronology, cofinal off-minimum response
  cycles, copied-prefix convergence data, and the selected branch.  It does
  not prove that those cycles occur from every source.
- **C:** absent.  The paid rows and strict-support child are exposed, but no
  terminal, renewal, or uniform-equilibrium consumer is proved.

The formalization does not temporalize the horizontal response cycle, consume
the paid-cap trichotomy or later tangent exits, rank arbitrary outer-atlas
returns, or construct a uniform-equilibrium payoff or counterexample.
