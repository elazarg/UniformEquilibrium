# Cap-near stopping-law redistribution contracts the Fin4 full-debt chamber

Authors: PAIRED_HULL_REVIEW

Independent reviews:
[SOCIAL_WEIGHT_REVIEW](../feedback/PAIRED_HULL_REVIEW__FULL_DEBT_ORTHOGONAL_PRODUCT_AND_PROJECTIVE_ATTACK__BY_SOCIAL_WEIGHT_REVIEW.md),
[CODEX_DESCENDANT falsification review](../feedback/FIN4_FULL_DEBT_CAP_NEAR_RESPONSE_SUPPORT_CONTRACTION__BY_CODEX_DESCENDANT.md)

## Exact statement

Let \(I=\operatorname{Fin}4\), and let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting-game reward table with \(|r_i(S)|\le M\), where \(M>0\).
At each live date the players independently randomize between Continue and
Quit. A unilateral response may be any behavioral strategy, including Never,
an unbounded pure stopping time, or an arbitrary randomized clock.

For a behavioral profile \(\sigma\), write

\[
U_i(\sigma)
\]

for its terminal payoff and

\[
B_i(\sigma)=\sup_{\tau_i}U_i(\tau_i,\sigma_{-i}),\qquad
d_i(\sigma)=B_i(\sigma)-U_i(\sigma),\qquad
D(\sigma)=\sum_i d_i(\sigma).
\]

Let \(\mathcal C^{\mathrm{law}}\) be the joint closure of prescribed payoff,
unrestricted cap, and terminal law, and put

\[
D_*:=\min_{z\in\mathcal C^{\mathrm{law}}}D(z.1).
\]

Let \(S\) be a supplied FinFourMinimumAtomProducer. Its retained residual is
the one used throughout: it already carries the no-uniform-payoff witness,
punishment normality, and the maintained quantitative hard residual. No
second, unrelated residual is assumed. Write its joint point as

\[
z=(x,\mu)\in\mathcal C^{\mathrm{law}},\qquad D(x)=D_*>0,
\]

and suppose that \(x\) is in the full-debt chamber,

\[
d_i(x)>0\qquad(i\in I).
\tag{1}
\]

Use one actual profile family \(\sigma_n\) from the causal chronology of
\(S\), so that its complete semantic/law packet converges to \(z\). Then,
after strict subsequence selection, one of the following two outputs exists.

### A. Reached redistribution followed by an off-minimum paid port

There are a fixed player \(i\), actual profiles \(\tau_n\), and finite cuts
\(c_n\) such that each \(\tau_n\) is a literal one-player update of
\(\sigma_n\), the source and target have identical live-path actions before
\(c_n\), and, for some \(g,p,\eta>0\),

\[
U_i(\tau_n)-U_i(\sigma_n)\ge g,\qquad
\Pr_{\sigma_n}(\text{all players reach }c_n)\ge p,
\tag{2}
\]

\[
d_i(\tau_n)\longrightarrow0,\qquad
D(\tau_n)\ge D_*+\eta.
\tag{3}
\]

The literal ancestry \(\sigma_n\to\tau_n\) and (3) also produce a standard
QuittingOffMinimumActualReachPaidPort at one target \(\tau_n\). Its paid row
is selected at \(\tau_n\); it need not have mover \(i\) or date \(c_n\).

### B. Source-faithful strict support child

There are the same kind of literal profiles \(\tau_n\), one fixed
\(s\in(0,1)\), actual one-player stopping-law chords \(H_n^s\), exact
cap--Nash words \(W_n\), and complete joint limits

\[
\sigma_n\to z=(x,\mu),\qquad
\tau_n\to y,\qquad H_n^s\to h^s,
\tag{4}
\]

such that \(D(y.1)=D(h^s.1)=D_*\) and

\[
d_k(h^s.1)=(1-s)d_k(x)+s\,d_k(y.1)\qquad(k\in I).
\tag{5}
\]

Moreover,

\[
d_i(y.1)=0,\qquad
\varnothing\ne\operatorname{supp}^+(y.1)
\subsetneq\operatorname{supp}^+(h^s.1)=I,\qquad
|\operatorname{supp}^+(y.1)|\le3.
\tag{6}
\]

Put

\[
A_n=W_n\star H_n^s,\qquad P_n=W_n\star\tau_n,
\tag{7}
\]

and let \(q_n\) be joint survival through \(W_n\). Then

\[
q_n\longrightarrow1,\qquad A_n\to h^s,\qquad P_n\to y,
\tag{8}
\]

and \(A_n\to P_n\) is a literal one-player suffix replacement with a payoff
gain bounded away from zero. The positive-finite-atom theorem and
nonempty_sourceFaithfulMinimumCausalChronology regenerate complete
FinFourMinimumAtomProducer sources at \(h^s\) and \(y\), with the original
hard residual, while retaining respectively the actual families \(H_n^s\)
and \(P_n\). The finite-window dates may be reselected.

Thus the full-debt source has a one-use phase transition to a minimum child
of support at most three. Once the child enters the existing renewable
tangent trace, at most two further nonempty strict-support descents are
possible.

## Conjecture-facing change

This strictly narrows the full-debt branch of the maintained
[Fin4 priority questions](../questions/README.md). The new content is the
source-attached cap-band family with fixed joint reach, mover debt tending to
zero, and the resulting minimum-fibre support child. A standard off-minimum
actual-reach paid port is already checked for every positive-minimum realizing
sequence; its bare existence is not the novelty here:

\[
\boxed{
\text{full debt}
\Longrightarrow
\text{off-minimum paid-port waist}
\quad\text{or}\quad
\text{strict-support minimum child}.}
\tag{9}
\]

The theorem does not consume either downstream output. In particular, it
does not prove a uniform-equilibrium payoff, turn the response into a
Nash--Bellman temporal edge, or close the off-minimum/reset-rigid waist.

## Definitions and assumptions

The terminal law is the law on Never and the fifteen nonempty coalitions.
All law topologies here are finite coordinatewise topology, equivalently
total variation. Behavioral randomization is ordinary independent private
randomization; no public coin or correlated mixture of whole profiles is
used.

For one player \(i\), every complete behavioral strategy induces its complete
live-spine stopping law on

\[
\overline{\mathbb N}:=\mathbb N\cup\{\infty\}.
\]

Conversely, every probability law on \(\overline{\mathbb N}\) has a
behavioral hazard realization. With opponents fixed, define

\[
v(q):=U_i(\sigma[i\leftarrow q])\qquad(q\in\overline{\mathbb N}).
\]

Behavioral pure-time extremality gives

\[
B_i(\sigma)=\sup_{q\in\overline{\mathbb N}}v(q).
\tag{10}
\]

The chord \(H_n^s\) mixes only player \(i\)'s complete stopping laws. It is
implemented by that player's private randomization and is therefore an
ordinary product behavioral profile.

## Source correspondence

The incoming object is FinFourMinimumAtomProducer in
[Source.lean](../../Research/Quitting/FinFourProducerAtlas/Source.lean). Its
causal atom contains an actual family converging to the displayed joint
minimum point. No unrelated realizer of \(x\) is chosen.

The cap identity (10) is
sSup_range_quittingTerminalPayoff_update_eq_pureTime in
[BehaviorPureTimeExtremality.lean](../../UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean).
Stopping-law payoff affinity and exact canonical realization are in
[StoppingLawCanonicalization.lean](../../UniformEquilibrium/Quitting/Terminal/StoppingLawCanonicalization.lean).

The fixed-threshold predecessor is
positiveDebt_exists_commonPrefix_profitableStoppingLawFork in
[FableCommonPrefixFork.lean](../fable/lean/FableCommonPrefixFork.lean).
It retains a reached prefix but leaves a fixed fraction of the mover debt.
The new step is redistribution of every source-positive clock outside an
arbitrarily thin cap band, which gives both a fixed reach floor and target
debt tending to zero.

The minimum chord inequality and its coordinatewise equality consequence are
represented by QuittingMinimumResponseChordLaw in
[MinimumResponseChordLaw.lean](../../Research/Quitting/MinimumResponseChordLaw.lean).
The strict arm uses the actual-reach selection underlying
QuittingOffMinimumActualReachPaidPort in
[ArbitraryClockMinimumActualReachPaidPort.lean](../../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ArbitraryClockMinimumActualReachPaidPort.lean).
Its useful supplied-ancestry constructor is currently private and should be
made public during formalization.

The positive finite atom is supplied by
exists_positive_finiteLawAtom_of_finFourHardResidual_minimum in
[TerminalSemanticFinFourMinimumLawFiniteAtom.lean](../../UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean).
The exact profile-preserving chronology is
nonempty_sourceFaithfulMinimumCausalChronology in
[SourceFaithfulMinimumLawCausalization.lean](../../Research/Quitting/SourceFaithfulMinimumLawCausalization.lean).
Unlike nonempty_sourceFaithfulMinimumCausalization, it does not require a
uniform supplied stage-mass floor: it reselects finite-window marks while
retaining the supplied profile family. The way to package it into a complete
source is exhibited by
[CanonicalPairFullReplacementSourceRegeneration.lean](../../Research/Quitting/FinFourProducerAtlas/CanonicalPairFullReplacementSourceRegeneration.lean).

The common-prefix complete-cap estimate is proved as ordinary mathematics in
[Common prescribed-prefix backward edge](../notes/SOCIAL_WEIGHT_REVIEW__COMMON_PRESCRIBED_PREFIX_BACKWARD_EDGE.md).
No paper theorem is used.

## Proof

### 1. Cap-band redistribution

Fix \(i\in I\), an actual profile \(\sigma\), and abbreviate

\[
B=B_i(\sigma),\qquad d=d_i(\sigma)>0.
\]

Let \(\nu\) be \(i\)'s actual complete stopping law. From stopping-law
affinity and (10),

\[
U_i(\sigma)=\mathbb E_\nu v,\qquad
d=\mathbb E_\nu(B-v).
\tag{11}
\]

Fix \(0<\varepsilon<d\). Select a pure time \(r\) with

\[
v(r)>B-\varepsilon/2
\tag{12}
\]

and define

\[
\mathcal A_\varepsilon=\{q:B-v(q)>\varepsilon\}.
\]

Let \(f(q)=r\) on \(\mathcal A_\varepsilon\) and \(f(q)=q\) otherwise, and
let \(\nu'=f_*\nu\). Every clock in the support of \(\nu'\) has value at least
\(B-\varepsilon\). Therefore the target \(\tau\), obtained by replacing only
\(i\)'s strategy with a realization of \(\nu'\), satisfies

\[
U_i(\tau)\ge B-\varepsilon.
\]

Its opponents are unchanged, so its unrestricted cap for \(i\) remains
exactly \(B\). Consequently

\[
d_i(\tau)\le\varepsilon,\qquad
U_i(\tau)-U_i(\sigma)\ge d-\varepsilon.
\tag{13}
\]

No cap is assumed attained; (12) uses only the definition of supremum.

### 2. A finite live-prefix cut and actual reach

Since both \(B\) and \(v(q)\) lie in \([-M,M]\), (11) gives

\[
d\le\varepsilon+2M\nu(\mathcal A_\varepsilon).
\tag{14}
\]

Thus the bad set has positive \(\nu\)-mass. If a finite bad clock has positive
mass, let \(b\) be its least date; otherwise put \(b=\infty\). Define
\(c=\min\{b,r\}\). The two entries cannot both be Never, because a bad Never
clock cannot be the near-cap receiver. Hence \(c<\infty\).

The source and pushed laws have identical finite masses and survival below
\(c\). Realize the target by literally copying the source's live-path hazards
below \(c\) and using the canonical residual hazards of \(\nu'\) thereafter.
This realizes exactly \(\nu'\). It asserts equality only on the unique live
all-Continue history; off-path actions after absorption are irrelevant.

Couple \(Q\sim\nu\) with \(f(Q)\). The profiles can differ in terminal outcome
only if all players reach \(c\). Hence

\[
|U_i(\tau)-U_i(\sigma)|
\le2M\Pr_\sigma(\text{all players reach }c).
\]

Together with (13),

\[
d-\varepsilon
\le2M\Pr_\sigma(\text{all players reach }c).
\tag{15}
\]

This is joint prescribed-source reach, not merely opponent-deleted survival.

### 3. Apply the construction along the full-debt source

Fix \(i\) and put \(a=d_i(x)>0\). Take
\(\varepsilon_n\downarrow0\), discard finitely many ranks so that
\(\varepsilon_n<d_i(\sigma_n)\), and apply Sections 1--2. Then

\[
d_i(\tau_n)\to0,\qquad
U_i(\tau_n)-U_i(\sigma_n)\ge a/2,\qquad
\Pr_{\sigma_n}(\text{reach }c_n)\ge a/(4M).
\tag{16}
\]

Joint semantic/law compactness supplies a strict subsequence on which
\(\tau_n\) converges and \(D(\tau_n)\) converges to some \(L\ge D_*\).

If \(L>D_*\), choose \(\eta=(L-D_*)/2\). Equation (16) gives the reached
redistribution family and eventually \(D(\tau_n)\ge D_*+\eta\). Choose one
such target. Since its total debt exceeds \(D_*>0\), some player has debt at
least \(D_*/4\). The checked actual-reach paid-row theorem at that target,
together with the literal one-replacement ancestry from its source, gives
the off-minimum port. This is a second selected row, not the redistribution
edge.

Suppose instead that \(L=D_*\), and call the target joint limit \(y\). Then
\(y\) is a global minimum and continuity gives \(d_i(y.1)=0\).

### 4. Minimum-fibre chord equality

Fix \(s\in(0,1)\). Let \(H_n^s\) replace player \(i\)'s stopping law by

\[
(1-s)\nu_n+s\nu'_n.
\]

After a further common subsequence, let \(h^s\) be its joint limit.
Prescribed payoffs and terminal laws are affine in this one player's law.
For each other player's cap, every fixed response payoff is affine and the
supremum of affine functions is convex. Player \(i\)'s cap is constant because
the opponents are unchanged. Therefore

\[
d_k(H_n^s)\le(1-s)d_k(\sigma_n)+s\,d_k(\tau_n)
\qquad(k\in I).
\tag{17}
\]

Summing (17) and using global minimality,

\[
D_*\le D(H_n^s)
\le(1-s)D(\sigma_n)+sD(\tau_n)\longrightarrow D_*.
\]

The four nonnegative coordinate gaps in (17) have sum tending to zero, so
each tends to zero. Passing to the limit proves (5).

Because \(x\) has four positive debts and \(s<1\), (5) gives
\(d_k(h^s.1)>0\) for every \(k\). The target has \(d_i(y.1)=0\), while
\(D(y.1)=D_*>0\), proving (6).

### 5. Preserve the actual response edge and regenerate the child

For each \(n\), select an exact cap--Nash word \(W_n\) of length \(n+1\)
against \(H_n^s\). Let \(q_n\) be its joint Continue product. Exact debt
scaling gives

\[
D(W_n\star H_n^s)=q_nD(H_n^s).
\]

The left side is at least \(D_*\), so

\[
\frac{D_*}{D(H_n^s)}\le q_n\le1.
\]

Since \(D(H_n^s)\to D_*\), this proves \(q_n\to1\).

Define \(A_n,P_n\) by (7). They have literally identical prefix actions and
differ only in \(i\)'s suffix. If
\(g_n=U_i(\tau_n)-U_i(H_n^s)\), the common-word identity gives

\[
U_i(P_n)-U_i(A_n)=q_ng_n.
\tag{18}
\]

Stopping-law affinity gives

\[
g_n=(1-s)(U_i(\tau_n)-U_i(\sigma_n))
\ge(1-s)a/2,
\]

so (18) retains a fixed positive gain eventually. The opponents of \(i\) are
identical at \(A_n,P_n\), hence their mover caps agree. Exact source debt
scaling then also gives

\[
d_i(P_n)=q_n d_i(\tau_n)\longrightarrow0.
\tag{19}
\]

Coupling the common word with the suffix gives convergence of payoffs and
laws because \(q_n\to1\). For caps, every pure response either stops inside
the nonempty word, obtaining a value within \(2M(1-h_{k,n})\) of the singleton
payoff, or survives it and obtains a value within the same error of a suffix
response; here \(h_{k,n}\to1\) is player \(k\)'s opponent-survival through
the word. Therefore

\[
\left|B_k(W_n\star T_n)-
\max\{r_k(\{k\}),B_k(T_n)\}\right|
\le2M(1-h_{k,n}).
\tag{20}
\]

At every positive global minimum the checked singleton margin gives

\[
B_k-r_k(\{k\})\ge D_*>0.
\]

Thus the maximum in (20) is eventually the tail cap, proving (8).

At \(h^s\) and \(y\), the hard-residual positive-finite-atom theorem selects
a positive terminal coordinate. Apply
nonempty_sourceFaithfulMinimumCausalChronology to the supplied families
\(H_n^s\) and \(P_n\), respectively. It retains those families, reselects a
finite window and positive date, and supplies exact cap--Nash words. Packaging
each chronology as a causal atom gives complete same-residual
FinFourMinimumAtomProducer objects. A paired wrapper stores (7)--(8), the
literal update, (18)--(19), and both regenerated sources. No carrier point,
profile family, or response edge is replaced.

The child support bound in (6) gives the one-use phase-rank decrease

\[
5>1+|\operatorname{supp}^+(y.1)|.
\]

Every later recursive tangent edge strictly drops the nonempty support, so
at most two such edges remain.

## Boundary tests

1. If \(\varepsilon\ge d\), the bad set may have zero source mass and no
   changed finite cut exists. The strict condition \(0<\varepsilon<d\) is
   essential.
2. If Never is the only bad source clock, the receiver is finite and the cut
   is the receiver. If the receiver is Never, a finite bad clock exists and
   the cut is its least positive-mass date. Thus the argument does not hide a
   finite-support assumption.
3. In the exact two-clock test \(v(0)=0,v(1)=1,\nu=\delta_0\), any
   \(\varepsilon<1\) sends clock \(0\) to receiver \(1\), gives target debt
   zero, gain one, and cut zero. This checks (13)--(15).
4. Literal equality on arbitrary off-path histories is false for canonical
   hazard reconstruction. The theorem copies source hazards only on the
   unique live history, which is exactly what the reach coupling requires.
5. Without both endpoint limits on the global minimum fibre, (17) is only an
   inequality and coordinatewise affinity need not hold. Without full debt at
   \(x\), the chord source need not have support four.
6. A positive limiting terminal atom need not have a uniform mass at one
   supplied date. This is why the proof uses
   nonempty_sourceFaithfulMinimumCausalChronology, which reselects marks,
   rather than the stronger fixed-mark causalization interface.

## Adapter and consumer

The conditional theorem consumes a supplied full-debt
FinFourMinimumAtomProducer. Its own causal chronology is the family
\(\sigma_n\), and the cap-band redistribution is performed directly on that
family, retaining literal ancestry and actual joint reach. In the full-debt
arm of the maintained law-tight classifier, a same-point producer can be
assembled by applying finFourHardResidual_minimumLaw_causalSuffixAtom to the
selected minimum and retained residual. That composition is routine from the
checked declarations, but no named direct classifier-to-producer adapter
currently packages it.

Arm A enters the already named off-minimum paid-port waist. Arm B constructs
a complete source of support at most three and enters the existing renewable
tangent trace with a strict one-use phase rank. These are strict contractions
of the full-debt chamber, not terminal consumers. The remaining consumers are
exactly the off-minimum paid/reset waist and the tangent exits.

## Lean handoff

Suggested declarations:

    QuittingCapBandRedistribution
    positiveDebt_exists_capBandRedistribution
    QuittingCapBandRedistribution.livePrefix_eq
    QuittingCapBandRedistribution.gain_ge_debt_sub
    QuittingCapBandRedistribution.targetDebt_le
    QuittingCapBandRedistribution.gain_le_jointReach
    FinFourFullDebtMinimumContraction
    FinFourFullDebtMinimumContraction.offMinimumPort
    FinFourFullDebtMinimumContraction.minimumChord
    FinFourFullDebtMinimumContraction.copiedPrefixEdge
    FinFourFullDebtMinimumContraction.regeneratedSources

The first structure should expose the source law, bad-set map, receiver, cut,
literal target strategy, stopping-law equality, live-prefix equality, and
formulas (13)--(15). It must not require a maximizing response.

The minimum arm should reuse stopping-law affinity, cap convexity, the checked
minimum-fibre stopping-law equality, the exact cap--Nash stack debt identity,
the common-prefix cap estimate (20), the hard-residual finite-atom theorem,
and nonempty_sourceFaithfulMinimumCausalChronology. The generic redistribution,
compact split, and common-prefix stability belong under UniformEquilibrium;
the FinFourMinimumAtomProducer regeneration and renewable-rank wrapper belong
in Research. QuittingMinimumResponseChordLaw may be a Research delegate, not
a production dependency. The child atom should be packaged as in
FinFourFullReplacementSourceRegeneration.atom, retaining the actual \(P_n\)
family.

The off-minimum arm should expose the currently private supplied-ancestry
constructor for QuittingOffMinimumActualReachPaidPort, or duplicate its short
average-debt and actual-reach proof. A regression test should include bad
Never mass, a Never receiver, and a source strategy whose off-path actions
differ from canonical reconstruction.

## Scope and nonclaims

* This is ordinary mathematics, not yet Lean-checked as the combined theorem.
* Thus the combined result currently has evidence seal M only. A checked
  supplied-producer wrapper would have branch-local source A; the direct
  classifier-to-producer adapter is not yet named. The minimum child can feed
  the existing Research renewal trace, but no terminal or uniform-equilibrium
  consumer C is supplied.
* The cap is unrestricted over all behavioral deviations.
* The response edge is not an exact Nash--Bellman or punishment-floor edge.
* The off-minimum port's paid row is not the redistribution row.
* The theorem does not consume the off-minimum, reset-rigid, positive-slope,
  support-entry, or other tangent exits.
* The phase rank is a one-use entry into the existing trace, not a rank on
  arbitrary outer-atlas returns.
* No uniform-equilibrium payoff or counterexample is constructed.

## Lean formalization record

This packet's original content is preserved above with pre-record SHA-256
`8d089a0757864b070b1bc3cacd2883473cafd89cb41f0e572062e488005d2366`.
The generic cap-band foundation was integrated at commit
`bc62b72f3ed7cc6002342d9221feaa8aeea2a69a`; common-prefix cap stability,
source-independent minimum-response chord geometry, and the public
off-minimum ancestry seam were integrated at commit
`a777a49684bf2ccb6bb41b48bf608605f9ed50c0`; the complete supplied-source
Fin4 chain was integrated into the Research umbrella at commit
`e8a626337fee145711c7023c38a015c76aba099a`.

The checked foundation comprises:

* `stoppingLawSourceCapDebt_le_epsilon_add_two_mul_badMass` and the exact
  survival-preserving cap-band pushforward in
  `MathUE/Probability/StoppingLawCapBandRedistribution.lean`;
* `exists_quittingCapBandFiniteCut` and the literal behavioral target,
  unchanged mover cap, debt subtraction, payoff-gain, and `2M` reach bounds
  in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/CapBandRedistribution.lean`;
* `abs_quittingContinuationBestResponseValue_literalRootStack_sub_le` and
  its convergence wrappers in
  `UniformEquilibrium/Quitting/Root/CommonPrefixCapStability.lean`; and
* `QuittingMinimumResponseChordLaw.ofProfiles`,
  `QuittingMinimumResponseChordLaw.chord_debt_eq_affine`,
  `QuittingMinimumResponseChordLaw.chord_debtSum_eq_endpoint`, and the Fin4
  strict-support/cardinality consequences in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticMinimumResponseChord.lean`.

The Research supplied-source chain is exposed by:

* `nonempty_finFourFullDebtCapBandTargetCompactification_and_alternative`
  and `nonempty_finFourFullDebtCapBandTargetDispatch`, which preserve the
  literal source chronology and return either the strict compact target or
  the same-minimum fixed-weight chord branch;
* `nonempty_finFourFullDebtOffMinimumActualReachPaidPort`, which retains the
  strict branch's source index, finite cut, unilateral update, gain at least
  half the limiting mover debt, and the one-quarter-debt reach inequality;
* `nonempty_finFourFullDebtFixedWeightChordCompactification`, which forms
  actual rowwise chord profiles on one common refinement and proves that the
  minimum target support is a nonempty strict subset of the chord support of
  cardinality at most three;
* `nonempty_finFourFullDebtCommonPrefixResponse`, whose common exact cap--Nash
  root words give the packet's debt, law, payoff, unrestricted-cap, and
  prescribed-payoff limits without asserting that a finite row is minimal;
* `nonempty_finFourFullDebtPairedSourceChronologyRegeneration`, which
  regenerates the exact positive global-minimum target law point with the
  incoming residual and stores the literal chord-to-target update as a
  separate origin chronology; and
* `nonempty_finFourFullDebtSupportContractedRenewal`, which begins the neutral
  renewable trace at that regenerated target, retains the one-use origin edge
  separately, and permits at most two further strict-support descents.

The same-point regeneration declaration
`FinFourMinimumAtomProducer.regeneratedAtLawPoint` now has the narrow owner
`Research/Quitting/FinFourProducerAtlas/SamePointMinimumAtomProducerRegeneration.lean`.
The source-independent `FinFourRenewableTerminalExit`,
`FinFourRenewableTrace`, and
`FinFourRenewableMinimumSourceNode.nonempty_renewalTrace` have the neutral
owner `Research/Quitting/FinFourProducerAtlas/RenewableSourceTrace.lean`;
their public names and types are preserved.

Evidence seals are `M` and `L` for the full conditional chain.  Its core
compiler consumes a supplied positive full-debt `FinFourMinimumAtomProducer`.
`finFour_noUniformPayoff_exists_fullDebtTargetDispatch_or_resetRigid` gives
conditional source `A` by packaging a same-point producer only in the
full-debt arm of the maintained no-uniform-payoff classifier; the reset-rigid
arm remains unchanged.  There is branch-local `C`: the strict arm attaches
`FinFourFullDebtOffMinimumActualReachPaidPort.exists_summablePort_exactTrichotomy`,
and the minimum arm reaches the support-contracted renewable trace.

There is no terminal or uniform-equilibrium consumer.  In particular, the
checked result does not identify the independently selected residual with
the classifier's internal residual, identify the public paired chronology
with the regenerated producer's internal chronology, make a finite target or
chord profile minimal, consume any structural terminal exit, make the
off-minimum paid row equal to the redistribution row, prove Nash play or
terminal approximation, or construct a uniform-equilibrium payoff or
counterexample.  The packet's boundary tests are explanatory rather than
separately formalized regression declarations.
