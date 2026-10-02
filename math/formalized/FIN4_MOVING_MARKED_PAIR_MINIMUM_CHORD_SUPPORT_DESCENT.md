# Moving marked-pair minimum chord gives source-faithful support descent

Authors: PAIRED_HULL_REVIEW

Independent reviews:
[SOCIAL_WEIGHT_REVIEW](../feedback/PAIRED_HULL_REVIEW__ORIENTED_PAIR_TO_SINGLETON_OR_RENEWABLE_CHORD_SECTION17__BY_SOCIAL_WEIGHT_REVIEW.md),
[CODEX_DESCENDANT, Section 17 delta](../feedback/PAIRED_HULL_REVIEW__ORIENTED_PAIR_TO_SINGLETON_OR_RENEWABLE_CHORD__BY_CODEX_DESCENDANT.md#10-delta-review-after-the-section-17-repairs),
[PAIRED_HULL_REVIEW on the common-prefix edge](../feedback/SOCIAL_WEIGHT_REVIEW__COMMON_PRESCRIBED_PREFIX_BACKWARD_EDGE__BY_PAIRED_HULL_REVIEW.md),
[CODEX_DESCENDANT on the common-prefix edge](../feedback/SOCIAL_WEIGHT_REVIEW__COMMON_PRESCRIBED_PREFIX_BACKWARD_EDGE__BY_CODEX_DESCENDANT.md)

## Exact statement

Let \(I=\operatorname{Fin}4\), let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting-game reward table, and suppose
\(\lvert r_i(S)\rvert\le M\) for every \(i,S\), where \(M>0\).
Strategies are ordinary behavioral strategies with independent private
randomization. A unilateral cap always ranges over all behavioral strategies,
including every finite pure stopping time and Never.

Let \(S\) be a supplied `FinFourMinimumAtomProducer` carrying:

1. a hard residual for the fixed reward table;
2. a joint terminal-semantic/law point \(x\);
3. the positive global minimum
   \[
   D_*:=D(x)=\inf_\sigma D(\sigma)>0;
   \]
4. a causal positive finite atom and its public source chronology.

The ordinary producer does **not** store the moving endpoint ancestry below.
Supply in addition one moving-marked-pair contract over \(S\), whose fields
are the actual profiles, marks, fixed labels, mass floor, convergence, and
literal update data stated next. This is a theorem hypothesis, not an output
currently constructed from `FinFourMinimumAtomProducer`.

Fix a two-player coalition \(K\subset I\), a player \(q\notin K\), and put
\(K'=K\cup\{q\}\). Suppose the retained ancestry supplies actual behavioral
profiles \(X_n\) and marked dates \(t_n\) such that:

1. the complete semantic/law points of \(X_n\) converge to \(x\);
2. conditional on reaching \(t_n\), the prescribed product root is the pure
   pair \(K\): precisely the players in \(K\) Quit surely and all other
   players Continue surely;
3. the unconditional reach of the marked row satisfies
   \[
   L_n:=\Pr_{X_n}(\text{reach }t_n)\ge\lambda>0;
   \]
4. changing only \(q\)'s action at \(t_n\) from Continue to Quit is locally
   strictly better for \(q\), with the fixed reward difference
   \[
   \Delta:=r_q(K')-r_q(K)>0.
   \]

Let \(Y_n\) be that literal one-row update. It retains every earlier action,
every earlier absorption possibility, every other player's complete
strategy, and the literal post-mark continuation of \(X_n\). Define

\[
 R_n:=d_q(Y_n)\ge0,\qquad
 e_n:=D(Y_n)-D_*\ge0.
\]

For any fixed \(s\in(0,1)\), let \(H_n^s\) retain the whole profile \(X_n\)
except that \(q\)'s action at \(t_n\) is the independent \(s\)-mixture toward
the action in \(Y_n\).

Then at least one of the following holds after explicit strict-subsequence
selection. Every output stores a map `select : ℕ → ℕ` and a proof
`StrictMono select`; every profile, law, reach, and marked-date field in that
output is reindexed through that same map. In a refined arm the returned map
is the literal composition of the earlier selector with the refinement, with
strict monotonicity proved by composition. Relabelling selected sequences by
\(n\) below is only notation for this data-bearing conclusion.

### A. Positive residual

There is \(\rho>0\) such that \(R_n\ge\rho\). Against the literal opponents
of \(Y_n\), player \(q\) then has a source-supported pure-clock
first-disagreement row strictly before \(t_n\), with payoff gain at least
\(\rho/4\). The standard actual-reach bounds also give positive own,
opponent, and joint reach floors depending only on \(\rho\) and \(M\).

This is a source-faithful paid-cap-port output. It is not asserted to be an
exact cap--Nash prefix.

The output stores both the strict-earlier paid row and the result of
`paidFirstDisagreement_capPortTrichotomy` at the supplied global minimum. A
paid row alone is not called a consumed port.

### B. Quantitative off-minimum endpoint

\[
 R_n\longrightarrow0
 \quad\text{and}\quad
 e_n\ge\eta>0.
\]

The literal endpoint edge \(X_n\to Y_n\) has exact gain

\[
 U_q(Y_n)-U_q(X_n)=L_n\Delta\ge\lambda\Delta
\]

and its target has total debt at least \(D_*+\eta\). The complete source
calendar, marked date, and tail remain unchanged.

If this arm is advertised as entering the universal paid-port waist, its
output must additionally contain a `QuittingOffMinimumActualReachPaidPort`
for the literal ancestry \(X_n\to Y_n\), followed by the corresponding
cap-port dispatch. The repository's core construction for a supplied
off-minimum ancestry is currently private, so this small public adapter is a
formalization obligation; the endpoint and excess alone do not constitute a
checked consumer.

### C. Regenerated minimum child with strict support drop

\[
 R_n\longrightarrow0
 \quad\text{and}\quad
 e_n\longrightarrow0.
\]

There is one common strict subsequence and joint terminal-semantic/law limits

\[
 X_n\longrightarrow x,\qquad
 Y_n\longrightarrow y,\qquad
 H_n^s\longrightarrow h^s,\qquad
 L_n\longrightarrow L\ge\lambda
\]

such that \(D(y)=D(h^s)=D_*\), and, for every player \(i\),

\[
 d_i(h^s)=(1-s)d_i(x)+s\,d_i(y).
\tag{1}
\]

For the mover,

\[
 d_q(y)=0,\qquad
 d_q(x)=L\Delta>0,\qquad
 d_q(h^s)=(1-s)L\Delta>0.
\tag{2}
\]

Consequently,

\[
 \varnothing\ne\operatorname{supp}^+(y)
 \subsetneq\operatorname{supp}^+(h^s),
 \qquad
 |\operatorname{supp}^+(y)|\le3.
\tag{3}
\]

The limiting laws retain the exact moving-row provenance:

\[
\begin{aligned}
 \operatorname{Law}(y)
   &=\operatorname{Law}(x)+L(\delta_{K'}-\delta_K),\\
 \operatorname{Law}(h^s)
   &=\operatorname{Law}(x)+sL(\delta_{K'}-\delta_K).
\end{aligned}
\tag{4}
\]

At every selected finite rank, \(Y_n\) has \(K'\)-mass \(L_n\) at the
original date \(t_n\), while \(H_n^s\) has \(K'\)-mass \(sL_n\) there.
Source-faithful minimum causalization of \(H_n^s\) selects a nonempty exact
cap--Nash word \(W_n\). Put

\[
 A_n:=W_n\star H_n^s,
 \qquad
 P_n:=W_n\star Y_n,
\tag{5}
\]

and let \(c_n\) be joint survival through \(W_n\). Then \(c_n\to1\),
\(A_n\to h^s\), \(P_n\to y\) in the complete semantic/law packet, and
\(A_n\to P_n\) is a literal one-player full-strategy replacement. Exactly,

\[
\begin{aligned}
 U_q(P_n)-U_q(A_n)&=c_n(1-s)L_n\Delta,\\
 B_q(P_n)&=B_q(A_n),\\
 d_q(P_n)&=c_nR_n\longrightarrow0.
\end{aligned}
\tag{6}
\]

At the shifted date \(|W_n|+t_n\), \(P_n\) has exact \(K'\)-mass \(c_nL_n\),
which is at least \(\lambda/2\) eventually. Causalizing this actual target
family regenerates the complete minimum source at \(y\). Both regenerated
sources copy the incoming hard residual literally. A paired-ancestry wrapper
stores both causalizations, \(A_n,P_n\), their literal update equality,
the identities (5)--(6), their complete limits, and the shifted marked mass.
No unrelated source or realizer is selected.

More literally, let `residualSelect`, `excessSelect`, and `compactSelect` be
the selectors used in the three successive refinements. This arm returns
their composed strict selector, and \(X,Y,H,L,t\) are all pulled back by that
one composition. When the eventual bound \(c_nL_n\ge\lambda/2\) is used,
choose \(N\), put `tailSelect n = N + n`, and pull back \(A_n,P_n,W_n\) and
the shifted mark \(|W_n|+t_n\) through the same `tailSelect`. Only this
tail-reindexed target family is passed to source-faithful causalization. The
paired wrapper records both selector compositions and their `StrictMono`
proofs.

The child at \(y\) enters the existing renewable tangent trace. With one
nonrecurrent origin phase, the natural rank

\[
 \rho(\mathsf{terminal})=0,\qquad
 \rho(\mathsf{tangent}(z))=1+|\operatorname{supp}^+(z)|,\qquad
 \rho(\mathsf{origin})=5
\tag{7}
\]

strictly decreases on entry, on every later recursive minimum-fibre support
descent, and on exit. Since the first child has support at most three, at
most two later nonempty strict-support descents can occur.

The copied-prefix edge in (5) is a literal behavioral response edge with
gain bounded away from zero. Formula (7) is a one-use source/rank transition
into the checked tangent lane. Neither assertion makes the edge a
punishment-floor Nash--Bellman edge or assigns a rank to arbitrary returns
from an outer atlas.

## Conjecture-facing change

This is a strict reduction to the maintained quantitative paid-port question.
It supplies the source-faithful minimum-chord support-drop requested in item
3 on the zero-residual, minimum-target arm, without normalizing the actual
source to a date-zero mass-one pair or replacing its tail by Never.

The theorem makes the supplied marked-pair sequence exhaustive up to
subsequence:

\[
\boxed{
\begin{array}{ll}
\text{positive residual}
  &\Longrightarrow\text{strictly earlier actual paid port},\\
\text{zero residual and off minimum}
  &\Longrightarrow\text{literal off-minimum paid endpoint},\\
\text{zero residual and minimum}
  &\Longrightarrow\text{same-residual strict-support child}.
\end{array}}
\tag{8}
\]

Thus nonmover cap leakage is no longer an untyped fourth arm. At a minimum
target it is absorbed by the coordinatewise affine identity (1); away from
the minimum it is recorded by the off-minimum excess.

This does not close the whole strategic-pair question. The paid-port
debt-descent and inert outputs remain open, as do the positive-slope,
support-entry, and off-minimum terminal exits of the tangent trace.

## Definitions and assumptions

For a behavioral profile \(\sigma\), write

\[
 U_i(\sigma)
\]

for player \(i\)'s prescribed terminal payoff and

\[
 B_i(\sigma)
 =\sup_{\tau_i}U_i(\tau_i,\sigma_{-i})
\]

for the complete unilateral behavioral cap. Define

\[
 d_i(\sigma)=B_i(\sigma)-U_i(\sigma),
 \qquad
 D(\sigma)=\sum_{i\in I}d_i(\sigma).
\]

The ordinary terminal law is a probability law on the finite set consisting
of Never and all nonempty quitting coalitions. The existing
`QuittingTerminalSemanticLawPoint` stores prescribed payoff, the unrestricted
cap vector, and the ordinary terminal law. The four player-deleted laws are
useful auxiliary coordinates for the copied-prefix convergence proof, but
they are not fields of `FinFourMinimumAtomProducer`. If the paired-ancestry
wrapper retains them, their convergence is a derived coupling conclusion. It
must not be presented as incoming source data. Convergence is coordinatewise
in the retained finite coordinates; for each finite law this is equivalent
to total-variation convergence.

The one-row chord is ordinary behavioral randomization. Only \(q\)'s
date-\(t_n\) Bernoulli action is mixed; there is no public correlation and no
correlated mixture of whole profiles.

The source-ancestry hypothesis is literal data, not a carrier
reconstruction: the supplied profiles \(X_n\), their actual marked dates
\(t_n\), their earlier roots and absorption, and their post-mark tails are
retained by the additional moving-marked-pair contract. The theorem changes
only \(q\)'s action at the displayed row.

## Source correspondence

The incoming source type is
FinFourMinimumAtomProducer in
[Source.lean](../../Research/Quitting/FinFourProducerAtlas/Source.lean).
Its fields provide the hard residual, the minimum point, positivity of the
global minimum, and the causal finite atom. They do not provide \(X_n\),
\(t_n\), the pair \(K\), the mover \(q\), or an incoming endpoint edge. The
new moving-marked-pair contract supplies those fields explicitly.

The exact supplied-profile causalization theorem is
nonempty_sourceFaithfulMinimumCausalization in
[SourceFaithfulMinimumLawCausalization.lean](../../Research/Quitting/SourceFaithfulMinimumLawCausalization.lean).
It chooses new exact cap--Nash prefix words and cutoffs but keeps the supplied
base profiles and marked dates definitionally.

The prescribed-payoff scaling identity for a literal common root word is
quittingTerminalPayoff_literalRootStack_sub_eq_continueProduct_mul in
[TerminalCapNashChronology.lean](../../UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean).
Behavioral pure-time extremality, including Never, is in
[BehaviorPureTimeExtremality.lean](../../UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean).
The singleton moat used to identify the limiting cap is
minimumTerminalSemantic_singletonMargin in
[TerminalSemanticAuxiliaryNashBudget.lean](../../UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean).
The unrestricted almost-silent cap estimate (20), its copied-prefix use, and
the paired-ancestry wrapper are new ordinary mathematics.

The complete-cap chord inequality and its minimum-fibre affine consequence
are represented by quittingTerminalSemanticDebt_responseChord_le and
QuittingMinimumResponseChordLaw in
[MinimumResponseChordLaw.lean](../../Research/Quitting/MinimumResponseChordLaw.lean).

[MinimumResponseChordRegeneration.lean](../../Research/Quitting/FinFourProducerAtlas/MinimumResponseChordRegeneration.lean)
already regenerates same-residual chord and endpoint sources from a supplied
minimum response rectangle. It does not produce that minimum rectangle from
the moving marked-pair source, does not split the residual \(R_n\), and does
not prove that a target sequence with uncontrolled nonmover caps converges
back to the minimum fibre. Those are the new steps here.

The positive-residual arm uses
positiveDebt_exists_actualJointReach_paidRow_mem_support in
[ActualReachPaidFirstDisagreement.lean](../../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualReachPaidFirstDisagreement.lean),
together with the screened marked-row argument proving that the resulting
first disagreement is strictly earlier than \(t_n\).
The complete reviewed proof of precisely that strict-residual branch remains
the separate packet
[Actual reached-pair residual and strict-earlier paid port](ACTUAL_REACHED_PAIR_PREMARK_RESIDUAL_AND_STRICT_EARLIER_PAID_PORT.md);
it is invoked here rather than merged into the minimum-chord result.

The downstream tangent source and finite trace use:

- exists_positiveMinimumDebtTangentFamily_of_pair in
  [PositiveMinimumDebtTangentFamily.lean](../../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean);
- FinFourRenewableMinimumSourceNode and its source attachment in
  [CanonicalPairEndpointSourceRegeneration.lean](../../Research/Quitting/FinFourProducerAtlas/CanonicalPairEndpointSourceRegeneration.lean);
- FinFourRenewableMinimumSourceNode.nonempty_renewalTrace and
  FinFourRenewableTrace.descentCount_lt_support_card in
  [CanonicalPairRenewableSourceRank.lean](../../Research/Quitting/FinFourProducerAtlas/CanonicalPairRenewableSourceRank.lean).

The normalized date-zero theorem in
[FinFourOrientedMinimumPairChord.lean](../../UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FinFourOrientedMinimumPairChord.lean)
does not supply this result: it assumes a mass-one pair at date zero with
Never tail and therefore discards the actual prefix and moving mark. The new
argument works with the original actual profiles and their unrestricted caps.

No paper theorem is invoked.

## Proof

### 1. Exact endpoint gain, residual, and law

Before \(t_n\), \(X_n\) and \(Y_n\) are identical. On the event that the row
is reached, another member of \(K\) Quits surely under either action of \(q\).
Thus the game terminates at \(t_n\), in coalition \(K\) for \(X_n\) and in
coalition \(K'\) for \(Y_n\). Therefore

\[
 U_q(Y_n)-U_q(X_n)=L_n\Delta.
\tag{9}
\]

The opponents of \(q\) are unchanged, so \(B_q(Y_n)=B_q(X_n)\). Subtracting
the prescribed payoff change gives the exact residual account

\[
 d_q(X_n)=L_n\Delta+R_n,\qquad d_q(Y_n)=R_n.
\tag{10}
\]

The same coupling proves the complete terminal-law identities

\[
\begin{aligned}
 \operatorname{Law}(Y_n)
   &=\operatorname{Law}(X_n)+L_n(\delta_{K'}-\delta_K),\\
 \operatorname{Law}(H_n^s)
   &=\operatorname{Law}(X_n)+sL_n(\delta_{K'}-\delta_K).
\end{aligned}
\tag{11}
\]

Earlier absorption and the Never coordinate are identical on the two sides,
so (11) includes them rather than conditioning them away.

### 2. The positive-residual arm

Every nonnegative sequence \(R_n\) has either a subsequence bounded below by
some \(\rho>0\), or a subsequence tending to zero.

The theorem output stores the strict selector realizing this split. In the
zero-residual arm, every later sequence is definitionally pulled back through
that selector; the notation below does not reset the index family.

Suppose \(R_n\ge\rho\). Apply the complete actual-reach paid-row theorem to
the actual profile \(Y_n\) and player \(q\), at debt scale \(R_n\). It gives
a pure source clock in the actual stopping-law support of \(Y_{n,q}\), a
strictly better receiving pure clock, and their first-disagreement row. The
realized payoff gain is at least \(R_n/4\ge\rho/4\). It also gives

\[
\begin{aligned}
 R_n&\le4M\,S_q,\\
 R_n&\le8M\,\operatorname{OppReach}_q,\\
 R_n^2&\le32M^2\,\operatorname{JointReach}.
\end{aligned}
\tag{12}
\]

The first-disagreement row must be strictly before \(t_n\). Indeed, because
\(Y_n\) makes \(q\) Quit surely at \(t_n\) whenever that row is reached, any
supported source clock which has not stopped earlier stops at \(t_n\).
Continuing instead at \(t_n\) yields the \(K\)-endpoint, which is strictly
worse than the selected \(K'\)-endpoint. A receiving clock equal to \(t_n\)
has no gain, and a later clock or Never has the weakly worse Continue value.
Hence a positive paid first disagreement cannot start at or after \(t_n\).

This proves A while retaining the actual opponents, prefix, mark, and tail.

### 3. The target-excess split

Assume along a strict subsequence that \(R_n\to0\). Since every actual
profile lies in the carrier,

\[
 e_n=D(Y_n)-D_*\ge0.
\]

After a further strict subsequence, either \(e_n\ge\eta>0\) or \(e_n\to0\).
In the first case, (9) and \(L_n\ge\lambda\) give B.

This second selector is composed with the residual selector. The target
profile, source profile, mark, reach, outcome law, and chord profile all use
that same composite map.

Assume henceforth \(e_n\to0\).

### 4. Common compactification

The joint semantic/law carrier is compact, and \([0,1]\) is compact. Pass to
one common strict subsequence on which

\[
 \operatorname{SemLaw}(Y_n)\to y,\qquad
 \operatorname{SemLaw}(H_n^s)\to h^s,\qquad
 L_n\to L\ge\lambda.
\tag{13}
\]

The already supplied convergence of \(X_n\) to \(x\) survives the same
subsequence. Closedness of the carrier places \(y,h^s\) in it. Continuity of
total debt and \(e_n\to0\) give \(D(y)=D_*\).

### 5. Complete-cap convexity and the minimum squeeze

For \(i\ne q\), fix any complete behavioral response \(\tau_i\). Since
\(H_n^s\) changes only the independent strategy of opponent \(q\), the payoff
of \(\tau_i\) is affine in \(s\). Taking the supremum over every
\(\tau_i\) makes the cap convex. For \(i=q\), the opponents are fixed and the
cap is constant. Prescribed payoff is affine for every player. Thus

\[
 d_i(H_n^s)
 \le(1-s)d_i(X_n)+s\,d_i(Y_n)
\qquad(i\in I).
\tag{14}
\]

Summing and using the global lower bound,

\[
 D_*
 \le D(H_n^s)
 \le(1-s)D(X_n)+sD(Y_n)
 \longrightarrow D_*.
\tag{15}
\]

Hence \(D(h^s)=D_*\). Passing (14) to the common subsequence yields

\[
 d_i(h^s)\le(1-s)d_i(x)+s\,d_i(y).
\tag{16}
\]

Both sides of (16), summed over \(i\), equal \(D_*\). Every coordinate slack
is nonnegative, so every slack is zero. This proves (1).

By (10), (9), \(R_n\to0\), and \(L_n\to L\),

\[
 d_q(y)=0,\qquad d_q(x)=L\Delta,\qquad
 d_q(h^s)=(1-s)L\Delta.
\]

For \(0<s<1\), the coordinatewise affine identity also gives

\[
 \operatorname{supp}^+(h^s)
 =\operatorname{supp}^+(x)\cup\operatorname{supp}^+(y).
\tag{17}
\]

Since \(q\) belongs to the support of \(x\) but not to the support of \(y\),
and \(D(y)=D_*>0\), (3) follows.

Passing (11) to the same common subsequence proves (4). The finite-rank
stage-mass statements are stronger: they hold before taking the limit at the
literal dates \(t_n\).

### 6. Common prescribed prefix and same-residual regeneration

Apply source-faithful minimum causalization first to

\[
 (H_n^s,t_n,K',s\lambda).
\tag{18}
\]

Let \(W_n\) be the chosen exact cap--Nash word. The construction gives
\(|W_n|=n+1\), so every \(W_n\) is nonempty. Let \(c_n\) be joint survival
through \(W_n\), let \(H_{i,n}\) be survival of all opponents of player
\(i\), and define the profiles in (5). Source-faithful causalization gives

\[
c_n\longrightarrow1,
\qquad
H_{i,n}\longrightarrow1\quad(i\in I).
\tag{19}
\]

We need one elementary unrestricted-cap lemma. For every behavioral tail
\(T\), every player \(i\), and every nonempty finite prescribed word \(W\),

\[
\left|B_i(W\star T)-
  \max\{r_i(\{i\}),B_i(T)\}\right|
\le 2M(1-H_i(W)).
\tag{20}
\]

Against fixed opponents, every behavioral response is a probability mixture
of a deterministic finite stopping time and Never. If a pure response Quits
inside \(W\), then on opponent survival through the word it Quits alone and
receives \(r_i(\{i\})\); only the complementary event can change the payoff.
If it Continues through \(W\), couple it to the corresponding tail pure time;
again the outcomes can differ only on the opponent-prefix absorption event.
Both payoff errors are at most \(2M(1-H_i(W))\). Taking the supremum proves
the upper bound. Immediate Quit and a shifted epsilon-optimal tail pure time
give the matching lower bound. This includes arbitrarily late stopping,
Never, and arbitrary mixtures.

At either minimum limit, the checked singleton margin gives

\[
B_i-r_i(\{i\})\ge D_*>0.
\tag{21}
\]

Thus the maximum in (20) eventually selects the tail cap. Prescribed payoffs
and ordinary terminal laws couple with error at most \(1-c_n\); after deleting
player \(i\), the corresponding laws couple with error at most
\(1-H_{i,n}\). Equations (19)--(21) therefore prove the complete limits

\[
\operatorname{SemLaw}(A_n)\longrightarrow h^s,
\qquad
\operatorname{SemLaw}(P_n)\longrightarrow y.
\tag{22}
\]

The common word is prescribed identically at both endpoints, including for
player \(q\). Hence \(A_n\to P_n\) is a literal one-player replacement that
changes only \(q\)'s suffix. On prefix absorption their payoffs agree, and on
joint survival the suffix gain is \((1-s)L_n\Delta\). Therefore

\[
U_q(P_n)-U_q(A_n)=c_n(1-s)L_n\Delta.
\tag{23}
\]

The opponents of \(q\) are identical, so their unrestricted caps are equal.
Moreover, exact cap--Nash debt scaling at the source gives
\(d_q(A_n)=c_nd_q(H_n^s)\). Since

\[
d_q(H_n^s)=(1-s)L_n\Delta+R_n,
\]

subtracting (23) yields

\[
B_q(P_n)=B_q(A_n),
\qquad
d_q(P_n)=c_nR_n\longrightarrow0.
\tag{24}
\]

At date \(|W_n|+t_n\), the target \(P_n\) has exact \(K'\)-mass \(c_nL_n\).
Choose \(N\) such that this is at least \(\lambda/2\) for every \(n\ge N\),
and define the strict tail selector \(\chi(n)=N+n\). Reindex \(A,P,W,t,L\)
through \(\chi\) together. Apply source-faithful minimum causalization to

\[
(P_{\chi(n)},|W_{\chi(n)}|+t_{\chi(n)},K',\lambda/2).
\tag{25}
\]

where every family in (25) is the tail-reindexed family. For each causal atom,
copy from the explicitly supplied source \(S\) the hard
residual, the global-minimum comparison, positivity of the terminal debt
infimum, and the equality of the new point's debt with that infimum. This
constructs complete `FinFourMinimumAtomProducer`s at \(h^s\) and \(y\), both
with residual definitionally equal to the residual of \(S\).

The ordinary producer does not contain an incoming-edge field. Define a thin
paired-ancestry wrapper storing: the two causalizations; the actual families
\(A_n,P_n\); the literal update equality; (22)--(24); and the shifted
marked-mass identity. It also stores the composed common selector, the tail
selector, both `StrictMono` proofs, and the literal equalities
`sourceChild.residual = S.residual` and
`targetChild.residual = S.residual`. Every field is constructed from the
supplied profiles, the same selected word, and the same moving marks. No
unrelated minimum-law realizer, source, or fixed calendar date is introduced.

### 7. Rank and downstream trace

Attach a positive-minimum debt tangent family at the regenerated source
\(y\), and build the existing FinFourRenewableMinimumSourceNode. Its recursive
minimum-fibre child transition strictly lowers positive-debt support; its
other outputs are the named tangent exits.

Use the three-state phase tag in (7). At entry, the tangent rank is at most
\(1+3=4<5\). Every recursive child edge strictly lowers the support
cardinality, and a terminal edge lowers the rank to zero. No constructor
returns to the origin phase. Hence this is a well-founded natural-valued rank
on the constructed lane. The checked inequality that trace length is
strictly below initial support cardinality gives at most two later recursive
descents.

The strict inclusion (3) is an actual full-cap statement between the two
regenerated semantic points. The paired wrapper additionally retains the
literal copied-prefix response from the source approximants to the target
approximants. This is stronger than merely remembering an unprefixed suffix
edge, but it is not a Nash--Bellman temporal edge.

This completes C and the theorem.

## Boundary tests

### Exact affine-support test

The debt vectors

\[
 d(x)=(1,0,0,0),\qquad d(y)=(0,1,0,0)
\]

have the same total debt one. The forced chord identity gives

\[
 d(h^s)=(1-s,s,0,0),
\]

so \(\operatorname{supp}^+(y)=\{1\}\) is a strict subset of
\(\operatorname{supp}^+(h^s)=\{0,1\}\). This checks that killing the mover
need not make every other coordinate unchanged; the theorem needs only
coordinatewise affine transport.

### Off-minimum target

If

\[
 d(x)=(1,0),\qquad d(y)=(0,2),
\]

then a midpoint debt vector \((1/2,1/2)\) satisfies the cap-convexity upper
bound but is strictly below its affine right side \((1/2,1)\). Thus
coordinatewise affine equality cannot be inferred when the target is off
minimum. The \(e_n\)-split is essential.

### Positive residual

If \(R_n\to R>0\), then the mover is not killed at the target and (2)--(3)
need not hold. The actual-reach row is the correct output; silently setting
\(R=0\) would erase a complete behavioral response which changes strategy
before the mark.

### Vanishing marked reach

If \(L_n\to0\), both the mover gain \(L_n\Delta\) and the new \(K'\)-atom can
vanish. Source-faithful causalization then has no positive marked atom to
retain. The uniform floor \(\lambda>0\) is necessary.

### Common subsequence

Independently compactifying \(Y_n\) and \(H_n^s\) can choose unrelated limit
points, making (1) and (4) meaningless. The proof uses one finite-product
compactification and retains the same literal indices throughout.

### Copied prescribed prefix versus shifted response

The tempting shifted response is invalid for this purpose: it forces \(q\)
to Continue through the inserted word and therefore does not start at the
prescribed prefixed source. The construction instead copies every prescribed
prefix action to both \(A_n\) and \(P_n\) and changes only the suffix. This is
why the update is literal.

Nonemptiness in (20) is a real boundary. If \(W\) is empty and
\(B_i(T)<r_i(\{i\})\), its right side is zero but its displayed maximum need
not equal \(B_i(T)\). Here \(|W_n|=n+1\), so no rank has an empty word. The
strict singleton moat (21) is also essential: without it, even a vanishing
prefix can leave singleton cash-out as the limiting cap instead of the tail
cap.

### Arbitrary earlier absorption and tail

Equations (9)--(11) use only equality before the marked row and sure
absorption at the marked pure pair. Earlier terminal outcomes cancel, and
the post-mark tail is unreachable on the marked reach event. No Never-tail,
zero-earlier-absorption, or date-zero assumption is used.

## Adapter and consumer

The maintained question describes the desired actual screened-pair source;
it is not itself a checked source adapter. Finite pigeonholing fixes the pair
\(K\), mover \(q\), and endpoint orientation only after an upstream family
has supplied a strictly profitable orientation at every selected rank. The
resulting table difference \(\Delta\) is then one fixed positive number. Its
positivity is a hypothesis inherited from that family, not a consequence of
\(D_*>0\). No current declaration constructs the whole moving-marked-pair
contract from `FinFourMinimumAtomProducer`, so the present theorem has no
global actual-source seal.

If a pair member already has a strict locally profitable leave, changing that
member only at the marked row gives a literal source-attached response with
gain equal to marked reach times its fixed reward difference. The theorem
addresses the complementary outsider-join arm.

Output A enters the existing universal paid-cap-port waist when its explicit
cap-port dispatch field is returned. Output B does so only after the supplied
off-minimum-ancestry adapter required above is public and applied; the bare
endpoint/excess conclusion is not that adapter. Output C regenerates a
complete same-residual source and enters the existing renewable tangent trace.
Its incoming literal behavioral edge is exposed by the paired-ancestry wrapper
rather than falsely attributed to the ordinary child producer. No branch
replaces the source by a normalized mass-one pair.

The consumer is a strict reduction, not terminal UE. Output C can recurse
only through strict support descent and reaches a positive-slope,
support-entry, or off-minimum paid terminal exit. Outputs A and B retain the
open debt-descent/inert paid-port arms. No claim is made that those outputs
are already consumed.

## Lean handoff

The narrow implementation should define a packet extending one supplied
FinFourMinimumAtomProducer with:

1. actual profiles \(X_n\), marks \(t_n\), the fixed pair \(K\), and mover
   \(q\);
2. literal endpoint profiles \(Y_n\) and their one-row update equality;
3. the uniform marked-stage mass floor;
4. convergence of \(X_n\) to the source point; and
5. the positive endpoint reward gap.

This packet is a supplied-data contract. No constructor from the bare
`FinFourMinimumAtomProducer` is claimed. The branch result should be a
data-bearing sum whose constructors each store their `select` map and
`StrictMono select`. The minimum constructor additionally stores the named
residual, excess, compactness, and finite-tail selectors, their literal
composition, and the fact that all profile, law, reach, and mark families are
pulled back through that same composition.

Suggested proof order:

1. prove the payoff, mover-debt, and full-law identities (9)--(11);
2. split \(R_n\) by strict subsequence and use
   positiveDebt_exists_actualJointReach_paidRow_mem_support in the positive
   branch;
3. split \(e_n\) on the zero-residual refinement;
4. compactify \((Y_n,H_n^s,L_n)\) jointly;
5. reuse quittingTerminalSemanticDebt_responseChord_le and the
   minimum-sum squeeze to construct a QuittingMinimumResponseChordLaw;
6. causalize \(H_n^s\), retain its nonempty word \(W_n\), and prove the
   unrestricted cap estimate (20);
7. define \(A_n=W_n\star H_n^s\) and \(P_n=W_n\star Y_n\), prove the literal
   update equality and (22)--(24), choose one strict tail selector on which
   the \(\lambda/2\) floor holds at every rank, then causalize the reindexed
   \(P_n\) at the correspondingly reindexed shifted mark;
8. assemble both producers by copying the input source fields, following the
   pattern of FinFourMinimumAtomProducer.regeneratedAtLawPoint, and define the
   paired-ancestry wrapper as a separate structure;
9. attach the node at \(y\) using
   exists_positiveMinimumDebtTangentFamily_of_pair; and
10. define the one-use origin/tangent/terminal state and prove rank decrease.

For the off-minimum arm, expose a public supplied-ancestry version of the
currently private `offMinimumAncestry_exists_actualReachPaidPort`, and return
its paid-cap dispatch if that branch is to carry a consumer seal.

Tests should include \(s=1/2\), both orientations of a one-coordinate
endpoint toggle, a moving mark \(t_n=n\), profiles with nonzero earlier
absorption, an arbitrary post-mark tail, positive residual, off-minimum
target, an empty-word countertest for (20), early Quit, arbitrarily late Quit,
Never, and the difference between shifted and copied-prefix responses.

The theorem should not be encoded by storing the affine identity, support
drop, or regenerated sources as assumptions. They are conclusions of
compactness, convexity, global minimality, and causalization.

## Evidence status

- **M:** PASS as ordinary mathematics with the explicit selector, supplied
  ancestry, and branch-output repairs above.
- **L:** absent for this packet. The cited debt-chord, causalization,
  paid-row, and renewable-trace declarations are checked ingredients, not a
  checked moving-marked-pair dispatch.
- **A:** absent globally. No checked theorem currently constructs the
  moving-marked-pair contract, including fixed \(K,q,K'\), \(\Delta>0\), and
  the uniform marked-reach floor, from a bare minimum source.
- **C:** absent for the packet as a whole. The positive-residual and renewable
  branches have matching conditional consumers once their literal adapters
  are built. The off-minimum branch still needs the public supplied-ancestry
  paid-port adapter described above. None of these compositions is a uniform
  equilibrium theorem.

## Scope and nonclaims

- This is ordinary mathematics, not yet checked in Lean.
- It does not prove a uniform-equilibrium payoff or a Fin4 counterexample.
- It does not consume the universal off-minimum paid-port waist.
- It does not consume positive-slope, support-entry, or off-minimum exits of
  the renewable tangent trace.
- It does not produce a punishment-floor-admissible Nash--Bellman edge.
- The paired ancestry is an explicit wrapper; it is not a field of the
  existing FinFourMinimumAtomProducer.
- It does not assert that the target causalization reuses \(W_n\); only the
  pre-causalization target \(P_n\) uses the copied source word.
- It does not replace a moving marked row by a date-zero mass-one pair.
- It does not replace the actual tail by Never.
- The origin phase is one-use inside this construction; arbitrary returns
  from an outer atlas are not assigned the same rank.
- Its completeness is only up to strict subsequence extraction, stated
  explicitly in the theorem.

## Lean formalization record

The packet prefix above is preserved at SHA-256
`29a7559862bdf9750c5a51a9c52fcfe04942bba34510a2d7e4bae0f9fbbc7121`.
Its checked implementation landed in commit
`8fd6a10c8f573641e0f475e8dedc1fef7632c465`.

The generic positive-floor/vanishing split is
`Math.nonempty_nonnegativeSubsequenceAlternative` in
`MathUE/Topology/NonnegativeSubsequenceDichotomy.lean`.  Complete
terminal-law transport behind varying almost-silent common words is provided
by
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/CommonPrefixTerminalLawStability.lean`.

The supplied moving-family interface and its exact marked-toggle payoff,
debt, law, and chord identities are in
`Research/Quitting/FinFourProducerAtlas/MovingMarkedPairSource.lean` and
`MovingMarkedPairChordMarkedMass.lean`.  The host is only required to be
nonempty.  When the mover is routed to Continue, the distinct surely quitting
screening player proves target nonemptiness; no support-cardinality theorem is
deduced from the host size.

`nonempty_finFourMovingMarkedPairResidualAlternative` and
`nonempty_finFourMovingMarkedPairPrecompactAlternative` split the supplied
family into the positive-residual, off-minimum, and minimum-approach arms.
`nonempty_finFourMovingMarkedPairOffMinimumActualReachPaidPortAt` supplies the
off-minimum actual-reach port.  In the minimum arm,
`nonempty_finFourMovingMarkedPairMinimumChordCompactification` constructs the
literal fixed-weight stopping-law chord and proves its target support is
nonempty of cardinality at most three.
`nonempty_finFourMovingMarkedPairCommonPrefixResponse` supplies the common
exact cap--Nash prefix and complete payoff, cap, debt, and law convergence.
`nonempty_finFourMovingMarkedPairSameResidualSupportDescent` retains the
literal response edge while regenerating at the target law point, and
`nonempty_finFourMovingMarkedPairSupportContractedRenewal` attaches the
neutral renewable trace.  The exhaustive checked interface is
`nonempty_finFourMovingMarkedPairSupportDescentAlternative`.

- **M:** complete for the supplied moving-family compiler.
- **L:** complete as checked Research Lean, with the generic prerequisites
  integrated under the production umbrellas.
- **A:** absent; no theorem constructs the moving family, its fixed labels,
  positive reward gap, or uniform marked-reach floor from a bare source.
- **C:** branch-local.  The off-minimum arm reaches the checked paid port and
  the minimum arm reaches same-residual support-contracted renewal.

The result does not identify the public paired chronology with the regenerated
producer's internal chronology, consume the resulting terminal exit, construct
a Nash--Bellman temporal edge, prove terminal approximation, or establish a
uniform-equilibrium payoff or counterexample.
