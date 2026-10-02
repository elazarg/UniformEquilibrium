# Normalized oriented pure pair: singleton response or one-use renewable-lane entry

Identity: `PAIRED_HULL_REVIEW`

## Status

**Adapter retracted.** Sections 2--7 prove a correct local
ordinary-mathematics theorem for an **attained mass-one date-zero pure-pair
global minimum with a Never tail**. That normalized object is not the actual
screened endpoint supplied by the source atlas.

**Normalized local compiler integrated.** Commit
`c83e30b5d738cdb71be53b40ba6b07cf88f8cbab` proves the valid normalized
dispatch and minimum-fibre chord in Lean.  The thin literal-profile adapters
are in
`UniformEquilibrium/Diagnostics/Quitting/PureCoalitionOneDateNeverAdapters.lean`;
the compiler is in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FinFourOrientedMinimumPairChord.lean`.
In particular,
`FinFourOrientedMinimumPairData.terminalDispatch_nonempty`,
`pairToJoinedTripleChord_debt_eq`,
`pairToJoinedTripleChord_debtSum_eq`,
`quitNowResponse_from_pairToJoinedTripleChord_gain_eq`, and
`joinedTripleResponse_from_midpoint_gain_eq_half` are checked declarations.
This gives the normalized local result seals `M` and `L` only.  It supplies no
actual-source `A` for the screened endpoint and no source regeneration or
renewable downstream `C`.

Section 4.1 adds an ordinary-mathematics strengthening not contained in those
checked declarations: even when the joined triple is off minimum, an old pair
member has a complete leave response from it of gain at least \(D_*/2\).

The real screened endpoint retains an arbitrary pre-mark calendar, possible
earlier absorption, and its literal post-mark continuation. Its marked pair
is pure only conditionally on reaching the row. Replacing it by the
mass-one profile \(M^{\{a,b\}}\) discards precisely the source data that a
consumer must preserve. In particular:

- a local endpoint defect at the marked pair scales to an actual payoff gain
  by the marked-row live mass;
- but an unrestricted behavioral response may change actions before the
  marked row, so the whole-profile debt need not equal that scaled local
  defect;
- the simultaneous overwrite that installs the pure pair is not asserted
  profitable, cap--Nash, or minimum; and
- a minimum conditional spine does not imply that the corresponding
  whole-profile pure sibling is a global minimum.

Therefore the screened-endpoint claim has **no actual-source seal and no
export seal**, and its former claim that the screened pair enters the
renewable lane is withdrawn. The withdrawn export must not be used as an
atlas adapter.  The integrated `M/L` result applies only to the supplied
normalized date-zero data described above.

For the normalized input, the valid trichotomy remains:

1. a pair member has a positive full-behavior pair-to-singleton response;
2. the other outsider has a full response of gain \(D_*\) to an off-minimum
   triple, which is exactly the open paid-port waist; moreover, one old pair
   member was leave-indifferent at the pair and has a full leave response from
   that triple of gain at least \(D_*/2\); or
3. that triple is also minimum, and the complete one-player chord is minimum.
   The triple regenerates as a complete same-residual source and enters the
   already checked renewable tangent lane through a one-use phase transition.

The normalized minimum-chord calculation also proves a strict one-time support inclusion
from the half-chord profile to the triple and bounds the triple's support by
two. It does **not** instantiate checked
`FinFourRenewableMinimumSourceNode.nonempty_supportDescent`: that theorem
requires absence of inactive-coordinate entry for every active mover column,
whereas the chord controls only the distinguished outsider column.

Thus the normalized pair minimum-fibre arm has a renewable lane entry, not a
new recursive support edge. This statement is conditional on the normalized
profile itself being the actual global-minimum source. It does not apply to
the maintained screened endpoint without the additional localization
hypotheses isolated in Section 14.

Section 15 records the unconditional marked-row residual decomposition and
localizes every positive residual to a source-supported paid pure-time row
strictly before the mark.  This is still not a renewed pair source or an exact
Nash--Bellman prefix edge.

Section 17 gives a reviewed ordinary-mathematics reduction for the moving
approximant arm: joint compactification of the full literal
source/endpoint/chord profiles forces coordinatewise affine debt at the
minimum limit and regenerates a strict-support child while retaining the
moving marks. Copying the source causalization's prescribed word onto the
target also gives a literal prefixed behavioral response edge, stored in an
explicit paired-ancestry wrapper. Its hypotheses explicitly retain the incoming complete
`FinFourMinimumAtomProducer` and its hard residual. The trichotomy is only
asserted after strict subsequence extraction. It is not a prefixed
Nash--Bellman edge or terminal consumer.

The normalized local dispatch and chord described in Sections 1--7 are now
proved in Lean by the declarations above.  The later support, atlas-source,
causalization, and regeneration sections remain ordinary mathematics or
conditional proposals, not integrated declarations.  The checked cap
identities quantify over unrestricted behavioral responses, including Never
and arbitrarily late stopping.  Section 14 records the strongest honest
source-faithful conditional lift and the missing producer field.

## 1. Exact theorem

Let \(I=\operatorname{Fin}4\), and let \(D_*>0\) be the global minimum of
terminal-semantic total debt. Fix distinct players \(a,b,p,q\), put

\[
 K=\{a,b\},\qquad K_p=K\cup\{p\},\qquad K_q=K\cup\{q\},
\]

and write \(M^S\) for the product profile in which exactly the members of
\(S\) Quit surely at date zero and everyone else plays Never.

Assume:

* \(X=M^K\) is an actual global-minimum profile, so \(D(X)=D_*\);
* the retained source ancestry contains the strict full endpoint edge
  \(M^{K_p}\to X\) in which \(p\) changes Quit to Continue.

All tails are literally Never. The law of \(X\) is the pair atom \(K\) with
mass one.

> **Oriented minimum-pair theorem.** One of the following holds:
>
> 1. one of \(a,b\) has a strict full Continue best response from \(X\) to a
>    singleton;
> 2. \(q\) is the unique debtor of \(X\), its full Quit response has gain
>    \(D_*\), and its target \(Y=M^{K_q}\) is strictly off minimum; moreover,
>    some \(i\in\{a,b\}\) was exactly leave-indifferent at \(X\) and has a
>    full Continue response from \(Y\) of gain at least \(D_*/2\); or
> 3. \(q\) is the unique debtor, \(Y\) is minimum, and:
>    \[
>      \varnothing\ne\operatorname{supp}^+(Y)\subseteq\{a,b\};
>    \]
>    every point \(H_t\) on the literal \(q\)-response chord is minimum;
>    \[
>      \operatorname{supp}^+(Y)
>        \subsetneq\operatorname{supp}^+(H_{1/2});
>    \]
>    and \(Y\) regenerates as a complete same-residual minimum source which
>    enters the checked renewable tangent trace with a strict phase-tagged
>    natural-rank decrease.

The alternatives are exhaustive. No claim is made that alternative 2 is
already consumed. If the screened dispatcher reaches an off-minimum pair
rather than the assumed minimum \(X\), it has already reached the same open
paid-port waist.

## 2. Complete cap and debt formula at the pair

At \(X=M^K\), every player has a sure date-zero quitting opponent. Any
unilateral behavioral response is therefore screened at date zero. For a
member, the only values are staying in the pair and leaving it; for an
outsider they are staying outside and joining it. Hence

\[
\begin{aligned}
d_a(X)&=[r_a(\{b\})-r_a(K)]_+,\\
d_b(X)&=[r_b(\{a\})-r_b(K)]_+,\\
d_p(X)&=[r_p(K_p)-r_p(K)]_+,\\
d_q(X)&=[r_q(K_q)-r_q(K)]_+.
\end{aligned}
\tag{2.1}
\]

These are complete behavioral debts. The incoming strict dropout says

\[
 r_p(K)>r_p(K_p),
\tag{2.2}
\]

and therefore

\[
 d_p(X)=0.
\tag{2.3}
\]

## 3. The profitable singleton branch

If

\[
 r_a(\{b\})>r_a(K)
 \quad\text{or}\quad
 r_b(\{a\})>r_b(K),
\tag{3.1}
\]

the corresponding member's complete best response is to Continue at date
zero. The terminal singleton occurs with probability one, and the
continuation is never reached. The exact whole-profile gain is the positive
difference in (3.1). Because only the mover changes strategy, its cap is
unchanged and its target debt is zero.

This is the requested strategically oriented pair-to-singleton route. It is
not the unsigned route stored by `QuittingSameStageSingletonRoute`.

## 4. Failure of the singleton branch leaves one outsider debtor

Assume neither member leaves profitably. From (2.1)--(2.3) and
\(D(X)=D_*>0\),

\[
 d_a(X)=d_b(X)=d_p(X)=0,
 \qquad d_q(X)=D_*.
\tag{4.1}
\]

Thus

\[
 r_q(K_q)-r_q(K)=D_*>0,
\tag{4.2}
\]

so \(q\)'s unique endpoint best response is

\[
 X=M^K\longrightarrow Y=M^{K_q}.
\tag{4.3}
\]

Its exact gain is \(D_*\), and \(d_q(Y)=0\). This is a literal full response
inside the normalized profile family. It is horizontal replacement, not
automatically an exact Nash--Bellman predecessor edge or an actual screened-
source edge.

### 4.1 The joined triple always has a paid old-member leave

The following local strengthening does **not** assume that \(Y\) remains on
the minimum fibre. For \(0\leq t\leq1\), let \(Z_t\) keep \(a,b\) surely
quitting at date zero and \(p\) playing Never, while \(q\) Quits at date zero
with probability \(t\). Thus \(Z_0=X\) and \(Z_1=Y\).

For each old pair member \(i\in K\), put

\[
 A_i=r_i(K\setminus\{i\})-r_i(K)\leq0,
 \qquad
 C_i=r_i((K\setminus\{i\})\cup\{q\})-r_i(K_q).
\tag{4.4}
\]

The sure other member of \(K\) screens every unilateral response at date
zero, so the unrestricted behavioral debts are exactly

\[
 d_i(Z_t)=[(1-t)A_i+tC_i]_+
 \qquad(i\in K).
\tag{4.5}
\]

Likewise \(q\)'s two endpoint values are \(r_q(K)\) and \(r_q(K_q)\).
Equation (4.2) therefore gives

\[
 d_q(Z_t)=(1-t)D_*.
\tag{4.6}
\]

Player \(p\)'s join-versus-stay-out difference is affine in \(t\) and is
strictly negative at \(t=0\) by (2.2). Hence \(d_p(Z_t)=0\) for every
sufficiently small positive \(t\). Global minimality then yields

\[
 D_*
 \leq D(Z_t)
 =(1-t)D_*+\sum_{i\in K}[(1-t)A_i+tC_i]_+,
\tag{4.7}
\]

and consequently

\[
 \sum_{i\in K}[(1-t)A_i+tC_i]_+\geq tD_*.
\tag{4.8}
\]

Divide by \(t\) and let \(t\downarrow0\). If \(A_i<0\), the corresponding
positive part vanishes on a neighborhood of zero. Hence

\[
 \sum_{i\in K:A_i=0}[C_i]_+\geq D_*.
\tag{4.9}
\]

Since \(|K|=2\), there exists \(i\in K\) with

\[
 A_i=0,
 \qquad
 C_i\geq D_*/2.
\tag{4.10}
\]

At \(Y=M^{K_q}\), player \(i\)'s pure Continue response changes the
date-zero coalition from \(K_q\) to \((K\setminus\{i\})\cup\{q\}\). Another
sure quitter remains, so this is a complete unrestricted-behavior response
of exact gain \(C_i\geq D_*/2\). Thus the hard normalized pair branch always
contains the literal two-edge square

\[
 M^K\xrightarrow[q\text{ joins}]{D_*}M^{K_q}
 \xrightarrow[i\text{ leaves}]{\geq D_*/2}
 M^{(K\setminus\{i\})\cup\{q\}}.
\tag{4.11}
\]

This is a local normalized statement only. It does not supply the missing
actual-screened-source adapter, and neither horizontal response is thereby a
Nash--Bellman temporal edge. The final pair in (4.11) need not be a global
minimum.

If \(D(Y)>D_*\), the first edge is the open off-minimum paid-port output,
now carrying the additional paid old-member response (4.11). It remains to
consider \(D(Y)=D_*\).

## 5. Coordinatewise affine minimum-chord identity

For \(0\le t\le1\), let \(H_t\) be obtained from \(X\) by making \(q\) Quit
at date zero with probability \(t\). The other strategies and the Never tail
are unchanged. Thus \(H_0=X\) and \(H_1=Y\).

Prescribed payoffs are affine in \(t\). Player \(q\)'s cap is independent of
its own strategy, so

\[
 d_q(H_t)=(1-t)D_*.
\tag{5.1}
\]

For \(i\ne q\), each fixed complete deviation has payoff affine in \(q\)'s
mixture. The supremum of these affine payoffs obeys

\[
 B_i(H_t)\le(1-t)B_i(X)+tB_i(Y).
\]

Subtracting the affine prescribed payoff and using \(d_i(X)=0\),

\[
 d_i(H_t)\le t d_i(Y).
\tag{5.2}
\]

Equations (5.1)--(5.2) imply \(D(H_t)\le D_*\). Global minimality gives the
reverse inequality, so

\[
 D(H_t)=D_*
 \qquad(0\le t\le1).
\tag{5.3}
\]

For \(i\ne q\), the defects

\[
 e_i(t):=t d_i(Y)-d_i(H_t)
\]

are nonnegative. Since \(D(Y)=D_*\), \(d_q(Y)=0\), and (5.1), (5.3) hold,

\[
\begin{aligned}
\sum_{i\ne q}e_i(t)
 &=t\sum_{i\ne q}d_i(Y)-\sum_{i\ne q}d_i(H_t)\\
 &=tD_*-\bigl(D_*-(1-t)D_*\bigr)=0.
\end{aligned}
\]

Therefore every defect vanishes:

\[
 d_i(H_t)=t d_i(Y)\qquad(i\ne q).
\tag{5.4}
\]

For \(0<t<1\),

\[
 \operatorname{supp}^+(H_t)
   =\{q\}\cup\operatorname{supp}^+(Y),
 \qquad
 \operatorname{supp}^+(Y)
   \subsetneq\operatorname{supp}^+(H_t).
\tag{5.5}
\]

The strict incoming \(p\)-dropout sharpens this. Player \(p\)'s
join-versus-stay-out difference is affine in \(t\) and strictly negative at
\(t=0\) by (2.2). Hence \(d_p(H_t)=0\) for all sufficiently small positive
\(t\). Equation (5.4) forces

\[
 d_p(Y)=0.
\tag{5.6}
\]

Together with \(d_q(Y)=0\) and \(D(Y)=D_*>0\),

\[
 \varnothing\ne\operatorname{supp}^+(Y)\subseteq\{a,b\},
 \qquad |\operatorname{supp}^+(Y)|\le2.
\tag{5.7}
\]

If \(d_a(Y)>0\), then (5.4) makes \(a\)'s leave debt positive at every
\(H_t\), \(t>0\). Its endpoint difference is affine in \(t\), and at \(X\)
it is nonpositive by failure of (3.1); it must therefore be exactly zero at
\(X\). Thus every member activated at \(Y\) was already an exact
pair-to-singleton tie at \(X\). At least one such member exists by (5.7).

At \(t=1/2\), the full response \(H_{1/2}\to Y\) has exact gain \(D_*/2\),
kills \(q\)'s debt, and has the strict one-time support inclusion (5.5).

## 6. Exact source regeneration at the triple

The profiles \(H_{1/2}\) and \(Y\) are literal product profiles in the
carrier, on the same date-zero calendar and Never tail. Both absorb at date
zero with probability one. At \(H_{1/2}\), coalitions \(K\) and \(K_q\)
each have mass \(1/2\); at \(Y\), coalition \(K_q\) has mass one.

For \(Y\), construct a complete source without selecting another realizer:

1. use the constant suffix profile sequence \(Y_n=Y\);
2. retain date zero and coalition \(K_q\);
3. prefix \(n+1\) copies of the all-Continue root at the semantic cap of
   \(Y\).

At a positive global minimum,
`minimumTerminalSemantic_is_allContinuePlateau` makes that root exact
cap--Nash and makes its semantic prefix neutral. Thus every stack is exact,
its Continue product is one, the prefixed debt is constantly
\(D_*=\inf D\), and the marked atom reappears at the shifted date with mass
one. Suffix cutoff one and mark zero verify
`QuittingMinimumLawCausalSuffixAtom`, and unpacking it gives a
`FinFourMinimumAtomChronology`. Copy the incoming hard residual literally.
This produces a `FinFourMinimumAtomProducer` whose joint point is the actual
semantic/law point of \(Y\).

Now apply the checked
`exists_positiveMinimumDebtTangentFamily_of_pair` at the exact semantic pair
of \(Y\), and assemble
`FinFourRenewableMinimumSourceNode` from the regenerated source, its literal
chronology, and that tangent family. This is permitted by the node's checked
definition: the tangent sequence need not be the source chronology, while
the complete source and hard residual remain attached literally.

No supplied-profile tangent adapter is needed, and no claim is made that
\(H_{1/2}\to Y\) inhabits checked `nonempty_supportDescent`.

## 7. Honest one-use phase rank

Define a proof-state type with:

* one `incoming` state containing the oriented pair, \(H_{1/2}\), and the
  literal response \(H_{1/2}\to Y\);
* ordinary `tangent node` states
  `FinFourRenewableMinimumSourceNode`;
* one `terminal` state.

Assign ranks

\[
 \rho(\text{incoming})=6,\qquad
 \rho(\text{tangent node})=
   1+|\operatorname{supp}^+(\text{node})|,
 \qquad
 \rho(\text{terminal})=0.
\tag{7.1}
\]

The legal transitions are:

\[
\begin{aligned}
\text{incoming}&\longrightarrow\text{the regenerated }Y\text{ node},\\
\text{tangent parent}&\longrightarrow
  \text{checked strict-support child},\\
\text{tangent node}&\longrightarrow\text{declared exit}.
\end{aligned}
\tag{7.2}
\]

For the normalized theorem, the first transition is literal and
source-attached by Sections 5--6. It strictly lowers rank: (5.7) gives target
rank at most three, and the generic Fin4 bound would already give at most
five. Later recursive transitions are
exactly the checked strict support descents. No constructor targets
`incoming`, so regeneration cannot reset rank six.

This is the same one-way phase discipline as
`CanonicalPairRenewableSourceRank`. The strict inclusion (5.5) explains the
geometry of the entrance, but the formal rank proof uses the nonrecurring
phase tag and does not pretend that the distinguished-column calculation
controls all columns of an arbitrary tangent family.

The checked `nonempty_renewalTrace` now applies from the \(Y\) node. It ends
at positive total slope, flat support entry, or an off-minimum paid
first-disagreement endpoint. Those declared exits remain open consumers.

## 8. Insider ties and strict refusals

If \(r_a(\{b\})=r_a(K)\), then \(X\to M^{\{b\}}\) is a zero-gain complete
response. If that singleton is minimum, its owner carries all debt by the
minimum singleton margin, and the checked pure-time descent eventually exits
to an off-minimum paid port. This is not a positive pair-to-singleton edge.

If \(r_a(\{b\})<r_a(K)\), then \(M^{\{b\}}\) cannot be a positive global
minimum: outsider \(a\) has positive join debt there, while the minimum
singleton margin puts debt at least \(D_*\) on owner \(b\), exhausting total
minimum debt. The singleton face is therefore off minimum. The same
statements hold with \(a,b\) exchanged.

## 9. Existing dropout and charged-edge interfaces

`exists_positive_pair_to_singleton_dropout_of_finalDefect_eq_zero` needs a
supplied finite fractional-reset word ending at zero total Nash defect. It
extracts a cardinal crossing but gives it no payoff sign.

`exists_signed_pairDropout_negativeMoat_or_pairReplacement` additionally
requires every move to select the better endpoint. Under strict member
refusal the Continue dropout selects the worse endpoint, exactly as recorded
by `TerminalSemanticPairDropoutSignRegression.lean`. The pure pair alone
also gives no finite better-endpoint word ending at zero defect.

The positive edge (4.3) is not directly a
`QuittingPositiveAdmissibleReturn` edge. That structure requires an exact
Nash--Bellman predecessor edge between punishment-floor states. At \(X\),
\(q\)'s coordinate root defect is \(D_*>0\). Calling the horizontal gain
temporal charge would be a type error.

## 10. Exact sign tests

Take \(K=\{0,1\}\), \(p=2\), \(q=3\), and prescribe the relevant rewards by

\[
\begin{array}{c|cccc}
 &r_0&r_1&r_2&r_3\\ \hline
K&0&0&1&0\\
K_p&*&*&0&*\\
K_q&0&0&*&1\\
\{1\}&0&*&*&*\\
\{0\}&*&0&*&*
\end{array}
\]

with omitted entries low enough not to create another displayed endpoint
gain. Then \(p\) strictly leaves \(K_p\), neither member strictly leaves
\(K\), and \(q\) joins \(K\) with gain one. The only pair debt is \(q\)'s.
Thus incoming orientation alone does not force branch 1.

For a flat-chord check, set \(r_0(\{1,3\})=1\) while retaining
\(r_0(K)=r_0(K_q)=0\). Along the \(q\)-mixture, \(q\)'s debt is \(1-t\) and
player \(0\)'s is \(t\), so total debt is identically one. Player \(0\)'s
dropout is tied at \(t=0\) and strict at \(t=1\), matching Section 5.

These are local exact tests, not positive-gap counterexamples; singleton
rewards may be chosen so all-Never has zero debt. They only rule out deriving
a positive member dropout from the finite pair signs without global
minimality.

## 11. Checked inputs and new mathematics

Named checked inputs:

* `minimumTerminalSemantic_is_allContinuePlateau`;
* the pair-dropout sign regression;
* `exists_positiveMinimumDebtTangentFamily_of_pair`;
* `FinFourRenewableMinimumSourceNode` and its source-regeneration interfaces;
* `FinFourRenewableMinimumSourceNode.nonempty_renewalTrace`; and
* `CanonicalPairRenewableSourceRank` as the phase-rank template.

New ordinary mathematics:

* the pair debt split (2.1)--(4.2);
* the coordinatewise affine chord identities (5.1)--(5.5);
* the strict-incoming exclusion (5.6), support bound (5.7), and forced tie;
* the explicit constant-profile causal chronology for \(Y\); and
* the one-use normalized oriented-pair entrance into the existing renewable
  trace.

These statements are not exportable as an actual-source result. The source
construction and entrance transition are relevant only after an independent
producer supplies the normalized input or the localization data of
Section 14.

## 12. Sources checked

* `Research/Quitting/FinFourPureNonsingletonCollisionScreening.lean`;
* `Research/Quitting/SameStageEndpointMonodromyImpossible.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauFractionalResetDropout.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSignedPairDropoutConsumer.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPairDropoutSignRegression.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/MinimumFiberSupportDrop.lean`;
* `Research/Quitting/FinFourProducerAtlas/Source.lean`;
* `Research/Quitting/FinFourProducerAtlas/CanonicalPairEndpointSourceRegeneration.lean`;
* `Research/Quitting/FinFourProducerAtlas/CanonicalPairFullReplacementSourceRegeneration.lean`;
* `Research/Quitting/FinFourProducerAtlas/CanonicalPairRenewableSourceRank.lean`;
* `Research/Quitting/SourceFaithfulMinimumLawCausalization.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualReachPaidFirstDisagreement.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMinimumFiberAffine.lean`.

## 13. Lean handoff

Suggested declarations:

```text
FinFourOrientedMinimumPairTerminalDispatch
  .positivePairToSingleton
  .offMinimumUniqueOutsiderJoin
  .minimumUniqueOutsiderJoin

nonempty_finFourMinimumAtomProducer_of_pureTripleMinimum
nonempty_orientedPairMinimumRenewableNode

OrientedPairRenewableState
OrientedPairRenewableTransition
orientedPairRenewableRank
orientedPairRenewableTransition_rank_lt
nonempty_orientedPairRenewalTrace
```

The pure-triple source constructor must retain the constant actual profile
and its date-zero atom. It must not replace \(Y\) by an arbitrary minimum-law
realizer.

## 14. Strongest honest marked-row lift

There is a source-faithful conditional version, but the current screened
packet does not supply its decisive hypothesis.

Let \(X\) now be an actual behavioral profile with arbitrary earlier calendar
and arbitrary tail. Suppose that at an actually reached date \(t\), of live
mass \(L>0\), its root is the pure pair \(K=\{a,b\}\). Let \(p,q\) be the two
outsiders, and retain a strict same-row \(p\)-dropout into \(K\). Let \(Y\)
be the literal profile obtained by changing only \(q\)'s action at date \(t\)
from Continue to sure Quit, so the reached root becomes \(K_q\). All earlier
actions, earlier absorption, off-path prescriptions, and the post-mark tail
remain unchanged.

Assume the following **whole-profile marked-row localization**:

\[
\begin{aligned}
D(X)&=D_*,\\
d_a(X)&=d_b(X)=d_p(X)=0,\qquad d_q(X)=D_*,\\
U_q(Y)-U_q(X)&=D_*.
\end{aligned}
\tag{14.1}
\]

The last line says that the complete cap debt of \(q\), not merely its local
conditional endpoint defect, is attained by this literal reached-row update.
It implies \(d_q(Y)=0\), because changing \(q\)'s own strategy does not change
its unrestricted cap.

If \(D(Y)>D_*\), \(X\to Y\) is a literal source-faithful off-minimum paid
port. If \(D(Y)=D_*\), mix only \(q\)'s action at the same marked row and call
the resulting whole profile \(H_s\), \(0\le s\le1\). Fixed-response payoffs
are affine in \(s\), while every nonmover cap is a supremum of affine
functions. Exactly the same convexity argument as in Section 5 gives

\[
\begin{aligned}
d_q(H_s)&=(1-s)D_*,\\
d_i(H_s)&=s\,d_i(Y)\qquad(i\ne q),\\
D(H_s)&=D_*.
\end{aligned}
\tag{14.2}
\]

Hence, for \(0<s<1\),

\[
\operatorname{supp}^+(Y)
\subsetneq
\operatorname{supp}^+(H_s),
\qquad
\varnothing\ne\operatorname{supp}^+(Y)
\subseteq I\setminus\{q\}.
\tag{14.3}
\]

Unlike the normalized calculation, the strict local \(p\)-dropout does not
force \(d_p(Y)=0\): another complete response of \(p\), possibly before the
marked row, may become optimal immediately along the \(q\)-chord. Thus the
honest bound is

\[
|\operatorname{supp}^+(Y)|\le3,
\tag{14.4}
\]

not the normalized bound two.

The minimum target \(Y\) nevertheless regenerates source-faithfully. Its
unconditional \(K_q\)-mass at the marked date is exactly \(L>0\). Use the
constant suffix sequence \(Y\), retain the same date \(t\), prefix only
all-Continue plateau roots, and copy the same reward-table residual. This
keeps every original earlier row and the literal tail inside the suffix,
while shifting the entire actual profile by the neutral prefix. It gives a
complete minimum source at the exact semantic/law point of \(Y\), followed by
the same one-use phase entry into the renewable tangent lane. The target
support has cardinality at most three, so the phase rank still decreases.

Thus (14.1) would salvage a genuine source-faithful theorem:

\[
\boxed{
\text{localized marked pair}
\Longrightarrow
\text{off-minimum paid port}
\ \lor\
\text{regenerated minimum child with a one-use support drop}.
}
\tag{14.5}
\]

What the current screened packet supplies is only the local conditional
endpoint formula and the scaled payoff identity

\[
\text{actual same-row gain}
=L\times\text{conditional endpoint gain}.
\tag{14.6}
\]

It does not supply (14.1). In particular it does not show that the pure-pair
sibling is globally minimum, that its three nonselected whole-profile debts
vanish, or that the selected complete cap is attained at the marked row.
Earlier stopping responses can carry or activate debt while leaving every
local pair sign unchanged. This is the exact source-adapter gap; a positive
reach floor alone does not close it.

## 15. Exact residual at the real marked source

The actual-source defect admits a sharp decomposition, but not the missing
rank transition.  For a selected mover \(i\), let \(\bar X\) be the literal
profile using the better of its two screened actions at the marked row.  Let
\(\Delta_i\) be the corresponding conditional endpoint difference and let
\(L\) be the actual joint reach of the mark.  If \(B_i(X)\) is the unrestricted
behavioral cap, define

\[
 R_i^t(X)
 :=
 B_i(X)-\bigl(U_i(X)+[L\Delta_i]_+\bigr).
\tag{15.1}
\]

Then

\[
 d_i(X)=[L\Delta_i]_+ +R_i^t(X),
 \qquad
 d_i(\bar X)=R_i^t(X).
\tag{15.2}
\]

Thus the conditional pair compiler kills the actual mover exactly when
\(R_i^t(X)=0\).  If the residual is positive, every cap-near complete response
must alter \(i\)'s prescribed strategy before the marked date.  This is a
strategy statement, not a statement that the selected paid row is earlier.

There is nevertheless an exact paid-row localization.  Apply
positiveDebt_exists_actualJointReach_paidRow_mem_support to the actual
profile \(\bar X\) at scale \(R_i^t(X)\).  The resulting row has declared
gain \(R_i^t(X)/4\), a source pure clock in \(\bar X_i\)'s actual stopping-law
support, and the checked own-survival, opponent-live-mass, and joint-reach
floors.  Its first-disagreement date is **strictly earlier** than the marked
date.  If the supported source clock is at or after the mark, it selects the
locally optimal endpoint: support is concentrated at the mark in the Quit
case, while every supported later time and Never has the screened Continue
value in the Continue case.  No receiving clock first disagreeing at or after
the mark can then have strictly larger value.  Consequently

\[
 R_i^t(X)>0
 \Longrightarrow
 \text{a source-supported paid row strictly before the mark}.
\tag{15.3}
\]

This does not repair the adapter.  In the first arm, the receiving full
replacement can destroy the marked pair, so decreasing the calendar date is
not a renewable rank on the same source type.  The row is priced by
first-disagreement reach, not by the marked mass \(L\).  Nor is the current
root proved to be an exact cap--Nash prefix: a paid pure-time comparison is
not by itself an accepted Nash--Bellman chronology.

The exact remaining source split is therefore:

\[
\boxed{
\begin{array}{ll}
R_i^t(X)=0
  &\Longrightarrow \text{the conditional killed-mover chord may lift},\\
R_i^t(X)>0
  &\Longrightarrow \text{a paid row strictly before the mark, with no renewed
     pair state yet}.
\end{array}}
\tag{15.4}
\]

This sharpens the adapter diagnosis but does not answer the maintained
source-faithful strategic-pair question.

## 16. Exact attained-minimum version needs no unique debtor

The whole-profile hypothesis (14.1) can be weakened substantially if the
actual source itself attains the global minimum.

Let \(X\) be an actual profile with \(D(X)=D_*\), let \(Y\) be the literal
better-endpoint marked-row update by \(q\), and assume

\[
 g:=U_q(Y)-U_q(X)=d_q(X)>0.
\tag{16.1}
\]

Equivalently, the marked update attains all of \(q\)'s debt, so its residual
in (15.1) is zero.  Own-strategy invariance of the cap gives
\(d_q(Y)=0\).  If \(D(Y)>D_*\), the literal edge \(X\to Y\) is already the
source-faithful off-minimum paid output.

Suppose instead that \(D(Y)=D_*\).  Mix only \(q\)'s marked-row action and
write \(H_s=(1-s)X+sY\) for the resulting literal behavioral profile.  For
every player, prescribed payoff is affine in \(s\), while the unrestricted
cap is a supremum of affine fixed-response payoffs.  Hence

\[
 d_i(H_s)
 \le
 (1-s)d_i(X)+s\,d_i(Y).
\tag{16.2}
\]

Summing (16.2) gives \(D(H_s)\le D_*\).  Since every \(H_s\) is an actual
carrier profile, global minimality gives the reverse inequality.  Every
coordinate slack in (16.2) is nonnegative, so equality of their sum forces
equality in every coordinate:

\[
 d_i(H_s)
 =
 (1-s)d_i(X)+s\,d_i(Y)
 \qquad(i\in I).
\tag{16.3}
\]

For \(0<s<1\),

\[
 \operatorname{supp}^+(H_s)
 =
 \operatorname{supp}^+(X)\cup\operatorname{supp}^+(Y).
\tag{16.4}
\]

Because \(q\in\operatorname{supp}^+(X)\) and
\(q\notin\operatorname{supp}^+(Y)\), while \(D(Y)=D_*>0\),

\[
 \varnothing\ne\operatorname{supp}^+(Y)
 \subsetneq\operatorname{supp}^+(H_s),
 \qquad
 |\operatorname{supp}^+(Y)|\le3.
\tag{16.5}
\]

Thus an **attained actual minimum** has the exact source-faithful dispatch

\[
\boxed{
R_q^t(X)=0
\Longrightarrow
\text{off-minimum paid target or literal minimum support child};
\qquad
R_q^t(X)>0
\Longrightarrow
\text{strictly earlier supported paid row}.
}
\tag{16.6}
\]

The first arm regenerates from the literal full profile \(Y\), not from a
normalized date-zero replacement.  No assertion about the strict incoming
outsider's debt and no uniform nonmover cap modulus is needed.

This still does not seal the maintained atlas source.  Its marked rows occur
along actual approximating sequences; neither an exact global-minimum
realizer at each row nor a fixed marked date is supplied.  Passing (16.1)--(16.5)
through a moving-row compactification while retaining unconditional mass,
caps, and ancestry is precisely the remaining source adapter.

## 17. Moving-row minimum-chord compactification

The moving-row obstruction in the last paragraph can be removed at the level
of supplied actual profile sequences. This is ordinary mathematics, not yet
an integrated Lean declaration.

Fix an incoming complete source
\(S:\mathrm{FinFourMinimumAtomProducer}(r,M)\), including its retained Fin4
hard residual, positive global minimum \(D_*\), and public source ancestry.
Fix a pair \(K\), a player \(q\), and the opposite endpoint coalition \(K'\).
Let \(X_n\) be actual behavioral profiles and \(t_n\) arbitrary marked dates
in that retained ancestry such that:

1. the complete semantic/law points of \(X_n\) converge to the source's
   global-minimum point \(x=S.\mathrm{point}\), with total debt \(D_*>0\);
2. conditional on reaching \(t_n\), the root is the same pure pair \(K\);
3. the unconditional stage mass satisfies
   \(L_n:=\Pr_{X_n}(\text{reach }t_n)\ge\lambda>0\);
4. changing only \(q\)'s action at \(t_n\) selects the locally better endpoint
   \(K'\), with fixed reward difference \(\Delta>0\); and
5. for the literal target \(Y_n\), put \(R_n:=d_q(Y_n)\geq0\).

Because the reward table and the two endpoint coalitions are fixed,
\(\Delta\) is independent of \(n\).  Put

\[
 g_n:=U_q(Y_n)-U_q(X_n)=L_n\Delta
 \ge g_0:=\lambda\Delta>0.
\tag{17.1}
\]

Own-strategy cap invariance and the residual decomposition give

\[
 d_q(X_n)=g_n+R_n,\qquad d_q(Y_n)=R_n.
\tag{17.2}
\]

For a fixed \(s\in(0,1)\), let \(H_n^s\) be the literal profile which retains
the whole prefix and tail of \(X_n\) and uses the \(s\)-mixture toward \(Y_n\)
only in \(q\)'s action at \(t_n\).  These are ordinary independent behavioral
profiles, not correlated laws.  Their exact stage laws satisfy

\[
\begin{aligned}
\operatorname{Law}(Y_n)
 &=\operatorname{Law}(X_n)+L_n(\delta_{K'}-\delta_K),\\
\operatorname{Law}(H_n^s)
 &=\operatorname{Law}(X_n)+sL_n(\delta_{K'}-\delta_K).
\end{aligned}
\tag{17.3}
\]

In particular, the \(K'\)-stage mass at the same literal mark \(t_n\) is
\(L_n\) in \(Y_n\) and \(sL_n\) in \(H_n^s\).

### 17.1 Residual and target-excess split

First pass to a strict subsequence. At least one of the following holds:

* there is \(\rho>0\) with \(R_n\geq\rho\) on that subsequence; or
* \(R_n\to0\) on that subsequence.

From this point onward, every selected profile family and marked-date family
is reindexed by that same strict selector. Any later refinement is composed
with it before the sequences are relabelled. Thus the convergence assertions
below are subsequential assertions about one common literal family, not
assertions about the unselected original sequence.

In the first arm, the exact residual theorem of Section 15 supplies, for each
selected \(n\), an actual source-supported paid pure-time row strictly before
\(t_n\), with gain at least \(R_n/4\geq\rho/4\). The source profile, moving
mark, and incoming hard residual are unchanged. This is the positive-residual
output; it is not a renewed pair source or a Nash--Bellman prefix.

Assume henceforth that \(R_n\to0\). Write
\(e_n=D(Y_n)-D_*\geq0\). After a further strict subsequence, at least one of
the following holds.

* There is \(\eta>0\) with \(e_n\ge\eta\).  Then the literal endpoint updates
  \(X_n\to Y_n\) retain gain at least \(g_0\), the full source calendar and
  tail, and a quantitative off-minimum excess.
* \(e_n\to0\).  This is the only minimum-fibre arm.

The intermediate possibility causes no gap: any sequence \(e_n\ge0\) has
either a positive-liminf subsequence or a subsequence tending to zero.

### 17.2 Full-profile chord at the minimum limit

Assume \(e_n\to0\).  Joint compactness of the finite-dimensional
semantic/law carrier and of \([0,1]\) gives one strict common subsequence on
which

\[
\begin{aligned}
\operatorname{SemLaw}(X_n)&\longrightarrow x,\\
\operatorname{SemLaw}(Y_n)&\longrightarrow y,\\
\operatorname{SemLaw}(H_n^s)&\longrightarrow h^s,\\
L_n&\longrightarrow L\ge\lambda.
\end{aligned}
\tag{17.4}
\]

Both \(y\) and \(h^s\) lie in the carrier.  Continuity of total debt gives
\(D(y)=D_*\).  For every player \(i\), fixed-response payoff against the
one-row \(q\)-mixture is affine in \(s\); taking the unrestricted supremum
makes the cap convex.  Hence, at every \(n\),

\[
 d_i(H_n^s)
 \le
 (1-s)d_i(X_n)+s\,d_i(Y_n).
\tag{17.5}
\]

After summing,

\[
 D_*
\le D(H_n^s)
\le (1-s)D(X_n)+sD(Y_n)
\longrightarrow D_*.
\tag{17.6}
\]

Therefore \(D(h^s)=D_*\).  Passing (17.5) to the common subsequence gives

\[
 d_i(h^s)
 \le
 (1-s)d_i(x)+s\,d_i(y).
\tag{17.7}
\]

Both sides sum to \(D_*\), so every coordinate slack vanishes:

\[
\boxed{
d_i(h^s)=(1-s)d_i(x)+s\,d_i(y)
\quad\text{for every }i.
}
\tag{17.8}
\]

For the mover, (17.1)--(17.2) sharpen this to

\[
d_q(y)=0,\qquad
d_q(x)=L\Delta\ge g_0,\qquad
d_q(h^s)=(1-s)L\Delta>0.
\tag{17.9}
\]

Thus

\[
\boxed{
\varnothing\ne\operatorname{supp}^+(y)
\subsetneq
\operatorname{supp}^+(h^s),
\qquad
|\operatorname{supp}^+(y)|\le3.
}
\tag{17.10}
\]

Deleted-reach cap leakage has not been assumed small.  It is present in the
individual coordinates \(d_i(Y_n)\).  The global-minimum squeeze (17.6)
forces its limiting contribution to satisfy the affine identities (17.8);
this is exactly why no playerwise deleted-reach estimate is needed in the
\(R_n\to0\), \(e_n\to0\) arm.

The limiting laws retain the literal marked provenance:

\[
\operatorname{Law}(y)
=\operatorname{Law}(x)+L(\delta_{K'}-\delta_K),
\qquad
\operatorname{Law}(h^s)
=\operatorname{Law}(x)+sL(\delta_{K'}-\delta_K).
\tag{17.11}
\]

In particular \(y\) has \(K'\)-mass at least \(L\), and \(h^s\) has
\(K'\)-mass at least \(sL\).  More importantly, these masses are realized
at the exact supplied moving dates \(t_n\), not merely in the limiting
time-forgetting law.

### 17.3 Source regeneration, paired ancestry, and rank

Apply source-faithful minimum causalization first to

\[
(H_n^s,t_n,K',s\lambda).
\tag{17.12}
\]

Write \(W_n\) for its selected nonempty exact cap--Nash word,
\(c_n\) for joint survival through \(W_n\), and set

\[
A_n:=W_n\star H_n^s,
\qquad
P_n:=W_n\star Y_n.
\tag{17.13}
\]

The same prescribed word is copied literally at both endpoints, including
player \(q\)'s prescribed prefix actions.  Hence \(A_n\to P_n\) is an actual
one-player full-strategy replacement which changes only \(q\)'s suffix.  It
is not the invalid shifted-response construction, which would force \(q\) to
Continue through the new word and would therefore change the source corner.

Source-faithful causalization gives \(c_n\to1\) and every player-deleted
opponent-survival probability through \(W_n\) tending to one.  The common
prescribed-prefix cap estimate of
`SOCIAL_WEIGHT_REVIEW__COMMON_PRESCRIBED_PREFIX_BACKWARD_EDGE.md` gives, for
every nonempty word and every tail \(T\),

\[
\left|B_i(W_n\star T)-
  \max\{r_i(\{i\}),B_i(T)\}\right|
\le 2M(1-H_{i,n}).
\tag{17.14}
\]

This estimate ranges over all behavioral responses, including early Quit,
arbitrarily late Quit, mixtures, and Never.  At both minimum limits the
checked singleton margin gives
\(B_i-r_i(\{i\})\ge D_*>0\), so the maximum in (17.14) eventually selects
the tail cap.  Direct couplings give the analogous convergence of prescribed
payoffs, ordinary laws, and all player-deleted laws.  Consequently

\[
\operatorname{SemLaw}(A_n)\to h^s,
\qquad
\operatorname{SemLaw}(P_n)\to y.
\tag{17.15}
\]

The copied word also gives the exact identities

\[
\begin{aligned}
U_q(P_n)-U_q(A_n)&=c_n(1-s)L_n\Delta,\\
B_q(P_n)&=B_q(A_n),\\
d_q(P_n)&=c_nR_n\longrightarrow0.
\end{aligned}
\tag{17.16}
\]

The first line is common-prefix payoff scaling, the second is own-strategy
cap invariance, and the third combines them with exact source debt scaling
for the cap--Nash word \(W_n\).  No target-side cap--Nash assertion is used.
At the shifted date \(|W_n|+t_n\), the target has exact \(K'\)-mass
\(c_nL_n\), hence at least \(\lambda/2\) eventually.

Now apply source-faithful minimum causalization to the actual target family
\((P_n,|W_n|+t_n,K',\lambda/2)\).  Assemble the source and target causal atoms
with the explicitly supplied source \(S\): copy
\(S.\mathrm{residual}\), \(S.\mathrm{minimum}\), \(S.\mathrm{inf\_pos}\),
and the equalities of the new points' debts with \(S\)'s minimum.  This gives
complete `FinFourMinimumAtomProducer`s at \(h^s\) and \(y\), both with
residual definitionally equal to the incoming hard residual.  Neither
causalization replaces the displayed profile family, mark, or tail.

The ordinary producer type has no incoming-edge field.  Exact ancestry is
therefore stored in a thin paired-ancestry wrapper containing the source
causalization, target causalization, the actual families \(A_n,P_n\), the
literal update equality, (17.15)--(17.16), and the shifted marked-mass
identity.  This wrapper selects no new source, law, or response.  It merely
retains data already constructed from one common prescribed word.

Equation (17.10) is a strict natural-valued support transition between the
regenerated minimum source at \(h^s\) and the child at \(y\).  The child has
support cardinality at most three and may enter the checked renewable tangent
trace.  Any later recursive minimum-fibre child strictly decreases the same
support cardinality.  The initial \(X_n\to H_n^s\) lane change is recorded by
a one-use origin phase which cannot be recreated inside the constructed child
trace.  This is a literal prefixed behavioral-response transition with paired
ancestry and a one-use source-level rank.  It is not a punishment-floor
Nash--Bellman edge and does not define a rank for arbitrary returns from an
outer atlas.

### 17.4 Exact dispatch and boundary

Combining Section 15 with the moving-chord argument gives the following
supplied-sequence dispatch: **after passing to one strict subsequence, and to
one further strict subsequence in the zero-residual arm, at least one** of the
following holds:

\[
\boxed{
\begin{array}{ll}
\liminf R_n>0
 &\Longrightarrow \text{uniformly paid supported rows strictly before }t_n,\\
R_n\to0,\ \liminf e_n>0
 &\Longrightarrow \text{literal quantitative off-minimum endpoint family},\\
R_n\to0,\ e_n\to0
 &\Longrightarrow \text{regenerated minimum child with strict support drop}.
\end{array}}
\tag{17.17}
\]

Every branch uses literal refinements of the same actual endpoint profiles
and marked dates. No
fixed calendar date, attained finite-\(n\) minimum, mass-one pair law, or
Never tail is assumed.

This is not yet a terminal UE theorem.  The first branch enters the
paid-cap trichotomy and leaves its debt-descent/inert arms open; the second
enters the universal off-minimum paid waist; and the third enters the existing
renewable tangent exits.  Its claimed progress is narrower: it repairs the
actual-source adapter for the locally optimal pair endpoint and removes
positive pre-mark residual as an untyped fourth arm.
