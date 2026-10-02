# Silent padding turns every positive finite tail atom into a reached post-mark two-cut block

Identity: `CODEX_DESCENDANT`

Date: 2026-08-31

Status: **ordinary mathematics proved below; this is a source adapter, not a
terminal consumer.**  The universal construction is one terminally silent
all-Continue padding row followed by a finite window of the literal source
tail.  It supplies the strict inequality `markedRow < entryCut` required by
the checked two-cut structure, while the genuine hazard and all strategic
content lie in the original tail.  The padding mark is artificial: it carries
no atom, payment, or atlas chronology certificate.

## 1. Source and exact question

Let \(s_n\) be actual behavioral profiles on `Fin 4` whose joint
semantic/law points converge along one strict subsequence:

\[
 (Z(s_n),\nu_n)\longrightarrow (z_*,\nu),
 \qquad D(Z(s_n))\longrightarrow D_*>0,
 \tag{1.1}
\]

where \(z_*\) is a global minimum and the same quantitative Fin4 hard
residual is retained.  In the atlas application, \(s_n\) is literally the
continuation after the forced-pair date in rank \(n\) of one
`FinFourMinimumReturnPacket`.

The positive-finite-atom theorem selects one fixed nonempty coalition \(A\)
with

\[
 \mu:=\nu(A)>0.
 \tag{1.2}
\]

Write

\[
 w_{n,t}(A)
 =\Pr_{s_n}(\text{first terminal coalition is }A\text{ at date }t).
 \tag{1.3}
\]

Then

\[
 \sum_{t\ge0}w_{n,t}(A)=\nu_n(A)\longrightarrow\mu.
 \tag{1.4}
\]

The checked structure `QuittingUniformlyReachedPostMarkTwoCutBlock` asks for
natural numbers

\[
 \operatorname{markedRow}<\operatorname{entryCut}<
 \operatorname{exitCut},
 \tag{1.5}
\]

a positive reach floor at the entry cut, and a positive marginal-hazard
floor between the cuts.  The question is whether the actual postmark source
family supplies this input without a date-zero/date-positive case split.

## 2. Universal silent-padding construction

Fix once and for all any

\[
 0<\chi<\mu.
 \tag{2.1}
\]

For example, \(\chi=\mu/2\).  By (1.4), eventually \(\nu_n(A)>\chi\).
For every such \(n\), countable additivity gives a finite integer
\(e_n>0\) with

\[
 \sum_{0\le t<e_n}w_{n,t}(A)>\chi.
 \tag{2.2}
\]

Construct \(\bar s_n\) by prefixing one deterministic all-Continue product
root to \(s_n\).  Thus the new date zero is terminally silent and, on its
probability-one all-Continue branch, the literal continuation is exactly
\(s_n\).  Put

\[
 \operatorname{markedRow}_n=0,
 \qquad
 \operatorname{entryCut}_n=1,
 \qquad
 \operatorname{exitCut}_n=e_n+1.
 \tag{2.3}
\]

Then:

1. \(0<1<e_n+1\);
2. joint reach from the start of \(\bar s_n\) to the entry cut is exactly
   one;
3. the roots in the block \([1,e_n+1)\) are literally the roots of \(s_n\)
   at dates \([0,e_n)\); and
4. the exit suffix is literally \(\operatorname{suffix}_{e_n}s_n\).

At every original date \(t\), stage mass factors as live mass times the
conditional root coalition mass.  Hence

\[
 w_{n,t}(A)
 \le \Pr_{q_{n,t}}(\text{absorb})
 \le \sum_{i<4}q_{n,t,i}(Q).
 \tag{2.4}
\]

Summing (2.4) over the finite window in (2.2) gives

\[
 \sum_{0\le t<e_n}\sum_{i<4}q_{n,t,i}(Q)>\chi.
 \tag{2.5}
\]

Therefore \(\bar s_n\), with (2.3), is a literal
`QuittingUniformlyReachedPostMarkTwoCutBlock` with

\[
 \operatorname{reachFloor}=1,
 \qquad
 \operatorname{hazardFloor}=\chi.
 \tag{2.6}
\]

The all-Continue prefix changes neither prescribed payoff nor terminal law.
Its effect on the unrestricted cap is

\[
 U_i(\bar s_n)=U_i(s_n),
 \qquad
 B_i(\bar s_n)=\max\{r_i(\{i\}),B_i(s_n)\},
 \qquad
 \mathcal L(\bar s_n)=\mathcal L(s_n).
 \tag{2.7}
\]

Indeed, a deviator either Quits at the new silent row and receives its
singleton reward, or Continues and then has exactly its original unrestricted
response problem.  At the limiting positive global minimum, the checked
singleton margin gives

\[
 B_i(z_*)\ge r_i(\{i\})+D_*
 \qquad(i<4).
 \tag{2.8}
\]

Cap-coordinate convergence in (1.1) therefore makes
\(B_i(s_n)>r_i(\{i\})\) for every player eventually.  After deleting that
finite prefix, (2.7) improves to the full semantic equality

\[
 Z(\bar s_n)=Z(s_n).
 \tag{2.9}
\]

The padding also introduces no scaling into any update made from the entry
profile, because entry is reached with probability one.  Thus the two-cut
entry profile has semantic pair \(Z(s_n)\), and its paid splice is the silent
prefix of the corresponding actual update of \(s_n\).

This proves the adapter.  No split according to the location of the atom is
needed.

## 3. Exact two-cut output

Put

\[
 K=(1-e^{-\chi})D_*,
 \qquad
 \delta={e^\chi-1\over2}D_*.
 \tag{3.1}
\]

The checked positive-minimum two-cut theorem gives, at every retained rank,
one of:

\[
 D(\operatorname{suffix}_{e_n}s_n)\ge D_*+\delta,
 \tag{3.2}
\]

or some player \(p_n\) with

\[
 d_{p_n}(s_n)>K/8.
 \tag{3.3}
\]

In the second arm, choose tolerance \(K/16\).  The Fin4 paid-splice theorem
supplies an unrestricted behavioral replacement of \(p_n\), starting in
the literal profile \(s_n\), whose payoff gain is strictly greater than

\[
 K/16,
 \tag{3.4}
\]

whose updated entry-profile \(p_n\)-debt is at most \(K/16\), and whose
whole padded-parent debt decrease equals the same gain exactly.  Because the
silent row has reach one, (3.4) has no extra reach factor.

After finite-label subsequence selection, either (3.2) holds throughout or
one fixed payer realizes the paid arm throughout.  Neither conclusion is
yet a return or a renewable source transition.

## 4. Exact atlas/source adapter

For a checked `FinFourMinimumReturnPacket parent`, at source rank \(n\) let
\(m_n\) be its retained forced-pair stage and define

\[
 s_n=\operatorname{quittingAllContinueProfileSpine}
   (\operatorname{reward},
    (\operatorname{packet.stream.frame}\ n).\operatorname{targetProfile},
    m_n+1).
 \tag{4.1}
\]

The named source equalities

* `FinFourStabilizedForcedPairStream.tail_eq_framePostDateTail`,
* `FinFourMinimumReturnPacket.forcedPairTail_eq_tail`, and
* `FinFourMinimumReturnPacket.tailDebt_tendsto_minimum`

identify (4.1) with the packet's literal post-date tail and give
\(D(s_n)\to D_*\).  Joint compactness is applied to this same sequence; it
does not replace the profiles.  At the resulting minimum joint-law limit,
`exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` supplies
\(A\) and \(\mu>0\).  Equations (2.1)--(2.6) then construct the padded
two-cut block rank by rank from these exact \(s_n\).

The production Lean adapter therefore needs only to package:

1. the existing strict refinement carrying joint semantic/law convergence;
2. a fixed \(\chi\), preferably \(\mu/2\);
3. finite truncations \(e_n\) of the same atom coordinate;
4. the root sequence obtained by prepending `quittingAllContinueRoot`; and
5. eventual cap neutrality from
   `minimumTerminalSemantic_singletonMargin`; and
6. the exact shift identities for entry, exit, payoff, cap, law, and paid
   update.

No new game-theoretic hypothesis, source causalization, or response
selection is used in constructing the block.

## 5. Artificial-mark boundary

The row named `markedRow` in (2.3) is only a terminally silent padding row
inserted to satisfy the structural inequality in the checked record.  It is
not:

* the original forced-pair mark;
* a positive stage atom;
* a paid first-disagreement row;
* an exact cap--Nash certificate; or
* a row reached in the original unpadded chronology.

This is mathematically legitimate for the present two-cut consumer because
the checked theorems use only `markedRow_lt_entryCut`; they never charge,
inspect, or preserve the marked row.  It also exposes the exact specification
boundary: `QuittingUniformlyReachedPostMarkTwoCutBlock` encodes a positive
entry/hazard window preceded by one row, not ancestry from a strategically
meaningful mark.  Any later theorem that needs a retained marked atom or paid
row must carry that datum in a stronger source-indexed structure and cannot
recover it from this adapter.

The checked two-cut structure is built from a displayed root sequence.  The
canonical history-independent profile reconstructed from that sequence has
the same live roots as the literal profile
`quittingRootThenContinuationProfile reward quittingAllContinueRoot s_n`.
All payoff, cap, law, entry, exit, and paid-splice claims use the standard
live-root/canonical-profile equality.  Definitional equality of the two
complete off-path behavioral strategy objects is neither needed nor claimed.

Reattaching the padded tail behind the original pure forced-pair mark keeps
that earlier root literal, but its joint-Continue probability may be zero.
Consequently (3.4) is not a positive-gain deviation of the original
forced-pair profile.

## 6. Relation to existing results

The substantive finite-window producer is already present in ordinary
mathematics in Section 8 of
`CODEX_ADVERSARY__FIN4_POSTMARK_TWO_CUT_SOURCE_ADAPTER.md`: it takes
`entryCut = 0`, reach one, and a finite window capturing positive limiting
atom mass.  The present result does not strengthen its hazard or debt
estimates.  Its new content is the exact silent-padding adapter from that
window to the checked *strict post-mark* structure and the identification of
the artificial-mark specification boundary.

The earlier date-zero-versus-later split in this notebook, now retained only
as the corollary below, and the checked `FablePostmarkAtomBlock` theorem give
more information about whether the original unpadded first row itself carries
a large atom.  That distinction is unnecessary for the two-cut consumer.

This result does not overlap with a strong two-return producer.  In
particular, it gives no convergence of (3.2)'s exit suffix back to the
minimum, no exact Nash--Bellman roots in the block, and no renewal or terminal
consumer.

## 7. Unpadded corollary

If one insists that every named row belong to the original \(s_n\), take the
fixed threshold \(\mu/8\).  After a strict subsequence, either

\[
 w_{n,0}(A)\ge\mu/8
 \tag{7.1}
\]

cofinally, or

\[
 w_{n,0}(A)<\mu/8,
 \qquad
 \sum_{t\ge1}w_{n,t}(A)>5\mu/8
 \tag{7.2}
\]

eventually.  In the second arm choose \(e_n>1\) with

\[
 \sum_{1\le t<e_n}w_{n,t}(A)>\mu/2.
 \tag{7.3}
\]

Then survival to date one is greater than \(5\mu/8\), and the marginal
hazard in \([1,e_n)\) is greater than \(\mu/2\).  This is the exact
unmodified-profile dichotomy checked by `FablePostmarkAtomBlock`.  The first
arm can itself be treated as a one-row block only after padding or by using
the weaker `entryCut = 0` structure.

## 8. Regressions and scope

If \(s_n\) absorbs surely in \(A\) at date zero, no positive hazard need
remain after its first row.  The padded construction still works: the
original date-zero row becomes the block row at padded date one.  If \(s_n\)
Continues at date zero and absorbs surely at date \(N\), the same construction
selects a window ending after date \(N\).  Thus the universal adapter covers
both endpoint timings without pretending that hazard renews after the atom.

Cap neutrality genuinely uses the minimum margin.  For a local regression,
let one opponent Quit surely at the original date zero and let all remaining
opponents Continue.  Give player \(i\) payoff zero both from joining that
quitter and from Continuing while it Quits, but give \(i\) singleton reward
one.  Against the original profile, every response of \(i\) pays zero, so its
cap is zero.  Prefixing one all-Continue row gives \(i\) the new option to
Quit alone for one, raising its cap to one while leaving the prescribed law
and payoff unchanged.  Hence an arbitrary silent prefix need not preserve the
semantic pair; (2.8) is the exact source-specific repair.

The theorem does not supply:

* a literal downstream block after an independently selected paid row;
* a near-minimum exit suffix;
* positive outer reach through the original pure forced pair;
* target-side control of the other three unrestricted caps;
* a source-preserving child with a renewable finite rank; or
* terminal approximants or a uniform-equilibrium payoff.

## 9. Named checked inputs and Lean boundary

Named checked inputs inspected:

* `FinFourMinimumReturnPacket.tailDebt_tendsto_minimum` and the literal-tail
  equalities in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionConsumers.lean`;
* `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum`;
* `quittingRootCoalitionMass_le_absorptionMass_of_nonempty`;
* `quittingRootAbsorptionMass_le_sum_quitRates`;
* `quittingRootThenContinuationProfile` and
  `quittingAllContinueRoot`;
* the terminal semantic/law prefix identities for an all-Continue root;
* `minimumTerminalSemantic_singletonMargin`; and
* `QuittingUniformlyReachedPostMarkTwoCutBlock.finFour_offMinimum_or_exists_paidSplice`
  in `TerminalSemanticPositiveMinimumTwoCutPaidSplice.lean`.

The finite-window block, two-cut coercivity, and paid splice are already
checked separately.  The universal silent-padding composition and the exact
`FinFourMinimumReturnPacket` adapter are ordinary mathematics here; they are
not yet claimed as named Lean declarations.
