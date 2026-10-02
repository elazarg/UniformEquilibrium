# Direct post-mark debt handoff without a renewed row

Author: `CODEX_ADVERSARY`

Status: **PROVED IN ORDINARY MATHEMATICS; STRICTLY BYPASSES THE PROPOSED
ONE-STEP PRODUCER; DOES NOT CONSUME THE OFF-MINIMUM ENDPOINT OR THE TERMINAL
EXITS OF THE RENEWABLE SUPPORT LANE**

Linked source audit:
[`CODEX_ADVERSARY__FIN4_POSTMARK_TWO_CUT_SOURCE_ADAPTER.md`](CODEX_ADVERSARY__FIN4_POSTMARK_TWO_CUT_SOURCE_ADAPTER.md).

## 1. Contraction

The proposed one-step producer is unnecessary for the conclusion for which
it was introduced in `NONZERO_PERSIST_ATTEMPT_1`, Followup 3.

That argument uses a uniformly reached charged block only to prove that one
fixed player has uniformly positive debt at the beginning of the literal
post-mark continuation.  But the current minimum-return packet already gives
actual post-mark continuations $s_n$ with

\[
D(s_n)\longrightarrow D_*>0.
\tag{1}
\]

All four debt coordinates are nonnegative.  Hence a finite-label
pigeonhole argument gives one fixed player with uniformly positive debt on a
strict subsequence.  A complete behavioral best response by that player,
made from the beginning of the post-mark port, gives the same support-handoff
input while preserving the preceding marked row literally.

Thus neither `entryCut`, `exitCut`, a downstream reached row, a hazard floor,
nor near-minimality of an exit suffix is needed for this handoff.

## 2. Self-contained theorem

Let the player set be `Fin 4`.  Fix a reward table and a globally minimizing
terminal-semantic pair $z_*$ such that

\[
D_*:=D(z_*)>0,
\qquad
D(z_*)\le D(z)
\quad\text{for every carrier point }z.
\tag{2}
\]

Let $s_n$ be actual behavioral profiles satisfying (1).  Suppose also that
each $s_n$ is stored behind a displayed marked date $m_n$, with live-path
factorization

\[
\widehat s_n
=A_n\triangleright x_n^{\rm mark}\triangleright s_n.
\tag{3}
\]

Then, after a strict subsequence, there are:

- one fixed player $p$;
- positive errors $\varepsilon_n\to0$;
- complete behavioral strategies $\tau_n^p$; and
- actual targets

  \[
  t_n=\operatorname{update}(s_n,p,\tau_n^p)
  \tag{4}
  \]

such that

\[
d_p(s_n)\ge \frac{D(s_n)}4>\frac{D_*}{8},
\qquad
d_p(t_n)\le\varepsilon_n\longrightarrow0,
\tag{5}
\]

and

\[
U_p(t_n)-U_p(s_n)
\ge d_p(s_n)-\varepsilon_n.
\tag{6}
\]

Joint compactification of the source, target, and literal half stopping-law
mixture then gives exactly one of:

1. an endpoint cluster $T$ with

   \[
   D(T)>D_*,\qquad d_p(T)=0;
   \tag{7}
   \]

2. a minimum endpoint cluster $T$ and a minimum half-mixture cluster $H$
   with

   \[
   \operatorname{supp}_+(T)
   \subsetneq \operatorname{supp}_+(H).
   \tag{8}
   \]

Moreover the reattached profiles

\[
\widehat t_n
=\operatorname{quittingCrossTailClosure}
  (\widehat s_n,t_n,m_n)
\tag{9}
\]

copy exactly the live roots of the displayed upstream profile
$\widehat s_n$ through its marked row $m_n$ and have literal all-Continue
continuation $t_n$ after that row.  Therefore the marked live root, its
reach, every atom created there, and every terminal branch ending no later
than that row are unchanged.  This is the exact same-witness ancestry needed
here; no equality of irrelevant off-live prescriptions is asserted.

## 3. Proof

By (1), eventually $D(s_n)>D_*/2$.  Since

\[
D(s_n)=\sum_{i\in\operatorname{Fin}4}d_i(s_n)
\]

and every coordinate is nonnegative, for every sufficiently large $n$ some
player $p_n$ satisfies

\[
d_{p_n}(s_n)\ge\frac{D(s_n)}4>\frac{D_*}{8}.
\tag{10}
\]

There are four labels, so pass to a strict subsequence on which $p_n=p$.
Reindex and retain the name $s_n$.

Choose any positive $\varepsilon_n\to0$.  Approximate attainment of the
unrestricted behavioral cap gives a complete strategy $\tau_n^p$ with

\[
U_p(t_n)\ge B_p(s_n)-\varepsilon_n.
\tag{11}
\]

One may take a pure deterministic quitting time, including Never, by
`exists_quittingPureTime_terminalPayoff_ge_bestResponse_sub` in
`Research/Quitting/StoppingLawMixtureFiniteWitnessPassport.lean`; no
strategy-class restriction is being imposed on the cap.

Only $p$ changes in (4), so the opponents faced by $p$ are identical and

\[
B_p(t_n)=B_p(s_n).
\tag{12}
\]

Equivalently, (12) is the fixed-opponent identity underlying
`quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain` in
`TerminalSemanticOwnStrategyTransport.lean`.  Combining (11)--(12) gives
(5)--(6).

Now use compactness of the terminal-semantic carrier three times, on the
source profiles, the targets, and

\[
h_n=\operatorname{quittingHalfStoppingLawProfile}(s_n,t_n,p).
\]

After a common strict subsequence write

\[
Z(s_n)\to S,
\qquad Z(t_n)\to T,
\qquad Z(h_n)\to H.
\tag{13}
\]

Continuity and (1), (5) imply

\[
D(S)=D_*,
\qquad d_p(S)\ge D_*/4,
\qquad d_p(T)=0.
\tag{14}
\]

Global minimality gives $D(T)\ge D_*$.  If the inequality is strict, (7)
holds.

Suppose $D(T)=D_*$.  The checked stopping-law convexity inequality gives,
coordinatewise,

\[
d_i(H)\le\frac{d_i(S)+d_i(T)}2.
\tag{15}
\]

After summing, (15) gives $D(H)\le D_*$.  Global minimality gives the reverse
inequality.  Hence equality holds in the sum and therefore in every
coordinate of (15):

\[
d_i(H)=\frac{d_i(S)+d_i(T)}2.
\tag{16}
\]

Consequently

\[
\operatorname{supp}_+(H)
=\operatorname{supp}_+(S)\cup\operatorname{supp}_+(T).
\tag{17}
\]

By (14), $p$ belongs to the first support and not the endpoint support, so
(8) follows.  This is exactly the ordinary asymptotic-zero variant of
`exists_minimumEndpointSupportRankHandoff_or_debtAscent` in
`Research/Quitting/StoppingLawMinimumEndpointSupportRankHandoff.lean`.

Finally, define (9) using the checked
`quittingCrossTailClosure` construction from
`UniformEquilibrium/Quitting/Root/SelfTailClosure.lean`.
`quittingProfileLiveRoot_crossTailClosure_eq_of_le` proves exact equality of
every live root through $m_n$, while
`quittingAllContinueProfileSpine_crossTailClosure` identifies the complete
post-row continuation literally with $t_n$.  This proves the ancestry
statement independently of semantic compactification.

## 4. Application to the current Fin4 minimum-return packet

For `packet : FinFourMinimumReturnPacket parent`, let $m_n$ be the stage of
`packet.stream.frame n`, let
$\widehat s_n=(\operatorname{packet.normalizedDecoratedFamily}).\operatorname{profile}n$
(the actual forced-pair target), and take

\[
s_n=
\operatorname{quittingAllContinueProfileSpine}
  (\widehat s_n)(m_n+1).
\]

The two declarations

- `FinFourMinimumReturnPacket.forcedPairTail_eq_tail`; and
- `FinFourMinimumReturnPacket.tailDebt_tendsto_minimum`

give (1) with $D_* = D(\operatorname{source.point}.1)$.  The forced-pair
profile itself supplies the already retained marked row, and
`FinFourMinimumReturnPacket.normalizedDecoratedFamily` supplies its fixed
terminal and fixed owner.  More quantitatively,
`FinFourSourcePreservingForcedPairPacket.resolution_le_forcedPairStageMass`
together with `row_forcedTerminal_eq_normalizedTerminal` gives the uniform
same-row atom floor

\[
\operatorname{source.minimumSingletonClockResolution}
\le
\Pr_{\widehat s_n}(\text{the fixed pair quits at }m_n),
\]

and that resolution is strictly positive.  Reattaching $t_n$ by
`quittingCrossTailClosure reward \widehat s_n t_n m_n` copies those same
prefix live roots and restarts $t_n$ literally.  Hence the theorem applies
directly to the actual current packet with exact same-row ancestry.

No information about the roots of $s_n$ is used.

## 5. Same-residual regeneration in the minimum endpoint arm

The support handoff itself is source-independent.  In Fin4, its minimum
endpoint can also be rebuilt as a same-residual source without using a
canonical payer or a downstream marked-row floor.

Compactify the complete terminal laws of the actual target profiles along
the subsequence in (13), obtaining a joint carrier point

\[
P=(T,L_T).
\]

The hard residual is punishment-normal.  At the supplied minimum point $P$,
`exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` gives a
positive finite terminal coordinate.  Applying
`nonempty_sourceFaithfulMinimumCausalChronology` to the same target profiles
retains those profiles and selects literal positive dates and exact cap--Nash
prefix words.  Its fields package a
`QuittingMinimumLawCausalSuffixAtom reward P`.  Together with the unchanged
hard residual, $P$, and the global-minimum proof, this is a new
`FinFourMinimumAtomProducer` at the endpoint.

Thus the minimum endpoint is not merely an abstract carrier point: it admits
a same-residual, target-profile-faithful source regeneration.  Pairing its
source and chronology with the handoff's `nextFamily` and base equality
literally fills the four fields of `FinFourRenewableMinimumSourceNode` in
`CanonicalPairEndpointSourceRegeneration.lean`.  The handoff's
`next_support_ssubset_parent` is the one-time strict rank comparison against
the separately constructed half-mixture parent family.  This is ordinary
mathematical assembly of checked components; the repository does not
currently expose this arbitrary-mover assembly as one declaration.  In
particular, it is not being advertised as a renewable descent from the
*incoming* source support: the checked handoff file explicitly makes the
half-mixture $H$, not $S$, the comparison parent.

The reattached upstream profiles (9) remain a separate ancestry port.  Their
old atom is retained exactly; it is not identified with the finite atom used
to causalize the downstream endpoint point $P$.

## 6. What this does and does not settle

This theorem is a **consumable alternative to the one-step renewed-row
producer** for the precise support-handoff purpose of Followup 3.  It proves
the same minimum-support-child versus off-minimum-zero-debt dichotomy with a
larger direct debt floor and fewer hypotheses.

It does not construct the requested literal `entryCut`/`exitCut` row.  Such a
row is not forced by terminal-law mass alone: a singleton terminal law can be
spread over $n$ dates with mass $1/n$ at each date.  The current
source-faithful causal chronology explicitly promises only a positive
reselected date, not a uniform per-date floor; the nonsingleton
anti-diffusion theorem and singleton clock compression require separate
mechanisms.  This timing regression is not a positive-minimum Fin4
counterexample, so it does not rule out a new theorem using additional hard
residual geometry.

The result also does not consume the off-minimum endpoint in (7), the three
terminal outputs of the renewable support lane, or prove terminal
approximation or uniform equilibrium.  Those remain exactly the downstream
obligations already recorded in the frontier.

## Source declarations inspected

- `FinFourMinimumReturnPacket.tailDebt_tendsto_minimum` and the post-date
  spine accessors, especially
  `FinFourMinimumReturnPacket.forcedPairTail_eq_tail`, in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`
  and `SourcePreservingCompletionConsumers.lean`;
- `quittingCrossTailClosure`,
  `quittingProfileLiveRoot_crossTailClosure_eq_of_le`, and
  `quittingAllContinueProfileSpine_crossTailClosure` in
  `UniformEquilibrium/Quitting/Root/SelfTailClosure.lean`;
- `quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`;
- `exists_quittingPureTime_terminalPayoff_ge_bestResponse_sub` in
  `Research/Quitting/StoppingLawMixtureFiniteWitnessPassport.lean`;
- `quittingTerminalSemanticDebt_halfStoppingLawProfile_le` and
  `exists_minimumEndpointSupportRankHandoff_or_debtAscent` in
  `Research/Quitting/StoppingLawMinimumEndpointSupportRankHandoff.lean`;
- `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- `QuittingSourceFaithfulMinimumCausalChronology` and
  `nonempty_sourceFaithfulMinimumCausalChronology` in
  `Research/Quitting/SourceFaithfulMinimumLawCausalization.lean`; and
- `FinFourRenewableMinimumSourceNode` in
  `Research/Quitting/FinFourProducerAtlas/CanonicalPairEndpointSourceRegeneration.lean`
  and the downstream renewable support-lane declarations in
  `CanonicalPairFullReplacementSourceRegeneration.lean` and
  `CanonicalPairRenewableSourceRank.lean`.

No AGKRS source was used.  No Lean file or export was modified.
