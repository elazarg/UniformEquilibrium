# Second independent review: Fin4 positive-Never late-release chronology

Reviewer: CODEX_EULER

Date: 2026-08-26

Note reviewed:
[CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY.md](../notes/CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY.md)

Prior review:
[CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY__BY_CODEX_RAMSEY.md](CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY__BY_CODEX_RAMSEY.md)

## Verdict

**REVISE for one remaining subsequence/indexing defect and one matching
live-path wording cleanup.  The mathematical theorem and all quantitative
constants otherwise PASS after an explicit unrestricted-strategy
falsification attempt.**

Three of Ramsey's four requested repairs are fully present:

1. the current finite-support construction replaces the erroneous generic
   discrepancy sentence and makes the late release exact;
2. Theorem 4.1(2) correctly states live-path agreement and gives the literal
   Function.update identity;
3. Corollary 4.2 uses the complete target strategy, states the two alternatives
   are inclusive, and explains the optional further alternative subsequence.

The recipient-subsequence repair is acknowledged in the proof but is not yet
reflected in the theorem's displayed quantifiers.  This is the sole
mathematical-statement blocker.

## 1. Remaining exact repair

The theorem first indexes roots by the original natural number and asserts

\[
|R_n|=n+1
\]

and stage locations \(n+1+t\).  It then passes to a recipient subsequence,
reindexes it, and correctly observes in the proof that the new root length is
\(\operatorname{subseq}(n)+1\), not \(n+1\).  But items 1, 3, and 4 still
display \(n+1\).  Those statements cannot all be read literally after the
announced reindexing.

The cleanest repair is not to reindex.  State:

> There are a fixed \(b\ne a\) and an infinite cofinal set
> \(J\subseteq\mathbb N\) such that items (4.1)--(4.5) hold for every
> sufficiently large \(n\in J\).

Keep \(|R_n|=n+1\) and the shifts \(n+1+t\) for the original indices
\(n\in J\), delete the proof sentence which reindexes, and restrict
Corollary 4.2 to sufficiently large \(n\in J\).  If a fixed decoder
alternative/coalition is selected, replace \(J\) by a further infinite
cofinal subset.  This preserves every constant and the literal stage labels.

Alternatively, after reindexing define \(\ell_n=|R'_n|\ge n+1\) and replace
every stage shift by \(\ell_n\).  Mixing these two conventions is the present
defect.

For the prior live-path repair, also change the unqualified introductory
sentence “the deviation agrees with the source through the exact prefix and
through the whole retained S-window” to “has the same live-path prefix roots
and suffix hazards through the retained S-window.”  Theorem 4.1(2) already
uses the correct formulation, so this is a bounded consistency edit rather
than a proof issue.

## 2. Same-point law and finite-clock provenance

The simultaneous \(q>0\) and \(m>0\) data are valid.  The point-specific
declaration finFourHardResidual_minimumLaw_causalSuffixAtom applies to the
supplied minimum joint-law point itself.  Its proof invokes the stronger Fin4
fact that every such minimum law has a positive finite coalition coordinate;
it is not using the generic exclusive Never-or-atom dispatch.  Thus

\[
q=\mu(\mathrm{none})>0,\qquad
m=\mu(\mathrm{some}\ S)>0
\]

are co-realized at one point.

The canonical common-quantile compression is compatible with this provenance.
Applied profilewise to the same joint-law realizers:

- its coordinate quotient sends Never literally to Never, so each marginal
  Never atom, and hence the product joint-Never probability, is exact;
- it reconstructs an actual independent finite-date-plus-Never profile;
- away from the common-cell collision event it preserves the order and tie
  set of all finite clocks; and
- the finite union of pair-collision errors tends to zero.

Therefore every fixed earliest-coalition coordinate, in particular the
selected \(S\), converges to its original law coordinate.  Choosing the
compression level diagonally with the original realizing index proves

\[
\operatorname{Sem}(\sigma_n)\to z,\quad
\operatorname{Law}(\sigma_n)(\mathrm{none})\to q,\quad
\operatorname{Law}(\sigma_n)(\mathrm{some}\ S)\to m.
\]

I checked the current implementation of the compression in
Research/Quitting/EscapeAwareQuantileClockHierarchy.lean and
Research/Quitting/EscapeAwareQuantileClockCollision.lean; the former compiles
at current head.  The unrestricted cap coordinate is part of the two-sided
pure-time transport, not a finite-horizon proxy.

Fresh exact cap-root words may then be selected over these compressed literal
profiles.  Continuity of semantic debt gives
\(D(\sigma_n)\to D_*\).  Exact cap-stack transport and global minimality
squeeze

\[
D_*\le D(R_n*\sigma_n)\le D(\sigma_n),
\]

while capNashStack_continueProduct_lowerBound gives

\[
\frac{D_*}{D(\sigma_n)}\le c_n\le1.
\]

Since \(D_*>0\), both the prefixed debt and \(c_n\) converge as claimed.
This is a fresh-stack construction on the compressed same-law source; it does
not identify the root words returned for a different realizing sequence.

## 3. Exact late release and unrestricted deviations

Choose \(K_n\) strictly above every finite atom of every compressed marginal
and take \(N_n=K_n\).  The finite-cap behavior copies mover \(a\)'s live
hazard before \(N_n\) and quits surely at \(N_n\).

Under the natural product-clock coupling, source and target outcomes differ
only when all four original clocks are Never:

- if any clock is finite, its time is below \(K_n\), and both profiles have
  the same live hazards through the resulting absorption;
- on joint Never, the source has no terminal coalition and the target exits
  at \(N_n\) with exactly \(\{a\}\).

Consequently the suffix identities are exact:

\[
U_a(\sigma_n^{[a,N_n]})-U_a(\sigma_n)=s_aq_n,
\qquad
\Pr(\text{singleton }\{a\}\text{ at }N_n)=q_n.
\]

The terminal witness supplies one fixed \(a\) with \(s_a\ge\Gamma>0\).
No strategic completeness is assumed here: the capped object itself is one
legal complete behavioral deviation.  On the cap side, changing only
\(a\)'s strategy leaves its unrestricted best-response envelope exactly
unchanged because that envelope overwrites \(a\) and depends only on the
opponents.  Hence the own-debt identity is exact.

Prefixing source and target by the same literal root word multiplies every
suffix event mass and their payoff difference by the joint Continue product
\(c_n\).  Eventually

\[
q_n\ge q/2,\quad \operatorname{Law}(\sigma_n)(S)\ge m/2,\quad c_n\ge1/2,
\]

which gives \(m/4\), \(q/4\), and \(\Gamma q/4\) exactly.  This also verifies
that the old \(S\)-window precedes the new singleton release on the same
literal source/target pair.

The source root word is exact cap-Nash only for \(P_n\).  Nothing proves it
exact for \(Q_n\), and the note now preserves this distinction.

## 4. Transfer and decoder constants

With \(e_n=D(P_n)-D_*\to0\), the checked signed account
minimumReference_opponentTransfer_of_coordinateDecrease gives

\[
g_n\le e_n+\sum_{j\ne a}(d_j(Q_n)-d_j(P_n)).
\]

Using \(g_n\ge\Gamma q/4\) and eventually \(e_n\le\Gamma q/8\) yields

\[
\sum_{j\ne a}(d_j(Q_n)-d_j(P_n))\ge\Gamma q/8.
\]

There are three recipients, so at least one signed coordinate increase is
at least \(\Gamma q/24\).  Infinite finite-label pigeonhole fixes \(b\);
this is exactly where the cofinal-set repair above is needed.

For \(\operatorname{card}(\mathrm{QuittingTerminalOutcome}(\mathrm{Fin}\ 4))
=16\), hasQuittingEndpointDebtRecipientAtom_of_pos gives

- direct prescribed-difference atom at least
  \((\Gamma q/24)/(2\cdot16)=\Gamma q/768\);
- rectangle atom at least
  \((\Gamma q/24)/(4\cdot16)=\Gamma q/1536\).

The endpoint target is exactly QStrategy_n and
Function.update \(P_n\ a\ \mathrm{QStrategy}_n=Q_n\).  The rectangle's
counterfactual recipient deviation may vary.  No Bellman, floor, or Nash
property is inferred for \(Q_n\).

## 5. Export and seal assessment

After the cofinal-index repair, the theorem is rigorous ordinary mathematics
with two substantive unrestricted-strategy reviews.  Its honest current seal
is **M only**: the complete composition (late release, transfer, and ordered
decoder output) is not yet a checked Lean declaration.  It has no honest C
seal because the decoder output is not consumed into a punishment-floor edge,
cumulative near-return, rank decrease, or uniform payoff.

Under the current exports/README significance gate and the explicit partial
answer gate in FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE, I do **not** recommend an
export packet yet.  It is a strong Research formalization candidate and a
genuine same-source chronological producer, but it ends at the already named
prescribed-atom/rectangle seam and does not close a semantic arm or decrease a
maintained well-founded obstruction.  Formalizing the theorem would be useful;
it would not by itself supply the missing consumer.

The result must remain narrowly described as:

> positive minimum-law Never mass produces a deep exact **source** chronology
> and a later legal fixed-gain endpoint move with quantitative opposite-face
> transfer and decoder atom.

It is not an exact target chronology, admissible Bellman path, cumulative
return, regenerated minimum source, or uniform-payoff theorem.

