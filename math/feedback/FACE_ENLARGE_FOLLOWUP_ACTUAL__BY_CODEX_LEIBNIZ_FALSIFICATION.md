# Falsification review of the actual face-enlargement follow-up

Identity: CODEX_LEIBNIZ

Source reviewed: [`../FACE_ENLARGE_FOLLOWUP.md`](../FACE_ENLARGE_FOLLOWUP.md)

## Verdict

**REVISE.** The central mathematical output survives the requested falsification attempt: the deletion lift, pure-time handoff, paid-collision extraction, and live-weighted endpoint consumer form a valid same-source chain of **actual profile updates**, with unrestricted behavioral debt throughout. The stated constants (7,14,56) are correct, as is the claim that the endpoint mover differs from the helper.

One substantive provenance statement is false as written: neither

\[
\sigma\longrightarrow\tau
\quad\text{nor}\quad
\tau\longrightarrow\tau'
\]

is a chronological Nash--Bellman edge. They are counterfactual unilateral replacements of a complete behavioral profile. Calling (5) or (23) a “chronology” conflates an actual-data update chain with temporal succession. The result should be exported, if otherwise approved, only after replacing this language by “literal same-source profile-update chain” and explicitly disclaiming an admissible-path conclusion.

There are also two formal-facing omissions that should be repaired in the note: spell out invariance of a player's cap under replacement of that player's prescribed strategy, and transport the hard residual's standard-(Q)/no-homogeneous fields from the normal subtype to the full four-player matrix using the full-normal-core equality. Neither omission invalidates the ordinary mathematics.

## Claim tested

The note claims that a blocker-selected outside player (j) in a four-player terminal-gap table can be deleted, then reinserted as `Never`, then changed to a finite pure quitting time so that:

1. the three surviving players initially have debt at most \(\varepsilon\);
2. the ambient gap is initially carried by (j);
3. after the pure-time update, (j)'s debt is at most \(\delta\), while a survivor carries the full ambient gap;
4. if the helper's solo premium \(\pi_j\) is below the gap, a literal nonsingleton stage atom pays a quantitatively positive collision margin;
5. the existing live-weighted collision theorem turns that atom into a tail-debt excursion or a distinct survivor's exact endpoint debt drop, retaining a nonempty routed atom with no stage-mass loss; and
6. the stronger passive-helper floor condition is impossible inside the maintained hard residual.

The review specifically tried to break the construction using unrestricted behavioral deviations, a `Never` pure-time selector, zero live mass, negative collision summands, selection of (q=j), loss under routing, and source/chronology confusion.

## 1. The deletion and pure-time handoff passes

The source is literal. `quittingTerminalPayoff_liftDeletedProfile` and `quittingBestReplyValue_liftDeletedProfile` in
`UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean` preserve, for each survivor, the on-path payoff and the supremum over all behavioral deviations. Hence a terminal \(\varepsilon\)-Nash profile of the three-player restriction lifts to an ambient profile \(\sigma\) satisfying

\[
d_k(\sigma)\le\varepsilon\qquad(k\ne j).
\]

The three-player source is available from
`quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three` and
`exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff`.
Therefore, when \(\varepsilon<\gamma\), the ambient terminal gap at \(\sigma\) must be carried by (j):

\[
d_j(\sigma)\ge\gamma.
\]

This transfer is against the full behavioral strategy class; it is not restricted to stationary or finite-time deviations.

Given an arbitrary response within \(\delta/2\) of (B_j(\sigma)),
`exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`
selects an `Option ℕ` pure time within another \(\delta/2\). The option cannot be `none`: `none` is exactly the `Never` strategy already prescribed to (j), hence gives gain zero, whereas the selected gain is at least

\[
d_j(\sigma)-\delta\ge\gamma-\delta>0.
\]

Thus the selected date is genuinely finite.

Replacing (j)'s prescribed strategy does not change (j)'s opponents, so its best-reply cap is unchanged:

\[
B_j(\tau)=B_j(\sigma).
\]

This is immediate from the opponent-only definition of the best-reply value, but the proposed Lean handoff should cite or add the corresponding named update-self invariance theorem instead of leaving this step implicit. It follows that

\[
U_j(\tau)-U_j(\sigma)\ge\gamma-\delta,
\qquad d_j(\tau)\le\delta.
\]

Applying the ambient gap to the **actual profile** \(\tau\), with \(\delta<\gamma\), now forces some survivor (i\ne j) to satisfy

\[
d_i(\tau)\ge\gamma.
\]

This argument does not require the helper to be blocker-selected: it works for any omitted player in Fin4. The blocker is used to make the choice of (j) relevant to the later face analysis and to prove the no-dispensability conclusion.

## 2. The paid-collision extraction and constants pass

The exact pure-time transport identity at the selected date splits the helper's gain into:

* the event that all survivors Continue at that date, with solo-versus-tail increment; and
* the seven nonempty survivor coalitions, with collision increments
  \(r_j(S\cup\{j\})-r_j(S)\).

The all-Continue term is at most \(\pi_j\), because the actual `Never` continuation payoff is bounded below by the continue floor. Hence, under

\[
0<\delta<\gamma-\pi_j,
\]

the collision sum is at least \(\gamma-\pi_j-\delta>0\). The summands need not all be nonnegative, but this does not damage the averaging step: among seven real summands whose sum is at least (A>0), at least one is at least (A/7). Therefore some nonempty (S\subseteq C) satisfies

\[
m_t(S)\bigl(r_j(S\cup\{j\})-r_j(S)\bigr)
\ge {\gamma-\pi_j-\delta\over7}.
\]

The selected increment is positive, so (c_j>0), and its definition bounds that increment by (c_j). Division is consequently legitimate and yields

\[
m_t(S)\ge {\gamma-\pi_j-\delta\over 7c_j}.
\]

The terminal coalition (R_S=S\cup\{j\}) is nonsingleton. In the pair-face case, the additional sign assumption for the other outsider removes exactly the singleton choice (S=\{k\}); the average then runs over six eligible subsets, so the denominator (6) is correct.

No stationarity, bounded support, or restricted deviation class is inserted in this derivation.

## 3. The live-weighted collision consumer passes

`quittingFinFourLiveWeightedCollisionTransfer_tailEscape_or_endpointGain` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`
applies to the literal profile \(\tau\), literal date (t), and literal nonsingleton terminal (R_S). It yields

\[
L_t E_t\ge {m_t(S)D_*\over2}
\]

or a stage-best-endpoint update by some (q) with actual payoff gain

\[
G_q\ge {m_t(S)D_*\over8}.
\]

In the first branch, the right-hand side is positive, so (L_t>0) and (E_t>0). Since (L_t\le1), it is valid to pass from the checked weighted conclusion to the unweighted estimate

\[
E_t\ge {m_t(S)D_*\over2}
\ge { (\gamma-\pi_j-\delta)D_*\over14c_j}.
\]

The note should say explicitly that this division-free argument is how “weighted shifted-tail excess” becomes (20).

The endpoint branch similarly gives (21). The assertion (q\ne j) withstands scrutiny. The helper's global (Q_t)-versus-`Never` gain is positive. Its exact pure-time decomposition is the live mass times its root Quit-minus-Continue difference at date (t); the positive collision term already ensures positive stage/live mass. Thus this root difference is positive. Since \(\tau_j\) prescribes pure Quit at that root, (j)'s played-action root Nash defect is zero. The collision theorem chooses a mover with strictly positive endpoint gain/root defect, so it cannot choose (j).

The identities and provenance after that selection are also exact:

* `quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain` proves the mover's unrestricted semantic debt falls by exactly (G_q);
* `quittingStageCoalitionMass_le_stagePureEndpointRouted` proves that a nonsingleton stage atom routes to a nonempty coalition without loss of unconditional stage mass.

The survivor (i) supplied by the ambient gap need not equal the endpoint mover (q), and the statement should not suggest otherwise. The checked collision theorem selects (q) from the local root defects, independently of (4).

## 4. Provenance failure: this is not a chronology

The displayed objects are all actual profiles in the same reward table and are source-matched in the useful counterfactual sense:

\[
\tau=\sigma[j\leftarrow Q_t],
\qquad
\tau'=\tau[q\leftarrow\text{stage-}t\text{ pure endpoint}].
\]

But these arrows are not dates of one play, exact Bellman edges, or an admissible punishment-floor path. In particular, play under \(\sigma\) does not transition to \(\tau\), and play under \(\tau\) does not transition to \(\tau'\). They are unilateral counterfactual replacements of complete behavioral strategies. Nothing here proves an exact current/tail payoff identity that would allow the path compiler to consume the pair of arrows.

Accordingly, replace:

* “unconditional, literal chronology” in (5);
* “literal two-edge chronology” before (23); and
* “executable collision chronology” in (29)

by “literal same-source profile-update chain” (or equivalent). Add the explicit nonclaim that the chain is not yet a prescribed-payoff Nash--Bellman chronology and does not by itself compile to a uniform equilibrium.

This is a real correction, not cosmetic terminology, because the project's outstanding producer problem is exactly the conversion of source-matched counterfactual data into ordered chronological realization.

## 5. The algebraic no-dispensability lemma passes, with a transport caveat

The restriction argument is correct. If row (j) is nonnegative outside its diagonal, extend an arbitrary restricted LCP right-hand side by (q_j=1). In every full solution,

\[
w_j=1+\sum_{k\ne j}M_{jk}z_k\ge1,
\]

so complementarity forces (z_j=0), leaving a restricted LCP solution. A homogeneous restricted direction extends by zero at (j), and the same row sign makes the added coordinate nonnegative. Thus standard (Q) and absence of a homogeneous solution descend to the restriction.

For a three-player strict blocker face, the usual (q=-\mathbf1) separation contradicts standard (Q). For a two-player strict blocker face, the checked
`standardQ_and_noHomogeneous_iff_orientation_and_determinant` (equivalently the cyclic-label formulation) in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeByThreeZeroDiagonalQ.lean`
forces a strict directed-cycle sign orientation on the three-player restriction; hence the reciprocal entries on every pair have opposite signs. This contradicts the two strictly negative blocker entries.

The formal statement must first reindex the residual's matrix from its normal-player subtype to `Fin 4`, using the hard residual's proof that the normal core is all players. Treating these types as definitionally equal would be an implementation gap. Once transported, the conclusion

\[
r_j(\{j\})>f_j
\]

is sound.

## 6. Boundary example and class claim

The displayed matrix has a strict blocker face (\{0,1\}), fails projective \(\bar Q\), has the stated uniform nonnegative direction, and admits a reward completion in which player 2 is block-dispensable. The existing block-deletion theorem and three-player existence then provide a uniform-equilibrium payoff.

The wording “full dispensability defines a strictly larger solved class than projective \(\bar Q\)” is set-theoretically ambiguous: the dispensable class has been shown to contain an example outside projective \(\bar Q\), not to contain the entire projective class. The precise conclusion is that the **union** of the projective-\(\bar Q\) solved class and the block-dispensable solved class is a strict enlargement of the former.

## Strongest surviving theorem

After the provenance correction, the following is supported.

> Let a Fin4 quitting table have terminal all-behavior gap \(\gamma>0\), positive minimum terminal-semantic debt (D_*>0), and let (j) be any omitted player. For every (0<\varepsilon,\delta<\gamma), there is a literal deletion-lift profile \(\sigma\), a finite pure-time helper update \(\tau=\sigma[j\leftarrow Q_t]\), and a survivor (i\ne j) such that survivor debts at \(\sigma\) are at most \(\varepsilon\), (d_j(\sigma)\ge\gamma\), the helper gains at least \(\gamma-\delta\), (d_j(\tau)\le\delta\), and (d_i(\tau)\ge\gamma\), all against unrestricted behavioral deviations.
>
> If additionally \(\pi_j<\gamma\) and (0<\delta<\gamma-\pi_j\), then some literal nonsingleton stage coalition (S\cup\{j\}) satisfies the paid-mass and mass bounds (14)--(16). From that same profile and stage, either the literal shifted suffix has debt excess at least
> \((\gamma-\pi_j-\delta)D_*/(14c_j)\), or a distinct survivor endpoint update gains at least
> \((\gamma-\pi_j-\delta)D_*/(56c_j)\), loses exactly that much unrestricted debt, and retains a nonempty routed stage atom with no mass loss.

For a blocker-selected helper in the maintained hard residual, the additional algebraic theorem shows \(\pi_j>0\). Hence the useful hard-residual split is

\[
\pi_j\ge\gamma
\quad\lor\quad
\text{the literal collision/profile-update packet above}.
\]

This is a genuine actual-data producer and has a checked downstream collision consumer. It does **not** produce total-debt descent, support-rank descent, an admissible exact path, or a uniform-equilibrium payoff. Its export gate should therefore be judged as a strict narrowing of the face-enlargement obligation, not as chronological closure.

## Source audit

The narrow source audit used:

* `PlayerDeletionLift.lean`: exact survivor payoff, arbitrary-deviation, and best-reply naturality under the Never lift;
* `BehaviorPureTimeExtremality.lean`: epsilon domination of an arbitrary behavioral deviation by a deterministic finite time or Never;
* `PlayerReindex.lean` and `TerminalUniformPayoffSelection.lean`: three-player uniform existence and terminal-profile extraction;
* `TerminalSemanticLiveWeightedCollisionTransfer.lean`: Fin4 live-weighted tail/endpoint dispatch, exact mover debt loss, and no-loss stage-atom routing;
* `ThreeByThreeZeroDiagonalQ.lean`: exact zero-diagonal (3\times3\) standard-(Q), no-homogeneous sign classification;
* `BlockDeletion.lean`, `ContinueFloor.lean`, and `BlockDeletionInequality.lean`: the passive-helper comparison point.

No source declaration turns the two unilateral profile replacements into a temporal path. That is the sole mathematical overstatement found in the central construction.
