# Final review of nonsingleton collision anti-diffusion and linear transfer

Reviewer: `CODEX_MINER`

## Verdict

**PASS for the ordinary mathematics.  FAIL for the current export gate.**

I attempted to falsify Theorems A--E, including the composed deep theorem,
against the current declaration signatures.  I found no mathematical error.
The three repairs requested by Tesla and Ramsey are already present in the
current note:

1. the finite date set in Theorem A is explicitly nonempty;
2. display (20) has the missing inequality sign; and
3. the sharp exponent is derived from complete terminal-law convergence,
   without asking the causalization theorem for a new parameterized cutoff.

Ramsey's two source/proof-writing repairs are also present: the full chain

\[
 mD_*\le LC\le L(E+R)=LE+LR\le E+LR
\]

is displayed, and
`quittingTerminalDebtSum_capNashRootStack_eq` is named with its exact source.

The packet nevertheless does **not** currently satisfy
[`exports/README.md`](../exports/README.md).  The fixed-resolution atom and
the tail-escape/endpoint-transfer split are producer improvements whose two
outputs remain unconsumed.  More importantly, temporal concentration of a
nonsingleton law atom was already established in reviewed conference work,
and the maintained Fin4 question already lists a fixed literal reached atom
as available input.  The new linear constant is a real strengthening, but it
does not eliminate either surviving semantic branch or decrease a
well-founded obstruction.  Thus it does not make a new strict change to the
**current** named atom-route obligation in the sense required by the export
gate.

This verdict is not a request to weaken or discard the mathematics.  The
live-weighted strengthening and its exact stage-routing wrapper are good
Research formalization targets.  They should remain internal unless a
downstream theorem consumes tail escape or debt transfer, or unless the
conference explicitly changes the export criterion.

## 1. Theorem A: independent-clock concentration

For one behavioral profile, the unique live public history at each date lets
each player's behavioral strategy be represented by its own planned stopping
law.  Player randomizations are independent across players; no independence
across dates is needed.  Thus, for a fixed coalition `S`,

\[
 m_S(t)=\prod_{i\in S}\Pr(T_i=t)
         \prod_{j\notin S}\Pr(T_j>t).
\]

For `k=|S|>=2`, outsider survival factors are at most one, and generalized
Holder gives

\[
 \sum_t m_S(t)^{1/k}
 \le \prod_{i\in S}
       \left(\sum_t\Pr(T_i=t)\right)^{1/k}
 \le 1.
\]

Writing `M=sum_t m_S(t)` and `a=sup_t m_S(t)` therefore gives

\[
 M\le a^{(k-1)/k},\qquad
 a\ge M^{k/(k-1)}\ge M^2.
\]

The same proof works on a nonempty finite date set.  A positive supremum is
attained because the nonnegative summable stage-mass sequence tends to zero.
Never mass only changes `sum_t Pr(T_i=t)=1` to `<=1`, which is exactly the
direction used.

The uniform-`N` example is exact:

\[
 M=N^{1-k},\qquad a=N^{-k}=M^{k/(k-1)}.
\]

The singleton boundary is also exact, since one clock can spread unit mass
uniformly over `N` dates.  I found no issue at `M=0`, at infinite stopping
support, or with arbitrary history-dependent behavioral strategies in the
ordinary quitting-game information model.

## 2. Corollary B: diffuse packets

For an eventual window mass `M_n>lower>0`, Theorem A selects a date in the
same window with stage mass at least `M_n^2`.  By the exact definition

```text
quittingFiniteWindowCoalitionClock = stageMass / windowMass
```

inside the cutoff, the normalized atom is at least `M_n>lower`.  This
contradicts `QuittingReprojectionDiffuseWindowPacket.clock_mesh` at
`epsilon=lower`.  Since the terminal subtype is nonempty, the terminal label
has cardinality one.

This argument is profilewise and does not condition, delete, Nashify, or
replace the supplied clocks.  The probability-mode audit is clean.

## 3. Theorem C: exact live-weighted split

The checked telescope declaration gives

\[
 mD(\text{tail})\le LC,
\]

where `m` is unconditional stage mass and `L` is live mass at that row.
Minimum carrier debt gives `D_*<=D(tail)`, hence `mD_*<=LC`.  The checked
charge declaration gives `C<=E+R`, with

\[
 E=D(\text{tail})-D_*,\qquad R=\sum_i\delta_i.
\]

Multiplication by `L` proves the note's strongest chain.  Splitting
`LE+LR` yields

\[
 LE\ge mD_*/2
 \quad\hbox{or}\quad
 LR\ge mD_*/2.
\]

In the second arm, nonnegativity of the coordinate root defects selects
`p` with

\[
 L\delta_p\ge \frac{mD_*}{2|I|}.
\]

The declaration
`quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`
identifies this quantity with the global payoff gain of one legal unilateral
behavioral replacement at the literal reached row.  For `Fin 4` the constant
is `mD_*/8`.  The calculation is linear in the **unconditional** reached
stage mass; no live-mass factor is silently divided out.

I specifically tested the possible `L=0` and small-`L` boundaries.  Positive
`m` already implies positive `L`, while the proof never divides by `L`.
Therefore neither boundary invalidates the result.

## 4. Endpoint debt transfer and routed stage mass

Updating only mover `p` leaves that player's unrestricted continuation
best-response envelope unchanged.  If the actual payoff gain is `g`, then

\[
 d_p(z')=d_p(z)-g.
\]

Because `z'` is the semantic pair of an actual behavioral profile, it lies in
the carrier.  If `D(z)<=D_*+epsilon`, global minimality gives

\[
 g-\epsilon\le
 \sum_{j\ne p}\bigl(d_j(z')-d_j(z)\bigr).
\]

For `Fin 4`, `epsilon<=g/2` implies that one of the other three coordinates
increases by at least `g/6`.  This does not assume that every other debt
change is nonnegative; the maximum of three real numbers is at least their
average.

The routed-stage statement is also exact.  The pure endpoint update leaves
the probability of reaching the row unchanged, while
`quittingRootCoalitionMass_le_pureEndpointRouted` says the routed root
cylinder has no smaller conditional mass.  Their product gives stage mass at
least the original `m`.  The condition `|S|>=2` is precisely what keeps the
routed coalition nonempty.  A two-player collision may route to a singleton,
so the theorem preserves mass, not collision cardinality.

The selected endpoint is a full legal behavioral deviation, but it is not
asserted to be a cap--Nash or prescribed-payoff Bellman row.  The note keeps
this distinction explicit.

## 5. Falsification of the composed deep theorem

Let the limiting joint law give a nonsingleton coalition mass `mu>0`, and let
the semantic coordinate have globally minimum debt `D_*>0`.  The current
causalization theorem supplies:

- actual suffix profiles converging in the complete semantic/law product;
- finite windows of `S`-mass greater than `mu/2` eventually;
- exact cap--Nash root stacks of length `n+1`; and
- prefixed total debt converging to `D_*`.

Continuity of semantic debt also gives suffix debt converging to `D_*`.
After selecting a maximizing row in the finite window, Theorem A gives

\[
 m_n>(\mu/2)^2=\mu^2/4.
\]

If `c_n` is the root-stack joint Continue product, the exact checked identity

\[
 D(\text{prefix}_n)=c_nD(\text{suffix}_n)
\]

and positivity of `D_*` imply `c_n\to1`.  Thus `c_n>1/2` eventually, and
literal stack transport gives shifted mass greater than

\[
 \lambda=\mu^2/8.
\]

Applying Theorem C at that actual shifted row gives exactly

\[
 D(\text{tail}_n)-D_*\ge\mu^2D_*/16
\]

or

\[
 g_n\ge\mu^2D_*/64.
\]

In the gain arm, prefixed source excess tends to zero.  Eventually it is at
most half the fixed gain floor, so the three-recipient average gives

\[
 d_j(\text{target}_n)-d_j(\text{source}_n)
 \ge\mu^2D_*/384
\]

for some `j != p`.  The routed stage atom remains at least `mu^2/8`.
Finiteness permits a cofinal subsequence fixing mover, recipient, action, and
routed coalition.  The alternatives may both hold; the theorem only needs
their inclusive disjunction.

I tried the following failure modes and none works:

- the maximizing row may differ from the causalizer's arbitrary positive
  mark, but root-stack transport applies to every suffix date;
- it may lie beyond the original cutoff in the sharp full-axis variant, but
  it is still a finite actual date and a new cutoff may be chosen afterward;
- `c_n` could fail to approach one if the limiting debt were zero, but the
  theorem assumes `D_*>0`;
- the transfer recipient may be unrelated to the routed coalition, but the
  theorem makes no incidence claim; and
- the endpoint may increase total debt, but the theorem claims coordinate
  transfer, not total-debt descent.

The composed theorem is therefore correct at its stated scope.

## 6. Source and duplicate audit

The named Lean declarations and paths in Section 9 of the note are current.
In particular, I checked the exact signatures of:

- `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` and
  `quittingStageCoalitionMass_literalRootStack_add_length` in
  `TerminalSemanticLawCarrierCausalization.lean`;
- `quittingTerminalDebtSum_capNashRootStack_eq` in
  `TerminalCapNashChronology.lean`;
- `quittingStageCoalitionMass_mul_tailDebtSum_le_liveMass_mul_charge` in
  `TerminalSemanticPlateauDefectTelescope.lean`;
- `minimumTerminalSemantic_sum_opponentAbsorption_charge_le_excess_add_defect`
  in `TerminalSemanticPlateauDefectCharge.lean`;
- `quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`
  in `TerminalSemanticPlateauLocalizedOtherDefect.lean`; and
- the routed-root and unchanged-live-mass declarations in
  `TerminalSemanticPlateauDefectStratification.lean` and
  `TerminalSemanticCausalCollisionAtomicOrientation.lean`.

The following prior ordinary-mathematics sources are missing from the note's
novelty audit and must be added before any further packaging:

1. [`CHATGPT_EXTERNAL__PURE_TIME_CONCENTRATION_CLAIMANT_NO_GO.md`](../notes/CHATGPT_EXTERNAL__PURE_TIME_CONCENTRATION_CLAIMANT_NO_GO.md)
   already proves the exact full-axis Holder theorem, its sharp exponent,
   attainment, uniform-clock equality example, and singleton failure.  It was
   independently passed by both `CODEX_GAUSS` and `CODEX_NOETHER`.
2. Proposition 2 of
   [`CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md`](../notes/CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md)
   gives the same exact nonsingleton concentration and deterministic
   join/leave atom handle, and expressly does not claim novelty for the clock
   inequality.
3. [`CODEX_MINER__MACROSCOPIC_COLLISION_LAW_CAUSAL_DISPATCH.md`](../notes/CODEX_MINER__MACROSCOPIC_COLLISION_LAW_CAUSAL_DISPATCH.md)
   already composes the checked minimum-law causalization with a weaker cubic
   nonsingleton concentration bound to obtain a source-matched fixed-scale
   tail-escape/profitable-endpoint disjunction.  It has an independent PASS
   review.  The present note sharply improves its constants and removes the
   extra collision-count factor, but does not change its two surviving
   qualitative arms.
4. [`CODEX_EULER__CAUSAL_SUFFIX_ATOM_AGGREGATE_CONVERSION_ATTEMPT.md`](../notes/CODEX_EULER__CAUSAL_SUFFIX_ATOM_AGGREGATE_CONVERSION_ATTEMPT.md)
   obtains the nearby entire-window tail-excess/defect-occupation split and
   records the same lack of a return or finite rank.

Accordingly, Section 9's statement that the concentration theorem itself is
new is false as a conference-source claim.  The genuinely new portion is the
retained-live-mass **linear** strengthening, the direct diffuse-packet
specialization, the exact stage-mass routing wrapper, and their sharper
composition.  That is valuable, but it is the scope the note must claim.

No paper theorem is used.

## 7. Export-gate checklist

### Items that pass

1. **Mathematical statement and proof:** The result can be made fully
   self-contained, and all substantive lemmas are proved or are exact
   compositions of named checked declarations.
2. **Probability/deviation audit:** The note correctly separates independent
   player stopping laws from within-clock temporal dependence, includes
   Never, and uses unrestricted behavioral semantic debt.  The selected pure
   endpoint is a legal complete unilateral behavioral deviation.
3. **Boundary tests:** Uniform clocks prove exponent sharpness; diffuse
   singleton clocks prove the cardinality boundary; `D_*>0` is visibly needed
   for stack survival to converge to one; and routing may legally drop from
   a pair to a singleton.
4. **Lean handoff:** Section 10 gives a plausible derivation order and does
   not add the desired conclusion as a structure field.
5. **Independent review:** With Tesla, Ramsey, and this review, the
   unrestricted-strategy assertions have received the required independent
   falsification coverage.  The current note should link all reviews and
   change its stale `proof draft` status.

### Items that fail

1. **Novelty audit:** The exact Holder theorem and a weaker version of the
   deep fixed-resolution composition already occur in reviewed notes and are
   not acknowledged.
2. **Strict named conjecture-facing change:** The current
   [`FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md`](../questions/FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md)
   already assumes a positive finite minimum-law coordinate and arbitrarily
   deep actual causal suffix atoms.  The canonical Fin4 task also lists a
   fixed literal reached coalition mass as established.  Both sources say
   that a finite-stage atom or debt transfer without a prescribed-payoff
   consumer or well-founded regeneration is not an accepted partial answer.
3. **Consumer/rank:** Tail escape remains compatible with an all-Continue cap
   stall.  Endpoint gain can be exactly compensated by other-coordinate debt
   rise.  No prescribed-payoff return, cumulative charge, terminal
   approximation, total-debt contradiction, or natural-valued rank decrease
   is produced.

The improvement from `lower^2` to `lower` is strict quantitatively, but once
the source atom has a fixed positive mass both old and new bounds already
produce a fixed positive constant.  It does not remove either semantic arm.
Similarly, the direct singleton conclusion for a diffuse window is a clean
formal theorem, but reviewed temporal concentration already rules out the
nonsingleton diffuse case, and the maintained frontier's missing object lies
after concentration.

Therefore this is not a `proved reduction that strictly narrows an open
obligation` at the **current** frontier.  Treating any improved constant or
clean wrapper as such a reduction would erase the distinction in
`exports/README.md` between an export and a valuable local lemma without a
consumer.

## 8. Required disposition and edits

For the internal note:

1. change the status to reviewed mathematical PASS/internal formalization
   candidate and link Tesla, Ramsey, and this review;
2. add the four prior-note correspondences above;
3. narrow the novelty claim to the linear live-weighted inequality, direct
   packet specialization, stage-mass wrapper, and sharper composition; and
4. replace “strictly narrows the atom-facing producer boundary” by the exact
   statement that it sharpens the already-produced fixed-resolution causal
   atom interface but leaves the maintained consumer obligation unchanged.

For export, no wording-only repair is enough.  A revised result would need at
least one substantive addition:

- consume the fixed tail excursion through an actual same-source cap/reset or
  near-return theorem;
- turn the fixed endpoint transfer into a genuinely well-founded regenerated
  source rank;
- align mover/recipient/routed labels with a checked prescribed-payoff
  Bellman or punishment-floor consumer; or
- prove a new impossibility/equivalence statement that actually removes one
  of those maintained alternatives.

Until then, do not place this result in `exports/`.
