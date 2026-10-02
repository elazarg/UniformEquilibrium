# Independent falsification of the macroscopic collision-law causal dispatch

**Reviewer:** `CODEX_RAMSEY`  
**Source:**
[`CODEX_MINER__MACROSCOPIC_COLLISION_LAW_CAUSAL_DISPATCH.md`](../notes/CODEX_MINER__MACROSCOPIC_COLLISION_LAW_CAUSAL_DISPATCH.md)  
**Verdict:** **PASS at the current repaired scope; no further repair.**  
**Disposition:** formalization-worthy finite probability lemma and causal
wrapper; retain internally.  It does not yet satisfy the export consumer gate.

I derived the probability bound and the causal constants independently before
comparing with Euler's review.  The three repairs requested there—non-strict
bad-mass summation, inclusive branch language, and explicit construction of a
terminal-gap witness before atomic orientation—are all present in the current
note.

## 1. Probability theorem

Let `L_t` be survival to date `t`, `q_t` the one-row absorption probability,
`r_t` the one-row probability of the exact fixed coalition `S`, and

\[
 m_t=L_tr_t,\qquad b_t=L_tq_t,\qquad s=\sum_tm_t.
\]

For `|S|>=2`, the exact `S` event is contained in the collision event.  The
checked product-law bound therefore gives

\[
 0\le r_t\le N_2q_t^2,
 \qquad N_2=\binom{|I|}{2}>0.                        \tag{1}
\]

Call `t` good if `s q_t<=2r_t`.  On a bad date,

\[
 m_t<(s/2)b_t.
\]

The `b_t` are disjoint first-absorption cylinders, so their total is at most
one, including in the presence of Never mass.  Hence bad dates carry at most
`s/2`, and good dates carry at least `s/2`.  The current note correctly uses a
non-strict inequality after the countable summation.

Let `t_0` be the first good date with `m_(t_0)>0`.  Every positive good
`S`-cylinder is at or after `t_0` and is contained in survival to `t_0`, so

\[
 L_{t_0}\ge s/2.                                    \tag{2}
\]

Positivity of `m_(t_0)` makes both `q_(t_0)` and `r_(t_0)` positive.
Goodness and (1) then give

\[
 q_{t_0}\ge s/(2N_2),\qquad
 r_{t_0}\ge s^2/(4N_2).
\]

Multiplying by (2) proves

\[
 m_{t_0}\ge s^3/(8N_2).                             \tag{3}
\]

The finite-window proof is identical with every sum restricted to `t<T`.
The first selected positive good date remains inside the window, and all
later good window cylinders are still subsets of its live event.

No conditional law, public correlation, or Nash property enters this proof.
The exact coalition event already includes Continue by every outsider;
forgetting that restriction only enlarges the collision event in (1).

## 2. Diffuse and boundary tests

- For two stationary clocks with common hazard `p`, the pair atom has
  `s=p/(2-p)` and maximal stage mass `p^2`, while (3) asks only for
  `p^3/[8(2-p)^3]`.
- For two independent clocks uniform on `H` dates, `s=1/H`, every diagonal
  stage has mass `1/H^2`, and the lower bound is `1/(8H^3)`.  Thus the result
  survives temporal diffusion but correctly loses a power.
- Rows with `q_t=0` have `r_t=0` and cannot be selected.
- Never mass changes `sum b_t=1` to `sum b_t<1`, which only strengthens the
  argument.
- Coalitions larger than two need no new factor: their exact event is still
  contained in the union of pair-collision events.

These tests expose no constant or probability-mode failure.

## 3. Joint-law mass to an actual chronological row

For limiting non-singleton law mass `a>0`, the checked causalization theorem
provides actual profiles `sigma_n` and finite windows with

\[
 s_n=\sum_{t<T_n}m_{n,t}>a/2
\]

eventually.  Applying the finite form of (3) yields an actual date
`t_n<T_n` with

\[
 m_{n,t_n}>a^3/(64N_2).                             \tag{4}
\]

This is an actual stage mass of the same realizing profile, not merely a
coordinate of the limiting joint law.

For the exact cap word, the checked bound

\[
 P_n\ge D_*/D(\sigma_n)
\]

and `D(sigma_n)->D_*>0` give `P_n>=1/2` eventually.  Literal root-stack
transport turns (4) into shifted stage mass strictly above

\[
 \lambda=a^3/(128N_2).                              \tag{5}
\]

The root stack, suffix profile, marked row, coalition, and shifted tail all
retain their original literal provenance.  No reselected stationary root is
substituted for the marked causal root.

## 4. Checked collision dispatch and constants

Apply
`causalCollision_tailEscape_or_quantitativeNearMinimumTransfer` with lower
bound `lambda` and

\[
 \epsilon_n=D(\widehat\sigma_n)-D_*\to0.
\]

The two inclusive branches are exactly:

\[
 D(T_n)-D_*\ge \lambda D_*/2                       \tag{6}
\]

for the literal shifted tail, with the checked cap-prefix debt account for
every exact root at that tail; or a legal reached endpoint deviation with

\[
 g_n\ge \lambda^2D_*/(2|I|),                       \tag{7}
\]

exact mover-debt loss `g_n`, and other-coordinate transfer at least
`g_n-epsilon_n`.  Eventually (7) makes that transfer positive, and finite
label/action extraction can fix a mover, endpoint, and positive recipient on
a subsequence.  The terminal-gap witness introduced in the current text is
needed only for the subsequent atomic-orientation wrapper; (6), (7), and the
recipient transfer are witness-free.

The square in (7) is correct: stage mass `lambda` first lower-bounds live
mass and also supplies the local-defect scale in the checked dispatch.

## 5. Source, novelty, and export assessment

The exact checked inputs are:

- `quittingRootCollisionMass_le_choose_card_mul_absorption_sq` in
  `UniformEquilibrium/Quitting/AbsorptionPath/CollisionConcentration.lean`;
- `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` and
  `quittingStageCoalitionMass_literalRootStack_add_length` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
- `capNashStack_continueProduct_lowerBound` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
- the causal collision dispatch in
  `TerminalSemanticLawCarrierCausalNashDispatch.lean`; and
- the minimum-transfer, recipient, and atomic-orientation wrappers in the
  corresponding `TerminalSemanticCausalCollision...` files.

A narrow search found no existing theorem with the fixed original-coalition
cubic stage bound.  The reset-face concentration theorem has additional reset
hypotheses and may change the selected coalition.  The finite-window cubic
lemma and its literal causalization wrapper are therefore genuine new
Research-level mathematics.

They are not yet a standalone export.  Current arbitrary hard-residual data
does not guarantee that the positive finite law atom is non-singleton; and,
even when this source hypothesis holds, (6) can stall at an exact all-Continue
cap root while (7) can circulate debt among labels.  Thus the output does not
yet reach a terminal approximation, cumulative return, well-founded descent,
or uniform payoff.  This is a strong producer improvement for the
non-singleton-law subcase, but the downstream consumer required by
`exports/README.md` remains absent.

## 6. Formalization recommendation

Formalize the finite-window statement first, using a finite good/bad
partition and avoiding `tsum`.  Then strengthen the existing causalization
theorem under `1<terminal.card`, transport the row by the exact prefix
product, and wrap the already checked collision dispatch.  No new
all-behavior deviation theorem is needed.  Keep the result in Research or an
internal note until one of the two fixed-scale branches gains a named
consumer.
