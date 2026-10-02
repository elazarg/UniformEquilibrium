# Minimum-source exact blocks have a normalized seam floor

Identity: `CODEX_SPINOZA`

## Current status

**Ordinary mathematics; theorem-level synthesis of checked declarations; no
Fin4 consumer.**  The result below rules out the proposed exact
source-reprojection producer on every tangent endpoint converging to the
minimum fibre.  It uses the full finite block, the compact minimum-fibre
moat, and the counterexample-side uniform capacity bound.  It is not another
one-row cap estimate.

The remaining exact producer can only live at an endpoint separated from the
minimum in total debt.  The paid first-disagreement row survives in both
branches, but does not itself provide a Nash--Bellman edge.

## 1. Question

Fix a four-player quitting reward table and suppose, for contradiction, that
it has no uniform-equilibrium payoff.  Let

\[
 D_*>0
\]

be the minimum terminal-semantic debt.  The tangent-frontier packet supplies
actual full-replacement source profiles \(Y_n\), converging semantic pairs
\(y_n\to y\), and source-supported paid rows of gain at least \(D_*/16\).

Can one turn those paid rows into canonical finite exact Nash--Bellman blocks
\(B_n\) of positive total marginal hazard \(C_n\), with terminal tails
reprojecting to the literal source payoffs at sublinear cost,

\[
 \frac{\operatorname{dist}(T_n,y_n^u)}{C_n}\longrightarrow0?
 \tag{1.1}
\]

Here \(T_n\) is the terminal continuation value of the block and \(y_n^u\)
is the prescribed-payoff coordinate of the actual source pair.  The exact
Bellman orientation is

\[
 v_t=F(q_t,v_{t+1}),\qquad T_n=v_{H_n}.
 \tag{1.2}
\]

## 2. Uniform near-minimum normalized seam theorem

### Theorem 2.1

There are constants \(\eta>0\) and \(\kappa>0\), depending only on the
reward table, such that the following holds.

Let \(s\) be any actual terminal-semantic carrier pair satisfying

\[
 D(s)<D_*+\eta.
 \tag{2.1}
\]

Let \(B\) be any finite exact Nash--Bellman block all of whose annotations
lie in the canonical payoff box.  Write

\[
 T=(B.\operatorname{state}(B.\operatorname{horizon}))^u,
 \qquad
 C=B.\operatorname{hazardCharge}.
\]

If \(C>0\), then

\[
 \operatorname{dist}(T,s^u)\ge \kappa C.
 \tag{2.2}
\]

In fact the proof gives a stronger fixed absolute floor

\[
 \operatorname{dist}(T,s^u)\ge \rho/2
 \tag{2.3}
\]

for one \(\rho>0\), and one may take

\[
 \kappa=\frac{\rho}{2\widehat H},
 \qquad \widehat H=\max\{1,H\},
 \tag{2.4}
\]

where \(H\) is any common upper bound on the hazard charge of canonical
finite exact blocks.

### Proof

Use
`exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff`.
It gives:

* the compact payoff projection \(K\) of the complete minimum fibre;
* an open exact all-Continue basin \(N\);
* \(\rho>0\) with
  \(\operatorname{thickening}_\rho(K)\subseteq N\); and
* uniqueness of the all-Continue exact root throughout the relevant basin,
  equivalently the displayed positive linear absorption-defect inequality.

Compactness of the terminal-semantic carrier and continuity of total debt
give \(\eta>0\) such that every carrier pair satisfying (2.1) obeys

\[
 \operatorname{infDist}(s^u,K)<\rho/2.
 \tag{2.5}
\]

This is exactly the public lemma
`exists_pos_carrierDebtMoat_of_infDist_minimumFiber` (and is also the
`source_close` field of
`FinFourCarrierSourceChargeDebtErrorGate`).

Suppose contrary to (2.3) that

\[
 \operatorname{dist}(T,s^u)<\rho/2.
\]

The one-Lipschitz property of distance to \(K\), together with (2.5), gives

\[
 \operatorname{infDist}(T,K)<\rho,
\]

so \(T\in N\).  Apply
`QuittingFiniteExactNashBellmanBlock.root_eq_allContinue_of_terminal_mem_uniqueBasin`.
Backward induction through the whole block makes every displayed root
all Continue.  Consequently every marginal Quit hazard is zero and \(C=0\),
contrary to the hypothesis.  This proves (2.3).

The checked counterexample-side declaration
`finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
and
`hasBoundedFiniteExactNashBellmanHazardCapacity_iff`
give one finite \(H\) bounding every canonical block charge.  Enlarging it
to \(\widehat H\ge1\), we have \(0<C\le\widehat H\).  Hence

\[
 \operatorname{dist}(T,s^u)
 \ge\frac{\rho}{2}
 \ge\frac{\rho}{2\widehat H}C,
\]

which is (2.2).  \(\square\)

## 3. Tangent-frontier consequence

Fix an active tangent mover and a compact full-replacement endpoint, using
the notation of
`CODEX_DESCENDANT__EVERY_FIN4_TANGENT_FRONTIER_HAS_QUANTITATIVE_PAID_PORT`:

\[
 Y_n=\operatorname{fullReplacementProfile}(p,\nu_n),
 \qquad
 y_n=\operatorname{Sem}(Y_n)\longrightarrow y.
\]

The checked tangent-frontier theorem selects one fixed observer \(j\ne p\)
and, eventually, source-supported rows at the literal profiles \(Y_n\) with
gain \(D_*/16\), limiting debt at least \(D_*/3\), eventual debt at least
\(D_*/4\), and the exact \(4M,8M,32M^2\) reach inequalities.

### Corollary 3.1 (minimum endpoint branch)

If \(D(y)=D_*\), then every sequence of positive-charge canonical exact
blocks \(B_n\), purportedly reprojected to the actual sources \(Y_n\), obeys
eventually

\[
 \frac{\operatorname{dist}(T_n,y_n^u)}{C_n}\ge\kappa>0.
 \tag{3.1}
\]

Indeed continuity gives \(D(y_n)<D_*+\eta\) eventually, and Theorem 2.1
applies.  Thus (1.1) is impossible even though the full paid-row packet is
present at those same literal sources.

This is the exact whole-block form of the minimum-cap obstruction.  The paid
row is a horizontal unrestricted response statement; the block is a vertical
exact Nash--Bellman object.  Source support, fixed observer, fixed gain, and
the reach bounds do not bridge those interfaces.

### Corollary 3.2 (exhaustive surviving branch)

For any chosen compact full-replacement endpoint, exactly the following
source alternatives remain relevant:

1. \(D(y)=D_*\): the paid port exists, but every positive exact
   source-reprojected block pays the normalized seam floor (3.1);
2. \(D(y)>D_*\): the full-replacement sources are eventually separated from
   the minimum by a fixed debt excess, and the existing signed retraction /
   paid-cap descent machinery applies, but no source-returning exact block is
   currently produced.

Therefore an exact charged-block proof cannot be obtained uniformly from the
tangent paid-port packet alone.  It must either consume the genuinely
off-minimum debt excess to construct a macroscopic source return, or leave
exact roots and build the approximate forward packet requested in
`FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md`.

## 4. Why bounded capacity is essential to the normalized statement

The open basin alone gives the absolute floor (2.3).  Without the uniform
upper bound on \(C\), it does not imply a positive lower bound on
\(\operatorname{dist}(T,s^u)/C\): arbitrarily large unrelated exact blocks
could make that quotient small.  Conversely, capacity alone gives no seam
floor.  The normalized exclusion is precisely their joint consequence.

This distinction matters for the requested producer.  A fixed positive seam
is not automatically fatal when charge may diverge, while in the bounded
capacity branch it is fatal to every little-oh reprojected family.

## 5. Boundary and nonclaims

* The theorem concerns exact Nash--Bellman blocks in the canonical box.  It
  does not rule out approximate roots with summable support-Nash and Bellman
  errors.
* The semantic source pair need not equal the block's first annotation for
  the estimate; only the claimed terminal reprojection to that source is
  used.  A fortiori it applies when the first annotation is literally the
  source payoff.
* No claim is made for sources with debt at least \(D_*+\eta\).
* The result does not consume the off-minimum endpoint branch.
* The paid row is retained at exactly the source profiles to which the
  exclusion applies; it is not discarded or replaced by an unrelated
  profile.
* No uniform-equilibrium payoff or counterexample is constructed.

## 6. Files and declarations inspected

* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`:
  `exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff`.
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect.lean`:
  `exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff`.
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourCarrierSourceChargeDebtErrorGate.lean`:
  `exists_pos_carrierDebtMoat_of_infDist_minimumFiber`.
* `UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRestartMoat.lean`:
  `root_eq_allContinue_of_terminal_mem_uniqueBasin` and
  `exists_uniform_terminal_separation_of_positiveAbsorption`.
* `UniformEquilibrium/Quitting/Bellman/Finite/UnboundedExactBlockHazardCapacity.lean`:
  `hasBoundedFiniteExactNashBellmanHazardCapacity_iff` and the finite-block
  hazard definitions.
* `UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`:
  `finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`.
* `questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md` and
  `questions/FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md`.

## 7. Next exact question

At a full-replacement cluster with \(D(y)>D_*\), can the signed debt excess
be spent to produce a literal exact block whose terminal tail returns to the
same off-minimum source, rather than merely a cap-envelope descent?  Any such
theorem must identify the paid row's actual prescribed payoff with a
Nash--Bellman endpoint or provide a backward compiler; the minimum-fibre
limit cannot supply that identification by Theorem 2.1.
