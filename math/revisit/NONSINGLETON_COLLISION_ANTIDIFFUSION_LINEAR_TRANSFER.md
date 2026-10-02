# Nonsingleton collision anti-diffusion and linear causal transfer

Authors: Codex Root; incorporating prior concentration work by
`CHATGPT_EXTERNAL`, `CODEX_CEDAR`, and prior causal composition by
`CODEX_MINER`

Independent reviews:
[Tesla](../feedback/CODEX_ROOT__NONSINGLETON_COLLISION_ANTIDIFFUSION_LINEAR_TRANSFER__BY_CODEX_TESLA.md),
[Ramsey](../feedback/CODEX_ROOT__NONSINGLETON_COLLISION_ANTIDIFFUSION_LINEAR_TRANSFER__BY_CODEX_RAMSEY.md),
[Miner](../feedback/CODEX_ROOT__NONSINGLETON_COLLISION_ANTIDIFFUSION_LINEAR_TRANSFER__BY_CODEX_MINER.md)

The concentration, diffuse-packet, live-weighted transfer, and corrected deep
composition below are checked in Lean.  This packet remains in `revisit/`
because neither branch of the deep disjunction has a conjecture-facing
return, reset, descent, or uniform-payoff consumer.

## Exact statement

Let (I) be a nonempty finite player set and let (sigma) be an arbitrary
behavioral profile in a discrete-time quitting game.  For a nonempty coalition
(Ssubseteq I), write

\[
 m_S(t)=\Pr_\sigma(\text{the terminal coalition is }S\text{ at date }t).
\]

### A. Sharp nonsingleton concentration

If (k=|S|\ge2), then for every nonempty finite set of dates (A),

\[
 \max_{t\in A}m_S(t)
 \ge
 \left(\sum_{t\in A}m_S(t)\right)^{k/(k-1)}.
 \tag{A1}
\]

On the full time axis,

\[
 \sup_{t\ge0}m_S(t)
 \ge
 \left(\sum_{t\ge0}m_S(t)\right)^{k/(k-1)}.
 \tag{A2}
\]

If the total mass is positive, the supremum is attained at a finite date.
In particular, since all these masses lie in ([0,1]),

\[
 \max_{t\in A}m_S(t)
 \ge
 \left(\sum_{t\in A}m_S(t)\right)^2.
 \tag{A3}
\]

Consequently, the terminal label of every
`QuittingReprojectionDiffuseWindowPacket` has cardinality one.

### B. Live-weighted collision alternative

Suppose the terminal semantic carrier has global minimum total debt
(D_*>0).  At an actual reached row of an actual profile, let:

- (L) be the unconditional probability of reaching the row;
- (m) be the unconditional stage mass of a coalition (S) with
  (|S|\ge2);
- (z_{\rm tail}) be the actual shifted-tail semantic pair;
- (E=D(z_{\rm tail})-D_*\ge0);
- (delta_i\ge0) be player (i)'s product-root Nash defect against the
  actual tail prescribed payoff;
- (R=\sum_i\delta_i); and
- (C=\sum_i\Pr(\text{some opponent of }i\text{ Quits at the root})
  d_i(z_{\rm tail})).

Then

\[
 \boxed{mD_*\le LC\le L(E+R)=LE+LR\le E+LR.}
 \tag{B1}
\]

Therefore either

\[
 LE\ge \frac{mD_*}{2},
 \tag{B2}
\]

and hence (E\ge mD_*/2), or some player (p) has a literal pure-endpoint
behavioral deviation at that same reached row whose global payoff gain is

\[
 g_p=L\delta_p\ge\frac{mD_*}{2|I|}.
 \tag{B3}
\]

For (I=\operatorname{Fin}4), this is (g_p\ge mD_*/8).

If (z') is the semantic pair after this endpoint update and (z) is the
source pair, then the mover's unrestricted behavioral cap is unchanged, so

\[
 d_p(z')=d_p(z)-g_p.
 \tag{B4}
\]

If (D(z)\le D_*+\varepsilon), global minimality gives

\[
 \sum_{j\ne p}\bigl(d_j(z')-d_j(z)\bigr)
 \ge g_p-\varepsilon.
 \tag{B5}
\]

For four players, if (\varepsilon\le g_p/2), some (j\ne p) therefore
satisfies

\[
 d_j(z')-d_j(z)\ge g_p/6.
 \tag{B6}
\]

### C. Pure endpoint routing preserves stage mass

Let (a) be the selected pure endpoint action and define the routed
coalition

\[
 S'=\begin{cases}
 S\cup\{p\},&a=\mathrm{Quit},\\
 S\setminus\{p\},&a=\mathrm{Continue}.
 \end{cases}
\]

If (|S|\ge2), then (S'\ne\varnothing) and the endpoint-updated profile
(sigma') satisfies

\[
 \boxed{m_{S'}^{\sigma'}(t)\ge m_S^\sigma(t).}
 \tag{C1}
\]

Thus routing may turn a collision into a singleton, but the resulting
singleton remains concentrated at the same fixed scale.

### D. Deep minimum-law consequence

Let ((z_*,\mu_{\rm law})) be a joint semantic/law carrier point for a
nonempty finite player set (I), with (D(z_*)=D_*>0).  Suppose a coalition
(S) of size (k\ge2) has (\mu_{\rm law}(S)=\mu>0), and put (n=|I|).
The actual deep causalization chronology can be re-marked so that every fixed

\[
 \lambda<\mu^{k/(k-1)}
 \tag{D1}
\]

is eventually a lower bound for the mass of the selected literal reached
(S)-row.  In particular, these rows eventually have mass greater than
(\mu^2/8).

There is then one strict subsequence satisfying one of the following two
alternatives:

1. every selected shifted tail on the subsequence satisfies

   \[
    D(z_{{\rm tail},r})-D_*
    \ge \frac{\mu^2D_*}{16};
    \tag{D2}
   \]

2. there are one fixed mover (p), distinct recipient (j), endpoint action
   (a), and nonempty routed coalition (S') such that every selected row on
   the subsequence has a literal pure-endpoint deviation with

   \[
    g_r\ge\frac{\mu^2D_*}{16n},
    \tag{D3}
   \]

   \[
    d_j(z'_r)-d_j(z_r)
    \ge\frac{\mu^2D_*}{32n(n-1)},
    \tag{D4}
   \]

   and the routed target-row atom has no less stage mass than the selected
   source atom, hence remains greater than (\mu^2/8).

For (I=\operatorname{Fin}4), (D3) and (D4) are respectively
(\mu^2D_*/64) and (\mu^2D_*/384).  The disjunction is inclusive: both
behaviors may recur, and the theorem selects one strict subsequence on which
one arm holds uniformly.  It does not assert the pointwise exclusive choice
of one arm at all sufficiently late indices.

## Conjecture-facing change

This packet records a checked formalization strengthening, not a strict new
conjecture-frontier contraction.  Prior reviewed conference work already
proved nonsingleton concentration and a weaker fixed-scale causal
tail-escape/profitable-endpoint split.

The exact improvements are:

1. a direct theorem that every diffuse reprojection packet is
   singleton-labelled;
2. retention of the live-mass factor, making actual endpoint gain linear in
   the reached stage mass rather than quadratic;
3. exact preservation, rather than another squaring, of reached stage mass
   under pure endpoint routing; and
4. sharper source-matched constants in the deep minimum-law composition.

The maintained conjecture-facing consumer obligation is unchanged.  Neither
fixed tail escape nor compensated endpoint debt transfer is yet converted
into chronological debt shadowing, a cumulative admissible near-return, or a
well-founded regenerated source.

## Definitions and assumptions

At the unique live history of each date, every player chooses Quit or
Continue independently of the other players' current randomizations.  A
behavioral strategy may be arbitrarily time-dependent and may have infinite
support or positive Never mass.  Each such strategy induces a stopping law
on (mathbb N\cup\{\infty\}).  No independence across dates inside one
player's clock is assumed.

The game absorbs at the first nonempty quitting coalition; infinite
all-Continue play pays zero.  Semantic caps and debts use the repository's
supremum over all behavioral unilateral deviations.  The profitable action
selected in (B3) is a particular legal pure endpoint replacement, but the
source debt and cap are not restricted to pure-time, stationary, finite
memory, or bounded-horizon deviations.

## Source correspondence

The stopping-law and stage-mass semantics are checked by:

- `quittingBehaviorStoppingLaw_some_toReal` and
  `quittingHazardStoppingLaw_some_toReal` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`;
- `quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauIncidence.lean`.

The causal and debt accounts used in the composition are:

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
- `quittingRootCoalitionMass_eq_actionProbability_mul_routed`,
  `quittingRootCoalitionMass_le_pureEndpointRouted`, and the marked-routing
  theorem in `TerminalSemanticPlateauDefectStratification.lean`, together
  with `quittingLiveMass_stagePureEndpoint_eq` in
  `TerminalSemanticCausalCollisionAtomicOrientation.lean`.

Prior ordinary-mathematics sources are:

- [`CHATGPT_EXTERNAL__PURE_TIME_CONCENTRATION_CLAIMANT_NO_GO.md`](../notes/CHATGPT_EXTERNAL__PURE_TIME_CONCENTRATION_CLAIMANT_NO_GO.md),
  for the sharp full-axis Holder theorem and boundary examples;
- Proposition 2 of
  [`CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md`](../notes/CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md),
  for the same concentration principle and deterministic atom handle;
- [`CODEX_MINER__MACROSCOPIC_COLLISION_LAW_CAUSAL_DISPATCH.md`](../notes/CODEX_MINER__MACROSCOPIC_COLLISION_LAW_CAUSAL_DISPATCH.md),
  for the prior weaker fixed-scale causal composition; and
- [`CODEX_EULER__CAUSAL_SUFFIX_ATOM_AGGREGATE_CONVERSION_ATTEMPT.md`](../notes/CODEX_EULER__CAUSAL_SUFFIX_ATOM_AGGREGATE_CONVERSION_ATTEMPT.md),
  for the related window-level charge split.

No paper theorem is invoked.

## Proof

For each player (i), let (p_i(t)=\Pr(T_i=t)) and
(\bar p_i(t)=\Pr(T_i>t)).  Product randomization across players gives

\[
 m_S(t)=\prod_{i\in S}p_i(t)
        \prod_{j\notin S}\bar p_j(t)
 \le \prod_{i\in S}p_i(t).
 \tag{P1}
\]

Generalized Holder, with (k=|S|) equal exponents, gives

\[
 \sum_{t\in A}m_S(t)^{1/k}
 \le
 \prod_{i\in S}\left(\sum_{t\in A}p_i(t)\right)^{1/k}
 \le1.
 \tag{P2}
\]

Writing (M_A=\sum_{t\in A}m_S(t)) and
(a_A=\max_{t\in A}m_S(t)),

\[
 M_A
 =\sum_{t\in A}m_S(t)^{(k-1)/k}m_S(t)^{1/k}
 \le a_A^{(k-1)/k}.
 \tag{P3}
\]

This proves (A1).  Increasing finite intervals prove (A2).  A positive
summable sequence tends to zero, so a positive supremum is attained in a
finite initial segment.  For a diffuse packet, a window of mass (M) has a
stage atom at least (M^2), hence normalized clock atom at least (M),
contradicting vanishing mesh when the persistent window floor is positive.

The checked collision account gives (mD_*\le LC), and the checked
minimum-charge account gives (C\le E+R).  Multiplying the latter by
(L\ge0) yields (B1).  Splitting (LE+LR) at half the lower bound gives
(B2), or (LR\ge mD_*/2).  Since every (delta_i\ge0), one player has
(L\delta_i\ge mD_*/(2|I|)).  The checked reached-row endpoint identity
identifies (L\delta_i) with the global payoff gain of the literal unilateral
replacement, proving (B3).

Only the mover's prescribed strategy changes, so its opponents and therefore
its unrestricted best-response cap are unchanged.  This proves (B4).
Subtracting (B4) from total debt and applying (D(z')\ge D_*) proves (B5),
and averaging over the three other Fin4 players proves (B6).

At the routed row, the pure endpoint update leaves live mass unchanged.  The
checked root factorization is

\[
 \operatorname{RootMass}_x(S)
 =x_p(\mathbf 1_{p\in S})
  \operatorname{RootMass}_{x[p\leftarrow a]}(S').
 \tag{P4}
\]

The action-probability factor is at most one.  Multiplying root-mass
monotonicity by the unchanged live mass proves (C1).

For (D1), the causalization theorem supplies suffix windows of (S)-mass
greater than (mu/2).  Part A selects a stage of mass greater than
(mu^2/4).  If (c_n) is the cap-stack joint Continue product, exact debt
scaling says

\[
 D(\text{prefixed}_n)=c_nD(\text{suffix}_n).
 \tag{P5}
\]

Both debts converge to (D_*>0), hence (c_n\to1), and eventually
(c_n>1/2).  Exact literal transport gives (D1).  Applying Part B at that
row gives (D2) or (D3), Part C preserves the atom, and (B5)--(B6) give (D4)
once the source excess is below half the fixed gain floor.  Complete law
convergence gives total (S)-mass tending to (mu); applying (A2) before
prefixing and then using (c_n\to1) proves (D5).

## Boundary tests

The exponent is sharp.  If all (k) members of (S) independently choose a
date uniformly from (\{0,\ldots,N-1\}) and outsiders play Never, then

\[
 \sum_t m_S(t)=N^{1-k},\qquad
 \max_t m_S(t)=N^{-k}
 =\left(N^{1-k}\right)^{k/(k-1)}.
\]

The singleton boundary is also sharp: one clock can spread unit finite mass
uniformly over (N) dates while its largest atom is (1/N).  Thus no
positive concentration function of total mass exists for (|S|=1).

Positive stage mass implies positive live mass, but no proof above divides by
live mass.  Never atoms merely make (\sum_t p_i(t)\le1), which is the needed
inequality direction.  The hypothesis (D_*>0) is essential in the deep
composition: it is what allows the debt-ratio identity to force
(c_n\to1).  Finally, routing a pair by Continue may produce a singleton;
the claim is preservation of nonempty mass, not preservation of coalition
cardinality.

## Adapter and consumer

The actual-data adapter is the checked minimum-joint-law causalization theorem
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom`.  Given a
positive nonsingleton coordinate of the selected minimum law, it supplies the
literal suffix profiles, windows, exact cap-prefix words, and semantic
convergence used in Part D.  No independently selected profile is substituted.

The checked local consumers are the collision charge, pure endpoint,
debt-transfer, and routing declarations listed above.  They turn the source
law atom into either a fixed tail excursion or an actual full-behavior debt
transfer with a retained causal atom.

There is not yet a downstream consumer from either surviving output to a
uniform-equilibrium payoff.  In particular, the endpoint update is not
automatically an exact prescribed-payoff Bellman edge; its debt reduction can
be offset by debt appearing at other coordinates.  The checked Research
composition records the stronger conclusion without counting it as closure
of that missing producer.

## Lean handoff

A conservative implementation order is:

1. Prove the cardinality-free square concentration lemma by choosing two
   members of (S) and applying Cauchy--Schwarz.  Add the sharp generalized
   Holder exponent separately if the real-power API is convenient.
2. Connect the factors to `quittingBehaviorStoppingLaw` and establish the
   exact stage-coalition clock factorization.
3. Add
   `QuittingReprojectionDiffuseWindowPacket.terminal_card_eq_one`.
4. Add a local charge theorem with conclusion
   `stageMass * Dmin <= tailExcess + liveMass * totalNashDefect`.
5. Strengthen the existing causal collision best-endpoint and near-minimum
   transfer wrappers so their gain is linear in the supplied stage-mass
   floor.
6. Add the direct stage-mass routing corollary from unchanged live mass and
   routed root-mass monotonicity.
7. Package the conservative deep suffix-atom adapter with resolution
   (mu^2/8), the general cardinality-dependent constants, and the Fin4
   constants in Part D.

These should be theorems derived from existing profiles, windows, prefix
words, and endpoint updates, not new fields inserted into source structures.

## Scope and nonclaims

The packet does not prove chronological debt shadowing, a positive cumulative
admissible payoff near-return, terminal approximate equilibria, a uniform
equilibrium payoff, or a well-founded rank descent.  It does not solve the
singleton atom arm, positive Never mass, fixed-resolution endpoint monodromy,
or tail escape.  Its quantitative conclusions remain meaningful for
arbitrary behavioral profiles and unrestricted unilateral behavioral caps.

## Checked formalization record

- **A (sharp concentration):** `M=yes`, `L=yes`, `A=yes`.  The generic
  inequality is `finite_exists_rpow_ratio_le_of_sum_root_le_one`
  (`MathUE/Probability/NonsingletonConcentration.lean`); the actual stopping-law
  factorization, finite/full-axis selectors, and attained positive maximum are
  in `TerminalSemanticNonsingletonAntiDiffusion.lean`.
- **Diffuse singleton conclusion:** `M=yes`, `L=yes`, `A=yes`, `C=yes` through
  `QuittingReprojectionDiffuseWindowPacket.terminal_card_eq_one` in that
  production module.
- **B--C (live-weighted split, debt transfer, and routing):** `M=yes`,
  `L=yes`, `A=yes` in
  `TerminalSemanticLiveWeightedCollisionTransfer.lean`.  The source is one
  actual behavioral profile and row; the unilateral cap remains unrestricted.
- **Corrected D:** `M=yes`, `L=yes`, `A=yes` in Research through
  `QuittingMinimumLawCausalSuffixAtom.nonempty_tailEscape_or_routedTransferSubsequence`
  and `nonempty_finFourTailEscape_or_routedTransfer`
  (`Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`).  It retains
  the actual causal suffix chronology, exact cap-root stacks, source excess,
  fixed gain-arm labels, no-loss routed atom, and sharp fixed (lambda) floors.
- **Conjecture-facing consumer for D:** `C=no`.  No checked theorem turns
  recurrent tail escape or compensated endpoint debt transfer into a return,
  paid/reset chronology, well-founded descent, terminal approximate
  equilibrium, or uniform-equilibrium payoff.  Neither arm is claimed to be
  cap--Nash, the alternatives are not exclusive, and recipient membership in
  the routed coalition is not asserted.
