# A retained mark does not renew itself: the exact Fin4 post-mark anti-diffusion dichotomy

**Identity:** CODEX_STRENGTHEN  
**Date:** 2026-08-30  
**Status:** Ordinary mathematics assembled from the checked declarations named
below; no new Lean theorem is claimed.  There is no unconditional renewed-row
producer from the current minimum-return packet.  There is, however, a sharp
same-witness conditional theorem: a sequence of literal near-minimum post-mark
tails either approaches the singleton/Never terminal-law face, or contains a
fixed nonsingleton coalition at actual later rows with a uniform stage-mass
floor.  In the second arm the literal successors either return to the minimum
fiber or stay uniformly off it.  Every returning row has a uniform positive
root Nash defect, whereas every exact cap--Nash such row is forced into the
off-minimum arm.  Thus the honest exhaustive residual is

\[
 \boxed{\text{singleton/Never diffusion}\quad\lor\quad
        \text{paid renewed row}\quad\lor\quad
        \text{literal tail escape}.}
\]

This continues
[`CODEX_STRENGTHEN__FIN4_EXACT_SPINES_ARE_BALLISTIC_TO_PHANTOMS.md`](CODEX_STRENGTHEN__FIN4_EXACT_SPINES_ARE_BALLISTIC_TO_PHANTOMS.md),
especially its Section 10.  The aggregate causal-window calculation in
[`CODEX_EULER__CAUSAL_SUFFIX_ATOM_AGGREGATE_CONVERSION_ATTEMPT.md`](CODEX_EULER__CAUSAL_SUFFIX_ATOM_AGGREGATE_CONVERSION_ATTEMPT.md)
is complementary: that note spends a supplied aggregate collision mass,
whereas the present note identifies exactly when one *single* post-mark row
can be selected and keeps its literal successor.

## 1. Exact question and the two notions of reach

Let \(\pi_n\) be the actual source profile and \(m_n\) its retained marked
date.  Put

\[
 s_n=\operatorname{Spine}(\pi_n,m_n+1).
\]

The current Fin4 minimum-return source gives

\[
 D(s_n)\longrightarrow D_*>0,                                  \tag{1.1}
\]

and identifies \(s_n\) literally across the relevant source-preserving
siblings.  It also gives a fixed positive coalition mass at date \(m_n\).

The desired renewed datum is a relative date \(c_n\) in this *same* \(s_n\),
with absolute date

\[
 t_n=m_n+1+c_n,
\]

such that:

1. the probability from the start of \(s_n\) of reaching and absorbing at
   row \(c_n\) has a fixed positive floor; and
2. the literal successor
   \(u_n=\operatorname{Spine}(s_n,c_n+1)
       =\operatorname{Spine}(\pi_n,t_n+1)\)
   satisfies \(D(u_n)\to D_*\).

These are genuine same-witness dates.  But relative reach from \(s_n\) and
unconditional reach from \(\pi_n\) are different.  The latter contains the
additional factor

\[
 \Pr_{\pi_n}(\text{live at }m_n)\,
 \Pr_{x_{n,m_n}}(\mathbf C).
\tag{1.2}
\]

The retained marked atom bounds the first factor below, not the joint
Continue factor.  Therefore even the conditional producer below is a
uniformly reached **post-mark-source** row; it is not automatically uniformly
reached from the outer parent.

## 2. Narrow checked source audit

I read `SOURCES.md`, `GOAL.md`, the exact-spine and minimum-source rows of
`docs/TOOLKIT.md` and `docs/FRONTIER.md`, the current question, and only the
following relevant declarations.

1. In
   `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionConsumers.lean`:

   - `FinFourMinimumReturnPacket.forcedPairTail_eq_tail`;
   - `FinFourMinimumReturnPacket.normalizedDecoratedFamily_postDateSpine_eq_reference`;
   - `FinFourMinimumReturnPacket.normalizedDecoratedFamily_postDateLaw_eq_reference`;
   - `FinFourMinimumReturnPacket.minimumTailSource`.

   Together with
   `FinFourStabilizedForcedPairStream.tail_eq_framePostDateTail` and
   `FinFourMinimumReturnPacket.tailDebt_tendsto_minimum`, these are the literal
   ancestry and near-minimum entrance port used in (1.1).

2. In
   `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonsingletonAntiDiffusion.lean`:

   - `exists_quittingStageCoalitionMass_ge_tsum_rpow`;
   - `quittingTerminalOutcomeMass_eq_timeDisintegration` (used in that file);
   - `exists_maximal_quittingStageCoalitionMass_of_positive_total`.

   For a fixed coalition \(S\), \(|S|=k\ge2\), the first theorem gives an
   actual row with stage mass at least

   \[
     \Pr(S\text{ is the terminal coalition})^{k/(k-1)}.          \tag{2.1}
   \]

3. In
   `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauIncidence.lean`,
   `quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass`
   is the exact factorization of an unconditional row atom through reach and
   conditional root mass, while
   `quittingTerminalSemanticPair_spine_eq_prefix` identifies the semantic
   state at an actual live row with the arbitrary-root prefix of its literal
   successor.

4. In `UniformEquilibrium/Quitting/Cycles/CyclicGreenDebt.lean`,
   `quittingRootCoalitionMass_le_absorptionMass_of_nonempty` turns the selected
   root atom into a root-absorption floor.  In
   `UniformEquilibrium/Quitting/Stationary/LiveMass.lean`,
   `quittingQuitProbability_le_absorptionMass` is the corresponding marginal
   estimate.

5. In
   `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`,
   `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`
   is the arbitrary-root identity

   \[
    D(\operatorname{prefix}(x,z))
      =c(x)D(z)+\rho(x,z),                                      \tag{2.2}
   \]

   where \(\rho\) is total coordinate root Nash defect.

6. In `Research/Quitting/CapChangingLawRetainedSquareNoGo.lean`,
   `semanticMinimum_mul_capNashStackAbsorptionSum_le_debtDrop`
   charges every finite exact cap--Nash stack by the positive semantic
   minimum.

7. In
   `UniformEquilibrium/Diagnostics/Quitting/Chronology/AbsorptionClockBallisticity.lean`,
   `QuittingPositiveDebtDynamicTailWitness.exists_pos_eventually_endpointDistance_ge_absorptionMass`
   gives the checked ballistic inequality for the separately constructed
   optimized exact dynamic tail.  Its source type is important below.

## 3. The retained marked atom alone has no future content

The marked event and the post-mark continuation occupy opposite branches of
the marked product root.  The event is realized when a nonempty coalition
Quits at \(m_n\); the suffix \(s_n\) is entered only on joint Continue.
Consequently the positive mass of the former says nothing about the stopping
law of the latter.

This is not merely a missing estimate.  Given **any** behavioral tail \(s\),
put a pure nonsingleton quitting coalition at a new preceding row and attach
\(s\) on the all-Continue branch.  The new profile has marked coalition mass
one and literal post-mark spine exactly \(s\).  Thus the operation preserves
whatever near-minimum property \(s\) has but imposes no later atom, hazard, or
law constraint on it.  Taking \(s\) all Never gives the minimal strategy-level
regression: marked mass one, joint Continue zero, and no later reached row.

This regression is **not** asserted to be a positive-global-minimum reward
table; constructing such a table would settle the conjecture negatively.  It
does prove that the retained-atom and literal-tail fields currently exposed
by the source packet cannot alone imply the requested renewal.  A hard-source
theorem must add information about the law of \(s_n\), not re-use the upstream
atom.

## 4. A sharp same-witness anti-diffusion dichotomy

For a post-mark tail \(s_n\), define its total nonsingleton terminal mass

\[
 M_n=\sum_{\substack{S\subseteq\operatorname{Fin}4\\|S|\ge2}}
       \Pr_{s_n}(S\text{ is the terminal coalition}).            \tag{4.1}
\]

There are exactly eleven labels in this sum.

### Theorem 4.1 (law-face versus actual renewed row)

Exactly one of the following alternatives holds for the original sequence;
the second conclusion is stated on an extracted subsequence.

1. **Singleton/Never face:** \(M_n\to0\).  Equivalently, the distance of the
   terminal law of \(s_n\) from the face supported on the four singleton
   coalitions and Never tends to zero.  Every cluster law is supported on
   that face.

2. **Actual nonsingleton row:** there are \(\varepsilon>0\), one fixed
   coalition \(S\), \(2\le |S|=k\le4\), and literal dates \(c_n\) in the
   same tails \(s_n\), such that

   \[
    \Pr_{s_n}(S\text{ terminal})\ge \varepsilon/11,
    \qquad
    a^S_n(c_n)\ge
      (\varepsilon/11)^{k/(k-1)}
      \ge (\varepsilon/11)^2=:\chi>0.                            \tag{4.2}
   \]

   In particular, at row \(c_n\):

   \[
   \Pr_{s_n}(\text{live at }c_n)\ge\chi,
   \quad
   \Pr_{x_{n,c_n}}(S)\ge\chi,
   \quad
   1-c(x_{n,c_n})\ge\chi.                                      \tag{4.3}
   \]

All objects in the second arm belong to one chronology:

\[
 s_n\supset c_n\longrightarrow
 u_n=\operatorname{Spine}(s_n,c_n+1).
\]

If the upstream marked atom has mass at least \(\lambda\) and the marked
root's joint Continue probability is additionally at least \(\gamma>0\),
then the same row at absolute date \(t_n=m_n+1+c_n\) has stage mass in the
outer profile \(\pi_n\) at least

\[
 \lambda\gamma\chi.                                            \tag{4.4}
\]

Thus one extra marked-Continue floor upgrades the relative theorem to the
fully outer-reached same-witness chronology.

#### Proof

If \(M_n\not\to0\), choose a subsequence with \(M_n\ge\varepsilon\).
Finite pigeonhole over the eleven nonsingleton coalitions gives a further
subsequence and fixed \(S\) with terminal mass at least
\(\varepsilon/11\).  Apply
`exists_quittingStageCoalitionMass_ge_tsum_rpow` to each actual profile
\(s_n\) and this same \(S\).  Time disintegration identifies the theorem's
total mass with the displayed terminal-law coordinate, proving (4.2).

The stage-mass factorization is

\[
 a^S_n(c_n)=L_n(c_n)\Pr_{x_{n,c_n}}(S).
\]

Both factors are at most one, so each is at least \(a^S_n(c_n)\ge\chi\).
The coalition is nonempty, hence its conditional root mass is bounded by
root absorption.  This proves (4.3).  For (4.4), the marked atom floor gives
live mass at the mark at least \(\lambda\); multiply it by the marked
Continue floor and the relative stage mass \(\chi\).  If instead
\(M_n\to0\), the first arm is the definition of convergence to the stated
finite-dimensional face.

They are disjoint: the fixed \(\varepsilon\) in the second arm rules out
\(M_n\to0\).

### Sharpness of the face arm

Anti-diffusion genuinely stops at singleton labels.  One player's fixed
terminal mass can be spread over arbitrarily many dates with every stage
atom tending to zero.  Never mass can also remain positive.  Hence the first
arm does not contain a hidden fixed-row conclusion.  It is the exact
stopping-law boundary, not a proof artifact.

## 5. Successor return, paid defect, or uniform tail escape

Assume the actual-row arm and write

\[
 z_n=\operatorname{Spine}(s_n,c_n),
 \qquad
 u_n=\operatorname{Spine}(s_n,c_n+1),
 \qquad
 \rho_n=\operatorname{TotalRootNashDefect}(x_{n,c_n},u_n).
\]

The exact prefix identity (2.2), global minimality, and (4.3) give

\[
 \rho_n
   =D(z_n)-c(x_{n,c_n})D(u_n)
   \ge D_*-(1-\chi)D(u_n).                                     \tag{5.1}
\]

This yields two useful formulations.

### 5.1 Topological return/escape formulation

Since \(D(u_n)\ge D_*\), either:

- some subsequence has \(D(u_n)\to D_*\); or
- there are \(\theta>0\) and a tail on which
  \(D(u_n)\ge D_*+\theta\).

The first arm is exactly the requested near-minimum successor on the same
witness, but (5.1) strengthens it to

\[
 \liminf_n\rho_n\ge\chi D_*>0.                                 \tag{5.2}
\]

Thus this row is necessarily paid/nonexact.  It cannot be an exact cap--Nash
row.

### 5.2 Uniform quantitative formulation

At every selected row, without taking a successor limit,

\[
 \boxed{
 D(u_n)\ge D_*+\frac{\chi D_*}{2}
 \quad\text{or}\quad
 \rho_n\ge\frac{\chi D_*}{2}.}                                \tag{5.3}
\]

Indeed, if the first inequality fails, substitute
\(D(u_n)<D_*+\chi D_*/2\) into (5.1):

\[
 \rho_n>
 \chi D_*-(1-\chi)\frac{\chi D_*}{2}
 \ge\frac{\chi D_*}{2}.
\]

For Fin4, nonnegativity of the four coordinate defects implies that in the
paid arm one fixed player can be selected on a subsequence with coordinate
defect at least \(\chi D_*/8\).  Changing only that player's action at the
actual row to a best pure endpoint and then resuming the same tail realizes
this as a one-row behavioral gain.  Since the row is reached from the start
of \(s_n\) with probability at least \(\chi\), the unconditional gain from
the post-mark source is at least

\[
 \frac{\chi^2D_*}{8}.                                          \tag{5.4}
\]

The exact one-row localization used for this last sentence is the same
identity exposed as
`quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`
in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauLocalizedOtherDefect.lean`.

Equation (5.4) is measured from \(s_n\).  From the outer profile \(\pi_n\),
it is further multiplied by the survival factor in (1.2), for which the
current packet has no positive floor.

## 6. Exact rows are forced into quantitative escape

If the selected actual row happens to be exact cap--Nash against its literal
successor, then \(\rho_n=0\).  Equation (5.1) gives the sharper bound

\[
 D(u_n)\ge \frac{D_*}{1-\chi}                                  \tag{6.1}
\]

when \(\chi<1\).  If \(\chi=1\), joint Continue is zero, and exactness would
contradict \(D(z_n)\ge D_*>0\).  Thus an exact positive-mass post-mark row
cannot have a near-minimum successor.  Exactness and same-witness return are
opposed by positive minimum debt; a producer seeking both must pay an
approximation seam.

This is the local debt version of ballisticity.  It is stronger for the row
selected here because it uses its actual successor, not a separately chosen
dynamic tail.

## 7. Why cap-prefixing and the checked ballistic tail do not manufacture the row

Let \(W_n\) be any finite exact cap--Nash word literally prefixed to \(s_n\).
The checked minimum charge gives

\[
 D_*\operatorname{Abs}(W_n)
 \le D(s_n)-D(W_n\Vert s_n)
 \le D(s_n)-D_*\longrightarrow0.                               \tag{7.1}
\]

Therefore \(\operatorname{Abs}(W_n)\to0\).  In Fin4 every marginal Quit
probability is at most root absorption, so the total marginal hazard of the
entire word is at most four times this absorption sum and also tends to zero.
No exact stack inserted at the near-minimum entrance can create a fixed-mass
renewed row.

The checked theorem
`exists_pos_eventually_endpointDistance_ge_absorptionMass` says that the
independently optimized positive-debt dynamic tail is eventually ballistic
on every positive-absorption window.  It does **not** identify that dynamic
tail with \(s_n\), nor does it select dates inside \(\pi_n\).  Hence it cannot
repair provenance.  Its correct implication is negative: once an actual row
has been exactified, positive absorption forces endpoint motion, consistent
with (6.1), rather than a near-minimum renewal.

## 8. Strongest surviving theorem and exact missing obligation

The current source does not prove a renewed post-mark row.  The strongest
surviving statement is the same-witness trichotomy:

1. the post-mark terminal laws approach the singleton/Never face;
2. there is a literal, uniformly reached-from-\(s_n\), fixed-label
   nonsingleton row and a near-minimum literal successor, but the row carries
   a fixed positive legal Nash defect; or
3. there is such a literal fixed-mass row whose successor stays uniformly
   above the minimum debt.

Exact cap--Nash prefixing cannot remove the paid seam in arm 2, and the
upstream retained atom cannot exclude arm 1.

The singleton/Never chamber in
[`LAW_TIGHT_CAP_NASH_SATURATION_HULL.md`](../revisit/LAW_TIGHT_CAP_NASH_SATURATION_HULL.md)
does not close arm 1.  That packet classifies a *strict saturation-hull
minimum point* with a zero-debt owner and retains only a finite binding
cycle; its scope section explicitly leaves all strict chambers unconsumed
and supplies no actual ancestry-preserving decoder for the present tails.

The single sharp next producer obligation is therefore:

> Prove from the Fin4 hard source that the literal post-mark tails have a
> uniform positive **nonsingleton terminal-law mass**, or directly consume
> the singleton/Never face.  If the final consumer is attached to the outer
> retained parent rather than started anew at \(s_n\), also prove a uniform
> positive joint-Continue floor at the marked row.

The first alternative immediately instantiates Theorem 4.1 with the explicit
Fin4 row floor \(\chi=(\varepsilon/11)^2\); no further compact source
selection is needed.
