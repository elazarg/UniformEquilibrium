# Normalized passport minimization eliminates support entry

Authors: FORCED_PAIR_REVIEW

Independent review:
[PAIR_WALL_REVIEW](../feedback/FORCED_PAIR_REVIEW__NORMALIZED_PASSPORT_MINIMIZER_ELIMINATES_SUPPORT_ENTRY__BY_PAIR_WALL_REVIEW.md)

## Exact statement

Let $I$ be a nonempty finite player set, let $r$ be a finite quitting reward
table, let $D$ be total unrestricted terminal semantic debt, and assume

\[
D_*:=\min_{z\in K_r}D(z)>0.
\]

Fix a source-attached sequence of actual behavioral profiles and marked dates
$(X_n,t_n)$. At every mark require:

1. one fixed pure nonsingleton coalition $C$;
2. one fixed marked owner $o$ with local root defect zero;
3. one fixed mover $p$ with positive pure-endpoint reward difference
   $\delta_p>0$;
4. complete post-mark joint semantic/law tail $(w_n,lawTail_n)$;
5. unconditional marked mass $m_n>0$; and
6. actual endpoint gain $g_n=m_n\delta_p>0$.

Assume, after one fixed-label subsequence, simultaneous convergence of the
decorated tuples

\[
((z_n,law_n),(w_n,lawTail_n),m_n,g_n)
\longrightarrow
((z,law),(w,lawTail),m,g),
\tag{1}
\]

where $z_n=\operatorname{Sem}(X_n)$ and

\[
D(w)=D_*,\qquad D(z)=L>0,\qquad m>0,\qquad g>0.
\tag{2}
\]

For every $n$ and every arbitrary finite word $W$ of product roots, form the
literal descendant $(W\triangleright X_n,t_n+|W|)$. No Nash condition is
imposed on $W$. Decorate it by its whole joint point, unchanged post-mark
joint tail, transported mass, and transported gain. Let $\mathcal R$ be the
union over all $n,W$, and let

\[
\mathcal K:=\overline{\mathcal R}
\subseteq
\mathcal J_r\times\mathcal J_r\times[0,1]\times[0,2M],
\tag{3}
\]

where $\mathcal J_r$ is the compact joint semantic/law carrier and $M$ is the
canonical reward bound.

Choose

\[
0<\theta<\frac mL,\qquad 0<\psi<\frac gL,
\tag{4}
\]

and define

\[
\mathcal K_{\theta,\psi}:=
\left\{((z',law'),(w',lawTail'),m',g')\in\mathcal K:
D(w')=D_*,\ m'\ge\theta D(z'),\ g'\ge\psi D(z')\right\}.
\tag{5}
\]

Then this slice is nonempty and compact, and whole debt has a minimizer
$x_0=((z_0,law_0),(w_0,lawTail_0),m_0,g_0)$. Its exact cap--Nash root
correspondence is

\[
\boxed{\operatorname{Nash}(z_0^B)=\{\mathbf C\}.}
\tag{6}
\]

If $D(z_0)=D_*$, actual finite-prefix descendants approaching $x_0$ form a
whole-source-return concentrated collision packet: whole debts and marked
tail debts tend to $D_*$, marked pair mass and gain retain positive floors,
and the owner defect is exactly zero. The checked Fin4 collision compiler
therefore produces its three-role transfer/limit-chord output.

For the maintained Fin4 forced-pair source, the strict reduction is

\[
\boxed{
\text{whole-source-return three-role output}
\quad\lor\quad
\text{off-minimum normalized-passport minimizer with unique all Continue}.}
\tag{7}
\]

The former positive-absorption support-entry alternative is absent.

## Conjecture-facing change

The strict canonical forced-pair ray previously ended at an off-minimum
cluster with

\[
\text{unique all Continue}\quad\lor\quad\text{support entry}.
\]

Restarting from support-entry points only decreased a real debt quantity and
gave no well-founded rank. The new selection minimizes debt after adjoining
the causal passport and closing under every literal prefix. The normalized
class is exactly invariant at carrier points, so minimality excludes every
positive-absorption exact root at once.

Thus support entry cannot recur and is no longer a live Fin4 obligation. The
remaining branch is exactly the source-attached off-minimum decorated
minimizer with unique all Continue. This does not consume that inert branch
and does not prove a uniform-equilibrium payoff.

## Definitions, probability, and strategy class

Profiles are arbitrary behavioral strategies in the discrete-time quitting
game. A unilateral deviator may use Never, arbitrarily late deadlines,
randomized hazards, and history-dependent behavior. The cap $B_i$ is the
supremum over this full class, $d_i=B_i-U_i$, and $D=\sum_i d_i$.

The complete terminal law includes every nonempty finite terminal coalition
and all-Never. The marked mass is unconditional and contains every earlier
survival factor.

For a word $W=(q_0,\ldots,q_{k-1})$, put

\[
s(W)=\prod_{h<k}\operatorname{Cont}(q_h).
\]

The raw orbit is explicitly

\[
\mathcal R=
\left\{\mathcal A(W\triangleright X_n,t_n+|W|):
n\in\mathbb N,\ |W|<\infty\right\}.
\tag{8}
\]

For a fixed product root $q$ with Continue mass $c$, the decorated prefix map
is

\[
\Phi_q((z,law),(w,lawTail),m,g)
=((T_qz,P_qlaw),(w,lawTail),cm,cg).
\tag{9}
\]

## Proof

### Compactness and nonemptiness

Both joint points lie in the checked compact carrier $\mathcal J_r$. Marked
mass is in $[0,1]$, and gain is in $[0,2M]$. Hence the ambient product and the
closed orbit carrier $\mathcal K$ are compact.

The empty word is allowed. Thus the simultaneous limit (1) belongs to
$\mathcal K$. Equations (2) and (4) put it in the slice. The tail-minimum
condition and density inequalities are closed because $D$ is continuous.
Therefore the slice is nonempty and compact.

### Prefix invariance

For every raw descendant, adding $q$ produces another raw descendant. Exact
literal transport gives

\[
m\mapsto cm,\qquad g\mapsto cg.
\tag{10}
\]

Semantic and law prefixing are continuous, so

\[
\Phi_q(\mathcal R)\subseteq\mathcal R
\quad\Longrightarrow\quad
\Phi_q(\mathcal K)\subseteq\mathcal K
\tag{11}
\]

for every fixed root, whether or not it is Nash at a raw source.

If $q$ is exact cap--Nash at $z^B$, the checked arbitrary-root debt account
has zero total-defect term. Hence

\[
D(T_qz)=cD(z).
\tag{12}
\]

Together with (10),

\[
cm\ge\theta D(T_qz),\qquad cg\ge\psi D(T_qz),
\tag{13}
\]

and the post-mark tail is unchanged. Thus exact prefixing maps the normalized
slice into itself with no threshold degradation.

### The minimizer

Let $\overline D=D(z_0)$ be the slice minimum. Global minimum provenance gives
$\overline D\ge D_*>0$. For any exact root $q$, slice invariance gives

\[
\overline D\le D(T_qz_0)=c\overline D\le\overline D.
\]

Therefore $c=1$. A product root has Continue mass one only when every
marginal is pure Continue. Conversely all Continue is exact at every carrier
cap because each cap coordinate dominates immediate singleton Quit, which is
one of its unrestricted deviations. This proves (6).

### Minimum-return actualizers

If $\overline D=D_*$, choose raw descendants converging to $x_0$. Their whole
and marked-tail debts tend to $D_*$; eventually their pair mass is at least
$\theta D_*/2$ and their gain at least $\psi D_*/2$. Labels, tail provenance,
zero owner defect, and exact mover-debt subtraction remain literal.

If desired, recursively add enough all-Continue prefixes to make marks
increase; this changes none of those data. With cutoff mark plus one and scale
$1/(n+1)$, these actual profiles define a
`QuittingReprojectionConcentratedPacket`. Its normalized owner defect is zero
and its whole source debt tends to $D_*$. Since marked-tail debt also tends to
$D_*$, the compiler's fixed positive tail-escape arm is eventually false.
The three-role transfer/limit-chord output follows.

## Source correspondence

Checked declarations used:

* `FinFourAtlasWeakConcentratedSingletonCore.nonempty_forcedPairPacket` and
  `FinFourWeakCoreForcedPairPacket` in
  `Research/Quitting/FinFourProducerAtlas/ForcedPair.lean`;
* `FinFourMinimumAtomProducer.nonempty_ownerCompressedSingletonProducer` and
  `FinFourOwnerCompressedSingletonProducer.nonempty_strongConcentratedPacket`;
* `quittingTerminalSemanticLawCarrier_isCompact`,
  `quittingTerminalSemanticLawPoint_mem_carrier`,
  `continuous_quittingTerminalOutcomeLawPrefix`, and
  `quittingTerminalSemanticLawPrefix_mem_carrier` in
  `TerminalSemanticResetIncidenceReturn.lean`;
* `continuous_quittingTerminalSemanticPrefix` in
  `Quitting/Root/TerminalSemanticPair.lean`;
* `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`
  in `CapDebtBellmanReduction.lean`;
* `eq_pure_false_of_quittingStationaryContinueMass_eq_one` in
  `Quitting/Stationary/LiveMass.lean`; and
* `ConcentratedCollisionFourRole.packet_eventually_tailEscape_or_threeRoleTransfer`
  and `packet_tailEscapeFrequently_or_threeRoleLimitChord` in
  `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`.

The fixed-label moving minimum-tail family is the reviewed mathematical
composition of `FIN4_WEAK_SINGLETON_TO_MINIMUM_TAIL_FORCED_PAIR.md` and the
strict ray arm of `FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md`; it is not
yet one checked composite declaration. The new content is the decorated
arbitrary-prefix orbit, invariant slice, minimization, and equality-arm
actualization.

## Boundary tests

### Positive boundary

If a canonical exact-prefix ray has scalar debt limit $D_*$, debt, marked
mass, and gain share the same survival factor. Its decorated limit lies in the
slice with minimum $D_*$, reproducing the reviewed whole-source-return packet.

### Necessity of positive minimum

If $D_*=0$, equality $D(T_qz)=cD(z)$ does not force $c=1$. The all-zero table
has zero debt and admits absorbing exact roots. Thus $D_*>0$ is essential.

### Finite-source density-loss falsifier

The raw packet class is not invariant. If $q$ is exact only at the limit and
has finite-source total defect $E_n>0$, then

\[
D(q\triangleright X_n)=cD(X_n)+E_n,\qquad
m(q\triangleright X_n)=cm_n.
\]

If $m_n=\theta D(X_n)$, its new density is strictly below $\theta$. The exact
scalar test

\[
D(X_n)=1,\quad c=\tfrac12,\quad m_n=\theta,\quad E_n=\tfrac1n
\]

violates the finite density inequality at every rank although the densities
converge to $\theta$. A later exact prefix cannot repair the ratio. The proof
therefore correctly claims invariance only for the closed carrier slice.

## Adapter and consumer

The checked local adapter is
`FinFourAtlasWeakConcentratedSingletonCore.nonempty_forcedPairPacket`. Finite
pigeonhole freezes the pair, owner, mover, and orientation before the orbit is
defined. Every raw element retains one original source rank and differs only
by a finite literal prefix.

When the slice minimum is $D_*$, the checked consumers are:

```text
ConcentratedCollisionFourRole.packet_eventually_tailEscape_or_threeRoleTransfer
ConcentratedCollisionFourRole.packet_tailEscapeFrequently_or_threeRoleLimitChord
```

In the strict arm there is no terminal consumer: the exact output is the new
decorated off-minimum inert point. Eliminating support entry is itself the
strict reduction.

## Lean handoff

Suggested declarations:

```text
QuittingMarkedPairDecoration
QuittingMarkedPairRawPrefixOrbit
QuittingMarkedPairPrefixOrbitCarrier
QuittingMarkedPairNormalizedPassportSlice

markedPairPrefixOrbitCarrier_isCompact
markedPairPrefixMap_mem_carrier
markedPairNormalizedSlice_mem_prefix_of_capNash
exists_minimum_markedPairNormalizedSlice
minimum_markedPairNormalizedSlice_unique_allContinue
minimum_markedPairNormalizedSlice_minimumReturnPacket_or_inert
```

The raw orbit must quantify over all source ranks and all finite root words;
it must not require exact roots. The finite-source density falsifier should be
kept as a regression against accidentally asserting raw-packet invariance.
The source theorem must derive the family, labels, and thresholds from the
named producer rather than store the desired conclusion as fields.

## Scope and nonclaims

* The decorated minimizer need not be behaviorally attained.
* Exactness is asserted only at the carrier minimizer, not raw approximants.
* Finite actualizers need not lie on the exact density boundary.
* The theorem does not consume unique all Continue.
* Marked law mass is not fresh root absorption.
* The paid endpoint is horizontal, not a prescribed-payoff Bellman edge.
* No minimum-fibre support containment is proved.
* No terminal approximants, cumulative return, uniform-equilibrium payoff, or
  counterexample are produced in the off-minimum arm.

## Formalization record

This packet is formalized through the generic normalized-passport layer and
an actual Fin4 minimum-atom adapter.

1. `Research/Quitting/NormalizedPassportPrefixOrbit.lean` defines
   `QuittingMarkedPairDecoration`, `QuittingMarkedPairDecoratedFamily`, its
   arbitrary finite-prefix orbit and compact carrier, and the normalized
   passport slice.  The exact source identities
   `QuittingMarkedPairDecoratedFamily.rawDecoration_markedMass_eq`,
   `QuittingMarkedPairDecoratedFamily.rawDecoration_actualGain_eq`, and
   `QuittingMarkedPairDecoratedFamily.descendant_postMarkSpine_eq` retain the
   marked-mass and gain scaling and the complete post-mark behavioral spine.
2. `Research/Quitting/NormalizedPassportMinimizer.lean` proves
   `QuittingMarkedPairDecoratedFamily.exists_minimum_normalizedPassportSlice_eq_or_strict_inert`.
   From a supplied convergent passport it selects a minimizer in the enlarged
   normalized slice and returns either exact equality with the displayed
   global minimum, or strict excess debt together with the exact statement
   that all Continue is its only exact cap--Nash root.
3. `Research/Quitting/NormalizedPassportMinimumReturn.lean` proves
   `exists_minimumReturnActualizer_and_threeRoleLimitChord`.  In the equality
   arm it extracts actual prefix-orbit rows, builds the concentrated packet,
   and reaches `ConcentratedCollisionFourRole.ThreeRoleLimitChord` with the
   retained positive mass and gain floors, zero marked-owner defect, and
   whole- and tail-debt convergence.
4. `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean` supplies the
   actual Fin4 adapter.  The definitions
   `FinFourOwnerCompressedMinimumReturnForcedPairPacket.normalizedSourceProfiles`
   and
   `FinFourOwnerCompressedMinimumReturnForcedPairPacket.normalizedDecoratedFamily`
   use the existing fixed-source forced-pair profiles directly.
   `FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_normalizedReturnSelection`
   derives the compact subsequence and convergent passport; neither is a
   caller hypothesis.  `FinFourNormalizedReturnSelection.sourceRank_strictMono`
   and the named source-profile, target-profile, marked-date, terminal,
   owner, gain, defect, spine, limit, passport, density, and actualizer-origin
   accessors retain the original packet indices, strictly increasing source
   ranks, finite prefix root words, fixed pair labels, and exact quantitative
   provenance.
5. `FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_normalizedReturnThreeRole_or_strictInert`
   returns the literal equality/strict-inert split for one actual packet.
   `FinFourNormalizedReturnThreeRoleOrStrictInert` stores the selected family,
   enlarged-slice minimizer, its minimality, the source minimum lower bound,
   and the exact outcome.  The equality arm stores an actualizer and the
   checked three-role chord.  The strict arm stores only strict excess debt
   and the all-Continue-only cap--Nash equivalence.
6. `FinFourMinimumAtomProducer.exists_normalizedReturnSource_for_all_resolutions`
   has the source-level quantifier order
   ```text
   exists returnSource, for every lambda with 0 < lambda < mu,
     Nonempty normalized-return source capstone.
   ```
   Thus one minimum-atom chronology and one table-selected outsider are fixed
   before every admissible resolution.  The actual packet, compact
   subsequence, minimizer, actualizer, and branch may depend on `lambda`.
   The module is reachable through
   `Research/Quitting/FinFourExhaustiveProducerAtlas.lean` and the `Research`
   reader umbrella.

Evidence seals:

- **M:** PASS.  The compact-prefix minimization, finite-source density-loss
  boundary, equality actualization, and strict-inert alternative were retained
  under the reviewed positive-minimum hypotheses.
- **L:** PASS.  The generic normalized-passport declarations and the actual
  Fin4 adapter are checked Lean.  Direct and named module builds, the reader
  and Research builds, full build, axiom-audit freshness, trust,
  documentation, duplicate-proof, derivable-telescope, unit, and source-format
  checks passed at promotion.  Reader reachability was checked directly; the
  global import-graph command was separately blocked only by the excluded
  untracked `Research.Quitting.MaximalCapSemanticPrefixOrbit` module.
- **A:** PASS for the Fin4 theorem.  Starting from a singleton
  `FinFourMinimumAtomProducer`, the adapter selects the fixed return source and
  constructs the actual forced-pair family, compact subsequence, passport,
  normalized minimizer, and outcome.  The generic theorem by itself remains a
  supplied-family interface.
- **C:** PASS only in the equality arm, through the actualizer and
  `ConcentratedCollisionFourRole.ThreeRoleLimitChord`.  The strict inert arm
  has no checked downstream consumer.

The selected minimizer may lie in the enlarged arbitrary-prefix slice rather
than the original cluster and need not be behaviorally attained.  Actualizer
origin indices and finite root words are retained exactly, but the origin
ranks are not asserted cofinal and the word is not canonical.  No intermediate
strategic-versus-collision theorem, canonical maximal ray, source
regeneration, support descent, recursive return, strict-inert consumer,
uniform-equilibrium payoff, or counterexample is proved.

The mathematical provenance is the FORCED_PAIR_REVIEW packet and the
PAIR_WALL_REVIEW linked at its head, followed by the checked generic and Fin4
source-adapter implementations.  No external paper theorem is imported.
