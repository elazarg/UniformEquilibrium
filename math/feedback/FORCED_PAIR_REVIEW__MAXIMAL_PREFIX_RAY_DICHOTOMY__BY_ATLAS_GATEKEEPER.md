# Adversarial review of the maximal-prefix ray dichotomy

Reviewer: `ATLAS_GATEKEEPER`

## Verdict

The central mathematics is correct and is suitable for export in a corrected,
narrow form.  It gives a genuine reduction of the live whole-source-return
seam:

\[
\boxed{
\begin{array}{c}
\text{source-attached pure-pair/minimum-tail family}\\
\Longrightarrow\\
\text{a concentrated collision packet whose whole sources return to }D_*
\quad\lor\quad
\text{a canonical off-minimum maximal-prefix ray stall.}
\end{array}}
\]

In the first arm, the diagonal family really does satisfy the existing
`QuittingReprojectionConcentratedPacket` interface and therefore enters the
checked three-role collision compiler.  In the second arm, every debt
coordinate, the pair mass, and the selected paid gain have one common scalar
factor, while all future charge available from the *same canonical maximal
orbit* tends to zero.  This is an exact architectural no-go, not a uniform-
equilibrium theorem.

Four corrections are required before export.

1. The actual-data hypothesis must be the reviewed moving pure-pair packet,
   including its zero marked owner defect and fixed positive other-player
   root defect.  Merely giving arbitrary tails and labels does not imply those
   two incentive facts.
2. In the equality arm, the note should spell out the diagonal concentrated
   packet and its resolution, mark, cutoff, scale, semantic-prefix, and defect
   fields before invoking the compiler.
3. “Recipient gain” in Sections 4.1 and 8 should be “paid mover gain” or
   “best-endpoint gain.”  The downstream compiler chooses a distinct debt
   recipient only after applying its near-minimum transfer argument.
4. The stall claims about vanishing future charge apply to the canonical
   recursively recomputed maximal roots.  They do not say that every exact
   cap-root continuation from a changed suffix has vanishing charge.

With those repairs, I found no mathematical gap.  The maximal roots cannot
vary across the near-minimum tails: after replacing the marked row by the
literal pure pair, the entire terminal semantic pair is tail-independent, and
the canonical selector is a function of its cap.  The roots can vary only
after a horizontal update changes that semantic cap, which the note correctly
classifies as leaving the ray.

## Claim audited

Let `I` be finite, let `C` be a finite coalition with at least two members,
and let `X_n` be actual profiles which start with the pure root `C` and use
arbitrary behavioral profiles `sigma_n` after the counterfactual all-Continue
outcome.  Assume additionally, in the Fin4 source-facing specialization, that
fixed distinct labels `j,o` satisfy `C={j,o}`, that `o` has zero coordinate
root defect at the pure pair, and that some fixed `p != o` has root defect at
least `delta_0>0`.  The reviewed forced-pair producer supplies these data and
literal tails with debt tending to the positive global minimum `D_*`.

Starting from any `X_n`, recursively prefix the canonical maximal-absorption
exact cap-Nash root.  The note claims:

* the resulting semantic orbit is independent of `n`;
* all player debts, total debt, shifted pair mass, and the fixed paid gain
  scale by one common survival product;
* if the total-debt limit equals `D_*`, a diagonal family supplies the missing
  whole-source-return packet and enters the checked collision compiler;
* if the limit is greater than `D_*`, normalized debt and positive-debt
  support are invariant, the tail charge of the canonical orbit tends to
  zero, and the fixed pair mass and paid gain remain positive; and
* a joint semantic/law limit retains the pair atom and admits all Continue as
  an exact root Nash action, with the checked unique-all-Continue/support-entry
  alternative.

All five claims survive, with the scope corrections above.

## Source and interface audit

I inspected the following declarations and their immediate definitions.

* `quittingTerminalPayoff_pureSetRoot`,
  `quittingStationaryUnilateralCap_pureSetRoot`, and
  `quittingTerminalSemanticDebt_pureSetRoot_eq` in
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.
* `quittingLiteralPureRootProfile`,
  `quittingPureRootOfCoalition`, and
  `quittingRootCoalitionMass_pureCoalitionAction_eq_one` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`.
* `exists_maximalAbsorption_isZeroQuittingRootNash`,
  `quittingMaximalCapPrefixRoot`,
  `quittingMaximalCapPrefixRoot_exactNash`,
  `quittingMaximalCapPrefixRoot_maximal`,
  `quittingMaximalCapPrefixProfile`,
  `quittingMaximalCapPrefixProfile_debt_succ`,
  `quittingMaximalCapPrefixProfile_stage_succ`,
  `quittingMaximalCapPrefixProfile_debt_mul_stage_eq`,
  `summable_maximalCapPrefix_absorption`,
  `maximalCapPrefix_atomMass_lowerBound`,
  `exists_offMinimum_retainedLaw_allContinue_or_supportEntry`,
  `quittingMaximalCapPrefixPunishmentFloorPrefix`, and
  `maximalCapPrefixPunishmentFloorPrefix_charge_le_semanticBudget` in
  `Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean`.
* `quittingTerminalDeviationDebt_rootThenContinuation_eq_continueMass_mul_of_capNash`
  and
  `quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`.
* `quittingTerminalDeviationDebt_capNashRootStack_eq` and
  `quittingTerminalDebtSum_capNashRootStack_eq` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`.
* `QuittingReprojectionConcentratedPacket` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTemporalSplit.lean`.
* `QuittingStageAtomConcentratedPacketAdapter.ownerMarkedDefect_eq_zero` and
  the constant packet constructors in
  `Research/Quitting/PositiveStageAtomConcentratedPacket.lean`.
* `ConcentratedCollisionFourRole.tailEscape_or_threeRoleTransfer`,
  `.packet_eventually_tailEscape_or_threeRoleTransfer`, and
  `.packet_tailEscapeFrequently_or_threeRoleLimitChord` in
  `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`.
* The actual source producer and limitations in
  `exports/FIN4_WEAK_SINGLETON_TO_MINIMUM_TAIL_FORCED_PAIR.md`, together with
  the maintained obligation
  `questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md`.

The generic maximal-prefix declarations already prove most of the scalar
account.  What is new is the tail-independent pure-pair specialization, the
common-orbit argument for an entire moving minimum-tail family, and the
diagonal adapter into the collision compiler.

## 1. Pure-pair semantics is fully tail-independent

If `|C| >= 2`, then after any unilateral behavioral deviation at least one
member of `C` still Quits at date zero.  Hence absorption occurs at date zero
under prescribed play and under every unilateral deviation.  For every
player `i`, the only effective choice is its date-zero membership toggle:

\[
U_i^C=r_i(C),
\qquad
B_i^C=\max\{r_i(C),r_i(C\triangle\{i\})\}.
\]

This covers privately randomized strategies, Never, and arbitrarily late or
history-dependent quitting.  Thus it proves equality of the *full*
terminal-semantic pairs, not only of prescribed payoffs or stationary caps.

It also proves equality of prescribed terminal outcome laws for all tails:
the law is the point mass at `C`.  This will matter for the later joint-law
limit.

The nearby checked pure-set declarations give exactly these static payoff and
cap formulas for the pure stationary profile.  A small adapter is still
needed to identify a date-zero pure root with arbitrary unreachable tail with
that same semantic pair.

## 2. The canonical root orbit cannot depend on the tail

The definition

```text
quittingMaximalCapPrefixRoot reward profile
```

chooses from

```text
exists_maximalAbsorption_isZeroQuittingRootNash reward
  (quittingTerminalSemanticPair reward profile).2.
```

There is no stopping-law or terminal-law argument in the choice predicate;
only the semantic cap occurs.  Therefore equality of the base semantic pairs
gives equality of the chosen roots.  Inductively, prefixing the same root onto
equal semantic pairs again gives equal semantic pairs, so every later chosen
root is common to all `n`.

This is propositional rather than definitional equality, because the public
selector accepts a profile.  Formalization should first prove an extensional
lemma of the form

```text
quittingMaximalCapPrefixRoot_eq_of_cap_eq
```

and then the semantic-orbit equality.  This is a Lean transport issue, not a
mathematical source-provenance gap.

In particular, the maximal root may not vary across the near-minimum tails in
the source family.  It may vary after the marked best-endpoint update, since
that operation changes the pure-pair semantic pair; copying the old exact
word after that update is not justified.

## 3. Exact common scaling

Let `q_k` be the common selected root, let

\[
c_k=\Pr_{q_k}(\text{all Continue}),\qquad
\alpha_k=\prod_{h<k}c_h,
\]

and let `Z_k` be the semantic pair after `k` outward prefixes.  The checked
one-step playerwise scaling theorem gives

\[
d_i(Z_{k+1})=c_kd_i(Z_k).
\]

Induction yields

\[
d_i(Z_k)=\alpha_kd_i(Z_C),\qquad
D_k=\alpha_kD_0.
\]

Since every `Z_k` is actual and `D_*>0` is globally minimal,

\[
D_k\ge D_*,\qquad
\alpha_k\ge D_*/D_0>0.
\]

Therefore positive-debt support and all normalized debt coordinates are
exactly invariant.  There is no hidden possibility of one coordinate
crossing zero along this orbit.

The same recursive stage-mass identity gives

\[
\Pr(C\text{ at shifted date }k)=\alpha_k,
\]

because the conditional pair-root mass is one.  If the selected player `p`
copies every outer prefix and changes only its endpoint at the shifted pure
pair, all earlier absorption outcomes are unchanged and its conditional
pair-row payoff improvement is still `delta_p`.  Hence its actual unilateral
gain is exactly

\[
g_k=\alpha_k\delta_p=(D_k/D_0)\delta_p.
\]

This is an unrestricted behavioral gain because the displayed copied-prefix
strategy is one legal behavioral deviation; no claim that it is a best
response is needed.

## 4. The equality arm really instantiates the collision compiler

Suppose `D_k -> D_*`.  For the `n`-th original tail, use the actual profile
with the first `n` common maximal roots outside the pure pair.  Define a
moving packet by

```text
profiles n := P_n^n
subseq      := id
mark n      := n
cutoff n    := n + 1
scale n     := 1 / (n + 1 : ℝ)
resolution  := D_* / D_0.
```

All required fields follow from the exact ray identities:

* `resolution > 0` because `D_*>0` and `D_0>=D_*>0`;
* pair stage mass is `alpha_n>=D_*/D_0`;
* the current/tail/root semantic-prefix equation is the literal decomposition
  of `P_n^n` at date `n`;
* the post-row all-Continue spine is literally `sigma_n`;
* the marked root is the unchanged pure pair;
* the marked owner defect is exactly zero, so its normalized expression is
  identically zero for the displayed scale; and
* whole source debt is `D_n -> D_*`.

Thus

```text
ConcentratedCollisionFourRole.packet_eventually_tailEscape_or_threeRoleTransfer
```

applies.  Its tail-escape threshold is fixed and positive, while
`D(Sem(sigma_n))->D_*`, so the tail-escape disjunct is eventually false.
The checked fixed-role/subsequence machinery can then produce its three-role
transfer or limit-chord output.

The preselected `p` and gain `g_k` are useful retained passport data, but `p`
is a **mover**, not yet the compiler's debt recipient.  The compiler derives
a recipient distinct from its selected mover using the near-minimum total-
debt inequality.

This construction is the key reason the result is more than a scalar
diagnostic: one arm fills the exact `(SR)` field named in
`questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md`.

## 5. The strict-limit stall account is exact but architecture-specific

The monotone sequence `D_k` has a limit `L>=D_*`.  If `L>D_*`, every source
on this orbit remains uniformly off minimum.  Since

\[
D_{k+1}=c_kD_k,
\]

the one-step identity is

\[
D_k(1-c_k)=D_k-D_{k+1}.
\]

Writing `a_k=1-c_k`, telescoping and `D_k>=D_*` give

\[
\sum_k D_ka_k=D_0-L,
\qquad
\sum_k a_k\le (D_0-L)/D_*<\infty.
\]

Therefore

\[
a_k\to0,
\qquad
\sup_{H\ge N}\sum_{k=N}^Ha_k\to0.
\]

The checked `quittingMaximalCapPrefixPunishmentFloorPrefix` packages the
roots in the outward Bellman orientation `Z_k -> Z_{k+1}` and its charge is
the displayed sum.  This should not be described as the chronological list
of roots in `P_n^n`, whose outer-to-inner order is reversed.  It is nonetheless
an exact accepted finite-prefix certificate under the project's forward
interface, and the charge calculation is unchanged.

The conclusion is only about restarting the same canonical maximal-root
orbit at a deep `k`.  It does not bound:

* a different exact root selected after changing the suffix cap;
* a marked horizontal endpoint update;
* a newly recomputed maximal ray based at that updated source; or
* exact roots which enter through the limit correspondence's support-entry
  arm.

Those distinctions are stated correctly in Section 6 and should remain
explicit in an export.

## 6. Compact joint-law normal form

For the pure-pair base, the prescribed semantic/law point after `k` prefixes
is independent of `n`.  Its marked date-`k` `C`-mass is exactly `alpha_k`.
Outer roots may themselves absorb at `C`, so the complete terminal law's
`C`-coordinate is only bounded below by `alpha_k`.  Thus every cofinal joint
limit has `C`-coordinate at least

\[
L/D_0>0.
\]

Summability gives `a_k -> 0`.  Since every individual Quit probability is at
most the root absorption probability, each coordinate of `q_k` tends to pure
Continue.  Passing root Nash inequalities to a convergent semantic/cap
subsequence therefore makes all Continue exact Nash at the limit.

The checked theorem

```text
exists_offMinimum_retainedLaw_allContinue_or_supportEntry
```

then gives the honest endpoint split: the limiting correspondence is uniquely
all Continue, or a positive-absorption exact root appears at the limit.
Maximality itself need not pass to the limit.  The direct common-scaling
calculation strengthens the generic theorem's retained atom lower bound from
`D_*/D_0` to `L/D_0` in this pure-pair case.  It does not assert equality of
the complete terminal-law coordinate, because the outer roots may contribute
additional `C`-mass.

The paid pair defect does not contradict all-Continue Nash at the outer cap:
the two statements refer to different roots and different continuation
objects.

## 7. Boundary correction

The regression in the note correctly shows that a paid pure-pair row can
coexist with a pointwise inert maximal ray, but as written both pair members
have positive marked defect.  It therefore does not test the full forced-pair
input, whose selected owner has zero marked defect.

A small modification gives the stronger boundary test.  Let `C={0,1}`.  For
players `0,2,3`, use

\[
r_i(S)=
\begin{cases}
2,&i\notin S,\\
1,&S=\{i\},\\
0,&i\in S,\ |S|\ge2.
\end{cases}
\]

For player `1`, set on every nonempty coalition

\[
r_1(S)=
\begin{cases}
1,&S=\{1\},\\
2,&\{0,1\}\subseteq S,\\
0,&\text{otherwise}.
\end{cases}
\]

At the pure pair,

\[
U=(0,2,2,2),\qquad B=(2,2,2,2),\qquad d=(2,0,0,0).
\]

Thus player `1` is a zero-defect marked owner and player `0` has a fixed
positive leave gain.  All Continue is the unique exact cap root: players
`0,2,3` have Continue strictly dominant against the cap vector, and once
player `0` Continues, player `1` gets `2` from Continue and `1` from Quit.
The table has the pure singleton `{1}` as a terminal Nash profile, so its
global minimum is still zero.  It is not a counterexample, but it tests every
local pair/owner/ray field and shows why positive global-minimum provenance is
essential.

The formal export should either give a complete reward table for this
regression or weaken the old example's advertised purpose to “paid-pair
stall without the zero-owner passport.”

## Maximal correct theorem

The strongest exportable result is the following two-level statement.

> **Tail-independent pure-pair maximal-ray theorem.**  For any finite quitting
> game and any pure coalition `C` of cardinality at least two, all behavioral
> profiles beginning with `C` surely quitting have one common terminal-
> semantic pair, independently of their tails.  Recursively prefixing the
> canonical maximal-absorption exact cap-Nash roots therefore gives one common
> semantic orbit.  At depth `k`, every debt coordinate, total debt, every
> shifted prescribed suffix atom, and every copied-prefix payoff difference
> at the fixed pure row equal their base values times the same positive
> survival factor.
>
> If the global terminal-semantic debt minimum `D_*>0`, the orbit debt has a
> limit `L>=D_*`.  If `L=D_*`, any supplied moving family of literal tails
> with debt tending to `D_*`, zero marked owner defect, and a nonsingleton
> pure marked coalition yields an actual concentrated packet whose whole
> sources tend to the minimum, so the checked collision compiler applies.  If
> `L>D_*`, normalized debt and positive-debt support stay fixed, the future
> charge of the canonical maximal orbit tends to zero, while the pure-coalition
> atom and every fixed positive row gain converge to positive limits.  A joint
> limit retains the coalition atom and satisfies the checked all-Continue/
> support-entry alternative.

For the Fin4 source-facing corollary, instantiate `C={j,o}` and the owner,
mover, tail, and quantitative fields from
`FinFourOwnerCompressedMinimumReturnForcedPairPacket` in the reviewed export.

## Conjecture-facing assessment

This is a strict narrowing of the named whole-source-return seam, but it is
not a complete consumer of the concentrated-singleton atlas node.  It removes
the entire `L=D_*` subarm by constructing the missing source-return packet and
leaves only the canonical, quantitative condition

\[
L>D_*.
\]

That remaining arm is substantially stronger than “the pure-pair target is
off minimum”: it includes invariant normalized debt/support, vanishing future
maximal-prefix capacity, a retained positive pair atom and paid gain, and the
all-Continue/support-entry joint-limit split.  It therefore qualifies as a
proved reduction plus an exact impossibility theorem for the natural maximal-
prefix repair architecture.

It must not be advertised as a terminal approximation, uniform-equilibrium
payoff, total-debt descent, support descent, or exhaustive no-go for all exact
prefix choices after state change.

## Lean handoff

The narrow new layer should contain:

```text
quittingPurePairProfile_semanticPair_eq
quittingPurePairProfile_terminalLaw_eq
quittingMaximalCapPrefixRoot_eq_of_semanticCap_eq
quittingMaximalCapPrefixProfile_semantic_eq_of_purePairTails
quittingMaximalCapPrefixProfile_debtVector_eq_survival_mul
quittingMaximalCapPrefixProfile_pairMass_eq_survival
quittingMaximalCapPrefixProfile_shiftedGain_eq_survival_mul
```

Then define the diagonal packet explicitly and prove:

```text
FinFourOwnerCompressedMinimumReturnForcedPairPacket
  .maximalPrefixLimit_eq_minimum_or_rayStall
```

The equality branch should return the actual
`QuittingReprojectionConcentratedPacket` (or immediately the checked
three-role result), not merely an assertion that the compiler applies.  The
strict branch should return the quantitative equalities and tail-charge
limit, with `canonical`/`maximalPrefix` present in the type or theorem name so
that it cannot later be mistaken for a universal exact-root no-go.

I did not review compilation.  This review concerns the mathematical claim
and its correspondence to the current interfaces.
