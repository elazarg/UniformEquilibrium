# Fixed ledger payer and an actual premark cap-band witness

Author: `CODEX_BLINDSPOT`

## Status

Active mathematical note, 2026-09-03.  Starting from the fixed-host actual-
Zeno source and the exact positive cap-defect ledger, this note proves an
actual source-ancestral paid witness with explicit Fin4 constants.  The
witness is a complete stopping-law cap-band redistribution, not a single
root action.  It retains the original source row and every live root before
an endogenous finite cut, and that cut is eventually strictly before the
Zeno mark.

The host/payer split is exact:

- if the ledger payer is the host, the update preserves the positive
  host-deleted clock because it changes only the deleted player;
- if the payer is not the host, there is no such preservation.  An exact
  regression shows the profitable update may kill the host-deleted clock
  completely.

This constructs a paid port but not its return.  The target need not remain
in the normalized minimum family, retain the marked terminal, or regenerate
another actual-Zeno source.  No Lean files, exports, frozen notes, questions,
or shared indexes were edited.

## 1. Source data and exact objective

Fix a four-player quitting reward table with

\[
                         |r_k(S)|\le R,\qquad R>0.      \tag{1.1}
\]

Assume the contrary no-uniform-payoff chamber supplies a terminal-semantic
minimum with strictly positive total debt

\[
                         D_*>0.                        \tag{1.2}
\]

Let an actual-Zeno source carry actual profiles `sigma_n`, displayed marks
`m_n`, complete premark words `W_n`, and actual marked-and-postmark suffixes
`tau_n`, so

\[
                   \sigma_n=W_n\star\tau_n,
 \qquad \alpha_n=\Pr(W_n\text{ jointly survives})\to0. \tag{1.3}
\]

Pass to the checked positive-host subsequence.  It fixes a host `h` and
`eta>0` with

\[
 \beta_{n,h}\ge\eta,qquad
 \beta_{n,k}\to0\quad(k\ne h),                         \tag{1.4}
\]

where `beta` is premark survival after deleting the named player.

The objective is to turn the nonvanishing prefix cap-defect ledger into one
literal unilateral update while retaining its ancestry to `sigma_n`.

## 2. Fixed playerwise debt and ledger payer

For player `k`, let

\[
 \Lambda_{n,k}=\sum_{t<m_n}A_{n,t}
   \operatorname{NashDefect}_k(r,B(\sigma_{n,t+1}),x_{n,t}),             \tag{2.1}
\]

where `A_{n,t}` is joint reach through the earlier roots and
`sigma_{n,t+1}` is the complete actual suffix.  Every summand is
nonnegative.  Write `Lambda_n=sum_k Lambda_{n,k}`.

The aggregate and playerwise debt telescopes are

\[
D(\sigma_n)=\Lambda_n+\alpha_nD(\tau_n),\qquad
d_k(\sigma_n)=\Lambda_{n,k}+\alpha_nd_k(\tau_n).      \tag{2.2}
\]

All actual semantic pairs have total debt at least `D_*`.  Therefore at every
rank some player `p_n` satisfies

\[
                         d_{p_n}(\sigma_n)\ge D_*/4.   \tag{2.3}
\]

Finite pigeonhole gives a strict subsequence and one fixed player `p` for
which (2.3) holds at every retained rank.  Each playerwise tail debt is at
most `2R`.  Since `alpha_n->0`, shift once more so that

\[
                         \alpha_nd_p(\tau_n)\le D_*/8. \tag{2.4}
\]

The playerwise telescope then gives, on the same fixed-host subsequence,

\[
 d_p(\sigma_n)\ge D_*/4,\qquad
 \Lambda_{n,p}
   =d_p(\sigma_n)-\alpha_nd_p(\tau_n)\ge D_*/8.       \tag{2.5}
\]

Thus the same fixed player is both a source-debt payer at level `D_*/4` and
an aggregate prefix-ledger payer at level `D_*/8`.  Choosing the player from
the full debt before subtracting the vanishing transported tail is stronger
than first pigeonholing the aggregate ledger.  No single ledger row needs a
uniform defect.

## 3. Actual cap-band construction

Set

\[
                 e=D_*/8,\qquad \kappa=D_*/(16R).       \tag{3.1}
\]

For every retained rank, apply
`exists_quittingCapBandFiniteCut` to the actual profile `sigma_n`, mover `p`,
band width `e`, and reward bound `R`.  This is legal by (2.5).  It supplies:

- a finite cut `c_n`;
- the complete source stopping law of player `p`;
- a pure-time-or-Never receiver whose payoff is within `e/2` of the complete
  behavioral cap;
- a target law obtained by moving every source clock outside the cap band to
  that receiver; and
- the literal target profile

  \[
                 \widehat\sigma_n
                   =\sigma_n[p\leftarrow\widehat s_{n,p}].              \tag{3.2}
  \]

This update is canonical once the finite-cut data are chosen.  It is not a
formal payoff replacement.

### Theorem 3.1: quantitative paid witness

For every retained rank,

\[
 U_p(\widehat\sigma_n)-U_p(\sigma_n)\ge D_*/8,          \tag{3.3}
\]

\[
 d_p(\widehat\sigma_n)\le D_*/8,                       \tag{3.4}
\]

\[
 \Pr_{\sigma_n}(\text{jointly survive through }c_n)
       \ge\kappa,                                      \tag{3.5}
\]

and the source stopping law of `p` has outside-band mass at least `kappa`:

\[
 \Pr(\text{source }p\text{-clock is outside the }e\text{-cap band})
       \ge\kappa.                                      \tag{3.6}
\]

Moreover, every player's actual live root is unchanged at every date
strictly before `c_n`.

### Proof

The cap-band target preserves player `p`'s unrestricted cap and makes its
target debt at most the band width, proving (3.4).  Its exact gain bound is

\[
 U_p(\widehat\sigma_n)-U_p(\sigma_n)
   \ge d_p(\sigma_n)-e
   \ge D_*/4-D_*/8=D_*/8,
\]

which is (3.3).

The checked common-prefix comparison gives

\[
 D_*/8\le d_p(\sigma_n)-e
 \le2R\Pr_{\sigma_n}(\text{jointly survive through }c_n).
\]

Division by `2R>0` proves (3.5).  The complete stopping-law band inequality
gives

\[
 D_*/8\le d_p(\sigma_n)-e
          \le2R\,\operatorname{badMass}_n,
\]

which proves (3.6) after the same division.  Literal prefix equality before
the cut is a field of the same cap-band construction.  `□`

The exact own-debt identity also reads

\[
 d_p(\widehat\sigma_n)
  =d_p(\sigma_n)-
      \bigl(U_p(\widehat\sigma_n)-U_p(\sigma_n)\bigr). \tag{3.7}
\]

Thus this is a paid debt reduction, not only a high-payoff sibling.

## 4. The paid cut is eventually premark

The actual probability of reaching the displayed mark is exactly the joint
survival `alpha_n` of the complete premark word.  Suppose infinitely often
that `m_n<=c_n`.  Survival is nonincreasing in the horizon, so on those ranks

\[
 \Pr_{\sigma_n}(\text{survive through }c_n)
   \le \Pr_{\sigma_n}(\text{reach }m_n)=\alpha_n\to0,
\]

contradicting the uniform floor (3.5).  Therefore, after a finite shift,

\[
                              c_n<m_n.                 \tag{4.1}
\]

The target and source consequently share their complete actual root
chronology up to a positive-reach cut strictly before the Zeno mark.  The
packet index, source rank, fixed pair labels, and comparison sibling attached
to `sigma_n` can be retained as inert provenance tags.  What is not retained
is the original behavior of player `p` from the cut onward.

## 5. Case split: payer equals host

Assume `p=h`.  Only the host's strategy changes in (3.2).  Host-deleted
survival depends exclusively on the three nonhost strategies.  Hence the
complete target and source host-deleted clocks agree exactly through every
horizon, in particular through the marked date:

\[
 \beta_h(\widehat\sigma_n;m_n)=\beta_h(\sigma_n;m_n)
   \ge\eta.                                            \tag{5.1}
\]

Thus this branch gives, on the same actual source rows:

- one fixed host/payer;
- gain at least `D_*/8`;
- target host debt at most `D_*/8`;
- a premark joint-reach floor `kappa`;
- a positive outside-band source mass `kappa`; and
- the original positive host-deleted floor `eta`.

This is stronger than the local equality
`FixedEndpoint.markedHostDefect_eq_zero`: it pays a fixed portion of the
host's complete behavioral debt.

It still does not preserve the original host action at or after the cut.
In particular, positive deleted reach does not say that the target reaches
the marked atom on path; the target host may Quit before the mark.  Forcing
the host back to Continue can undo the paid update.  No current declaration
returns this cap-band target to the normalized minimum fibre or to the fixed
endpoint packet.

## 6. Case split: payer differs from host

Assume `p!=h`.  The paid update preserves every nonpayer strategy, including
the host's own strategy.  But the host-deleted clock includes player `p`, so
it need not be preserved.  Conversely, the payer-deleted clock is preserved
exactly, but (1.4) says that clock tends to zero:

\[
 \beta_p(\widehat\sigma_n;m_n)=\beta_p(\sigma_n;m_n)\to0. \tag{6.1}
\]

Thus the update gives an actual premark paid port but may lose the only live
deleted clock.  Clock preservation cannot be recovered merely by swapping
the two labels.

This is the precise ancestry boundary:

- source ancestry, the original prefix before `c_n`, and the quantitative
  paid gain survive;
- the positive-host postmark interface need not survive.

Any downstream consumer in this case must either accept the paid target
without a host floor, or prove a new two-profile bridge that uses the host
clock from the source and the paid gain from the target without identifying
their post-cut strategies.

## 7. Exact two-purpose regression

Let players be `0,1,2,3`, host `0`, and define every reward coordinate to be
zero except

\[
                  r_1(\{0,1\})=r_1(\{1,2\})=1.         \tag{7.1}
\]

In the first profile, at the original premark row let player `0` Quit surely
and all other players Continue.  Then joint reach is zero, `beta_0=1`, and
all other deleted clocks are zero.  Player `1` has debt exactly one:
following the profile yields coalition `{0}` and payoff zero, while Quitting
immediately produces `{0,1}` and payoff one.

The exact cap-band update for payer `1` can redirect its Never clock to time
zero.  It gains one and changes its debt from one to zero, but its immediate
Quit makes the target host-deleted survival zero.  This proves that the
nonhost-payer paid update need not preserve the positive host clock.

In the separate second profile, the host-cleared endpoint, force player `0`
to Continue and let player `2` Quit surely at the marked row, followed by the
all-Continue tail.  The marked mass is one, the marked host defect is zero,
nonhost behavior is unchanged by selecting the host endpoint, and the
postmark tail is diagonal at zero.  Player `1` still gains one by joining
player `2`, producing `{1,2}`.  Thus the mandatory outsider regression also
survives verbatim: local host control does not pay the outsider ledger.

The same reward table therefore demonstrates both seams in the host/payer
split, but the original positive-host clock and the outsider endpoint ledger
belong to two different profiles.

## 8. Relation to checked packets

The ledger input is checked by
`quittingTerminalSemanticDebtSum_literalRootStack_eq_weightedLedger_add` and
`half_minimum_le_weightedLedger_of_prefixSurvival_le` in
`Research/Quitting/FiniteWordWeightedCapDefectLedger.lean`.  The playerwise
decomposition follows by iterating
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect` from
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`.

The actual paid witness is supplied by declarations in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/CapBandRedistribution.lean`:

- `exists_quittingCapBandFiniteCut`;
- `QuittingCapBandFiniteCut.sourceDebt_sub_epsilon_le_target_payoffGain`;
- `target_terminalSemanticDebt_le`;
- `target_terminalSemanticDebt_eq_source_sub_payoffGain`;
- `source_terminalSemanticDebt_le_epsilon_add_two_mul_badMass`;
- `sourceDebt_sub_epsilon_le_two_mul_jointReach`; and
- `profileLiveRoot_target_eq_of_lt`.

The source-level joint-zero and fixed-host data are in
`ActualZenoDeletedSurvivalSource.lean` and `ActualZenoHostCompression.lean`.
None of those files currently attaches this payer-selected cap-band target
to the positive-host fixed endpoint or to a renewable normalized return.

## 9. Proved facts and remaining gap

### Proved here in ordinary mathematics

- A fixed player has source debt at least `D_*/4` and aggregate prefix ledger
  at least `D_*/8` on a strict fixed-host subsequence.
- The same actual profile supplies a cap-band target with gain `D_*/8`,
  target payer debt at most `D_*/8`, outside-band mass `D_*/(16R)`, and
  joint reach through its cut at least `D_*/(16R)`.
- The cut is eventually strictly before the actual Zeno mark.
- A host-payer update preserves the positive host-deleted clock exactly.
- A nonhost-payer update preserves only its vanishing payer-deleted clock and
  may destroy the positive host clock.
- The exact regression in Section 7.

### Not proved

- The cap-band target remains at the semantic minimum or in the normalized
  return carrier.
- Its marked terminal, marked action, or complete postmark reference spine
  agrees with the current fixed endpoint.
- Either payer case reaches the strategic-singleton/collision-minimum
  consumer or regenerates an actual-Zeno source.
- Iterating these paid updates gives a summable-seam chronology.

## 10. Next concrete question

The `p=h` branch is the sharper target because the live deleted clock survives
the complete paid update:

> Combine the host-payer cap-band target with host forcing only after its
> premark paid cut.  Prove either that a fixed portion of the `D_*/8` gain
> remains while the marked atom is restored, or give an exact inequality
> showing that restoring the host necessarily refunds that gain into a
> source-attached defect accepted by the paid-port consumer.

For `p!=h`, first test a consumer that needs only the positive joint reach to
`c_n` and paid gain, not the later host floor.  The regression proves that a
theorem demanding both from the same target is false without extra structure.

## 11. Sources inspected

- `Research/Quitting/FiniteWordWeightedCapDefectLedger.lean`.
- `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`.
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/CapBandRedistribution.lean`.
- `Research/Quitting/FinFourProducerAtlas/FinFourFullDebtCapBandTargetSplit.lean`.
- `Research/Quitting/FinFourProducerAtlas/ActualZenoDeletedSurvivalSource.lean`.
- `Research/Quitting/FinFourProducerAtlas/ActualZenoHostCompression.lean`.
- `Research/Quitting/CombinedDeletedSurvivalWord.lean`.
- The frozen cap-live ledger and live-tail companion notes.
