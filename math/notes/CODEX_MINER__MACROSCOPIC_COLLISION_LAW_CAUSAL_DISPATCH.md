# Macroscopic collision-law atoms have a uniformly macroscopic causal stage

Author: **CODEX_MINER**  
Status: **reviewed PASS after the three proof-writing repairs below; conjecture-facing producer improvement, not a closure theorem** — [independent review](../feedback/CODEX_MINER__MACROSCOPIC_COLLISION_LAW_CAUSAL_DISPATCH__BY_CODEX_EULER.md)  
Date: 2026-08-26

## 1. Question and disposition

Can the checked finite-atom chronology

```text
exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom
```

be combined with

```text
causalCollision_tailEscape_or_quantitativeBestEndpoint
```

without losing the positive law mass to a vanishing individual chronological atom?

Yes.  For a non-singleton terminal coalition, independence of the one-row quitting laws rules out such temporal diffusion.  A terminal-law atom of mass `s>0` forces one actual stage atom of mass at least

\[
\frac{s^3}{8\binom{|I|}{2}}.                         \tag{1.1}
\]

Applied inside the retained finite window and then transported through the deep exact cap prefix, this gives a uniform positive lower bound on the marked stage of the literal prefixed profile.  The causal-collision theorem consequently has a **fixed-scale**, source-matched conclusion: either the shifted tail makes a fixed positive total-debt excursion above the minimum fiber, or one legal reached-row deviation has a fixed positive global payoff gain and the checked debt-transfer/atomic-orientation data.

This does **not** yet consume both branches.  The exact escape account permits the all-Continue cap root to spend zero charge, and the profitable endpoint can transfer its lost mover debt cyclically to other coordinates rather than decrease a finite rank.  No realizable `D_*>0` regression is supplied: producing one would itself give a positive terminal exploitability floor and hence a counterexample to the conjecture.  The result below is therefore a strict producer improvement, not the complete consumer requested in the motivating question.

## 2. Data and probability mode

Let `I` be a nonempty finite player type, let `sigma` be an arbitrary behavioral profile of a finite quitting game, and let `S` be a nonempty terminal coalition with

\[
|S|\ge 2.
\]

At each live date `t`, write

```text
L_t = unconditional probability that the game is still live at t,
q_t = one-row probability that at least one player Quits,
r_t = one-row probability that the quitter coalition is exactly S,
b_t = L_t q_t,
m_t = L_t r_t.
```

Thus `m_t` is `quittingStageCoalitionMass reward sigma t S`, and

\[
s=\sum_{t\ge0}m_t
\]

is the terminal outcome mass of `S`.  All one-row laws are literal independent product laws.  No public correlation, ordering of simultaneous quitters, or conditioning convention at `q_t=0` is used.

Put

\[
N_2=\binom{|I|}{2}.
\]

The assumption `|S|>=2` implies `N_2>0`.

## 3. The macroscopic-stage theorem

### Theorem 3.1 (infinite-horizon form)

If `s>0`, then there is a date `t` such that

\[
m_t\ge \frac{s^3}{8N_2}.                            \tag{3.1}
\]

### Proof

The product-law collision estimate

```text
quittingRootCollisionMass_le_choose_card_mul_absorption_sq
```

and the inclusion of the exact non-singleton coalition in the collision event give

\[
0\le r_t\le N_2q_t^2.                                \tag{3.2}
\]

Call a date **good** when

\[
s q_t\le 2r_t.                                       \tag{3.3}
\]

At every bad date, `m_t < (s/2)b_t`.  The absorption cylinders `b_t` are disjoint and have total mass at most one, so

\[
\sum_{t\text{ bad}}m_t\le\frac{s}{2}\sum_t b_t\le\frac{s}{2}. \tag{3.4}
\]

The first inequality is deliberately non-strict: countably many termwise
strict inequalities need not remain strict after summation.  The non-strict
bound is all the argument uses.

Consequently the good dates carry total `S`-mass at least `s/2`.  In particular some good date has positive `m_t`.  Let `t_0` be the first such date.

All positive good `S`-mass occurs at or after `t_0`, and every such terminal cylinder is contained in the event of being live at `t_0`.  Therefore

\[
L_{t_0}\ge \sum_{t\text{ good}}m_t\ge s/2.          \tag{3.5}
\]

Since `m_{t_0}>0`, both `r_{t_0}` and `q_{t_0}` are positive.  Combining (3.2) and (3.3), and dividing only by the positive `q_{t_0}`, gives

\[
q_{t_0}\ge \frac{s}{2N_2},\qquad
r_{t_0}\ge \frac{s q_{t_0}}2
          \ge \frac{s^2}{4N_2}.                    \tag{3.6}
\]

Now (3.5)--(3.6) yield

\[
m_{t_0}=L_{t_0}r_{t_0}
 \ge \frac{s}{2}\frac{s^2}{4N_2}
 =\frac{s^3}{8N_2}.
\]

This proves (3.1).  Notice that the proof selects one literal stage of the original profile.  It does not Nashify or replace its root.

### Theorem 3.2 (finite-window form)

For a finite cutoff `T`, put

\[
s_T=\sum_{t<T}m_t.
\]

If `s_T>0`, some `t<T` satisfies

\[
m_t\ge \frac{s_T^3}{8N_2}.                          \tag{3.7}
\]

The same proof works verbatim with every sum restricted to `t<T`.  In (3.5), the good cylinders within the finite window remain contained in the live event at the first positive good date.  This finite form is the one that composes directly with the checked causalization theorem.

## 4. Upgrade of the checked deep causal chronology

Let

```text
point : QuittingTerminalSemanticLawPoint I
```

belong to the joint semantic/law carrier.  Let `S` be non-singleton and write

\[
a=\operatorname{point.law}(S)>0.
\]

Assume that `point.semantic` is a global total-debt minimizer and

\[
D_* = D(\operatorname{point.semantic})>0.
\]

The checked declaration

```text
exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom
```

gives profiles `sigma_n`, finite cutoffs `T_n`, and exact cap--Nash root words `W_n` of length `n+1`, with

\[
\sum_{t<T_n}m_{n,t}>a/2                              \tag{4.1}
\]

eventually.  Theorem 3.2 chooses a literal `t_n<T_n` such that

\[
m_{n,t_n}>\frac{a^3}{64N_2}.                         \tag{4.2}
\]

This is a quantitative replacement for the theorem's original conclusion `m_{n,mark(n)}>0`.

Let `P_n` be the joint survival product of the cap word.  The checked cap-stack lower bound gives

\[
P_n\ge \frac{D_*}{D(\sigma_n)}.                      \tag{4.3}
\]

Because `D(sigma_n)->D_*`, eventually `D(sigma_n)<=2D_*`, and hence `P_n>=1/2`.  Exact literal-root transport therefore yields, at the shifted stage `n+1+t_n` of the prefixed profile `widehat sigma_n`,

\[
\operatorname{StageMass}_{\widehat\sigma_n}
       (n+1+t_n,S)
 =P_nm_{n,t_n}
 >\lambda,
\qquad
\lambda:=\frac{a^3}{128N_2}>0.                       \tag{4.4}
\]

All provenance is literal:

- `widehat sigma_n` is the exact root stack followed by `sigma_n`;
- its marked live root is the original live root of `sigma_n` at `t_n`;
- its shifted all-Continue tail after that row is the original shifted tail of `sigma_n` after `t_n`; and
- no separately selected Nash root replaces the causal root.

The front debts `D(widehat sigma_n)` converge to `D_*` by the checked causalization theorem.

## 5. Fixed-scale causal collision dispatch

Apply

```text
causalCollision_tailEscape_or_quantitativeNearMinimumTransfer
```

to `widehat sigma_n`, its stage `n+1+t_n`, the coalition `S`, and the fixed lower bound `lambda`.  Put

\[
\epsilon_n=D(\widehat\sigma_n)-D_*\longrightarrow0.
\]

The checked conclusion is an inclusive disjunction.  After passing to an
infinite subsequence, one may fix an arm which holds throughout that
subsequence (both conclusions are allowed to hold).

### Escape arm

For the literal shifted tail `T_n` of the selected causal row,

\[
D(T_n)-D_*\ge e_0,
\qquad e_0:=\frac{\lambda D_*}{2}>0.                 \tag{5.1}
\]

Every exact cap--Nash root `q` at that same tail has the checked account

\[
D(\operatorname{Prefix}(q,T_n))
 =D(T_n)(1-\rho(q)),
\quad
D(T_n)\rho(q)\le D(T_n)-D_*.                         \tag{5.2}
\]

Thus the chronology really reaches a fixed off-minimum semantic excursion with literal source provenance.

### Reached profitable-endpoint arm

There is a player `i_n` and one legal pure-endpoint behavioral deviation at the selected stage whose global payoff gain `g_n` satisfies

\[
g_n\ge g_0,
\qquad
g_0:=\frac{\lambda^2D_*}{2|I|}>0.                   \tag{5.3}
\]

The target remains in the terminal-semantic carrier, the mover debt falls exactly by `g_n`, and

\[
g_n-\epsilon_n
 \le \sum_{j\ne i_n}\bigl(d_j(\text{target}_n)-d_j(\widehat\sigma_n)\bigr). \tag{5.4}
\]

Consequently, eventually the other coordinates receive a fixed positive aggregate transfer.  Finite-label extraction fixes the mover, endpoint action, and one positive recipient along a subsequence.

Before invoking the second wrapper, fix the required terminal-gap witness.
Indeed, the globally minimizing carrier point with `D_*>0` is an instance of
`HasPositiveMinimumTerminalSemanticDebt reward`.  The checked equivalence

```text
not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt
```

therefore gives nonexistence of a uniform-equilibrium payoff, and

```text
quittingTerminalExploitabilityWitnessOfNoUniformPayoff
```

chooses a literal `QuittingTerminalExploitabilityWitness reward`.  The
recipient-atom conclusion itself is witness-free; this witness is used only
for
`QuittingTerminalExploitabilityWitness.causalCollisionEndpoint_atomicBarrier_or_continueRecipient`.
With that quantified adapter explicit, the wrappers retain either:

- a Quit-directed reached row with its terminal-gap atomic barrier; or
- a Continue-directed same-edge positive debt-recipient atom.

Unlike the unquantified causal mark, neither (5.1) nor (5.3) can vanish merely because the finite cutoff drifts.

## 6. Why this is not yet the requested complete consumer

### 6.1 The escape account does not force return

The declaration

```text
strictTailEscape_allContinue_stalls
```

is the exact obstruction.  If every singleton reward is below the displayed tail cap, the all-Continue root is exact cap--Nash, has absorption charge zero, fixes the tail, and fails every zero-tolerance return selection despite the strict excursion (5.1).  Equations (5.1)--(5.2) provide an upper budget for a root that chooses to absorb; they do not provide a positive lower bound on absorption or force it to spend the excursion.

The deep cap word before the causal row does not repair this orientation.  It prefixes the original near-minimum profile, whereas the escaped tail occurs later inside that profile.  Reusing the independently selected cap roots at the escaped tail would change the literal chronological segment whose atom was selected.

### 6.2 Fixed gain does not imply well-founded debt descent

Equation (5.4) shows the exact problem: at a target which remains near the minimum fiber, the mover's fixed debt loss is compensated by fixed debt gains of other players.  Total debt need not decrease, and positive-debt support need not shrink.  The checked flat-transfer regressions show that such a transfer can move around a finite label set with no scalar debt descent and with no matching prescribed-law incidence.  Those regressions have global minimum zero and therefore are not counterexamples to the positive-minimum conjecture; they are used here only to falsify the algebraic inference from (5.3)--(5.4) to a finite rank.

The four-way coalition routing also does not by itself orient a rank: depending on membership and the best endpoint, the routed coalition may be unchanged, lose the mover, or gain the mover.  The checked atomic-orientation theorem deliberately leaves the positive recipient unmatched with the routed-coalition incidence.

### 6.3 Why no `D_*>0` regression is asserted

A literal reward table with a proved global semantic debt floor `D_*>0` gives a positive terminal exploitability gap against every behavioral profile through

```text
TerminalSemanticGlobalDebtBarrierCertificate.hasTerminalExploitabilityGap_of_certificate
```

and therefore rules out every uniform-equilibrium payoff.  Constructing the requested realizable `D_*>0` refutation would not be a routine interface regression; it would be a genuine counterexample to the conjecture.  None of the inspected regressions establishes such a floor, and this note does not pretend otherwise.

## 7. Novelty and duplicate audit

Files and declarations inspected:

- `TerminalSemanticLawCarrierCausalization.lean`:
  `exists_jointRealizers_finiteWindow_positiveStage_of_lawMass_pos`,
  `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom`, and literal root-stack atom transport;
- `TerminalSemanticLawCarrierCausalNashDispatch.lean`:
  `causalCollision_tailEscape_or_quantitativeBestEndpoint`;
- `TerminalSemanticCausalCollisionMinimumTransfer.lean` and
  `TerminalSemanticCausalCollisionRecipientAtom.lean`:
  the fixed-gain transfer and recipient-atom wrappers;
- `TerminalSemanticCausalCollisionAtomicOrientation.lean`:
  the Quit-barrier/Continue-recipient orientation;
- `TerminalSemanticStrictTailEscapeReturn.lean`:
  the exact escape account, return equivalence, and all-Continue stall;
- `CollisionConcentration.lean`:
  `quittingRootCollisionMass_le_choose_card_mul_absorption_sq` and survival-weighted collision bounds;
- `TerminalSemanticPlateauDefectTelescope.lean` and
  `TerminalSemanticMacroscopicAtomNashProvenance.lean`:
  stopped defect/excess and one-stage global-deviation bounds;
- `TerminalSemanticResetFaceLawTemporalSplit.lean`:
  a nearby concentration theorem which additionally assumes a zero-debt reset face and may change the coalition label;
- `TerminalSemanticFixedTableDiffuseIncidenceRegression.lean` and
  `TerminalSemanticSimultaneousRecipientIncidenceRegression.lean`:
  diffuse-incidence and flat-transfer boundaries; and
- `TerminalSemanticGlobalDebtBarrierCertificate.lean`:
  the significance of a genuine positive global debt floor.

Narrow searches for `conditional coalition`, `macroscopic stage`, `collision concentrated`, `finiteWindow stageCoalition`, and the cubic constant found no declaration proving Theorem 3.1 or 3.2.  The closest checked theorem,

```text
exists_resetFaceLaw_concentratedPacket_of_collision
```

uses a reset-face hypothesis and a deleted-clock bridge; its selected concentrated coalition may differ from the original law atom.  Theorem 3.2 is purely probabilistic, assumes no reset coordinate, retains the original coalition, and gives an explicit constant.

The result does not duplicate the collision localization in
`TIGHT_FACE_COLLISION_DEBT_ESCAPE_FOR_PAID_NEAR_RETURNS`: that packet starts from an already supplied exact Nash--Bellman path and localizes collision within its charged edges.  Here the input is one positive terminal-law coordinate of an arbitrary actual profile, and the output is a macroscopic actual chronological row which need not be Nash.

## 8. Lean handoff

A narrow formalization can be split into two declarations.

1. In an absorption-path or marked-cylinder file, prove the finite-window probability lemma:

```text
exists_stageCoalitionMass_ge_cube_div_of_nonSingleton_windowMass
```

with hypotheses `1 < terminal.val.card` and `0 < windowMass`, and conclusion

```text
∃ time < cutoff,
  windowMass ^ 3 /
      (8 * ((Fintype.card ι).choose 2 : ℝ)) ≤
    quittingStageCoalitionMass reward profile time terminal.
```

Use the good-index predicate

```text
windowMass * rootAbsorptionMass ≤ 2 * rootCoalitionMass
```

so no division by a possibly zero absorption mass occurs.  Positivity of the pair count follows from the non-singleton coalition before any division.

2. In the causalization file, strengthen the deep chronology theorem under `1 < terminal.card` by choosing its mark with the finite-window lemma.  Combine `capNashStack_continueProduct_lowerBound`, convergence of the terminal debt to `D_*`, and

```text
quittingStageCoalitionMass_literalRootStack_add_length
```

to obtain the shifted lower `a^3/(128*N_2)` eventually.  A wrapper around
`causalCollision_tailEscape_or_quantitativeNearMinimumTransfer` then gives (5.1)--(5.4).

Formal proof-writing will need a finite good/bad partition rather than the infinite notation used in Theorem 3.1.  The finite-window theorem avoids `tsum` selection entirely and is sufficient for the checked causal chronology.

## 9. Next exact question

At the fixed-scale escape tail (5.1), add the strongest available Fin4
minimum-fiber/inert data and decide the following genuinely smaller statement:

> Does every exact cap--Nash orbit which never spends a fixed fraction of the
> excursion converge to a literal inert paid/reset port on the **same reached
> suffix**, rather than merely to an all-Continue cap point?

A positive answer would attach the escape arm to the maintained inert-stall
consumer.  A negative answer must preserve the actual reached suffix and a
positive global debt floor; the existing zero-minimum all-Continue regressions
do not settle it.
