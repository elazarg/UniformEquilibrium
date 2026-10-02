# Signed causal windows do not determine executable Bellman flow

Author: **CODEX_EULER**  
Status: **ordinary mathematics; REVISE -> PASS after delta review; internal
only**  
Date: 2026-08-26

Independent review:
[`feedback/CODEX_EULER__SIGNED_CAUSAL_WINDOW_OCCUPATION_FLOW_EXECUTABILITY_NOGO__BY_CODEX_RAMSEY.md`](../feedback/CODEX_EULER__SIGNED_CAUSAL_WINDOW_OCCUPATION_FLOW_EXECUTABILITY_NOGO__BY_CODEX_RAMSEY.md).
The reviewer confirmed the repaired pure reach-boundary example, the
cross-coalition cancellation diagnosis, and the narrowed same-row scope.  No
hard-residual consumer is claimed.

## 1. Exact question and verdict

The reviewed fixed-scale recycling/sprinkler packet now gives a literal
source--target edge and a finite causal window with a fixed positive signed
observer sum.  Can one regard this window as an occupation flow and extract
from it a positive exact punishment-floor edge, cumulative admissible charge,
or a strict debt/support rank loss?

**Not from the signed window and its complete source/target laws alone.**
There are two independent obstructions:

1. the signed occupation can be carried entirely by different probabilities
   of reaching the same strategically neutral row; independently, a positive
   normalized fixed-coalition atom can cancel against another coalition in
   the full endpoint payoff at that same row; and
2. even with common reach and a literal one-stage source/target comparison,
   the sign can be a pure observer externality.  The observer has no
   profitable behavioral deviation, neither displayed row is exact Nash, and
   total debt is merely transferred between two labels.

These failures occur in exact rational product stopping-law games; the
cross-coalition and common-reach regressions are already checked, while the
pure reach-boundary example below is ordinary mathematics.  Hence enlarging
the state by the whole finite
window law, its reach weights, terminal label, and source/target semantic
pairs does not supply Bellman executability.  A valid converter must use an
additional source-matched all-player Nash/floor certificate or genuinely use
the positive-global-minimum provenance after the reset.

This is a no-go for a **source-local finite-window conversion architecture**.
It is not a refutation of the Fin4 hard residual: the regressions below have
global minimum zero.

## 2. Exact occupation decomposition

Fix a nonempty terminal coalition `T` and two actual profiles `P,Q`.  At date
`t`, write

```text
L_P(t) = quittingLiveMass(P,t),
p_P(t,T) = quittingRootCoalitionMass(root_P(t),T),
```

and similarly for `Q`.  Then

```text
StageMass(P,t,T)-StageMass(Q,t,T)
 = L_P(t)(p_P(t,T)-p_Q(t,T))
   +(L_P(t)-L_Q(t))p_Q(t,T).                        (2.1)
```

Multiplying by the fixed observer reward `r_j(T)` and summing over a finite
window gives

```text
signedWindow = normalizedRootTerm + reachBoundaryTerm.  (2.2)
```

The first term is the only part visible after conditioning on reaching each
row.  The second records different earlier survival.  It has no fixed sign
and is not controlled by the terminal semantic pair, total terminal mass, or
the fact that both profiles are literal product laws.

Equation (2.1) is the elementary identity `ab-cd=a(b-d)+(a-c)d`, together
with
`quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass`.  No limiting
interchange is involved for a finite window.  For the full terminal atom,
absolute summability follows from the domination by the two nonnegative
stage-mass series, as in the reviewed signed-stage disintegration theorem.

## 3. Two exact failures at one displayed positive row

### 3.1 A genuine reach-boundary atom

Use Fin4 players `o,c,d,e`.  Give `o` reward one exactly when `c` belongs to
the terminal coalition, and give every other payoff coordinate reward zero.
At date zero, `o,c,e` Continue in both profiles.  In the target, `d` also
Continues and then plays Never.  In the source, `d` Quits at date zero with
probability `1/2` and, conditional on Continue, plays Never.  At date one,
`o,c` Quit surely in both profiles and `d,e` Continue.

For `T={o,c}`, the conditional date-one roots are identical and assign `T`
mass one, whereas

```text
L_target(1)=1,       L_source(1)=1/2.
```

Therefore

```text
StageMass(target,1,T)-StageMass(source,1,T)=1/2.    (3.1)
```

With `P=target,Q=source` in (2.1), the normalized-root term is exactly zero
and the reach-boundary term is exactly `1/2`.  Both reaches are positive.
At the marked row `o` receives one whether it Quits with `c` or Continues
while `c` Quits, so its endpoint difference and coordinate Nash defect are
zero for every attached tail.

After any common prefix with survival `C>0`, every displayed mass and the
boundary sign scale by `C`; the normalized term remains zero.  This proves
that a positive fixed-coalition atom at a displayed row need not give a
strategic sign at that same row when the sign is carried by reach.

### 3.2 Normalized atom sign can cancel across coalitions

Miner's exact Fin4 regression
[`CODEX_MINER__FIN4_PREPARED_PREFIX_SIGN_REPROJECTION_NOGO`](CODEX_MINER__FIN4_PREPARED_PREFIX_SIGN_REPROJECTION_NOGO.md)
gives the complementary failure.  At its positive date-two row and
`T={o,c}`, orient `P` as Miner's target and `Q` as its source.  Then

```text
L_P=1/16, p_P(T)=1, L_Q=0, p_Q(T)=0.
```

Thus (2.1) assigns the positive `1/16` to the normalized fixed-`T` term, not
to the reach term.  Nevertheless the full endpoint payoff difference at the
row is zero: the selected `{o,c}` contribution is `+1/16`, while the
unselected `{c}` contribution is `-1/16`, and both coalitions pay `o` one.
Equivalently,

```text
Quit value of o = r_o({o,c})=1,
Continue value of o = r_o({c})=1.                  (3.2)
```

Hence fixed-coalition normalization still does not imply a payoff or Nash
sign at that same selected row.  This example does contain an earlier
profitable first-disagreement row, so it is not used to exclude a consumer
allowed to select a different date in the window.

## 4. Common reach still does not supply agency or Nash

The checked two-player
`CounterfactualAtomExternalityRegression` is stronger in the complementary
direction.  Its literal source has observer `j` Quit surely at date zero and
mover `w` Continue; its target changes only `w` to Quit at that same date.
Both profiles have reach one at the compared row.  On the joint terminal,

```text
r_w({w,j})=1,  r_j({w,j})=-1,
```

and all singleton rewards are zero.  The exact declarations prove:

```text
signed observer atom(source,target,j,{w,j}) = 1,    (4.1)
w's replacement is an exact terminal best response,
d(source)=(1,0),  d(target)=(0,1),
D(source)=D(target)=1.                              (4.2)
```

Nevertheless every unrestricted behavioral deviation by `j` at the source
has gain at most zero.  The positive observer atom compares two **mover**
laws; it is not an action available to `j`.

Moreover neither displayed sure-exit row can be the root of an exact
Nash--Bellman edge, for any tail:

- at the source, mover `w` gains exactly one by changing Continue to Quit;
- at the target, observer `j` gains exactly one by changing Quit to Continue.

Both comparisons absorb at the current row, so these defects are independent
of the attached tail payoff.  Hence no choice of punishment-floor annotation
repairs exact root Nash.  The source-to-target move also gives neither total
debt descent nor support-cardinality descent: it rotates singleton debt
support from `{w}` to `{j}` while preserving total debt one.

Finally, the regression admits arbitrary-depth literal all-Continue exact
root prefixes with unchanged complete terminal semantic pair and unit
  mover-deleted survival.  Thus adding a finite exact-prefix word, its whole
  law, or its semantic annotations to these displayed roots does not create
  an edge or rank loss.

The Bool example embeds in Fin4 by adding two passive zero-reward Never
players.  This padding is used only for the architecture no-go; no hard-class
or positive-minimum claim is made.

## 5. Formal no-go statement

The two regressions refute each of the following universal implications.

### No-go A: same-row occupation normalization

```text
positive signed T-stage at a displayed row
+ exact product law and reach data at that row
=> positive endpoint payoff difference or Nash defect
   at that same positively signed row.
```

Section 3.1 refutes this by pure reach boundary, and Section 3.2 refutes the
stronger attempt that first conditions the selected coalition atom.  Neither
example excludes an earlier paid first-disagreement row or a converter that
constructs a different source.

### No-go B: externality-to-admissible-edge

```text
positive signed observer stage
+ common reach
+ literal one-stage source/target update
+ exact best response of the mover
+ complete source/target semantic pairs
=> a displayed positive exact punishment-floor Nash--Bellman edge,
   observer gain, or strict total-debt/support-cardinality loss.
```

Section 4 refutes every conclusion simultaneously.  The exact-edge failure
occurs before checking floors: the required product root is not Nash.

Together these are decisive for any converter whose input is only the signed
window packet and whose output is required to use the same positively signed
row or one of the displayed counterfactual source/target roots.  They do not
rule out an earlier paid first-disagreement row, a different selected root,
or a nonlocal theorem that uses the positive global minimum to construct a
different source and proves its full Nash/floor data.

## 6. What an executable conversion must add

An exact punishment-floor edge needs data absent from occupation flow:

1. a tail payoff and product root with the Bellman equality
   `currentPayoff=Succ(tailPayoff,root)`;
2. exact Nash complementarity for **every** player against the prescribed
   tail payoff, not merely positivity of one observer externality;
3. coordinatewise punishment-floor admissibility of the tail state; and
4. if the goal is rank descent, a maintained rank whose full source producer
   is regenerated at the target.

The checked pure-time rectangle consumer supplies a useful but weaker
sequence-level conclusion in its positive-target collision orientation:
`exists_markedTailCluster_escape_or_otherNashDefect_of_positiveTargetRectangleStage`.
It does not manufacture (1)--(4).  The counterfactual regression shows that
dropping any explicit agency/Nash requirement would be unsound.

Therefore the finite-window occupation/flow route does not convert the
reviewed causal-sign window into an executable object.  Its only viable next
use must be genuinely global—e.g. combine the post-reset point with positive
minimum-fiber variational information—rather than normalize or splice the
window locally.

## 7. Checked sources and novelty

- `TerminalSemanticPlateauTimeDisintegration.lean`:
  `tsum_quittingStageCoalitionMass`;
- `TerminalSemanticPositiveSlopeTargetEdgeStateMatchRegression.lean` and
  Miner's Fin4 prepared-prefix extension: fixed signed mass with neutral
  reached row;
- `CounterfactualAtomExternalityRegression.lean`:
  exact best-response replacement, source/target debts, no observer gain,
  exact-prefix persistence;
- `Research/Quitting/SignedResetCommonEdgeSourceMismatchNoGo.lean`:
  `prefixed_terminalOutcomeMass_eq_source` and
  `combined_atom_collision_signedReset_but_sourceMismatch` give the complete
  terminal-law preservation and combined source-mismatch packet;
- `PunishmentFloorAdmissibleChargedRelation.lean`:
  `QuittingPunishmentFloorAdmissibleEdge` and its exact Nash--Bellman field.

Miner's regression and the common-reach externality regression are existing
checked/local inputs; Section 3.1 is ordinary mathematics.  The new
contribution is the anchored occupation decomposition (2.1)--(2.2) and the
combined same-row theorem showing why neither reach enrichment, selected-atom
normalization, nor common-reach state matching converts the displayed sign.
No export is proposed.
