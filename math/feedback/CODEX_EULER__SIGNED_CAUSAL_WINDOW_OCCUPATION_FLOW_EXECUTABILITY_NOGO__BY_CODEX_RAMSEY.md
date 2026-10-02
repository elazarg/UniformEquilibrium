# Review of signed-window occupation-flow executability no-go

Reviewer: **CODEX_RAMSEY**  
Source:
[`CODEX_EULER__SIGNED_CAUSAL_WINDOW_OCCUPATION_FLOW_EXECUTABILITY_NOGO`](../notes/CODEX_EULER__SIGNED_CAUSAL_WINDOW_OCCUPATION_FLOW_EXECUTABILITY_NOGO.md)  
Verdict: **REVISE -> PASS after the reach-boundary replacement and same-row
scope repair; internal/no export**  
Date: 2026-08-26

## 1. Claim checked

The proposed architecture theorem combines:

1. the exact stage-mass decomposition
   `L_P p_P-L_Q p_Q = L_P(p_P-p_Q)+(L_P-L_Q)p_Q`;
2. Miner's prepared-prefix signed-atom regression, intended to show a pure
   reach-boundary sign with zero normalized strategic content; and
3. the checked counterfactual externality regression, intended to show that
   common reach and a literal one-stage mover update still do not turn an
   observer atom into an observer action, an exact displayed Nash root, or a
   total-debt/support-cardinality descent.

Items 1 and 3 pass.  Item 2 does not have the decomposition asserted in the
note.

## 2. Decomposition audit: PASS

For every fixed coalition `T` and date `t`,

```text
StageMass(P,t,T)-StageMass(Q,t,T)
 = L_P(t)(p_P(t,T)-p_Q(t,T))
   +(L_P(t)-L_Q(t))p_Q(t,T).
```

This follows exactly from
`quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass` and
`ab-cd=a(b-d)+(a-c)d`.  Finite-window summation needs no limit exchange.  For
the infinite atom, absolute summability follows from

```text
|StageMass(P,t,T)-StageMass(Q,t,T)|
 <= StageMass(P,t,T)+StageMass(Q,t,T),
```

whose sum is at most two.  Sections 2.1--2.2 are mathematically correct as
identities.

The split is anchor-dependent: the equally valid form

```text
L_Q(p_P-p_Q)+(L_P-L_Q)p_P
```

allocates the cross term differently.  Thus “normalized term” versus
“boundary term” must always refer to the exact displayed anchoring, not be
treated as an invariant classification when one reach is zero.

## 3. Earliest fatal gap: Miner's row is not a reach-boundary row

Use the note's positive orientation: `P=Qbar` (Miner's target) and `Q=Pbar`
(Miner's source), at date two and `T={o,c}`.  The exact data are

```text
L_P=1/16,  p_P(T)=1,
L_Q=0,     p_Q(T)=0.
```

Substitution into the note's own formula gives

```text
normalizedRootTerm = (1/16)(1-0)=1/16,
reachBoundaryTerm  = (1/16-0)*0=0.                 (3.R)
```

Therefore the sentence “all of (3.1) is survival history” is false, as is
the claimed realization of obstruction 1 in the introduction.

The marked endpoint difference is nevertheless zero, for a different and
important reason.  At the conditional source root the outcome is `{c}` and
at the target root it is `{o,c}`; both pay `o` exactly one.  The selected
`{o,c}` normalized atom contributes `+1/16`, while the unselected `{c}` atom
contributes `-1/16`.  The **full root-payoff aggregation cancels across
coalition labels**.  This is a valid atom-to-Bellman obstruction, but it is
not the reach-boundary obstruction claimed in Sections 1 and 3.

## 4. No-go A is also overquantified

As printed, No-go A concludes that some reached row has positive normalized
endpoint difference.  Miner's example does have an earlier source-matched
strategic row: after the common prefix, `Pbar` makes `o` Quit alone for zero,
whereas `Qbar` makes `o` Continue toward `c`'s later Quit for payoff one.
Thus the example cannot refute a converter allowed to scan the whole window
and retain that first-disagreement row.

The exact implication refuted by the example is narrower:

```text
positive signed T-stage at t
 + exact reach/root data at that same t
 => positive endpoint payoff difference or Nash defect
    at that same selected row.                     (4.R)
```

Even (4.R) fails by the cross-coalition cancellation above.  Please insert
“at the same positively signed/displayed row” in No-go A and everywhere the
introduction or conclusion currently says that the whole finite window
cannot supply *any* executable row.  The regression does not exclude an
earlier paid first-disagreement consumer.

## 5. Two valid repair routes for Section 3

### Route A: reframe the existing regression

Keep Miner's example, but replace “reach-boundary obstruction” by
“selected-atom normalization does not determine the full endpoint payoff.”
Print the two normalized coalition contributions `+1/16` on `{o,c}` and
`-1/16` on `{c}`.  The combined architecture then has two distinct local
obstructions:

1. cross-coalition payoff cancellation at the same reached row; and
2. counterfactual agency mismatch at common reach.

The occupation identity remains a useful warning but its second term is not
realized by this regression.

### Route B: add an actual reach-boundary regression

If the intended theorem specifically needs a pure boundary example, the
following exact Fin4 construction supplies it.

Use players `o,c,d,e` and rewards

```text
r_o(S)=1 iff c in S;   every other coordinate reward is zero.
```

After any common prefix, let both profiles program `o,c` to Quit together at
one later date and let `e` play Never.  In the target, `d` plays Never.  In
the source, at the preceding date `d` Quits with probability `1/2` and,
conditional on Continue, plays Never.  At the marked `{o,c}` date the two
conditional roots are identical, but their live masses differ by a factor
`1/2`.  With a common-prefix survival `C`,

```text
L_target=C,       p_target(T)=1,
L_source=C/2,     p_source(T)=1,
signed T-stage = C/2.
```

Under the displayed anchoring the normalized term is zero and the boundary
term is exactly `C/2`.  Both reaches are positive.  At the marked root, `o`
gets one whether it Quits with `c` or Continues while `c` Quits, so its
endpoint difference and Nash defect are zero for every tail.  This is the
literal boundary example Section 3 currently describes.  It is ordinary
mathematics and would need its own formalization/review; it is not supplied
by the cited Miner regression.

Even after Route B, the universal conclusion must remain same-row/local.  A
whole-window converter may inspect other dates unless those are separately
controlled.

## 6. Common-reach externality regression: PASS

The checked `CounterfactualAtomExternalityRegression` has exactly the stated
data:

- source root: observer Quits surely, mover Continues;
- target root: both Quit surely;
- joint rewards `(+1,-1)` and singleton rewards zero;
- mover replacement is an exact terminal best response;
- source debts `(1,0)`, target debts `(0,1)`, hence total debt one on both
  sides and debt-support cardinality one on both sides;
- every unrestricted observer deviation at the source has gain at most zero;
- the actual source root has mover defect one and the target root has observer
  defect one, independently of the attached tail; and
- arbitrary replicated all-Continue prefixes are exact zero-charge root
  stacks preserving the source semantic pair and mover-deleted survival.

Thus No-go B passes **provided “displayed edge” means one of these two actual
sure-exit roots**.  It does not exclude a different root chosen from the same
reward table, a first-disagreement row elsewhere, or a global-minimum
reselection.  It proves no total-debt or support-cardinality descent; it does
not refute every possible natural-valued regenerated rank.

The complete-law preservation for the exact prefix is declared in
`Research/Quitting/SignedResetCommonEdgeSourceMismatchNoGo.lean`, not in the
base diagnostics regression.  Add that exact file/declaration to Section 7.

## 7. Formalization/export assessment

The current note should **not** support an export packet until Sections 1, 3,
5, and 6 are repaired.  After either Route A or a separately reviewed Route
B, a narrow formalization packet is viable if it states only:

1. the exact anchored occupation decomposition;
2. failure of selected signed-atom data to imply a payoff/Nash sign at the
   same displayed row; and
3. failure of a common-reach counterfactual observer atom to make either
   actual source/target root Nash or to decrease total debt/support
   cardinality.

Required nonclaims for such a packet:

- no exclusion of earlier paid first-disagreement rows;
- no exclusion of converters selecting a different root or source;
- no exclusion of global positive-minimum/terminal-witness arguments;
- no claim against arbitrary regenerated natural-valued ranks; and
- no Fin4 hard-residual or uniform-payoff conclusion.

With those repairs, the result is a formalizable architecture no-go.  Its
standalone export significance is modest because most regression fields are
already checked; I would recommend formalization as a Research addendum and
export only if the packet explicitly documents the current signed-window
consumer boundary and passes a fresh whole-packet gate.

## 8. Delta review of the repaired note: PASS

The current note implements both repair routes without conflating them:

1. Miner's prepared-prefix row is now used only for **cross-coalition payoff
   cancellation** at the same selected row; and
2. a separate `Fin 4` half-preemption construction supplies the genuine pure
   reach-boundary example.

No mathematical objection remains at the repaired local scope.

### 8.1 The new reach-boundary construction is exact

Use players `o,c,d,e`, with `r_o(S)=1` exactly when `c in S` and every other
payoff coordinate zero.  Equivalently, take `o,c` to use pure time one, `e`
to use `Never`, target `d` to use `Never`, and source `d` to Quit at date zero
with probability `1/2` and use `Never` after survival.  This fully specifies
literal product behavioral profiles; values after the sure date-one
absorption may be set to Continue without changing any calculation.

At date one and `T={o,c}`, both conditional roots are the same deterministic
root and have coalition mass one.  The target always reaches the row, while
the source reaches it exactly when `d` Continues at date zero.  Hence

```text
L_P=1, p_P(T)=1, L_Q=1/2, p_Q(T)=1,
StageMass(P,1,T)-StageMass(Q,1,T)=1/2.
```

Under the displayed anchoring,

```text
L_P(p_P-p_Q)=0,
(L_P-L_Q)p_Q=1/2.
```

Both reaches are positive.  At the marked root, `o` receives one by Quitting
with `c` and also one by Continuing while `c` Quits.  Since `c` surely Quits,
the attached tail is irrelevant.  Thus `o`'s endpoint difference and
coordinate Nash defect are zero for every tail.  In fact the other payoff
coordinates are identically zero, so there is no hidden other-player defect
needed to qualify this calculation.

Prepending any common product word with positive joint survival `C` multiplies
both live masses and the displayed stage difference by `C`; it does not alter
the common conditional root.  The normalized term remains zero and the
boundary term becomes `C/2`, exactly as claimed.

This example does have a perfectly usable exact terminal strategy elsewhere
(and `D_*=0`).  The note no longer uses it to deny all possible Bellman
consumers; it uses it only to refute a strategic sign at the same
reach-boundary row.  That is the correct conclusion.

### 8.2 The Miner row is now attributed correctly

At Miner's selected date-two row, with the repaired orientation,

```text
L_P=1/16, p_P({o,c})=1, L_Q=0, p_Q({o,c})=0.
```

The selected normalized coalition contribution is therefore `+1/16`, while
the anchored reach term is zero.  The full endpoint payoff nevertheless
cancels because `{o,c}` contributes `+1/16` and `{c}` contributes `-1/16`,
with both coalitions paying `o` one.  Section 3.2 now says exactly this and
explicitly preserves the earlier first-disagreement row as a possible
consumer.  The original false reach attribution has been removed.

### 8.3 Same-row quantifiers and source orientation

No-go A is now expressly

```text
positive signed T-stage at a displayed row
  does not force positive endpoint/Nash sign
  at that same positively signed row.
```

It does not quantify over all rows of the window.  No-go B is likewise
restricted to the two displayed charged source/target roots of
`CounterfactualAtomExternalityRegression`.  Its orientation is correct:

- `source` has `observer` Quit and `mover` Continue;
- `target=update source mover replacement` has both Quit;
- `quittingTerminalPayoffDifferenceAtom reward source target observer` is
  positive because the mass change is `0-1` and the observer's joint reward
  is `-1`;
- the mover's replacement is an exact best response from the source;
- every unrestricted observer deviation at the source has gain at most zero;
  and
- the source mover defect and target observer defect are both one for every
  tail, so neither displayed charged root is Nash before floors are examined.

The debt vectors `(1,0)` and `(0,1)`, total debt one, support-cardinality one,
complete-law prefix preservation, and unit mover-deleted survival agree with
the cited checked declarations.  The passive `Fin 4` padding is harmless for
unrestricted deviations when the two new payoff coordinates are identically
zero and the original coordinates ignore the passive labels; the new players
then have zero cap and debt, while original-player deviations face passive
`Never` strategies.

### 8.4 Formalization and export disposition

The result is ready for a narrow **Research formalization addendum**:

- state the anchored stage-mass identity;
- define the four pure-time/`Never` strategies in the reach-boundary table and
  prove its live-mass, root-mass, endpoint, and defect equalities; and
- compose those facts only at the same displayed row with the already checked
  Miner and counterfactual-externality regressions.

For the Lean handoff, define the reach-boundary profiles for every date (pure
time one for `o,c`, `Never` for `e` and target `d`, and a date-zero half hazard
followed by `Never` for source `d`) rather than relying on the prose statement
that null-event later actions are irrelevant.

I do **not** recommend export.  The repaired theorem decisively excludes a
specific same-row/source-local occupation-flow grammar, but it neither answers
a named `questions/` acceptance item nor narrows the maintained positive-
minimum hard residual.  Two of its three regressions are already checked/local,
the new identity is elementary, and every negative example has `D_*=0` and an
available equilibrium elsewhere.  Under `exports/README.md`, this is a useful
local architecture no-go without the actual-data consumer or strict live-
obligation reduction required for the export queue.

Final delta verdict: **PASS, internal/no export; suitable for optional
Research formalization.**
