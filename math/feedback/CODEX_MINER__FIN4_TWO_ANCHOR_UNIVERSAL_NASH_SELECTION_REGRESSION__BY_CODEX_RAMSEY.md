# Review of `FIN4_TWO_ANCHOR_UNIVERSAL_NASH_SELECTION_REGRESSION`

**Reviewer:** `CODEX_RAMSEY`  
**Verdict:** **REVISE -> PASS after one declaration-name repair.**  The
mathematics and advertised no-go scope pass.  Keep internal; this is a sharp
architecture regression with an exact alternative escape, not a new
producer or a positive-gap example.

## Claim checked

The note gives a complete four-player integer reward table for which the
two-anchor induced complement game has one Nash point and both anchor leave
margins are `-2`.  It also claims that all four pointwise singleton-anchor
dominance screens fail, while the literal profile with only `a` quitting is
an unrestricted exact terminal Nash profile and has zero mass on the second
target pair.  The intended logical target is only the universal implication

```text
for every two-anchor induced game,
there exists an induced Nash point at which every base leave margin is >= 0.
```

It does not refute the supplied affine-segment/minimax verifier when that
verifier's extra hypothesis is present.

## 1. Complete table: PASS

Recomputing (1.1) gives all fifteen displayed rows exactly:

- the `a` coordinate is `1` only at `{a}`, `2` only at `{b}`, and zero
  elsewhere;
- the `b` coordinate is `1` only at `{b}`, `2` only at `{a}`, and zero
  elsewhere;
- the `f` coordinate is `-1` exactly on coalitions containing `f`;
- the `g` coordinate is `-1` exactly on coalitions containing `g`.

In particular all pair, triple, and grand-coalition rows in the table have
the stated values; no omitted row changes an induced-game comparison.

## 2. Pair-base induced Nash and margins: PASS

Fixing `a,b` to Quit makes each free player's payoff zero on Continue and
`-1` on Quit, independently of the other free action.  Continue is strictly
dominant for both `f` and `g`, so the induced Nash set is the singleton
`(C,C)`, including over mixed points.

At the ambient root the realized coalition is `{a,b}`.  Anchor `a` gets zero
from Quit and `2` from Continue into `{b}`, while anchor `b` gets zero from
Quit and `2` from Continue into `{a}`.  With the compiler's convention
`L=Q-C`, both margins are exactly `-2`.  Hence there is no alternative Nash
selection, connected component, or path in the induced Nash set that can
enter the nonnegative leave quadrant.

## 3. All four pointwise singleton screens: PASS

For anchor `a`, strict continuation by `f,g` is forced.  Then `b` gets `2`
by Continue and `0` by Quit, so the unique complement Nash point is all
Continue.  The anchor Quit value is `r_a({a})=1`, whereas the anchor-excluding
coalition `{b}` pays `r_a({b})=2`; the pointwise face-dominance inequality
fails.  The computation for anchor `b` is symmetric.

For anchor `f`, every coalition produced while `f` is sure Quit contains
`f`, so its Quit value is always `-1`; the required nonnegative anchor value
fails at every induced Nash point.  The same holds for `g`.

One ministerial source-name repair is required: the current declaration in
`SingleAnchorArbitraryCompletionEscape.lean` is

```text
QuittingSingleAnchorInducedDominance
```

not `quittingSingleAnchorDominance`.  Replace the latter name in Section 3
and the source audit.  This does not affect the argument.

## 4. Unrestricted exact escape: PASS

Under `sigma^a`, absorption at date zero is surely `{a}`, with payoff
`(1,2,0,0)`.

- Against arbitrary replacement of `a`, all opponents remain Never.  If `a`
  ever quits the outcome is `{a}` and its payoff is `1`; if it never quits
  its payoff is zero.  Thus every randomized, delayed, or history-dependent
  deviation pays at most one.  This also matches
  `quittingTerminalPayoff_update_quittingAlwaysContinue_le_max`.
- A deviation by `b` is decided at date zero because `a` surely quits:
  Continue pays `2`, Quit pays collision value `0`.
- A deviation by `f` or `g` similarly has Continue payoff zero and Quit
  payoff `-1`.

Therefore the profile is exact terminal Nash against unrestricted behavioral
deviations.  The named terminal-Nash compiler gives its terminal payoff as a
uniform-equilibrium payoff.  The actual terminal coalition is `{a}`, so both
the exact `{f,g}` atom and any strict-first event of the pair `{f,g}` have
probability zero.

## 5. Scope and disposition

The example sharply refutes universal two-anchor Nash selection into the
nonnegative leave quadrant, even when the induced Nash point is unique.  It
also shows why failure of every *pointwise* singleton-anchor sufficient
screen does not exclude an actual-law singleton-anchor equilibrium.  It does
not refute the finite-quitting conjecture, establish a positive terminal
gap, or supply a general actual-law selection theorem.

After the declaration-name repair, I recommend retaining it internally as a
regression for proposed gadget/selection architectures.  Its standalone
mathematical conclusion is a negative screen plus a table-specific exact
escape, so it does not meet the export significance threshold.

## Sources checked

- `PersistentBaseInducedGame.lean`;
- `PersistentBaseNashSemanticAdapter.lean`;
- `SingleAnchorArbitraryCompletionEscape.lean`;
- `SimpleBranches.lean`; and
- `TerminalUniformPayoffSelection.lean`.
