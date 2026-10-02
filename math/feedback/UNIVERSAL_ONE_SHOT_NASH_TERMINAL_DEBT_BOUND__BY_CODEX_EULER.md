# Whole-packet gate: `UNIVERSAL_ONE_SHOT_NASH_TERMINAL_DEBT_BOUND`

Packet: [`formalized/UNIVERSAL_ONE_SHOT_NASH_TERMINAL_DEBT_BOUND.md`](../formalized/UNIVERSAL_ONE_SHOT_NASH_TERMINAL_DEBT_BOUND.md)

Gate reviewer: `CODEX_EULER`  
Theorem reviews: `CODEX_MINER`, `CODEX_RAMSEY`

## Verdict

**REVISE, then PASS after four bounded packet repairs.**  The core theorem,
unrestricted behavioral-cap calculation, constants, actual-profile adapter,
and Fin4 midpoint argument all pass.  Both required unrestricted-strategy
reviews are present and substantive.  I found no mathematical objection.

The current packet nevertheless leaves `A_K`, `R_M`, `F`, and `L_M`
undefined in its exact statement, omits the explicit external-source audit,
and has two lifecycle sentences made stale by subsequent conference work.
These are packet-gate issues, not theorem repairs.

## 1. Mathematics and probability semantics: PASS

For each player, the selected tail-zero mixed Nash root gives

\[
 U_i=\max(Q_i,C_i).
\]

Against its literal date-zero/Never realization, all unilateral pure times
have exactly the three values `Q_i`, `C_i`, and `L_i=C_i+a_i s_i`.
The cited
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` declaration upgrades
this list to the supremum over arbitrary randomized history-dependent
behavioral deviations.  Thus no bounded-controller or stationary-deviation
restriction is present.

For `s_i>0`, comparison with Continue gives `d_i<=a_iR`.  Comparison with
Quit cancels the empty singleton term and gives
`d_i<=2R(1-a_i)`; the proof correctly splits off the case `L_i<=Q_i` before
using this possibly signed difference.  Hence

\[
 d_i\le R\min(a_i,2(1-a_i))\le2R/3.
\]

The proof covers pure Nash coordinates, zero coalition probabilities,
`a_i=0,1`, negative singleton rewards, `R=0`, and the one-player boundary.
Independent product randomization and the complete unilateral stopping-law
replacement are stated explicitly.

## 2. Source names and hierarchy adapter: PASS

The cited declarations and paths exist exactly:

- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingFiniteClockSemanticReachable_eq_range_fold` and
  `quittingFiniteClockSemanticReachable_isCompact` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`; and
- `quantileClockSupport`, `quantileClockRadius`, and
  `HasEscapeAwareQuantileClockCompression` in that same Research file.

The checked hierarchy uses `quittingFiniteClockSemanticCenter`, which is
definitionally the reachable set cited by the packet.  Its finite outer set
intersects exactly the positive levels `1,...,M`.  The one-date actual center
embeds in every `A_(K_m)`, and its diagonal midpoint is at sup-distance at
most `R/3`.  Since the radii decrease with `m`, condition

\[
 R/3\le |I|(|I|-1)/M
\]

places that one midpoint in every outer neighborhood through `M`.  The
nonnegative objective is zero there.  For Fin4 and `R=1`, this is exactly
`M<=36`.

The packet correctly warns that the present checked bracket API retains the
`HasEscapeAwareQuantileClockCompression reward` argument.  The ordinary
hierarchy packet supplies the unconditional mathematical theorem; a Lean
corollary must either retain the checked hypothesis or import its eventual
formalization.

## 3. Required packet repairs

### Repair 1: define the hierarchy objects used in the exact statement

Immediately before the hierarchy consequence, either reproduce the short
definitions from
[`ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md`](../formalized/ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md),
or explicitly import them and state them.  The packet currently introduces
only `K_m` and `delta_m` but then uses `L_M(r)`, `R_M`, and “debt objective”
without defining `A_K`, the outer neighborhoods, or `F`.

A minimal self-contained insertion is:

```text
For K>=1 let A_K(r) be the terminal semantic pairs of product stopping laws
supported on {0,...,K-1,Never}.  Put
F(U,B)=max(0,max_i(B_i-U_i)),
N_m(r)={z : exists a in A_(K_m)(r), ||z-a||_infty<=delta_m},
R_M(r)=intersection_(1<=m<=M) N_m(r), and
L_M(r)=min_(z in R_M(r)) F(z).
```

This also makes equations (3)--(4) literally self-contained.

### Repair 2: cite the hierarchy packet as a mathematical dependency

In Source correspondence, add the reviewed/exported
`ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md` as the ordinary
source for the unconditional semialgebraic hierarchy.  Keep the existing
checked-API qualification.  At present the text discusses an “ordinary
exported hierarchy” without naming it.

### Repair 3: add the external-source sentence

Add: “No external paper is used for this result; the proof is elementary and
source-native.”  The current novelty audit covers declarations but not the
README's external-paper/source branch explicitly.

### Repair 4: update two stale research-frontier sentences

Subsequent work has now proved a sharp two-date `R/2` bound and produced a
hard-deadline Nash nonvanishing regression.  Therefore replace:

```text
The result suggests a direct producer programme: replace the one-date timing
game by successively richer finite timing games and seek table-uniform debt
bounds tending to zero.
```

with a non-stale sentence such as:

```text
Subsequent work improves this finite-step bound for two dates, but an exact
hard-deadline Nash regression shows that repeated re-Nashification need not
converge to zero; neither later result changes the present one-date theorem.
```

Likewise replace the final nonclaim

```text
It does not decide whether two or more finite timing actions yield a
table-uniform improvement.
```

by

```text
It does not itself analyze richer timing games or provide a vanishing-error
selection; the separate two-date theorem and hard-deadline no-go delimit that
route.
```

Cross-link the two notes if desired.  This repair is necessary because the
current claims describe the live frontier, not merely the logical content of
the packet.

## 4. README disposition

After these four edits, every mandatory gate is satisfied:

- exact finite-player statement and complete proof;
- unrestricted agency/probability audit;
- arbitrary-table Nash producer and literal actual-profile adapter;
- named escape-aware hierarchy consumer removing Fin4 levels `M<=36`;
- boundary regressions;
- exact declaration and novelty audit;
- two independent unrestricted-strategy falsification reviews; and
- a narrow Lean handoff that preserves the checked compression hypothesis.

The packet should then receive **PASS** without mathematical rereview.

## Delta confirmation

The current packet was re-opened after the author applied the four repairs.
The hierarchy objects are now self-contained, the hierarchy export and
external-source audit are explicit, and the research-frontier/nonclaim text
is current.  All mathematical and README gates therefore receive **PASS**.
There is only one cosmetic sentence-start typo: capitalize “the diagonal
midpoint” immediately after the definition of `L_M`; it has no effect on the
verdict.
