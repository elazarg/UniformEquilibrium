# Alternating pair-base selector: the atom survives, its payoff sign does not

**Author:** CODEX_EULER  
**Status (2026-08-25):** new ordinary-mathematics composition and exact
interface regression; internal pending independent review.  The composition
is semantically subsumed by the checked arbitrary pair-base reset/endpoint
machinery and is not proposed for export.

## 1. Question and answer

Start from the reviewed selector in
[`CODEX_MINER__FIN4_ALTERNATING_PAIRBASE_NASH_MASS_SELECTOR.md`](CODEX_MINER__FIN4_ALTERNATING_PAIRBASE_NASH_MASS_SELECTOR.md).
Write

\[
B=\{d,e\},\qquad F=\{x,k\},
\]

where `x` is the selected collision predecessor of the gap debtor `d`.  At
the selected induced Nash point put

\[
u=q_x(Q),\qquad v=q_k(Q),\qquad m=u(1-v).
\]

The selector gives either `m>0` for a same-point full-gap debtor, or a pure
bad cell entering the checked `PurePaidBaseLeaveSource` chain.

The strongest valid semantic synthesis is:

1. if `m>0`, the actual stationary pair-base law has a date-zero atom
   `B union {x}` of mass exactly `m`, and a fixed-law reset keeps that complete
   atom;
2. the collision inequality at `{x}` does **not** pay this actual atom,
   because the other base label `e` Quits surely;
3. either selector arm can nevertheless enter the already checked
   pair-base paid/reset and endpoint-boundary machinery, using the terminal
   gap debtor and unit base incidence rather than the predecessor atom; and
4. the pure paid-chain refinement adds deterministic membership toggles, but
   only its singleton-to-pair join subcases have a currently named stationary
   consumer.  The remaining toggle shapes supply no floor edge or rank drop.

Thus there is a complete two-arm semantic **bypass**, but no new consumption
of the alternating predecessor sign.  The selector does not close or shrink
the maintained semantic residual beyond the unconditional pair-base theorem.

## 2. Exact source law and the face mismatch

Let `q` be the persistent-base root.  Both `d` and `e` are pure Quit, while
the free coordinates have independent rates `u,v`.  Therefore the actual
stationary outcome law satisfies

\[
 \mu_0(B\cup\{x\})=u(1-v)=m.                       \tag{2.1}
\]

Here the subscript indicates date zero; absorption is certain at that date.
Equivalently, the free-law atom `{x}` becomes the actual terminal coalition
`{d,e,x}`.

The selected singleton collision is

\[
 r_d(\{d,x\})-r_d(\{x\})\ge\Gamma.                 \tag{2.2}
\]

But a unilateral switch of `d` from Quit to Continue on the actual event in
(2.1) compares

\[
 r_d(\{e,x\})-r_d(\{d,e,x\}).                      \tag{2.3}
\]

The four reward coordinates in (2.2)--(2.3) are distinct.  In root-mass
language, the opponent coalition seen by `d` always contains `e`, so

\[
 \Pr_q(\text{opponent coalition}=\{x\})=0          \tag{2.4}
\]

even though the free marginal product mass of `{x}` is `m>0`.

Consequently (2.2) is a correctly signed term on the **missing-`e` face**,
not a paid cylinder of the actual source.  It does not by itself construct a
`QuittingPaidFirstDisagreementRow`, a positive-slope stopping-law atom, or a
Bellman edge.  The source does have a paid first-disagreement row for `d`, but
that follows independently from its terminal-semantic debt and is an average
over the actual opponent law containing `e`.

## 3. Exact same-source regression

The mismatch is not only a typing warning.  It is realizable with bounded
rational data at the complete pair-base source interface.

Take `Fin 4={d,e,x,k}`, `B={d,e}`, and choose the free two-player game to have

\[
 g_x(v)=1-2v,\qquad g_k(u)=2u-1.                    \tag{3.1}
\]

It has the unique induced Nash point `u=v=1/2`, hence

\[
 m=\Pr(F\cap A=\{x\})=1/4.                         \tag{3.2}
\]

Program player `d`'s missing-face collision rows as

\[
 r_d(\{x\})=0,\qquad r_d(\{d,x\})=1.               \tag{3.3}
\]

On the actual pair-base face, program the Continue-minus-Quit differences
for `d` by

\[
L(\varnothing)=L(\{k\})=2,
\qquad L(\{x\})=L(\{x,k\})=0,                     \tag{3.4}
\]

where

\[
 L(A)=r_d(\{e\}\cup A)-r_d(\{d,e\}\cup A).
\]

For example, realize a difference two by the pair `(1,-1)` and a difference
zero by `(0,0)`.  All reward coordinates remain in `[-1,1]`.  The free law is
uniform on its four subsets, so

\[
 \mathbb E[L]=1.                                    \tag{3.5}
\]

Thus `d` is a same-profile gap debtor of size one, (3.3) is a singleton
collision of size one, and the correctly selected predecessor atom has mass
`1/4`; nevertheless its actual eventwise payoff contribution is

\[
 r_d(\{e,x\})-r_d(\{d,e,x\})=L(\{x\})=0.           \tag{3.6}
\]

The `x,k` reward coordinates realizing (3.1), the `d` coordinates above, and
the unused `e` coordinates are independent, so the construction has no
coordinate conflict.  It is a local exact source regression, not a Fin4
counterexample: it does not claim the global terminal witness, positive
minimum, or every full-hard-residual field.

This also shows why a paid first-disagreement decoder cannot select the
collision event merely from `m>0`: the full gain one in (3.5) is paid by the
other two free-law atoms, while the marked atom contributes zero.

## 4. The common checked semantic bypass

Now restore the genuine no-uniform Fin4 hypotheses: a terminal witness and a
positive global-minimum carrier pair `X_*`.  At either Nash point selected by
the two-arm alternative, let

\[
 X=(U,B_X)=\operatorname{Sem}(\sigma),\qquad
 \mu=\operatorname{Law}(\sigma).
\]

The persistent-base semantics give:

- `(X,mu)` lies in the terminal semantic/law carrier;
- both free coordinates have zero unrestricted debt and lie above
  punishment;
- some `d in B` has debt at least `Gamma` and hence a same-profile
  `QuittingPaidFirstDisagreementRow`; and
- for either free owner `o`, `d_X(o)=0`, while the other base label has unit
  opponent incidence in `mu`.

These are precisely the inputs of
`QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch` in
`TerminalSemanticResetIncidenceCapReturn.lean`.  Therefore the selected law
itself admits a returned fixed-law reset point.  By
`QuittingFixedLawResetDispatch.prescribed_eq_target` in
`PairBasePaidResetPayoffAlignment.lean`, the returned prescribed payoff is
exactly `U`.

If some coordinate of `U` is below punishment, the free-coordinate floor
bounds localize that violation to `B`.  Otherwise
`nonempty_quittingPunishmentFloorEndpointEdgeAt` constructs an exact
punishment-floor edge with tail payoff `U`; it has positive absorption unless
singleton domination makes it the literal all-Continue self-loop.  This is
the selected-point version of the checked
`FinFourPairBasePaidResetEndpointBoundary` alternative.

In the positive-mass selector arm, the fixed reset law still contains the
actual atom `B union {x}` of mass `m`.  The reset does not change (2.3) into
(2.2), and the independently selected endpoint root is not coupled to that
law.  Hence the result is parallel same-payoff data, not an event-aligned
paid edge or chronological return.

The construction in this section does not need `m>0` or purity.  It applies
to every pair-base induced Nash point, which is why it is a semantic
**bypass** of the selector rather than a new consequence of its dichotomy.

## 5. Following the pure paid-chain arm

In the pure bad-cell arm the chosen point gives an actual
`PurePaidBaseLeaveSource`.  Under punishment normality the checked declaration

```text
QuittingTerminalExploitabilityWitness.hasPurePaidNormalChainFiniteResidual
```

returns one of the following finite deterministic residues.

1. A failed retained sign is re-equilibrated on four cells.  A
   positive-weight cell has a quantitatively stable `remaining` or `owner`
   coordinate and a strict membership toggle by a different label,
   represented by `HasRepairedRemainingToggleResidual` or
   `HasRepairedOwnerToggleResidual`.
2. A nonempty positive owner-floor cell fails the sure-exit screen, giving a
   strict leave by a retained member, a strict join by the other free label,
   or a strict join by the paid label.

These are actual reward-table toggles, but they contain no terminal semantic
pair, product root, punishment-floor annotation, or stopping-law observer.
Iterating the ambient witness from such a coalition reaches the already
checked static strict-toggle orbit and supplies no new chronology.

There is one useful existing semantic subconsumer in the full hard Fin4
residual, where all players are punishment-normal.  If the returned strict
toggle is an outsider joining a singleton, it is a positive pair premium.
The checked declarations
`pairPremium_pairJoin_or_leaveJoinStationaryTwoDebtorHandoff` in
`TerminalSemanticFinFourSoloWallDispatch.lean` and
`nonempty_finFourPairBaseStationaryTwoDebtorHandoff` in
`PairBaseStationaryTwoDebtorHandoff.lean` then give either the singleton-base
leave--join handoff or the pair-base stationary two-debtor handoff; both are
actual unrestricted-behavior sources with paid rows.  This is the formalized
version of Sections 18--19 of
[`CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY.md`](CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY.md).
It does not cover:

- a member leaving a pair or larger coalition;
- a positive pair-to-triple or triple-to-grand join whose margin is not the
  terminal gap; or
- an arbitrary repaired toggle at a coalition of another cardinality.

For these shapes, the current declarations do not orient the next
terminal-gap toggle, preserve the selected paid observer, establish a floor,
or decrease a maintained rank.  The pure source itself may still use the
common bypass of Section 4, but the refined paid-chain residue has no further
general semantic exit.

## 6. Source and novelty audit

Inspected declarations:

- `quittingPersistentBaseNashSet`,
  `quittingPersistentBaseRoot_free_purePayoff_le`;
- `FinFourPairBaseStationaryDebtLocalization` and
  `nonempty_finFourPairBaseStationaryDebtLocalization`;
- `FinFourPairBasePaidResetTarget`,
  `exists_finFour_pairBasePaidResetDispatch`;
- `QuittingFixedLawResetDispatch`,
  `exists_fixedLawResetDispatch`, and `prescribed_eq_target`;
- `nonempty_quittingPunishmentFloorEndpointEdgeAt` and
  `nonempty_finFour_pairBasePaidResetEndpointBoundary`;
- `PurePaidBaseLeaveSource`,
  `HasPurePaidNormalChainFiniteResidual`,
  `HasRepairedRemainingToggleResidual`,
  `HasRepairedOwnerToggleResidual`, and `HasPurePaidSureExitResidual`; and
- `exists_strictToggleClosedOrbit_from`.
- `pairPremium_pairJoin_or_leaveJoinStationaryTwoDebtorHandoff` and
  `nonempty_finFourPairBaseStationaryTwoDebtorHandoff`.

The common semantic composition is already implicit in the arbitrary
pair-base paid/reset endpoint declarations.  The only new mathematical
content here is the exact face-mismatch identity and regression, plus the
explicit accounting of which pure-chain toggle shapes have a named semantic
consumer.  Neither changes a named frontier chamber, so this note should stay
internal even after review.

## 7. Review request

Please check:

1. the actual atom identity (2.1) and opponent-face zero (2.4);
2. the distinction between collision increment (2.2) and actual source
   increment (2.3);
3. the rational regression (3.1)--(3.6), including the all-behavior debt of
   the sure-base source;
4. the selected-point fixed-law reset and endpoint-boundary adapter;
5. the exact pure-chain residual expansion and singleton-join subconsumer;
   and
6. the subsumption/nonchronology assessment.
