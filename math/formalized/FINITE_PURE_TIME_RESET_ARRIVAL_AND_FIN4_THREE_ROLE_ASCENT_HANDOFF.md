# Finite pure-time reset arrival and the Fin4 three-role ascent handoff

Authors: external proposer; CODEX_ROOT (scope, proof, and source audit)

Independent reviews:

- [`CODEX_DESCARTES`](../feedback/FIN4_THREE_ROLE_ASCENT_FINITE_RESET_COMPILER__BY_CODEX_DESCARTES.md), adversarial falsification and quantitative incidence strengthening;
- [`CODEX_TURING`](../feedback/FIN4_THREE_ROLE_ASCENT_FINITE_RESET_COMPILER__BY_CODEX_TURING.md), source and proof-completeness audit; and
- [`FINITE_RESET_STRENGTHENER`](../feedback/FIN4_THREE_ROLE_ASCENT_FINITE_RESET_COMPILER__BY_FINITE_RESET_STRENGTHENER.md), independent reconstruction and path-length strengthening.

## Exact statements

Let `I` be a finite player set with at least two players, and let `r` be a
finite quitting-game reward table.  Before absorption the only public history
at date `n` is that every
player Continued at all earlier dates.  Players may use arbitrary behavioral
strategies and private randomization.  Perpetual continuation has the game's
declared terminal payoff.

For a behavioral profile `sigma`, write

```text
U_i(sigma) = player i's terminal expected payoff,
B_i(sigma) = sup over all unilateral behavioral replacements by i,
d_i(sigma) = B_i(sigma) - U_i(sigma).
```

Assume there is `gamma > 0` such that, at every actual behavioral profile,
some player has terminal debt at least `gamma`.  This is the checked predicate
`HasQuittingUniformTerminalDebtFloor`.  A positive terminal exploitability
witness supplies this predicate.

### Theorem A: finite reset arrival

From every actual behavioral profile `sigma_0` there is a finite list of
actual profiles

```text
sigma_0, sigma_1, ..., sigma_L = pi
```

such that every successor is obtained from its predecessor by changing one
player's complete strategy to one deterministic pure stopping time, including
Never as a possible time, and there are distinct players `q` and `j` with

```text
d_q(pi) = 0,
Inc_q(j, law(pi)) > 0.
```

Here `Inc_q(j, law(pi))` is the total probability of finite terminal
coalitions containing `j`, with `j != q`.  The chain can be selected so that:

- before a finite stopper is installed, every step gains at least
  `3 gamma / 4` for its mover, and every Never step strictly decreases the
  number of players not yet certified to play Never; and
- after a player is installed at a finite deadline with debt below `gamma`,
  at most two exact pure-time best responses are needed to obtain positive
  incidence; each gains at least `gamma`.

The first phase has at most `card I` Never updates followed by one finite
update, so the complete all-profitable path has length at most `card I + 3`.

There is a second, quantitative selection.  If the exact phase continues
whenever its maximizing time is strictly earlier than the current deadline
and stops only at Never or the same deadline, it uses at most `T+1` exact
updates and ends with

```text
sum_{j != q} Inc_q(j, law(pi)) >= 1.
```

Hence some `j != q` has incidence at least `1/(card I - 1)`, which is `1/3`
for Fin4.  This quantitative selection need not satisfy the uniform
`card I + 3` path-length bound.  The cardinal assumption is automatic under a
positive terminal exploitability witness.

### Theorem B: actual-profile reset dispatch

Suppose additionally that `z_*` is a globally minimum terminal-semantic point,
its total debt `D_*` is positive, and the same game carries a terminal
exploitability witness.  For every actual starting profile `tau`, Theorem A
produces a finite pure-time path to an actual profile `pi`, distinct players
`q,j`, a terminal-semantic point `returned`, and the checked fixed-law reset
object

```text
QuittingFixedLawResetDispatch
  z_* Sem(pi) law(pi) q j returned.
```

The complete target law is the literal law of `pi`; no carrier representative
is substituted.

### Theorem C: Fin4 strict three-role ascent

Let a `FinFourMinimumAtomProducer` and a
`ConcentratedCollisionThreeRoleEndpointLaw` supply actual source profiles
`sigma_n`, actual pure-endpoint target profiles `tau_n`, fixed mover and
recipient, routed terminal data, and semantic limits

```text
Sem(sigma_n) -> x,
Sem(tau_n)   -> y.
```

Here `x` lies on the same minimum-total-debt fibre as the fixed source:
`D(x) = D(z_*)`.  Equality `x = z_*` is neither assumed nor concluded.
Assume `D(z_*) < D(y)`.  Then one can select one literal retained rank `N`
and apply Theorem B starting at the actual profile `tau_N`.  The first
pure-time update can be required to belong to the endpoint's fixed recipient
and to have one fixed positive gain.  The resulting dependent handoff
retains:

- the incoming minimum source and hard residual;
- `sigma_N`, `tau_N`, their literal one-date endpoint relation, and a strict
  finite total-debt ascent between them;
- the fixed mover, recipient, routed terminal, endpoint law, and an actual
  routed-terminal mass strictly greater than half the packet resolution at
  `tau_N`, as historical source provenance;
- an all-profitable pure-time path of length at most seven starting at
  `tau_N`, whose first mover is the fixed recipient; and
- the resulting fixed-law reset dispatch at its final actual profile.

This is the source-attached transition alternative in the maintained Fin4
three-role target-ascent question.

## Definitions and probability audit

For player `i` and `t` in `N union {infinity}`, let `Q_i(t)` Continue before
`t` and Quit surely at `t`; `Q_i(infinity)` is Never.  Against fixed
opponents, every behavioral strategy of `i` induces a probability law on its
first stopping time.  Its terminal payoff is the expectation, under that law,
of the deterministic pure-time payoff.  Consequently

```text
B_i(sigma)
  = sup_t U_i(sigma[i <- Q_i(t)]).
```

This equality covers Never, unbounded finite stopping times, calendar-
dependent hazards, private randomization, and arbitrary behavioral deviations.
It uses the special information structure of a quitting game: before
absorption there is only one live public history at each date.

Changing only `i`'s prescribed strategy leaves `B_i` unchanged, because the
opponents are unchanged.  Thus a pure-time update whose payoff is within
`epsilon` of `B_i` leaves `i` with debt at most `epsilon`; an update attaining
`B_i` leaves it with debt exactly zero.

## Proof of Theorem A

### 1. Approximate pure-time maximization

At the current profile, the uniform debt floor gives a player `i` with
`d_i >= gamma`.  Pure-time extremality gives a time `t` such that

```text
U_i(sigma[i <- Q_i(t)]) >= B_i(sigma) - gamma/4.
```

The update therefore gains at least `3 gamma/4`, and its mover's new debt is
at most `gamma/4 < gamma`.

If `t` is finite, this installs a finite stopper and the proof enters the
deadline phase.  Suppose `t` is Never.  The selected player was not already
prescribed Never, since in that case the update would be the identity and
would gain zero.

Maintain the finite set of players certified to be prescribed Never.  An
update of another player does not change any member's strategy.  As long as
the construction has not installed a finite stopper, every selected Never
update adds a new player to this set.  If a previously Never player is later
selected, another positive-gain Never update is impossible, so its selected
near-best pure time is finite and the phase ends.  Hence at most `card I`
Never updates occur.  If they exhaust the player set, the next debt-floor
witness at the all-Never profile must select a finite time, because its Never
update is the identity.

We have reached an actual profile `sigma`, a player `a`, and a natural number
`T` such that

```text
sigma_a = Q_a(T),
d_a(sigma) < gamma.
```

### 2. Exact cap attainment behind a finite stopper

The debt floor at `sigma` selects a player `i` with `d_i(sigma) >= gamma`.
Necessarily `i != a`.  Player `a` is an unchanged opponent of `i` and Quits
surely at `T`.

Every pure time strictly after `T` has the same payoff as Never: on the live
history at date `T`, player `a` terminates the game, and otherwise the game
has already terminated.  Pure-time extremality therefore reduces the full
behavioral cap of `i` to the maximum of the finite set

```text
Never, 0, 1, ..., T.
```

Choose an exact maximizing time `theta` and set

```text
sigma' = sigma[i <- Q_i(theta)].
```

The opponents of `i` are unchanged, so the maximizing update gives

```text
d_i(sigma') = 0.
```

It gains exactly `d_i(sigma)`, hence at least `gamma`.  The old stopper still
makes `sigma'` absorb by finite time `T` with probability one.

### 3. Incidence or a two-step time-zero reduction

If some `j != i` has positive terminal incidence at `sigma'`, take
`pi=sigma'` and `q=i`.  Otherwise every finite terminal coalition of positive
mass contains no player other than `i`.  Since absorption is certain and
terminal coalitions are nonempty, the complete law is exactly the singleton
law concentrated at `{i}`.  More explicitly, the finite stopper makes the
Never outcome have mass zero; terminal-law coordinates are nonnegative and
sum to one; and zero incidence for every `j != i` makes every nonempty
coalition other than `{i}` have mass zero.

Under this singleton law, replacing the selected maximizing time by Quit at
time zero gives the same certain terminal outcome `{i}` and hence the same
payoff for `i`.  (The selected maximizer cannot be Never, because the terminal
law contains `i` with probability one.)  Therefore Quit at zero is also an
exact best response against the original profile's opponents.  Treat
`sigma'` only as the diagnostic proving this equality, and make the direct
actual update

```text
sigma_0 = sigma[i <- Q_i(0)].
```

Thus the path contains `sigma -> sigma_0`, not the two edges
`sigma -> sigma' -> sigma_0`.  We have

```text
d_i(sigma_0) = 0,
sigma_0_i = Q_i(0).
```

Apply the debt floor once more at `sigma_0`.  It selects a player `k != i`.
Against the sure time-zero stopper `i`, every behavioral response of `k` has
the payoff of one of the two immediate endpoints: Quit at zero or Never.
Choose an exact endpoint and update `k`.  This second exact update gains at
least `gamma` and leaves `d_k=0`.  In either endpoint, every realized terminal
coalition contains `i`; consequently

```text
Inc_k(i, finalLaw) = 1.
```

Thus the exact finite-stopper phase needs at most two updates to obtain
positive incidence, proving Theorem A and the public path bound
`card I + 3`.

For the optional quantitative selection, represent every maximizer by Never
or a time at most the current finite deadline `T`.  If it is `t<T`, recurse
with the new zero-debt stopper `i` and deadline `t`, even if some incidence is
already positive.  If it is Never or exactly `T`, stop.  In either stopping
case every terminal coalition contains an opponent of `i`: a Never responder
never belongs to the coalition, while a time-`T` responder either is
preempted or Quits together with the old distinct stopper.  Hence

```text
sum_{j != i} Inc_i(j, law(final)) >= 1.
```

By finite pigeonhole, some `j != i` has incidence at least
`1/(card I - 1)`.  The deadline decreases strictly in every recursive case,
so this quantitative phase takes at most `T+1` exact updates.

The short selection recurses only in the already checked finite Never-set
acquisition.  The quantitative selection additionally recurses on the strict
natural deadline.  For formalization it is preferable to carry the certified
Never set explicitly rather than require decidable equality of behavioral
strategies.

## Proof of Theorem B

Apply Theorem A to `tau`, obtaining `pi,q,j`.  The pair

```text
(Sem(pi), law(pi))
```

is a literal point of the joint terminal semantic/law carrier.  Its `q`
coordinate has debt zero and its complete law has positive displayed
`q`--`j` incidence.  The global minimum point `z_*`, its positive total debt,
and the terminal exploitability witness are exactly the remaining hypotheses
of

```text
QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch.
```

Applying that checked constructor gives `returned` and the stated fixed-law
reset dispatch.  The finite path and starting profile are retained externally
in the source-attached wrapper.

## Proof of Theorem C

Put

```text
Delta = D(y) - D(z_*) > 0.
```

Semantic convergence to `x`, together with `D(x) = D(z_*)`, lets us choose
one retained `N` such that

```text
D(Sem(sigma_N)) < D(z_*) + Delta/4,
D(z_*) + 3 Delta/4 < D(Sem(tau_N)),
rho/2 < law(tau_N)(routedTerminal).
```

Therefore

```text
Delta/2 < D(Sem(tau_N)) - D(Sem(sigma_N)).
```

This selects an actual off-minimum endpoint row rather than only a limiting
inequality.

Let `rho>0` be the endpoint packet's resolution.  Its recipient-rise theorem
gives

```text
d_recipient(y) - d_recipient(sourceLimit)
  >= rho^2 D_* / 64.
```

Debts are nonnegative, so, after increasing `N` while preserving the strict
ascent, the actual target satisfies

```text
d_recipient(tau_N) > 3 eta/4,
eta = rho^2 D_* / 64 > 0.
```

Choose a recipient pure time within

```text
epsilon_0 = min(eta/4, gamma/4)
```

of the recipient cap.  This literal first update gains at least `eta/2` and
leaves recipient debt below `gamma`.  If it is finite, it is the first stopper
for the two-step exact phase.  If it is Never, it is the first strict Never-set
step, after which the checked bounded acquisition continues.  On `Fin 4`, at
most three further Never updates, one finite update, and two exact updates can
remain.  Hence this produces an all-profitable reset-arrival path of length at
most seven whose first mover is the fixed endpoint recipient.

Apply the fixed-law construction from the proof of Theorem B directly to this
final reset-arrival profile, while storing `sigma_N`, `tau_N`, their literal
endpoint relation, all original endpoint fields, and the complete finite
update path in the dependent handoff.  This proves Theorem C.

The reset-arrival part itself does not require strict total-debt ascent; strict
ascent is what certifies that the selected literal starting endpoint is
genuinely off the incoming minimum.  The general theorem is therefore stated
separately.

## Conjecture-facing change

This supplies item 4 of `FIN4_THREE_ROLE_TARGET_ASCENT_CONSUMER`: one retained
strict three-role endpoint target reaches the already defined fixed-law reset
component through a finite all-profitable actual pure-time path.  The selected
literal ascent row, endpoint relation, routed mass, fixed roles, and the whole
path coexist in one dependent handoff; the reset component is not selected as
an unrelated same-table object.

A fixed-law reset dispatch could already be produced from the positive Fin4
minimum by an independent prescribed-owner construction.  That fact alone did
not answer the endpoint transition question.  The new content is the directed
better-response reachability from the retained endpoint, with the fixed
recipient as its first mover and a uniform length bound.

This does not consume that component.  Its positive-absorption dynamic exit
and its cap-dominating all-Continue arm remain downstream obligations.  The
result may therefore add an edge within the surviving global SCC rather than
eliminate that SCC.  It is not a terminal consumer.

## Boundary tests

1. **Deadline zero.**  With a sure stopper at time zero, a distinct exact
   responder chooses Never or zero.  The old stopper belongs to every terminal
   coalition, so the selected incidence is exactly one.
2. **No-incidence exact response.**  Certain absorption and nonnegative law
   coordinates force the law to be the singleton law at the responder.  Quit
   at zero then realizes the same cap payoff, so the time-zero shortcut is an
   exact best response rather than a merely convenient rewrite.
3. **Incidence pigeonhole.**  In the quantitative deadline selection, the sum
   of opponent incidences at its stopping branch is at least one, although
   coalitions may be counted more than once.  Nonnegativity and the
   `card I - 1` opponent labels give the displayed lower bound; no disjointness
   assumption is used.  The uniformly short selection claims only positivity.
4. **Earlier third-party absorption.**  It cannot invalidate either branch:
   it already supplies an opponent-containing terminal coalition and hence
   positive incidence.
5. **Infinite player sets.**  Finiteness is essential in the Never phase; an
   infinite sequence could add a new Never player forever.
6. **Vanishing rather than fixed gap.**  A merely positive debt at each profile
   gives no common threshold separating the low-debt stopper from the next
   debtor.  The fixed `gamma` is essential to this proof.
7. **Law preservation.**  The pure-time path can change the endpoint terminal
   law and the active roles.  The theorem stores the original endpoint data
   historically and makes no same-law claim.
8. **One player.**  A positive terminal exploitability witness is impossible
   for a one-player quitting game.  The quantitative opponent bound is stated
   only after the resulting `card I >= 2` consequence.

## Source correspondence

The unrestricted pure-time reduction is checked in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`, notably
`exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub` and the exact
supremum bound for pure-time strategies.  The terminal-gap predicate is in
`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.

The finite-stopper acquisition phase is already checked in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticBoundedSelfReset.lean`
as `HasQuittingUniformTerminalDebtFloor`,
`exists_quittingPureTimeSelfResetStep`, and
`exists_bounded_quittingPureTimeSelfResetChain`.  The terminal-witness adapter
`QuittingTerminalExploitabilityWitness.hasUniformTerminalDebtFloor` is in
`UniformEquilibrium/Diagnostics/Quitting/Collision/BoundedSelfResetLocalization.lean`.

The incidence coordinate is
`quittingTerminalOpponentIncidenceMass` from
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDebtTransfer.lean`.
Literal profiles give joint carrier points by the existing terminal semantic/
law carrier API.  The destination constructor is
`QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`.

The actual three-role endpoint data are in
`Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean` and the
associated Fin4 producer-atlas files.  An independent stationary reset
dispatch from a prescribed positive-debt owner already exists as
`QuittingTerminalExploitabilityWitness.exists_finFour_prescribedOwner_resetDispatch`
in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourPrescribedOwnerResetAlignment.lean`.
It has no path from the three-role endpoint.

The new content is exact cap attainment behind an arbitrary finite stopper,
the two-step exact zero-debt/positive-incidence finish, the alternative
quantitative deadline finish, the all-profitable reset-arrival wrapper with a
`card I + 3` bound, and its fixed-recipient, source-attached three-role
adapter.  No original-paper theorem is invoked.

## Adapter and consumer

Theorem A is produced from arbitrary actual finite-quitting data plus the
uniform coordinate-debt floor; no stationary, finite-support, or attained-
minimum assumption is used.  A terminal exploitability witness is one checked
source of that floor.
Theorem B is the actual-data adapter to the checked fixed-law reset component.
Theorem C selects its starting profile directly from the retained endpoint
sequence and preserves the incoming object in one dependent wrapper.

The downstream consumer is the existing dynamic alternative stored by
`QuittingFixedLawResetDispatch`.  This packet does not claim to close either
of its branches.  Its accepted role is to close the previously missing
source-attached transition into that component.

## Original Lean handoff

The requested declarations were:

```text
bestReplyValue_eq_finsetMax_pureTime_of_opponent_quitsAt
exists_exactZeroDebt_positiveIncidence_of_finiteStopper
exists_exactZeroDebt_quantitativeIncidence_of_finiteStopper
nonempty_pureTimeResetArrival_of_uniformDebtFloor
nonempty_actualProfileFixedLawResetHandoff
nonempty_finFourThreeRoleStrictAscentResetHandoff
```

The first theorem should combine checked behavioral pure-time extremality with
the exact equality of every pure time after the opponent's deadline to Never.
The short finite-stopper theorem should use the singleton-law/time-zero
shortcut; its fallback branch returns unit incidence, while its immediate
branch returns the already positive incidence.  The quantitative theorem
should instead continue strict deadline descent until total opponent
incidence is at least one.  The reset-arrival theorem should reuse the checked
bounded self-reset chain for acquisition rather than reprove it.  Its public result
should retain the all-profitable path and the bound `card I + 3`.  The
three-role theorem then needs only common convergence selection (including
the actual routed-mass floor), the checked recipient-rise floor, and the
existing fixed-law reset constructor.

For the sharp Fin4 length-seven specialization, the implementation exposes
the certified-remaining-set version of the acquisition induction.  After a
forced recipient Never step, only the other three players can contribute new
Never labels before the finite update.  The public fixed-first-player theorem
then retains the complete bound `card I + 3`, which is seven on `Fin 4`.

No new compactness theorem, selected cap port, law minimizer, or real-valued
descent is required.

## Scope and nonclaims

- No theorem here proves terminal approximate Nash profiles or a uniform-
  equilibrium payoff.
- The fixed-law reset dispatch's all-Continue arm remains open.
- The pure-time path is a literal source-to-reset transition and provenance
  certificate consisting entirely of profitable unilateral updates.  It is
  not an equilibrium, near-return, or uniform-payoff backward compiler across
  those updates.
- The final reset law need not equal the incoming endpoint law.
- The mover, recipient, and routed atom need not remain active at the final
  reset profile.
- The endpoint source limit need not equal the fixed minimum semantic point;
  only their total debts are identified.  The final reset dispatch is based
  at the fixed minimum point, not at the endpoint source limit.

## Formalization record

The export packet at intake had SHA-256
`e590ce117ef64928b3761a8c81d305b8613004fab70f52de97a68e682781ca07`.
The checked implementation is present at repository revision
`5a10df1ace7e4e68b2b92a28c49c6686adcd0740`.

1. `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinitePureTimeResetArrival.lean`
   proves the pure-time cap reduction and the finite reset arrival.  The
   public capstones are
   `exists_pureTime_bestReply_of_opponent_quitsAt`,
   `nonempty_finiteStopperExactFinish`,
   `nonempty_pureTimeResetArrival_of_uniformDebtFloor`, and
   `QuittingPureTimeSelfResetStep.literalNever_certificate_strictGrowth`.
   The exact finite-stopper finish stores one or two cap-attaining updates,
   zero final owner debt, positive distinct-opponent incidence, and the
   unweakened per-edge gain floor.  The complete arbitrary-start path has
   length at most `Fintype.card ι + 3` and per-edge gain at least
   `3 * gap / 4`.
2. The same module separately defines
   `QuittingFiniteDeadlineIncidenceSelection` and proves
   `nonempty_finiteDeadlineIncidenceSelection`.  It stores an exact-cap path
   of length at most `deadline + 1`, zero final owner debt, and total opponent
   incidence at least one.  Under the explicit hypothesis
   `2 ≤ Fintype.card ι`,
   `exists_finiteDeadlineIncidenceSelection_with_selectedOpponent` selects a
   distinct opponent with incidence at least
   `1 / ((Fintype.card ι : ℝ) - 1)`.  A terminal exploitability witness has
   the stronger checked cardinal consequence
   `QuittingTerminalExploitabilityWitness.three_lt_card`.
3. `QuittingActualProfileFixedLawResetHandoff` and
   `nonempty_actualProfileFixedLawResetHandoff` attach the complete profitable
   path and literal final semantic/law pair to the existing
   `QuittingFixedLawResetDispatch`.  The adapter uses
   `QuittingTerminalExploitabilityWitness.hasUniformTerminalDebtFloor`; it
   does not assume a supplied reset-arrival certificate.
4. `Research/Quitting/FinFourProducerAtlas/ThreeRoleAscentResetHandoff.lean`
   defines `FinFourThreeRoleAscentResetHandoff` and proves
   `FinFourThreeRoleAscentResetHandoff.nonempty_of_strict_ascent`.  It selects
   one common retained endpoint rank, keeps the literal source and endpoint
   profiles, fixed transfer roles, routed terminal mass above half the packet
   resolution, and strict actual total-debt ascent.  The theorem
   `recipient_first_path` exposes a path structurally headed by the fixed
   recipient's displayed update, and `length_le_seven` gives the Fin4 bound.
   `dispatch_from_fixedMinimum` makes the fixed source of the final reset
   dispatch literal.

Evidence seals:

- **M:** PASS.  The deadline induction, singleton-law shortcut, Never-set
  growth argument, fixed-recipient first step, and compact-rank selection
  match the reviewed proof with their stated bounds.
- **L:** PASS.  Both implementation modules check in Lean; the generic module
  is reachable from the Diagnostics umbrella and exhaustive axiom audit, and
  the Fin4 adapter is reachable from the Research atlas umbrella.  The public
  capstones use only `propext`, `Classical.choice`, and `Quot.sound`.
- **A:** PASS for the stated source-attached transition.  The terminal witness
  constructs the uniform debt floor, while the Fin4 theorem selects its rank,
  literal profiles, first update, path, final law, and dispatch from the
  existing minimum source and endpoint-law object.
- **C:** PASS for item 4 of the three-role target-ascent question: the strict
  endpoint branch now enters an actual fixed-law reset dispatch by one
  source-attached profitable path.  This is branch-local `C`, not terminal
  `C`; neither dynamic branch stored by the reset dispatch is consumed.

The source-limit correction above is essential.  Lean proves convergence of
the recurrent source profiles to `endpoint.sourceLimit` and only the equality
of its total debt with the fixed minimum.  It separately proves that the
dispatch uses `source.point.1`.  No theorem identifies those semantic points.
