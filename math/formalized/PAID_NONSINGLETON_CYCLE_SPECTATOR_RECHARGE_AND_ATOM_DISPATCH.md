# Paid nonsingleton cycles force spectator recharge and a stopping-law atom dispatch

Author: `CODEX_LAGRANGE`

Independent review:
[CYCLE_RECHARGE_REVIEW](../feedback/CODEX_LAGRANGE__PAID_NONSINGLETON_CYCLE_RECHARGE_ATOM_DISPATCH__BY_CYCLE_RECHARGE_REVIEW.md)

## Exact statement

Let `I = Fin 4` and let

```text
r : {C : Finset I // C.Nonempty} -> (I -> R)
```

be a finite quitting reward table.  For an actual behavioral profile `sigma`,
write

```text
U_i(sigma) = its terminal payoff to i,
B_i(sigma) = the supremum payoff of an arbitrary behavioral deviation by i,
d_i(sigma) = B_i(sigma) - U_i(sigma),
D(sigma) = sum_i d_i(sigma).
```

The deviator may use an arbitrary history-dependent randomized behavioral
strategy.  Let

```text
D_* = inf_sigma D(sigma)
```

and assume `D_*>0`.

For every nonsingleton coalition `C`, define

```text
h_i(C) = max (r_i(C triangle {i}) - r_i(C)) 0,
H(C) = sum_i h_i(C).
```

Fix once and for all a deterministic tie-breaking order, choose `p(C)` to
maximize `h_i(C)`, and put

```text
F(C) = C triangle {p(C)}.
```

Suppose a sequence of actual source profiles `beta_n` and marked dates `t_n`
has live mass

```text
L_n >= lambda > 0.
```

Suppose also that the initial marked coalition is one fixed nonsingleton
coalition `C^in`.  At each `n`, pureify only the marked root of `beta_n` to
`C^in`, leaving every complete strategy unchanged away from `t_n`.

Then exactly one of the following finite alternatives occurs for the
table-level orbit of `F` from `C^in`.

1. **Paid singleton.**  Some selected maximum toggle reaches a singleton.
   Its literal one-date whole-profile payoff gain is at least

   ```text
   lambda * D_* / 4.
   ```

2. **Paid nonsingleton cycle.**  After deleting a finite transient, there is
   a fixed simple cycle

   ```text
   C_0 --p_0--> C_1 --p_1--> ... --p_(K-1)--> C_K=C_0
   ```

   of nonsingleton coalitions, where `K` is `4`, `6`, or `8` and
   `C_(k+1)=C_k triangle {p_k}`.  Let `sigma_(n,k)` be the actual profile
   obtained by pureifying only the `t_n` root of `beta_n` to `C_k`.  Then:

   ```text
   sigma_(n,K) = sigma_(n,0),
   sigma_(n,k+1) = Function.update sigma_(n,k) p_k theta_(n,k),
   g_(n,k) := U_(p_k)(sigma_(n,k+1))-U_(p_k)(sigma_(n,k))
             >= g_0 := lambda*D_*/4.
   ```

   Every sibling has the same complete pre-mark behavior, complete post-mark
   behavior, and marked live mass `L_n`.  Its complete terminal law is the
   common pre-mark subprobability law plus `L_n` times the point mass at its
   displayed coalition.

   There are a strict subsequence of the outer indices, one fixed cycle edge
   `k`, and one fixed observer `j != p_k` such that, after reindexing,

   ```text
   d_j(sigma_(n,k+1)) - d_j(sigma_(n,k))
     >= c := lambda*D_*/12                         (1)
   ```

   at every retained index.

   Put

   ```text
   q = 7*c/8 = 7*lambda*D_*/96,
   e_n = (q/8)/(n+1).
   ```

   For the literal source profile `sigma_(n,k)`, mover `p_k`, observer `j`,
   and complete target strategy `theta_(n,k)`, the checked stopping-law atom
   alternative holds at every retained index:

   ```text
   HasQuittingStoppingLawVanishingDebtAtomAlternative
     r sigma_(n,k) p_k j theta_(n,k) q e_n.         (2)
   ```

   In particular, `e_n>0`, `e_n -> 0`, and the charge `q` and all player and
   cycle labels are fixed.

There is a further exact compact split in the cycle arm.  Along one more
strict subsequence, compactify the actual source and endpoint semantic/law
pairs to `(X,mu)` and `(Y,nu)`.  If `T=C_(k+1)`, then

```text
d_j(Y)-d_j(X) >= c,
nu(T) >= lambda,
D(Y) >= D_*.
```

Hence either:

1. `D(Y)>D_*`, so `(Y,nu)` is a strict off-minimum joint-carrier cluster
   actualized by the retained endpoint sequence;
   or
2. `D(Y)=D_*`.  If the original source also carries a supplied
   `FinFourQuantitativeFullSupportHardResidual`, then the unchanged residual,
   the exact joint point `(Y,nu)`, and direct causalization of its particular
   atom `T` construct a fresh `FinFourMinimumAtomProducer` at the same target
   law.  The regenerated producer may take `T` as its causal terminal, and
   its joint-law coordinate satisfies `nu(T)>=lambda`.

The theorem is ordinary mathematics.  The cited downstream atom decoder and
minimum-law causalization are proved in Lean; the cycle-recharge composition
and its Fin4 forced-pair adapter are not yet Lean declarations.

## Conjecture-facing change

The live obstruction in
`notes/SERIAL_ENDPOINT_AUDITOR__PAID_SINGLETON_DYNAMICS_PAIR_BASE_NOGO.md`
was a source-attached paid nonsingleton cycle of period `4`, `6`, or `8` with
no persistent pair-base consumer.  The theorem replaces that undifferentiated
leaf, without adding a new source hypothesis, by the fixed output

```text
positive spectator debt recharge
  -> fixed-charge stopping-law atom alternative
  -> same-law minimum-source regeneration or strict off-minimum endpoint.
```

This strictly narrows the Fin4 cycle obligation.  It does not close the
remaining atlas: neither compact arm currently gives a chronological return
or renewable well-founded descent.

## Definitions and assumptions

The pureification used above is literal.  If `a_C : I -> Bool` is the
membership indicator of `C`, then

```text
sigma_(n,C)(i)(t,history) =
  pure(a_C(i))  if t=t_n,
  beta_n(i)(t,history) otherwise.
```

Thus off-path behavior at every other date is retained, not canonicalized.
The complete target strategy on an edge is

```text
theta_(n,k) = sigma_(n,k+1)(p_k).
```

The terminal law is the law of the actual behavioral profile, including the
Never outcome.  The cap `B_i` is against every unilateral behavioral
replacement by `i`; no stationary, pure-time, bounded-memory, or finite-
horizon restriction is imposed on that cap.

The compact target split uses convergence of the semantic pair and the
complete terminal law along the same actual endpoint subsequence.  It does
not replace the endpoint law with an arbitrary lift of `Y`.

## Source correspondence

The exact unrestricted debt of a pure coalition profile is given by
`quittingTerminalSemanticDebt_pureSetRoot_eq`
(`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`).  For a nonsingleton
pure root, both possible membership endpoints remain absorbing, so its debt
coordinate is exactly `h_i(C)`, independently of the counterfactual tail.

Literal one-date profiles, unilateral update equality, off-date preservation,
gain scaling, live-mass preservation, and exact own-debt subtraction are in
`Research/Quitting/SameStageEndpointMonodromy.lean`, notably:

```text
quittingLiteralPureRootProfile_update_eq_routed
quittingTerminalPayoff_literalOneDateProfile_gain_eq_liveMass_mul_defect
quittingTerminalSemanticDebt_literalOneDateProfile_eq_sub_gain
quittingLiveMass_literalOneDateProfile_eq.
```

The generic canonical endpoint version is
`quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`).

The maintained source is
`FinFourOwnerCompressedMinimumReturnForcedPairPacket`
(`Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`).  At
outer index `n`, take

```text
beta_n = packet.base.crossTailProfile (packet.subsequence n),
t_n = (packet.base.endpoint (packet.subsequence n)).stage,
C^in = packet.movingTerminal.val.
```

The definitions of the forced adapter and
`quittingLiteralPureRootProfile_update_eq_routed` identify its target profile
with the literal pure pair over `beta_n`.  The declarations

```text
forcedTerminal_val
forcedTerminal_card
lambda_lt_forcedPairStageMass
forcedPair_stageMass_eq_liveMass
forcedPair_postDateSpine_eq_reference
```

give the fixed pair, its marked mass floor, and the exact common post-date
spine.  The existing fixed payer is not used by the maximum-toggle cycle;
reselection is explicit.

The checked consumer in (2) is
`hasVanishingDebtAtomAlternative_of_endpointDebtRise`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`).
The law-atom inequality uses
`quittingStageCoalitionMass_le_terminalOutcomeMass`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPureTimeRectangleDisintegration.lean`).
The same-law regeneration uses
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` and
`QuittingMinimumLawCausalSuffixAtom`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`),
then fills `FinFourMinimumAtomProducer`
(`Research/Quitting/FinFourProducerAtlas/Source.lean`) with the unchanged
hard residual.

No literature theorem is invoked.  The finite cycle selection and recharge
identity are new elementary ordinary mathematics connecting these existing
interfaces.

## Proof

### 1. Uniform maximum-toggle floor and the finite orbit

The stationary pure-`C` profile is an actual behavioral profile.  Its
unrestricted debt vector is `h(C)`, so the definition of `D_*` gives

```text
H(C) >= D_*.
```

There are four players; hence

```text
h_(p(C))(C) >= H(C)/4 >= D_*/4.                 (3)
```

Because this number is positive, toggling `p(C)` is the strict best endpoint
at the pure `C` row.  Reaching `t_n` is decided before that root and has
probability `L_n`.  If the routed coalition is nonempty, absorption at the
pure row screens the tail, and the whole-profile gain is exactly

```text
g_n(C) = L_n*h_(p(C))(C) >= lambda*D_*/4.        (4)
```

If `F(C)` is a singleton, this proves the first alternative.  Otherwise
iterate the deterministic map on the eleven nonsingleton coalitions.  A
vertex eventually repeats; delete the transient and take the first repeated
segment.  It is a simple cycle in the Boolean cube.

The cube is bipartite by coalition-cardinality parity.  Among nonsingletons
there are only four odd vertices, the triples, so a simple cycle has length
at most eight.  Its length is even.  Length two is impossible: both edges
would toggle the same player across the same unordered cube edge, requiring
both opposite reward differences to be strictly positive.  Therefore the
length is `4`, `6`, or `8`.  The selector and initial coalition depend only
on the table, so this same finite cycle is used at every outer index.

### 2. Literal profile return and common law

All `sigma_(n,k)` are literal pure-root siblings over the same `beta_n` and
date.  Adjacent coalitions differ only in player `p_k`'s membership, hence

```text
sigma_(n,k+1)
  = Function.update sigma_(n,k) p_k sigma_(n,k+1)(p_k).
```

The equality holds as complete behavioral profiles: at the marked date the
one Boolean action is toggled, and at every other date both strategies equal
the same source strategy.  Since `C_K=C_0`, the final and initial complete
profiles are identical.

The same off-date equality proves common pre- and post-mark behavior.  Every
marked root is a nonempty pure coalition and therefore absorbs surely on
reaching the mark.  If `nu_n^pre` records the terminal mass accumulated
strictly before `t_n` and assigns zero to Never, then

```text
Law(sigma_(n,k)) = nu_n^pre + L_n*delta_(C_k).   (5)
```

Equation (4) gives the displayed gain floor on every cycle edge.

### 3. Spectator recharge

Write

```text
Delta_(n,k,i) = d_i(sigma_(n,k+1))-d_i(sigma_(n,k)).
```

Only `p_k`'s prescribed strategy changes.  Its opponents, and therefore the
set of payoffs obtainable by all of its unilateral deviations, are identical
at the two endpoints.  Its cap is unchanged, while its prescribed payoff
rises by `g_(n,k)`.  Thus

```text
Delta_(n,k,p_k) = -g_(n,k).                     (6)
```

Literal profile return gives, for every player `i`,

```text
sum_(k<K) Delta_(n,k,i) = 0.                    (7)
```

Sum (7) over all players and separate each edge's mover.  Using (6),

```text
sum_(k<K) sum_(j != p_k) Delta_(n,k,j)
  = sum_(k<K) g_(n,k)
  >= K*g_0.                                     (8)
```

There are `3K` spectator-edge pairs.  One has rise at least `g_0/3=c`.
The finite set of edge-observer labels permits a strict subsequence on which
both labels are fixed.  This proves (1).  No sign was assumed for any
individual spectator change; all cross-coordinate cap leakage is already
inside `Delta`.

### 4. Atom dispatch and constants

At the frozen edge, (1) is exactly the endpoint-debt-rise hypothesis of
`hasVanishingDebtAtomAlternative_of_endpointDebtRise`, because the endpoint
is the literal `Function.update` profile.  Also

```text
e_n <= q/8 = 7*c/64 <= c/8,
```

with `c>0` and `e_n>0`.  Applying the checked theorem with input charge `c`
produces output charge `7*c/8=q`, which is (2).  Its standard reciprocal
sequence tends to zero.

### 5. Compact target and same-law regeneration

The joint terminal-semantic law carrier is compact.  Take one common
subsequence on which the source and endpoint joint pairs converge.  Debt is
continuous, so (1) passes to the limit.  By (5), or directly by domination of
stage mass by terminal outcome mass,

```text
lambda <= Law(sigma_(n,k+1))(T).
```

Finite-coordinate convergence gives `nu(T)>=lambda`.

Every endpoint is an actual profile, so global minimality gives `D(Y)>=D_*`.
If the inequality is strict, the first compact arm holds.  If equality holds,
`(Y,nu)` is the actual subsequential joint-law lift, not a reselected lift,
and `nu(T)>0`.  Apply
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` directly
to `(Y,nu)` and `T`.  Package the resulting chronology with the unchanged
hard residual, joint and semantic carrier memberships, global-minimum proof,
positive infimum, and debt equality.  These are exactly the fields of a fresh
`FinFourMinimumAtomProducer` at `(Y,nu)`.

## Boundary tests

### Sharpness of the spectator constant

Take four abstract debt increments, one for each distinct mover.  On the edge
whose mover is `p`, assign increment `-g` to `p` and `g/3` to each spectator.
Starting from a sufficiently large positive debt vector keeps every
intermediate coordinate nonnegative.  Each coordinate moves once and is a
spectator three times, so its total increment is

```text
-g + 3*(g/3) = 0.
```

The cycle closes and no spectator rise exceeds `g/3`; the factor in (1)
cannot be improved from the debt ledger alone.

### Literal return is essential

For an open chain, mover debt may fall by `g` with no compensating spectator
rise: the terminal debt vector may simply have smaller total mass.  Equation
(7), and hence the recharge conclusion, genuinely uses equality of the final
and initial complete profiles.

### Positive minimum is essential

The exact eight-cycle in
`notes/SERIAL_ENDPOINT_AUDITOR__PAID_SINGLETON_DYNAMICS_PAIR_BASE_NOGO.md`
has strict unit toggle gains at the pure reward-table level but admits the
all-Never exact terminal Nash profile.  Thus `D_*=0`; the present formula
gives `c=q=0` and correctly supplies no positive atom charge.  This theorem
does not misclassify that regression as a positive-minimum obstruction.

### Endpoint law versus causal stage mass

The regenerated joint law satisfies `nu(T)>=lambda`.  The causalization
theorem guarantees positive selected-stage mass and, eventually, a retained
finite window with total `T`-mass greater than `nu(T)/2`; it does not assert
that one selected stage has mass at least `lambda`.  No proof step uses that
stronger false reading.

## Adapter and consumer

The arbitrary-source adapter is the checked cofinal forced-pair family in
`MinimumReturnForcedPair.lean`.  Its actual cross-tail profiles, fixed pure
pair, marked dates, and live-mass floor directly instantiate the theorem.
No maximal ray, freshly selected stationary pair-base profile, or replacement
law is used.

The first downstream consumer is the checked stopping-law atom decoder.  It
turns the produced debt rise into a fixed prescribed atom or a fixed
rectangle atom with vanishing observer debt.  The second is the checked
same-point minimum-law causalization, applicable only in the minimum compact
arm.  It reconstructs a complete minimum-atom source at the endpoint's own
joint law.

These consumers are static/source-regenerative.  No checked consumer makes
the horizontal endpoint occur after the source in one play.

## Probability and deviation audit

All source, sibling, endpoint, and response profiles are legal behavioral
profiles in the original quitting game.  Pure marked roots and pure-time
responses use no correlation or external randomization.  Live mass is the
unconditional probability of reaching the marked date; terminal-law mass is
the unconditional terminal probability.  No conditioning is exchanged with
expectation or a supremum.

The payoff cap in every debt coordinate quantifies over unrestricted complete
unilateral behavioral deviations.  Exact own-debt subtraction holds because
changing the mover's prescribed strategy leaves all opponents fixed and thus
leaves that mover's unrestricted cap fixed.  Spectator caps may change
arbitrarily; their signed changes are retained in the averaging identity.

No horizontal edge is interpreted as a chronological transition.  A
nonsingleton pure marked row absorbs immediately, so a play cannot visit two
cycle vertices in succession.

## Lean handoff

A narrow formalization can be organized around the following theorem shapes.

1. Define the deterministic maximum static toggle on nonsingleton Fin4
   coalitions and prove the paid-singleton-or-simple-`4/6/8`-cycle
   classification.  Reuse finite Boolean-cube combinatorics; do not store the
   desired recharge in the orbit structure.
2. Expose the forced pair as a
   `quittingLiteralPureRootProfile` over `crossTailProfile`.  The equality is
   already a short consequence of `targetProfile_eq_literalOneDateProfile`
   and `quittingLiteralPureRootProfile_update_eq_routed`.
3. Prove a generic finite-player literal update-cycle lemma: profile return,
   positive mover gains, and exact own-debt subtraction imply one spectator
   rise of at least `g_0/(card I-1)`.
4. Specialize it to Fin4 and compose it with
   `hasVanishingDebtAtomAlternative_of_endpointDebtRise` using the constants
   above.
5. Separately formalize the endpoint joint-law subsequence and package the
   equality arm as a `FinFourMinimumAtomProducer` using the particular routed
   terminal.

Likely imports are the four source files named in the source correspondence,
plus the existing finite Boolean endpoint-orbit module.  The narrow checks
are the new module's `lake env lean` invocation, its named Lake target, and
the project trust scan.  No conference file is imported and no result is
encoded as an assumed structure field.

## Scope and nonclaims

This result does not prove the Fin4 or general finite-quitting uniform-
equilibrium conjecture.  It does not produce terminal approximate Nash
profiles, a chronological debt-shadowing certificate, a positive admissible
return, or a well-founded recursive descent.

The stopping-law decoder's atom need not be either `C_k` or `C_(k+1)`.  A
fresh chronology regenerated at `(Y,nu)` is not a continuation of the old
endpoint profiles and need not contain the paid horizontal edge.  The strict
off-minimum arm has no return-to-minimum theorem here.  Repeated minimum-arm
regeneration may still circulate horizontally unless an additional
orientation or executable seam theorem is proved.

## Formalization record

The packet's deterministic cycle, actual forced-pair adapter, spectator
recharge, stopping-law atom dispatch, and compact endpoint classification are
proved in Lean in two checked Research modules.

`Research/Quitting/PaidNonsingletonToggleCycle.lean` contains the reusable
table and complete-profile layers.

- `quittingMaximumPositiveTogglePlayer` fixes one deterministic table-level
  maximizer.  `minimumDebt_div_four_le_selectedToggleGain` proves the exact
  `D_* / 4` conditional toggle floor at every nonsingleton coalition.
- `exists_finFourMaximumToggle_terminalOrbit_or_closedSegment` gives the
  singleton-or-simple-closed-segment dispatch.
  `FinFourMaximumToggleClosedSegment.period_eq_four_or_six_or_eight` gives the
  exact Fin4 period classification.
- `FinFourMaximumToggleClosedSegment.profileAt_period_eq_zero`,
  `profileAt_succ_eq_update`, `gainAt_floor`, and
  `moverDebt_succ_eq_sub_gain` retain literal complete-profile return, the
  one-player update, the `lambda * D_* / 4` whole-profile gain floor, and exact
  mover-debt subtraction.
- `FinFourLiteralSiblingCycle.exists_spectator_debtRise` is the generic
  complete-profile debt ledger.  Its Fin4 conclusion has the sharp divisor
  `3`; it assumes no chronological relation between sibling entries.
- `FinFourMaximumToggleClosedSegment.hasVanishingDebtAtomAlternative` is the
  narrow adapter to the checked stopping-law atom decoder.

`Research/Quitting/FinFourProducerAtlas/PaidNonsingletonCycle.lean` contains
the actual source-facing construction.

- `FinFourOwnerCompressedMinimumReturnForcedPairPacket.maximumToggleBaseProfile`
  and `maximumToggleStage` retain the original cross-tail source profiles and
  marked dates.  `movingProfile_eq_initialMaximumToggleSibling` identifies the
  original forced pair with the initial literal sibling, and
  `maximumToggleSibling_postDateSpine_eq_reference` retains its complete
  post-date reference spine.
- `nonempty_forcedPairPaidNonsingletonCycle` fixes one cycle edge and one
  distinct observer only after a strict subsequence of the original source
  indices.  `gain_floor`, `moverDebt_eq_sub_gain`, and
  `observerDebtRise_floor` expose the exact `lambda * D_* / 4` paid edge,
  exact mover subtraction, and `lambda * D_* / 12` spectator recharge.
- `FinFourForcedPairPaidNonsingletonCycle.atomCharge` is exactly
  `7 * lambda * D_* / 96`; `atomError_pos` and
  `atomError_tendsto_zero` give the positive vanishing errors; and
  `atomAlternative` produces the checked fixed-charge stopping-law atom
  alternative at every retained row.
- `nonempty_paidCycleEndpointLaw` jointly compactifies the actual source and
  endpoint semantic/law pairs along one further strict refinement.  The
  resulting endpoint retains the observer rise, routed terminal-law mass at
  least `lambda`, and debt at least `D_*`.
- In the equality arm, `nonempty_paidCycleMinimumRegeneration` and
  `FinFourPaidCycleMinimumRegeneration.next` construct a fresh
  `FinFourMinimumAtomProducer` at that exact endpoint joint point.
  `next_residual_eq`, `next_point_eq`, `next_terminal_eq`,
  `chronology_jointLaw_tendsto`, and
  `chronology_postDateSpine_eq_reference` retain the incoming hard residual,
  endpoint law, routed terminal, literal endpoint family, original source
  ranks, and post-date reference spines.
- `nonempty_paidNonsingletonCycleOutcome` is the exhaustive producer-facing
  capstone: a paid singleton, a strict off-minimum actual endpoint, or the
  same-law minimum-source regeneration.

Evidence seals:

- **M:** PASS.  The maximum-toggle floor, finite Boolean-cycle
  classification, telescoping spectator ledger, constants, compact limit,
  and minimum-equality causalization match the reviewed argument.
- **L:** PASS.  The named generic and Fin4 declarations are checked Lean and
  reachable through the Fin4 Research reader umbrella.
- **A:** PASS.  The Fin4 theorem starts from one actual
  `FinFourOwnerCompressedMinimumReturnForcedPairPacket` and retains its
  source profiles, marked dates, strict source ranks, fixed pair, post-date
  reference spines, actual source/endpoint laws, and unchanged hard residual.
- **C:** PASS only for the stated branch-local consumers.  Every closed-cycle
  row feeds the checked stopping-law atom alternative, and the compact
  equality arm feeds source-faithful minimum-law causalization to construct a
  fresh minimum-atom producer.  The paid-singleton and strict off-minimum arms
  have no further consumer here.

The complete terminal laws are compactified from the literal actual sibling
profiles, and the routed endpoint law retains mass at least `lambda`.  The
packet's auxiliary explicit decomposition as a common premark law plus a
single point mass is not separately named in the Lean surface and is not used
by either consumer.

No horizontal sibling edge is asserted to occur at successive dates in one
play.  The regenerated chronology need not contain that edge or reuse the old
finite cycle.  No strict off-minimum return, chronological debt shadowing,
renewable rank descent, terminal approximation, recursive atlas closure,
positive-gap counterexample, or uniform-equilibrium conclusion is proved.
