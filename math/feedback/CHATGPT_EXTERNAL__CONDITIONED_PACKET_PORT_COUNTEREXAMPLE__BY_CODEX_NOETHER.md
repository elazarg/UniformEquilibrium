# Review of the conditioned-packet residual-port proposal by `CODEX_NOETHER`

Reviewed note:
[`CHATGPT_EXTERNAL__CONDITIONED_PACKET_PORT_COUNTEREXAMPLE.md`](../notes/CHATGPT_EXTERNAL__CONDITIONED_PACKET_PORT_COUNTEREXAMPLE.md).

## Verdict

The rational Bayes calculation, semantic-pair equality, fixed-label switch,
and deleted-clock separation are valid ordinary mathematics for the **two
displayed residual ports**.  The positive-denominator `Omega_L` estimate is
also a valid sufficient stability lemma when the two sides use the same
component laws and differ only in their entrance weights.

The advertised negative answer to
`questions/CONDITIONED_PACKET_REPROJECTION.md` is not established.  There are
two exact interface failures.

1. The example realizes only the prescribed arm of
   `HasQuittingStoppingLawVanishingDebtAtomAlternative`.  It does not realize
   `QuittingVanishingDebtAtomAccess`: it supplies no positive-minimum tangent
   frontier, positive-debt-support mover, eventual rank family, or canonical
   frontier replacement.
2. More decisively, the example does not show that **every** reprojection with
   the stated reached semantic source loses the clock or the atom.  In this
   reward table one may splice an actual behavioral continuation whose packet
   root uses the frozen Continue probability `lambda`.  Its reached semantic
   pair is still `x_delta`, its deleted-`m` clock is exactly the frozen one,
   and terminal `{a,m}` still carries the frozen prescribed atom.  Behavioral
   strategies have no compulsory latent `A/B` branch state.  Retaining the
   posterior `hatLambda` is necessary only if one additionally insists on
   retaining that particular complete stopping-law mixture port.

Thus the example is a valid nonidentifiability diagnostic—semantic pairs do
not determine residual ports—but not a counterexample to the existential
conditioned-reprojection producer or its chronological consumer.  The
proposed “maximal repair” is a useful sufficient comparison bound, not a
proved replacement theorem.

I did not run Lean and claim no `L`, `A`, or `C` seal.

## 1. Exact Bayes and terminal calculations

With entrance weight `lambda=1/N` on branch `B`, survival of the preceding
date has mass

```text
(1-lambda)lambda^2+lambda.
```

Consequently the conditional `B` weight at the packet date is

```text
hatLambda
 = lambda/((1-lambda)lambda^2+lambda)
 = N^2/(N^2+N-1),
```

and `hatLambda-lambda>1/2` for `N>=17`.  This is exactly the conditional
hazard realization encoded by
`quittingStoppingLawMixtureBehaviorStrategy`
(`UniformEquilibrium/Quitting/Paths/StoppingLawMixture.lean`).

At the packet row, put `w=lambda` or `w=hatLambda`.  The terminal masses are

```text
P({a})   =1-delta,
P({a,m}) =(1-w)delta,
P({m})   =w delta.
```

Player `o` receives `-1` exactly when `m` Quits.  Continuing or Never gives
`-delta`, while every own Quit gives `-1`.  Therefore

```text
U_o=B_o=-delta,
```

and the `a,m` coordinates are zero.  Both ports have the exact semantic pair

```text
x_delta=((0,0,-delta),(0,0,-delta)).
```

They do **not** have the same terminal outcome law at the reset row: mass
`delta(hatLambda-lambda)` moves from `{a,m}` to `{m}`.  The resulting `l1`
distance is `2delta(hatLambda-lambda)<=2delta`.  The note's top-level phrase
“exactly matching ... terminal-semantic laws” must therefore be read as
semantic-pair equality, not semantic-law equality.

Annotating either literal profile by all its own shifted semantic pairs makes
the one-step prescribed and direct-debt defects zero by the exact prefix
identity.  This fact concerns exact data from that profile; it does not turn
one port into the other.

## 2. What the atom fields actually say

Let mover `m` Continue forever in the source and Quit surely at the packet
date in the target; let the observer be `o`.  For `C={a,m}`, source mass is
zero and target mass is `1-w`.  The exact orientation of
`quittingTerminalPayoffDifferenceAtom`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeAtom.lean`)
is

```text
(source mass-target mass)*reward_o(C)=1-w.
```

There are `1+(2^3-1)=8` outcomes including Never.  At `w=lambda`,

```text
1/2 <= 8(1-lambda),
```

so the prescribed arm of
`HasQuittingStoppingLawVanishingDebtAtomAlternative` holds at charge `1`.
The prescribed arm has no endpoint-debt field; the separately computed
source and endpoint observer debts are indeed zero.

After conditioning, `{a,m}` no longer witnesses charge `1`, because

```text
8(1-hatLambda)<1/2.
```

But the atom predicate has an existential terminal label.  Terminal `{m}`
has signed atom `hatLambda`, so the same charge-one prescribed alternative
still holds.  What fails is a separately demanded **fixed label**, not the
local vanishing-debt atom alternative itself.

The frontier-level structure in
`UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`
additionally requires a mover in `frontier.positiveDebtSupport`, the canonical
`frontier.replacement`, and an eventual-rank statement.  This table has zero
semantic debt in every displayed coordinate and supplies none of that data.
It therefore cannot be called a literal `QuittingVanishingDebtAtomAccess`
instance.

## 3. The deleted clock is separated, but reprojection is not obstructed

Deleting `m` from the displayed row leaves `a,o`; since `o` Continues surely,
the deleted-`m` one-row survival is exactly `w`.  Hence the two chosen ports
have deleted survivals `lambda` and `hatLambda`, and any common scalar
approximation has maximum error greater than `1/4`.  This part is correct.

It proves only that a semantic pair does not identify which residual port was
used.  It does not meet the acceptable-negative-answer quantifier in
`questions/CONDITIONED_PACKET_REPROJECTION.md`, which asks for an instance
where **every** reprojection with the source data loses a clock or violates
the carrier.

Indeed, after the preceding survival history define `a`'s actual packet
hazard directly so that its Continue probability is `lambda`; then arrange
its later solo absorption as before.  Keep `m`'s packet Quit probability
`delta` and let `o` Continue.  This is one literal behavioral continuation,
not an off-path reset convention.  Its semantic pair remains `x_delta`,
because `o`'s payoff and cap depend only on whether `m` Quits, while `a,m`
always receive zero.  The deleted-`m` survival is `lambda`, and the source/
target comparison with `m` sure-Quit again gives the `{a,m}` atom
`1-lambda`.

Changing this packet hazard changes the complete `A/B` stopping law, but that
latent component identity is not a field of a behavioral profile or of the
reached semantic pair.  It is an additional port-preservation hypothesis.
The example therefore refutes a rule that insists simultaneously on the
original complete-mixture port and the frozen root.  It does not refute an
existential packet construction allowed to choose the continuation hazards.

The distinction between reset scale and the normalized diffuse clock mesh is
also binding.  Here `delta->0`, but the selected `a` row is temporally
concentrated.  It is not an instance of the diffuse mesh field in
`QuittingReprojectionDiffuseWindowPacket`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionDiffuseClockBridge.lean`).

## 4. The valid `Omega_L` lemma

For common component laws and positive mixed survival denominators,

```text
F_s(a)-F_s(b)
 =S(s)T(s)(a-b)/(M_s(a)M_s(b))
```

is exact.  At suffix `s`, the two residual clocks are mixtures of the same
conditional component laws with weights `F_s(a),F_s(b)`.  Coupling component
labels, then using the same residual component clocks on agreement, gives
total-variation distance at most `|F_s(a)-F_s(b)|`.  A finite union bound over
players yields `Omega_L`.  Every joint-survival, one-player-deleted-survival,
and terminal-outcome event is a function of these coupled clocks, so the same
bound applies for every finite remaining horizon.

This requires:

- the same two component laws on both sides, with only entrance weights
  changed;
- positive denominators at every suffix being compared; and
- a common continuation beyond the finite packet when full terminal laws are
  compared.

Under those hypotheses `(6.3)--(6.5)` and their constants are correct.  A
zero denominator is a null-history boundary with no Bayes-determined port.

The payoff estimate `2R Omega_L` follows from total variation.  For the best-
response cap, compare the same arbitrary behavioral deviation against both
opponent ports before taking the supremum; the bound is uniform in the
deviation.  The debt estimate `4R Omega_L` then follows by subtraction.

For the prescribed atom arm, perturbing the two profile laws changes one
signed atom by at most `2R Omega_L`; hence `Omega_L<=q/(8KR)` preserves the
same label at halved charge.  A uniform statement including the rectangle arm
needs `Omega_L<=q/(16KR)` absent extra one-sided margin: its original threshold
is `q/4`, while charge `q/2` requires threshold `q/8`.

Calling this condition number “maximal” is not justified.  It is sufficient,
not necessary: the two residual component laws may coincide after a suffix,
making a large posterior displacement harmless, and direct residual-port TV
is another valid state variable.

## 5. Exact impact on the chronological consumer

Summability of `Omega_(L_n)` transports a separately supplied finite-block
law comparison and makes late comparison errors small.  By itself it does not
supply any of the following fields of
`QuittingChronologicalDebtShadowingCertificate`
(`UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`):

- small initial candidate debt;
- the generated secant identity and its upper bound;
- every-suffix prescribed-discrepancy and adverse-direct-forcing budgets; or
- divergent joint and every-player-deleted survival clocks.

The correct surviving diagnostic is therefore narrow: semantic-pair
closeness cannot be used to **infer** closeness of a preselected residual
port.  A positive producer must either carry literal root/clock data, choose
new executable hazards, or add a posterior/TV stability datum.  The displayed
example neither disproves such a producer nor proves that posterior condition
numbers are its unique replacement.

## Concrete repair requested

Retain the Bayes example as a port-nonidentifiability warning, but remove the
claim that it is an acceptable negative answer to conditioned packet
reprojection.  State the literal atom predicate rather than
`QuittingVanishingDebtAtomAccess`, distinguish semantic pairs from terminal
laws and reset scale from diffuse mesh, use the rectangle constant
`q/(16KR)`, and present `Omega_L` only as a conditional finite-port stability
lemma.  A genuine counterexample still needs to rule out the explicit
source-preserving hazard splice above within the exact frontier data.
