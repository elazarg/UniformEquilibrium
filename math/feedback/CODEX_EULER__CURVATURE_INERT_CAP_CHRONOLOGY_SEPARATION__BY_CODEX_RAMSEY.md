# Review of `CODEX_EULER__CURVATURE_INERT_CAP_CHRONOLOGY_SEPARATION`

**Reviewer:** `CODEX_RAMSEY`  
**Verdict:** **PASS**  
**Scope:** exact local converter no-go; internal only  
**Export assessment:** do not export.  The model has `D_*=0` and an exact
all-`Never` equilibrium, so it does not contract the maintained hard residual.

## Claim reviewed

I independently checked the rational `Fin 4` table, the three actual product
profiles `S,M,T`, all prescribed payoff and unrestricted cap coordinates, the
`1/4` cap curvature, uniqueness of the all-Continue exact product root at all
six displayed continuation vectors, invariance under inert prefixing, and the
directional nonclaim concerning an unrelated edge having a displayed vector
as its head.

## Exact profile enumeration

Players `3,4` play `Never` and are absent from every realized coalition.  At
`S`, the two equiprobable cases are

```text
(T_1,T_2)=(0,0): coalition {1,2}, payoff (1,0),
(T_1,T_2)=(1,0): coalition {2},   payoff (1/2,-1),
```

so `U_S=(3/4,-1/2,0,0)`.  At `T`, the cases are `{1}` with payoff `(0,1)` and
`{1,2}` with payoff `(1,0)`, giving `U_T=(1/2,1/2,0,0)`.  The four equally
likely midpoint cases give

```text
{1,2}: (1,0),  {1}: (0,1),  {2}: (1/2,-1),  {1,2}: (1,0),
```

and hence `U_M=(5/8,0,0,0)=(U_S+U_T)/2`.

Against player `2`'s three laws, player `1`'s pure-time values are exactly as
stated:

```text
S_2: max = 1 at time 0,
T_2: max = 1 at time 1,
M_2: V(0)=1/2, V(1)=3/4, V(t>=2 or Never)=1/2.
```

Against player `1`'s fixed half--half law, player `2` has values
`-1/2,1/2,1` at time `0`, time `1`, and every later time or `Never`.  The
dummies have cap zero.  The checked pure-time extremality theorem therefore
upgrades the enumeration to unrestricted behavioral deviations and gives

```text
B_S=(1,1,0,0), B_M=(3/4,1,0,0), B_T=(1,1,0,0).
```

The curvature and debt arithmetic follows:

```text
(B_S,1+B_T,1)/2-B_M,1 = 1/4,
d(S)=(1/4,3/2,0,0),
d(M)=(1/8,1,0,0),
d(T)=(1/2,1/2,0,0).
```

All other curvature coordinates vanish.

## Unique-root check

At every displayed continuation vector, each dummy strictly prefers Continue:
Quit gives `-1`, while Continue gives `0` whether another player quits or the
tail is reached.

With the dummies continuing, player `2` strictly prefers Continue against
each pure action of player `1`:

- against Quit, Continue gives `r_2({1})=1` and Quit gives
  `r_2({1,2})=0`;
- against Continue, Continue gives `Z_2>=-1/2` and Quit gives
  `r_2({2})=-1`.

Strict dominance against the two pure actions also covers every mixed product
action of player `1`.  Once player `2` Continues, player `1` compares singleton
Quit payoff `0` with `Z_1>=1/2`, and strictly Continues.  Thus all Continue is
the unique exact product root at each of
`U_S,U_M,U_T,B_S,B_M,B_T`.

## Prefix semantics and orientation

Prefixing the actual profiles by all Continue shifts every finite clock by one
date.  Prescribed outcome laws and payoffs are unchanged.  The cap after the
shift is

```text
max(original cap, own singleton payoff),
```

and the displayed caps dominate the singleton values `(0,-1,-1,-1)`, so the
caps and debts are unchanged as well.  The law midpoint and the `1/4`
curvature persist literally.  Since the exact root at every displayed **tail**
is unique all Continue, every forward cap-prefix orbit from those tails is the
zero-absorption self-loop.  No debt value or positive-debt support changes.

The tail qualification is essential.  As an algebraic root-game regression,
put

```text
W=(3/2,-2,0,0), q_1=1/2, q_2=3/4, q_3=q_4=0.
```

Both active players are indifferent: player `1`'s Quit and Continue values
are `3/4`, while player `2`'s are `-1/2`.  The successor is exactly
`U_S=(3/4,-1/2,0,0)`, with positive absorption.  Thus a displayed vector can
be the **head** of an unrelated positive exact algebraic edge.  Here `W` lies
outside the actual terminal-payoff box for the reward-bounded game, so this is
not a carrier edge and does not contradict the note.  It confirms that the
Section 6 disclaimer is necessary and correctly placed.

For maximum clarity, the phrase “no positive-charge exact prescribed-payoff
edge starts from any square corner” in Section 5 should always be read in the
repository's Bellman orientation `tail -> prefixed current`.  Replacing
“starts from” by “has a displayed square corner as its tail” would remove any
possible behavioral-chronology ambiguity, but this is not a mathematical
repair.

## Precise missing hard-residual input

The countermodel is defeated at the earliest hard-residual table consequence.
Its own singleton rewards are

```text
r_1({1})=0, r_2({2})=-1, r_3({3})=-1, r_4({4})=-1.
```

Therefore literal all `Never` has prescribed payoff and unrestricted cap both
zero.  It is an exact unrestricted terminal Nash profile, and
`quittingTerminalDebtSumInf=0`.

By contrast, a terminal exploitability witness with gap `Gamma>0` gives,
through
`QuittingTerminalExploitabilityWitness.exists_terminalGap_le_soloReward`, a
fixed owner `a` with

```text
Gamma <= r_a({a})_a.
```

Thus the exact premise that first excludes this table is the positive-solo
consequence of the terminal witness; equivalently at the semantic level, the
maintained `D_*>0` premise excludes its zero-debt all-`Never` carrier point.
No collision-map, response-square, or later tangent-family field is needed to
reject this particular model.

This also identifies what a positive-minimum proof must use beyond the static
curvature interface: it must retain and align the witness-selected
positive-singleton owner (or another consequence preventing zero-debt
all-`Never`) with the curvature/reset chronology.  Reapplying the unchanged
square alone cannot manufacture that alignment.

## Final disposition

The exact local no-go passes.  It refutes only a converter whose supplied data
are the actual cap square, its positive curvature, the exact prefix cocycle,
and unique all-Continue roots at the displayed tails.  It does not refute a
converter that essentially uses the positive terminal witness, positive
global minimum, floor-safe paid-row provenance, or a source-native reset
relation.  Internal retention is appropriate.
