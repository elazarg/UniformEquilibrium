# Review of Proposition 6AO

Reviewer: `CODEX_EULER`

Claim reviewed: Proposition 6AO in
[`CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md`](../notes/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md).

Verdict: **VALID ordinary mathematics in its stated conditional scope.**  The
periodic construction exposes a real weakness of the literal
`QuittingBudgetStablePacketData` interface: its declared scale occurs only in
lower hazard bounds and seam/radius costs, not in an upper bound on any root
hazard or packet mesh.

## Exact periodic provenance

Let `W` and `V` be the fixed length-`L` source and full-replacement words.
Repeating `W` gives a legal cyclic behavioral profile `X`; repeating the
mover coordinate of `V` and leaving the other repeated `W` coordinates
unchanged gives a legal profile `Y`.  The live-root identity
`quittingProfileLiveRoot_cyclicBehaviorProfile` in
`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` recovers the
specified roots exactly.  Shifting by one full period returns the same root
sequence, so conditioning on `L` all-Continue rows gives

```text
Residual_allC^L(X)=X,       Residual_allC^L(Y)=Y.
```

The source identity is an actually reached port whenever the one-period
joint reach is positive: every finite repetition then has positive reach.
The endpoint identity remains exact stopping-law provenance even if its
prefix has zero reach.  The first period is literally the frozen source/full-
replacement pair; no component label or pre-cutoff root is reconstructed
from semantic data.

The semantic pair of each cyclic phase gives the required candidate array.
Literal one-root prefix recursion proves every `exact_step`; the phase-`L`
pair equals the phase-zero annotation, so both endpoint seams are zero.  A
reward-table bound controls prescribed values, caps, and debts.  Hence the
periodic loop genuinely supplies the candidate fields of
`QuittingBudgetStablePacketData`, independently of the atom discussion.

## Atom and clock constants

The fixed-terminal atom estimate has the stated factor.  Coupling `P` with
`X` after their common `W` prefix changes the probability of one fixed
terminal coalition by at most the prefix joint reach, hence changes its
reward-weighted atom contribution by at most `M*epsilon`.  Coupling `E` with
`Y` after the common endpoint prefix has the same bound because the unchanged
second label has endpoint survival at most `epsilon`.  The two contributions
therefore give

```text
|A_C(X,Y)-A_C(P,E)| <= 2*M*epsilon.
```

This is a fixed-outcome-law estimate, so no extra factor two from the range
of a general bounded payoff variable is needed.  If the old charge-`q`
decoder gives `|A_C(P,E)|>=q/(2K)`, the condition

```text
2*K*M*epsilon <= q/4
```

leaves `|A_C(X,Y)|>=q/(4K)`, exactly the charge-`q/2` threshold.  The terminal
orientation and the prescribed branch are unchanged.

Each repeated source word has the original marginal-hazard lower bounds
`hazard_i(W)>=kappa*h_0` for the two retained labels.  Therefore the same
word satisfies `hazard_i(W)>=kappa*s` for every declared `0<s<h_0`.  This is
the precise place where the fixed word can masquerade as an arbitrarily
small-scale packet.

## Literal type audit

The declaration in
`UniformEquilibrium/Quitting/Debt/Dynamic/BudgetStableCompatiblePacketIteration.lean`
has only

```text
kappa*scale <= first_hazard,
kappa*scale <= second_hazard.
```

It contains no upper root-hazard, mesh, word-size, or total-hazard condition.
A one-point port with radius `h_0`, successor itself, and `omega=chi=0` can
therefore return the same periodic word for every legal smaller scale.  Zero
cost is operationally sublinear, the radius account is exact, and the two
endpoint seams vanish.  This is a genuine interface gap, not a hidden
selection of an infinite compatible chain.

## Scope

The result is conditional on one already validated prescribed-atom,
two-near-killed source/full-replacement word and on positive source reach.  It
does not cover the mixed-posterior or rectangle branches.  It does not give a
vanishing literal mesh, arbitrary reached-source entry, a small-debt seed, or
the Tier-II actual-source-to-artificial-anchor implementation.  Atom and
replacement provenance are additional mathematical data; the current packet
structure itself stores only candidate annotations, roots, labels, hazards,
seams, radius, and bounds.

Accordingly Proposition 6AO is not an intended Tier-I solution to
`CONDITIONED_PACKET_REPROJECTION.md`.  It correctly proves that the present
formal packet type is too weak to express that question's vanishing-mesh
reading.  Adding a literal upper-size field such as
`max rootHazard <= C*scale` blocks the fixed-word reuse and restores the
root-moving/restart problem.
