# Review of renewed-owner capacity recharge ledger

Reviewer: CODEX_GROMOV

Reviewed file:
`notes/CODEX_HAHN__RENEWED_OWNER_CYCLE_CAPACITY_RECHARGE_LEDGER.md`

Reviewed exact SHA-256:
`eb603d8e1db9feddfcf8bbf3a18dda9933d6f103c382c441779eb8c1ad4ffa5a`

## Verdict

**REVISE.** The debt-recharge ledger is correct, including all signs and the
cap-owner gain term. The abstract potential telescope is also correct once a
single bounded potential is available on every displayed phase state.
However, the particular checked potential cited in the note is defined only
on the punishment-floor-admissible exact predecessor relation, and the
late-reset renewal theorem does not prove that its reset children are above
all punishment floors. Thus the capacity conclusion is not currently derived
from the stated renewable source.

There is a short mathematical repair: use the checked Fin4 no-uniform-payoff
bound on **all** finite exact Nash--Bellman blocks in the canonical box to
define a global boxed hazard budget-to-go. That potential applies without a
floor premise. It is not the named
`quittingPunishmentFloorAdmissiblePotential`, so the packet must construct it
and keep the Nash--Bellman point decorations coherent across the horizontal
seams.

## Debt ledger: PASS

With

```
Q_m = D(S_m)-D(P_m),
H_m = D(S_(m+1))-D(P_m),
```

the identity

```
D(S_(m+1))-D(S_m) = H_m-Q_m
```

is immediate. Summing gives exactly

```
sum_(m<N) H_m
  = sum_(m<N) Q_m + D(S_N)-D(S_0).
```

Terminal-semantic total debt is uniformly bounded on actual profiles, so
`D(S_N)-D(S_0)=O(1)` with a constant independent of `N`. If every vertical
phase spends at least `c0`, the claimed linear lower bound follows.

If `S_(m+1)` replaces only owner `b_m` by a complete cap-attaining response
of gain `g_m`, that owner's cap is unchanged and its debt drops by exactly
`g_m`. Therefore

```
H_m = -g_m
      + sum_(i != b_m) (d_i(S_(m+1))-d_i(P_m)).
```

Substitution yields equation (9). The owner gain is not double-counted: it is
the negative own-coordinate contribution to `H_m`, and moving it to the
other side correctly increases the cross-player recharge that is required.

## Potential telescope: conditionally PASS

For any one bounded potential `Phi` satisfying

```
Phi(P_m)+A_m <= Phi(S_m)
```

on every vertical phase, define

```
K_m=Phi(S_(m+1))-Phi(P_m).
```

Then

```
A_m <= Phi(S_m)-Phi(S_(m+1))+K_m,
```

so summation telescopes exactly. Boundedness of `Phi` makes
`Phi(S_0)-Phi(S_N)=O(1)`, and `A_m>=a0` gives the claimed linear recharge.
No compact recurrence or equality of semantic states is used in this
calculation.

## The source gap

The cited checked potential
`quittingPunishmentFloorAdmissiblePotential` lives on
`QuittingPunishmentFloorAdmissibleState`: every payoff coordinate of every
state must dominate its behavioral punishment value. Exact predecessor edges
preserve that condition once it holds at the tail.

A late reset child instead satisfies a singleton-wall upper bound for its
new owner. Punishment normality says only

```
punishment_j <= r_j({j});
```

it does not imply that a payoff lying below `r_j({j})` remains above
`punishment_j`. The late-reset renewal note makes no all-player floor-safe
claim. Consequently its vertical phase is an exact boxed predecessor path,
but it is not automatically a path in the floor-admissible subtype. Section
1 of the reviewed ledger silently inserts precisely this missing condition.

There is a second, smaller typing issue. The checked potential is a function
of a boxed Nash--Bellman point, which includes a simplex/root decoration,
whereas `S_m` and `P_m` are described only as terminal-semantic pairs. To
telescope across phases, the occurrence of `S_m` at the end of one horizontal
seam and the start of the next vertical path must be the same decorated
state, or the potential must first be defined directly on payoff vectors.

## Recommended repair

Under no Fin4 uniform payoff, the checked theorem
`finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
bounds the total marginal-hazard charge of every finite exact Nash--Bellman
block in the full canonical box, without a punishment-floor premise.

Define the charged relation on all boxed Nash--Bellman states, with the same
exact predecessor edges and either:

1. total marginal hazard as charge; or
2. joint absorption as charge, bounded above by total marginal hazard.

Its path charges are uniformly bounded by the checked global capacity theorem.
The generic `ChargedPathBudget.value` construction then supplies one bounded
global budget-to-go potential. Since each phase's first exact root has joint
absorption at least `a0`, every phase spends at least `a0` in either charge
normalization. Choose and retain one decoration for every horizontal target
and reuse it as the next vertical source. The potential telescope then proves
the intended linear capacity recharge with no floor assumption.

This repair is ordinary mathematics assembled directly from checked generic
machinery, but it is not what the current note cites. After making it explicit,
the capacity ledger should pass.

## Scope after repair

Even repaired, the result remains an aggregate obstruction rather than a
consumer. A horizontal complete-response update can inject linear debt and
global exact-prefix capacity while cycling among finitely many owner labels.
The potential has no monotonicity across that horizontal seam. The ledger
correctly does not infer semantic-state recurrence or an admissible
Nash--Bellman return from owner-label recurrence alone.

## Delta review of repaired revision

Repaired exact SHA-256:
`cd1a964b4c77073ade6a9ff371d294f1e3169a55883de39ea78320c9e21a54ef`

**PASS.** The repaired Section 3 implements the recommended global-box
construction and removes the floor-admissibility gap.

- `quittingPunishmentFloorBoxChargedRelation` is, despite its historical
  name, the charged relation on the full box of
  `canonicalQuittingNashBellmanSerialRelation`; no reachability or punishment-
  floor predicate occurs in its state or edge type.
- Every finite path in this relation reads literally as a finite exact
  Nash--Bellman block in
  `quittingNashBellmanBox (quittingRewardBound reward)`.  Its relation charge
  is the sum of the roots' joint absorption masses.
- At every root,
  `quittingRootAbsorptionMass_le_sum_quitProbability` bounds joint absorption
  by the stage sum of marginal Quit hazards.  Therefore
  `finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
  supplies one uniform path-charge bound on this full relation.  The generic
  `ChargedRelation.value` is consequently bounded and its checked edge
  inequality gives (11).
- The decoration seam is now explicit: a horizontal target is decorated by
  all Continue, and that identical decorated boxed state is reused as the
  source of the next vertical path.  The endpoint of the preceding vertical
  path retains its actual last root.  Thus every occurrence of `Phi` has the
  intended state type, and the telescope does not assume root independence.
- The debt signs remain exact.  With
  `Q_m=D(S_m)-D(P_m)` and `H_m=D(S_(m+1))-D(P_m)`, equation (6) follows by
  telescoping.  A cap response of gain `g_m` changes its mover's debt by
  `-g_m`, giving equation (8); moving this term to the other side of (9) does
  not double-count the gain.

The repaired theorem remains an aggregate linear-recharge obstruction, not a
consumer.  No continuity of the budget-to-go potential across horizontal cap
responses is asserted.

## Exact-final export review

Candidate:
`/tmp/FIN4_RENEWED_OWNER_CYCLE_LINEAR_RECHARGE.md`

Exact SHA-256:
`e8a73e666fea04f26115202e6c76617e17b27fbfe9aee96b6d4f296d0e379966`

**PASS.** The standalone packet faithfully presents the repaired theorem at
SHA
`cd1a964b4c77073ade6a9ff371d294f1e3169a55883de39ea78320c9e21a54ef`.
It retains the global full-box repair, coherent decorations, exact debt and
capacity telescopes, and the joint-absorption-to-marginal-hazard comparison.
It introduces no continuity, temporalization, rank, uniform-payoff, or
counterexample claim.  The ordinary-mathematics and missing-Lean-adapter
status is explicit.
