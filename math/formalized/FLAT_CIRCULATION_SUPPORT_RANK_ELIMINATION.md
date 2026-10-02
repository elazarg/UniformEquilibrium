# Flat circulation is a support-rank descent or the existing paid exit

Authors: `CODEX_RAMSEY`

Independent review:
[CODEX_EULER](../feedback/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR__BY_CODEX_EULER__PROP_6BI.md)

Whole-packet gate:
[CODEX_EULER](../feedback/FLAT_CIRCULATION_SUPPORT_RANK_ELIMINATION__BY_CODEX_EULER.md)

## Exact statement

Let `I` be a finite decidable player type and let

```text
r : {S : Finset I // S.Nonempty} -> (I -> Real)
```

be a finite quitting-game reward table.  Write `D(z)` for the total terminal
semantic debt of a terminal semantic pair `z`.

Let `F` be a `QuittingPositiveMinimumDebtTangentFamily r`.  Its data include

```text
F.base                 a globally minimum positive-debt semantic pair,
F.positiveDebtSupport  the players with positive debt at F.base,
F.tangent(m,i)         the normalized debt tangent in coordinate i
                       for an active mover m.
```

Assume

```text
flat:
  forall m in F.positiveDebtSupport,
    sum_i F.tangent(m,i)=0,

noEntry:
  not HasQuittingStoppingLawFlatSupportEntry
    F.base F.positiveDebtSupport F.tangent.
```

For an active mover `m`, a
`FullReplacementCluster F m` consists of an actual terminal semantic cluster
`E.cluster`, an increasing subsequence `E.subseq`, and the endpoint limits of
the literal full-replacement profiles

```text
F.fullReplacementProfile m (E.subseq rank).
```

### Theorem A: arbitrary-mover endpoint dichotomy

For every `m in F.positiveDebtSupport` and every
`E : FullReplacementCluster F m`, exactly one of the following two ordered
alternatives holds.

1. **Minimum-fiber rank descent.**

   ```text
   D(E.cluster)=D(F.base),
   ```

   and there is a new `QuittingPositiveMinimumDebtTangentFamily F'` for the
   same reward table such that

   ```text
   F'.base=E.cluster,
   card(F'.positiveDebtSupport)<card(F.positiveDebtSupport).
   ```

2. **Existing off-minimum paid exit.**

   ```text
   D(F.base)<D(E.cluster),
   ```

   and there are `observer : I` and `gain : Real` such that

   ```text
   observer != m,
   0<gain,
   eventually rank,
     Nonempty (QuittingPaidFirstDisagreementRow r
       (F.fullReplacementProfile m (E.subseq rank)) observer gain).
   ```

The alternatives are exclusive because their debt comparisons are equality
and strict inequality.

### Theorem B: reduced finite support-rank alternative

Define the reduced exit predicate to mean that some positive-minimum tangent
family `G` for `r` satisfies one of the following three alternatives.

```text
(P) exists m, 0 < sum_i G.tangent(m,i);

(E) every tangent column is flat and
    HasQuittingStoppingLawFlatSupportEntry
      G.base G.positiveDebtSupport G.tangent;

(R) there are an active mover m and FullReplacementCluster endpoint E
    with D(G.base)<D(E.cluster), and observer!=m and gain>0 such that
    eventually the literal full-replacement profiles carry
    QuittingPaidFirstDisagreementRow r ... observer gain.
```

Every `QuittingPositiveMinimumDebtTangentFamily r` reaches this reduced
three-exit predicate after finitely many re-extractions.  In particular, the
old flat charged-circulation alternative is not a terminal fourth exit.

### Theorem C: three-consumer conditional capstone

Assume additionally `Nonempty I` and the following three hypotheses:

```text
hpositiveSlope :
  forall frontier : QuittingPositiveMinimumDebtTangentFamily r,
    (exists mover,
      0 < sum observer, frontier.tangent mover observer) ->
    forall eta : Real, 0 < eta ->
      Nonempty (QuittingChronologicalDebtShadowingCertificate r eta)

hsupportEntry :
  forall frontier : QuittingPositiveMinimumDebtTangentFamily r,
    HasQuittingStoppingLawFlatSupportEntry
      frontier.base frontier.positiveDebtSupport frontier.tangent ->
    forall eta : Real, 0 < eta ->
      Nonempty (QuittingChronologicalDebtShadowingCertificate r eta)

hpaid : PaidFirstDisagreementUniformPayoffConsumer r.
```

Then the quitting game with reward table `r` has a uniform-equilibrium payoff
against unrestricted behavioral deviations.  No circulation consumer is
required.

## Conjecture-facing change

The checked finite support-rank theorem previously ended in four branches:

```text
positive slope / support entry / charged circulation / paid row.
```

The new composition proves that the charged-circulation branch is always
either a strict decrease of the finite active-support rank or the already
maintained paid-row branch.  Hence the conjecture-facing conditional capstone
has only three independent producer obligations:

```text
positive slope / support entry / paid row.
```

This strictly removes the conditioned-packet/circulation producer as a
separate logical input to that capstone.  It does not solve any of the three
surviving obligations.

## Definitions and assumptions

The terminal semantic pair of a behavioral profile stores its prescribed
terminal payoff `U` and its unrestricted behavioral best-response cap `B`;
its debt is `B-U`.  A positive-minimum tangent family is extracted at a
globally minimum semantic pair whose total debt is positive.  Therefore its
positive-debt support is nonempty.

For an active mover, the full-replacement profile literally replaces that
player's stopping law by the selected comparison law.  Compactness supplies
a cluster of the corresponding semantic endpoints.  The cluster is not an
artificial Bellman tail and is not assumed to share a conditional port with
the source.

`QuittingPaidFirstDisagreementRow` stores two deterministic stopping-time
witnesses, their exact first temporal disagreement, the actual opponents'
survival mass reaching it, and a fixed positive payoff difference.  It is a
behavioral source object, not an exact Nash--Bellman edge.

## Proof

### 1. Total debt can only stay at the minimum or increase

For any full-replacement endpoint `E`, its `cluster_mem` field places
`E.cluster` in the terminal semantic carrier.  Global minimality of `F.base`
therefore gives

```text
D(F.base)<=D(E.cluster).
```

Split into equality or strict inequality.

### 2. Equality strictly lowers active-support cardinality

At every full-replacement endpoint, exact vanishing-regret extraction makes
the selected mover's endpoint debt zero.  Flatness and equality of total debt
identify every coordinate debt change with the selected tangent column.

For an old inactive player, terminal debt at the base is zero.  The tangent
in that coordinate is nonnegative.  If it were positive, it would be a flat
inactive-support entry, contrary to `noEntry`; hence it is zero.  Therefore no
old inactive player becomes positively indebted at the endpoint.  Since the
selected old active mover has become zero-debt, one obtains the strict
inclusion

```text
{i : 0<debt(E.cluster,i)} < F.positiveDebtSupport.
```

The checked minimum-fiber re-extraction theorem now constructs a fresh
positive-minimum tangent family `F'` based at `E.cluster`, whose active support
is the set on the left.  Its cardinality is strictly smaller.

### 3. Strict separation is exactly the maintained paid-row source

Suppose instead `D(F.base)<D(E.cluster)`.  Coordinatewise tangent domination,
flatness of the mover's column, and strict growth of total endpoint debt force
positive normalized curvature in some coordinate `observer!=m`.  The checked
curvature decoder produces a fixed `gain>0` and, eventually along `E.subseq`,
an exact

```text
QuittingPaidFirstDisagreementRow r
  (F.fullReplacementProfile m (E.subseq rank)) observer gain.
```

These are precisely the profile, endpoint, observer, gain, distinctness, and
eventuality fields quantified by `PaidFirstDisagreementUniformPayoffConsumer`.
No reprojection or source adapter is inserted.

This proves Theorem A.

### 4. Strong induction removes circulation

Induct on the natural number
`card(F.positiveDebtSupport)`.  The existing exhaustive tangent alternative
first separates positive slope and support entry.  Each remaining branch—
including both the old potential and charged-circulation branches—supplies
global flatness and `noEntry`.

The positive minimum makes the active support nonempty, so choose any active
mover and a full-replacement cluster and apply Theorem A.  In the equality
arm, re-extract and invoke the induction hypothesis at the strictly smaller
rank.  In the strict arm, stop at `(R)`.  This proves Theorem B.  Notice that
no potential-guided mover and no circulation packet is needed in this
shortened induction.

### 5. Remove the circulation hypothesis from the old capstone

Argue by contradiction to Theorem C.  Failure of a uniform-equilibrium payoff
gives a positive global minimum of terminal semantic debt and hence a tangent
family.  Apply Theorem B.

* In `(P)` and `(E)`, the supplied all-accuracy chronological certificates
  enter the existing unrestricted-behavior chronological compiler.
* In `(R)`, the stored fields apply directly to
  `PaidFirstDisagreementUniformPayoffConsumer r`.

Every case contradicts the assumed absence of a uniform-equilibrium payoff.
There is no circulation case.

## Probability and deviation audit

All stopping laws and full-replacement profiles are ordinary behavioral
strategies on the quitting game's unique live history.  Product mixing is
private and independent; no public correlating device is introduced.

The rank argument itself compares exact terminal semantic pairs.  Their cap
coordinates already take the supremum over all behavioral unilateral
deviations, not merely stationary or bounded-memory deviations.  The paid
row preserves actual deterministic pure-time deviations and actual opponent
survival probabilities but does not claim that either witness is a Bellman
root.

Theorem C's conclusion uses the existing chronological and paid consumers,
each of which concludes a uniform-equilibrium payoff against unrestricted
behavioral deviations.  The new rank reduction does not weaken their
probability or agency semantics.

## Boundary tests

1. **Minimum-fiber boundary.**  If `D(E.cluster)=D(F.base)`, no positive
   curvature or paid row is inferred.  The selected mover's exact zero debt
   nevertheless makes support inclusion strict, so the rank descent remains
   available.
2. **Off-minimum boundary.**  If the endpoint has strictly larger total debt,
   rank need not decrease.  The conclusion is only the eventual paid row,
   with no chronology or payoff return.
3. **Support-entry boundary.**  If an inactive coordinate has positive
   tangent, the equality-arm support-inclusion proof is false.  This is
   exactly why support entry remains its own exit `(E)`.
4. **Nonflat boundary.**  If some column has positive total slope, the
   curvature balance used here is unavailable.  This is exactly the surviving
   exit `(P)`.
5. **Local packet boundary.**  The theorem does not say that conditioned
   packet reprojection is false.  It says only that its circulation output is
   unnecessary as a fourth terminal branch of this global finite-rank
   induction.

## Adapter and consumer

The arbitrary-data adapter is the checked chain

```text
positive minimum terminal semantic debt
  -> nonempty_positiveMinimumDebtTangentFamily
  -> exhaustiveAlternative
  -> reduced finite support-rank alternative.
```

In every flat/no-entry branch,
`positiveDebtSupport_nonempty` supplies an active mover and
`exists_fullReplacementEndpointCluster` supplies its literal endpoint
cluster.  Equality uses
`exists_reextractedFrontier_of_minimumFiberEndpoint`; strict separation uses
`FullReplacementCluster.exists_eventually_paidFirstDisagreement`.

The downstream consumers are the existing all-error chronological compiler
for `(P)` and `(E)`, and `PaidFirstDisagreementUniformPayoffConsumer` for
`(R)`.  The new theorem changes the adapter graph by deleting the circulation
consumer edge.

## Source correspondence and novelty

The relevant checked declarations are:

* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/MinimumFiberSupportDrop.lean`
  - `exists_fullReplacementEndpointCluster`;
  - `FullReplacementCluster.mover_debt_eq_zero`;
  - `positiveDebtSupport_ssubset_of_exactDiagonal_of_flat_of_noEntry_of_minimumFiber`;
  - `positiveDebtSupport_card_lt_of_exactDiagonal_of_flat_of_noEntry_of_minimumFiber`.
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean`
  - `FullReplacementCluster.exists_eventually_paidFirstDisagreement`;
  - `exists_reextractedFrontier_of_minimumFiberEndpoint`;
  - `QuittingPositiveMinimumDebtTangentFamily.finiteSupportRankAlternative`.
* `UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`
  - `PaidFirstDisagreementUniformPayoffConsumer`;
  - `exists_uniformEquilibriumPayoff_of_finiteSupportRankExitUniformPayoffConsumers`.

The endpoint rank-drop and paid-row arms were checked separately, and the old
four-exit induction was checked.  The new content is their arbitrary-mover
composition on every flat/no-entry branch, the resulting three-exit strong
induction, and deletion of the circulation hypothesis from the conditional
capstone.  A narrow source audit in the independent review found no existing
declaration making this composition.

No literature theorem is invoked; this is an internal finite reduction of
the repository's stopping-law frontier.

## Lean handoff

1. Define a reduced predicate parallel to
   `HasQuittingStoppingLawFiniteSupportRankAlternative`, with only positive
   slope, support entry, and the existing paid-row fields.
2. Prove an arbitrary-mover endpoint lemma taking `frontier`, `flat`,
   `noEntry`, `mover`, and `endpoint`.  Split
   `frontier.base_minimum endpoint.cluster endpoint.cluster_mem` into equality
   and strict inequality.  Use the two checked declarations named above.
3. Prove termination by `Nat.strong_induction_on` the positive-debt-support
   cardinality.  In both exhaustive flat/no-entry branches, choose an active
   mover and apply the new endpoint lemma.  Do not modify the old four-exit
   predicate or theorem.
4. Add a three-consumer analogue of
   `exists_uniformEquilibriumPayoff_of_finiteSupportRankExitUniformPayoffConsumers`
   and reuse its `(P)`, `(E)`, and paid case proofs verbatim.
5. Kernel-check the theorem imports and ensure only the project's accepted
   foundational axioms occur.  Useful theorem-level regression checks are the
   equality/strict endpoint split and the strict `Nat` rank inequality.

## Scope and nonclaims

This packet does not:

* construct a chronological certificate for positive slope or support entry;
* turn a paid first-disagreement row into an exact Bellman path, admissible
  return, payoff near-return, or uniform equilibrium;
* produce a conditioned packet, actual-successor restart, or semantic-port
  reprojection;
* remove the paid consumer from the capstone;
* prove that every quitting game has a uniform-equilibrium payoff; or
* invalidate conditioned-packet reprojection as a local mathematical problem.

Its complete conclusion is the strict global reduction from four finite-rank
exits to three.
