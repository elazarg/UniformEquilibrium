# CODEX_MINER — the inert stall is invisible to the standard nonlocal literature quotients

**Status (2026-08-26):** proved ordinary-mathematics source correspondence;
internal and awaiting independent review.  This is a scoped no-go for feeding
the maintained inert paid-cap family directly into the published AGKRS
absorption-path or Simon payoff-orbit objects.  It is not a no-go for every
possible enriched absorption path, and it does not consume the inert stall.

## 1. Question and answer

Can one obtain the cumulative exact punishment-floor near-return requested in
`questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md` merely by applying a known
nonlocal compactification to the literal profiles in a paid-cap
`InertStall`?

For the standard objects in Ashkenazi-Golan--Krasikov--Rainer--Solan and
Simon, the answer is **no for an exact, source-audited reason**:

1. every finite inert cap lift is just the original behavioral profile with
   finitely many all-Continue dates inserted;
2. the AGKRS profile-to-absorption-path quotient deletes exactly those dates,
   so the entire family has one and the same absorption path;
3. on the cap annotations, every inserted root is all Continue, the semantic
   pair is constant, and every exact edge has zero absorption charge; and
4. the original full-gap paid pure-time row survives losslessly on every
   literal delayed profile, but it is not promoted to a prescribed-payoff
   exact Nash--Bellman edge.

Thus the two halves needed by the checked cumulative-return consumer remain
on disjoint objects:

```text
exact cap-Nash chronology:       zero charge, constant cap value;
literal paid-profile chronology: unchanged full-gap deviation, no exact
                                 prescribed-payoff path supplied.
```

AGKRS compactness identifies the first chronology's inserted delays and does
not repair the second chronology's strategic defect.  Simon's ambient
`F_0` dynamics sees at most the same zero-variation all-Continue cap
self-loop; the paid row is absent from that edge.

This is evidence-backed source correspondence of the third permitted output
type, not another residual split.

## 2. Exact maintained input

Fix a nonempty finite player type, a quitting reward table `reward`, and

```text
source : QuittingPaidCapLiftedSource reward,
port   : source.SummablePort,
stall  : source.InertStall port.
```

Write

```text
sigma_h = quittingCapLiftedPrefixProfile reward source.profile h.
```

The checked `InertStall` fields in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/`
`PaidCapPortExactTrichotomy.lean` give, literally for every finite `h`,

```text
root_h = all Continue,                                      (2.1)
semanticPair(sigma_h) = semanticPair(source.profile),       (2.2)
debt(sigma_h) = debt(source.profile),                       (2.3)
observerReach_h = 1,                                        (2.4)
```

and a paid first-disagreement row on `sigma_h` whose two witness times are
the original times shifted by `h`, with exactly the same live mass, reached
gain, orientation, and later-time offset.  In particular,

```text
gain <= liveMass_h * reachedGain_h
     = liveMass_0 * reachedGain_0.                          (2.5)
```

The source itself came from an actual behavioral profile.  Under a positive
terminal exploitability gap, this construction is available at every actual
profile by
`HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort`
(`ActualProfileTerminalGapPaidCap.lean`), and the charged-return arm is
excluded by its unrestricted-behavior consumer.  No attainment of the global
minimum by an actual profile is assumed here.

## 3. The delay-quotient theorem

### Proposition 3.1 (AGKRS absorption-path invisibility)

Let `pi(sigma)` denote the discrete absorption path induced by an absorbing
behavioral profile in the sense of AGKRS Remarks 4.4--4.5.  Whenever the
induced paths are defined,

```text
pi(sigma_h) = pi(source.profile)       for every finite h.  (3.1)
```

Consequently every subsequence of the inert lifted family is already constant
in the AGKRS absorption-path space.  Its compact limit cannot reveal a new
jump, continuous absorption interval, payoff return, or chronology which was
not present in the original path.

#### Proof

The recursive definition of `quittingCapLiftedPrefixProfile` says

```text
sigma_(h+1) = root_h followed by sigma_h.
```

Equation `(2.1)` makes `root_h` the literal all-Continue product row.  By
induction, `sigma_h` is the source profile preceded by exactly `h`
all-Continue stages.

AGKRS Remark 4.4 constructs the induced discrete absorption path from the
cumulative absorption probabilities at the absorbing stages.  Remark 4.5
states that inserting or deleting all-player-Continue stages leaves this path
unchanged (and identifies this as the ambiguity of the profile-to-path map).
Deleting the first `h` zero-absorption stages proves `(3.1)`.  A constant
sequence has only that same path as a subsequential limit. `QED`

### Proposition 3.2 (zero-charge exact cap image)

Let `B_h` be the cap/envelope coordinate of `semanticPair(sigma_h)`.  Then

```text
B_h = B_0,
root_h = all Continue,
successor(B_h,root_h) = B_h,
absorption(root_h) = 0.                                    (3.2)
```

The root is exact endpoint Nash against `B_h`.  Hence, after the standard
endpoint-Nash-to-support-Nash forgetting, `(B_0,B_0)` is an ambient Simon
`F_0` self-edge witnessed by all Continue, with zero Euclidean variation and
zero quitting mass.  This statement is only about the ambient edge: `B_0`
need not lie in Simon's exact feasible carrier.

In particular, every finite segment of the checked cap orbit has cumulative
charge zero.  It cannot instantiate a
`QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` at any positive
charge floor.

#### Proof

The first two identities are `(2.1)--(2.2)`.  The all-Continue successor
identity is the Bellman identity with joint survival one and terminal reward
part zero.  Exact endpoint Nash is
`quittingCapLiftedPrefixRoot_exactNash`; zero absorption is also an immediate
consequence of `(2.1)`.  Summing zeros proves the last assertion. `QED`

### Proposition 3.3 (the paid mark does not enter either exact edge)

For every `h`, the literal profile `sigma_h` retains the full source paid
difference `(2.5)`.  But the checked port asserts exact Nash only at the cap
coordinate `B_h`; it does not assert that `root_h` is exact Nash against the
prescribed payoff coordinate `U_h`, and it does not promote either pure-time
witness to a root of the punishment-floor exact relation.

Thus neither of the following inferences is valid from the inert fields:

```text
lossless paid row on sigma_h
    => positive exact Nash--Bellman edge at U_h;              (false gap)

constant AGKRS path pi(sigma_h)
    => sequentially zero-perfect absorption path.             (false gap)
```

#### Proof

The positive statement is exactly `stall.losslessShiftedPaidRow h`.  The two
negative statements are type/provenance audits of the same checked structure:
`InertStall` contains the cap-root exactness and literal paid rows as separate
fields and contains no prescribed-payoff edge or sequential-perfection field.
The full-gap terminal witness also shows that the literal profiles themselves
are not terminal approximate Nash profiles below the gap.  Quotienting their
common initial delays changes none of their terminal payoffs or deviations.
`QED`

## 4. Consequence for AGKRS absorption paths

The original-paper correspondence was checked against
`Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean`:

- Remarks 4.4--4.5 give exactly the induced-path construction and
  all-Continue deletion used in Proposition 3.1.
- Proposition 4.6 is a paper-level **approximate decoder**: it discretizes a
  supplied absorption path by finer product-row profiles.  It does not decode
  a path into a finite exact punishment-floor Nash--Bellman path.
- Proposition 4.9 is compactness in weak absorption time.
- Proposition 4.12 closes sequential perfection only when the approximating
  paths already carry vanishing sequential-perfection error.
- Theorem 4.13 converts a supplied sequentially zero-perfect path into
  approximate equilibria, subject to the paper's branch hypothesis.  In the
  Lean transcription it remains commentary because the full weak-Stieltjes
  closure and profile decoder are not formalized.

Applied to the inert family, Proposition 4.9 has nothing to compactify: by
`(3.1)` the family is already constant.  Proposition 4.12 has no premise,
because the inert source supplies no sequential-perfection certificate.
Proposition 4.6, even if fully imported, would return approximate behavioral
profiles from a separately supplied zero-perfect path; it would not turn the
preserved paid mark into the exact finite path requested by the current
cumulative-return consumer.

There is one checked arbitrary-data AGKRS path producer in the relevant
literature chamber:
`Literature.AshkenaziGolanKrasikovRainerAndSolan2022.theorem5_2` constructs a
continuous zero-perfect path under the principal-Q hypothesis.  Production
Lean has the corresponding corrected support-indexed construction and
already consumes it.  On the maintained `Fin 4` counterexample side,
`FinFourQuantitativeFullSupportHardResidual.residualHardClass.`
`not_full_projectiveQBar` explicitly negates this hypothesis
(`FullSupportProjectiveQBarResidual.lean`).  Therefore this literature
producer is a solved disjoint branch, not an adapter for the inert residual.

## 5. Consequence for Simon's finite-orbit method

The closest Simon object is genuinely nonlocal.  In
`Literature/Simon2007.lean`, `FiniteNearOrbitCondition.toCyclicOrbitCondition`
does the following at a fixed tolerance:

1. bounds the rational near-feasible carrier in one compact ball;
2. uses a charge-packing lemma to find two close payoff states separated by a
   block of large variation;
3. uses the exact Bellman identity on each `F_eta` edge and the estimate
   `motion <= 2 C * QuitProbability` to prove

   ```text
   1 <= sum(block quitting probabilities);                 (5.1)
   ```

4. reverses and periodizes the block, paying the row tolerance and the
   endpoint seam divided by block absorption.

This is the strongest literature analogue of the maintained cumulative
near-return target: it has close payoff endpoints and a fixed positive
cumulative absorption floor.  Its edges, however, are `eta`-Nash and its
states are only `eta`-rational.  The maintained consumer requires every edge
to be exact Nash and every state to satisfy the literal punishment floor.

On the actual inert cap orbit, Proposition 3.2 makes all Simon motion and all
row absorption zero, so the packing argument cannot even start.  The paid
row cannot be substituted for the cap edge: it is a pure-time deviation
witness on the literal prescribed profile, not an `F_eta` root at the same
payoff annotation.

More globally, Simon's finite-orbit condition is not an arbitrary-data
producer.  The corrected Theorem 3/Simon 2012 Theorem 2.1 makes it equivalent
to approximate-equilibrium existence after excluding the stationary and
instant branches.  In production this missing direction is deliberately
packaged as the supplied hypothesis
`SuppliedQuittingSimonFiniteOrbitNecessity`; no inhabitant is asserted in
`SuppliedCorrespondence.lean`.  Thus importing Simon's orbit condition at
every error would import an alternative formulation of the desired terminal
approximants, not derive it from the terminal witness or inert port.

The unbounded-length issue is load-bearing rather than cosmetic.  Simon's
paper explicitly notes that the minimal cycle length may depend on the
tolerance.  The independently reviewed bounded-length compact exactification
lemma in `notes/CODEX_CEDAR__PAID_ROW_REENTRY.md` proves that a uniform length
bound would allow vanishing-error closed-relation loops to exactify.  Its
irrational-circle regression proves that approximate returns of unbounded
length need not close into a finite exact path.  No Simon declaration supplies
the missing uniform length or an exact edgewise Nashification with controlled
total error.

## 6. Consequence for Solan--Vieille

`Literature/SolanAndVieille2001.theorem1_2` and its production implementation
construct cyclic subgame-perfect approximate equilibria under

```text
QuittingUnitSoloExit reward
QuittingCappedJointExit reward.
```

This is already a terminal-approximant producer for that special table class;
it does not consume a supplied inert source.  The checked theorem
`QuittingTerminalExploitabilityWitness.not_unitSoloExit_and_cappedJointExit`
(`TerminalExploitabilitySoloExitPreference.lean`) proves that a table carrying
the maintained terminal witness cannot satisfy both premises.  Hence the
Solan--Vieille cyclic construction is another solved disjoint branch, not a
nonlocal continuation of the inert profile.

This exclusion is exact and narrow.  It does not say that some new use of the
Solan--Vieille backward correspondence outside A.1--A.2 is impossible.

## 7. Exact conclusion and surviving theorem shape

The standard nonlocal sources do not compose with `InertStall` as currently
typed:

```text
AGKRS absorption quotient
    sees one unchanged literal absorption path;

Simon cap-payoff orbit
    sees one zero-variation, zero-charge all-Continue self-edge;

Solan--Vieille cyclic producer
    requires table hypotheses excluded by the terminal witness.
```

Therefore a literature-based repair must add genuinely new semantics before
compactification.  The smallest plausible additions are one of:

1. an enriched absorption path retaining the prescribed payoff, cap payoff,
   paid pure-time passport, and a finite decoder which produces exact
   punishment-floor edges;
2. a source-matched Nashification theorem turning the preserved paid row into
   a positive exact edge while keeping a bounded cumulative error account; or
3. a discrete source/rank reduction triggered by the fact that the standard
   absorption-time quotient is stationary while the paid mark remains
   positive.

Merely taking a weak limit, deleting the escaping delay, or invoking compact
recurrence cannot provide the missing positive charge.

## 8. Novelty and starving-note audit

Narrow duplicate searches used the phrases `absorption path`, `all-Continue`,
`quotient delay`, `bounded-length exactification`, `invariant measure`, and
`finite orbit` in the conference corpus and the named Lean subtrees.

- `notes/CODEX_RAMSEY__NORMALIZED_PAID_MARK_COMPACTIFICATION_NO_GO.md`
  independently gives the broader clock-escape/projective-mark dichotomy and
  an exact two-player regression.  It is currently unreviewed.  Proposition
  3.1 above adds the exact correspondence to the published AGKRS quotient;
  it does not supersede Ramsey's regression.
- `notes/CODEX_CEDAR__PAID_ROW_REENTRY.md`, Section 4, contains the reviewed
  bounded-length exactification lemma.  It is a useful internal theorem, but
  it still has no actual-data bounded-detour producer and therefore does not
  meet the export gate.
- `notes/CODEX_CEDAR__ERGODIC_NASH_BELLMAN_RECURRENCE.md` is reviewed and
  closed as a distinct route: positive invariant mean is already consumed by
  the checked unbounded exact-prefix theorem, while a terminal witness forces
  every invariant law to have zero absorption mean.
- `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`, Propositions 80--83,
  already separates generic transient-charge escape from the checked exact
  finite-prefix consumer.  The present note is narrower: it identifies why
  the actual inert family maps to zero charge before any recurrence theorem
  is applied.
- `notes/CODEX_CEDAR__STOPPING_TIME_COMPACT_GAME.md` proves that the plain
  compact stopping-law payoff graph loses relative-time information, but it
  is not independently reviewed and is not promoted here.

No reviewed result found in this crawl is both omitted from the current
checked/formalized packets and equipped with the arbitrary-data adapter and
named consumer required for export.  The bounded-length exactification lemma
is the most reusable reviewed item at risk of being buried in a long note;
its missing export criterion is still the bounded detour from actual paid
data.

## 9. Sources inspected

- `questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`;
- `UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/`
  `ActualProfileTerminalGapPaidCap.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/`
  `PaidCapLiftedSummablePort.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/`
  `PaidCapPortExactTrichotomy.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/`
  `FullSupportProjectiveQBarResidual.lean`;
- `UniformEquilibrium/Quitting/Classification/`
  `TerminalExploitabilitySoloExitPreference.lean`;
- `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/`
  `SuppliedCorrespondence.lean`;
- `Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean`, Sections 4--5;
- `Literature/SolanAndVieille2001.lean`, Theorem 1.2 and its exact
  assumptions;
- `Literature/Simon2007.lean`, corrected Theorem 3, Lemma 5/corrected motion,
  and the finite-near-orbit periodization proof;
- `Literature/Simon2012.lean`, Theorems 2.1--2.2 and corrected Lemma 2.1;
- `literature/SIMON_2007__CLEANED_TEXT.md` and
  `literature/SIMON_2007__PROOF_MAP.md` for the image-audited theorem wording
  and the explicit tolerance-dependent-period remark.

## 10. Requested independent check

Please verify the exact induction from inert cap roots to inserted
all-Continue stages, the use of AGKRS Remark 4.5 in `(3.1)`, the separation
between cap-value exact Nash and prescribed-profile paid gain, and the claim
that Simon's extracted block has `(5.1)` but only approximate Nash/floor
semantics.  The conclusion should remain scoped to the named standard
literature objects; an enriched marked absorption path is deliberately left
open.
