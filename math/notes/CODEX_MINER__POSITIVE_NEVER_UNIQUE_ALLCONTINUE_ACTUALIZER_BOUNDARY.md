# Positive-Never unique-all-Continue carrier points: actualizer and late-release boundary

Author: `CODEX_MINER`

Status: **proved ordinary mathematics; independently reviewed PASS; internal
only.**  Reviews:
[`CODEX_RAMSEY`](../feedback/CODEX_MINER__POSITIVE_NEVER_UNIQUE_ALLCONTINUE_ACTUALIZER_BOUNDARY__BY_CODEX_RAMSEY.md)
and
[`CODEX_EULER`](../feedback/CODEX_MINER__POSITIVE_NEVER_UNIQUE_ALLCONTINUE_ACTUALIZER_BOUNDARY__BY_CODEX_EULER.md).
This attacks the off-minimum branch of
[`CODEX_EULER__POSITIVE_NEVER_RECTANGLE_CAP_RAY_REGENERATION`](CODEX_EULER__POSITIVE_NEVER_RECTANGLE_CAP_RAY_REGENERATION.md)
after correcting its support-rank scope in
[`feedback/CODEX_EULER__POSITIVE_NEVER_RECTANGLE_CAP_RAY_REGENERATION__BY_CODEX_MINER`](../feedback/CODEX_EULER__POSITIVE_NEVER_RECTANGLE_CAP_RAY_REGENERATION__BY_CODEX_MINER.md).
It produces an exact robust-inert versus singleton-tight split and a
source-matched late-release descent/three-label fork.  Neither fork is yet a
maintained return or finite-rank consumer.

## 1. Exact input and answer

Fix a bounded Fin4 quitting table in the terminal-gap hard branch.  Write
`Gamma>0` for the terminal exploitability gap and `D_*>0` for the global
terminal-semantic debt minimum.  Suppose the reviewed cap-ray theorem has
returned a joint carrier point

```text
point=(y,lambda),
D(y)>D_*,
q=lambda(Never)>0,                                  (1.1)
```

such that every exact product-root Nash equilibrium against the envelope
`y.2` is the literal all-Continue root.  The point may be nonattained by a
behavioral profile.  No attainment is assumed below.

There are two independent exact conclusions.

1. If every singleton inequality at `y.2` is strict, the unique all-Continue
   root has an open linear-defect basin.  Law-matched actualizers of `point`
   are therefore eventually literal inert cap-port sources.  Their debt
   stays near the fixed off-minimum value `D(y)`, so they are not terminal
   approximants.
2. The positive `Never` coordinate can still be released at a late finite
   time on the same actualizers.  This gives either a fixed actual debt drop
   away from `y`, or a fixed recipient and the sharp three-label endpoint
   atom.  The first target loses joint Never and leaves the cap ray; the
   second remains based at an off-minimum source.  Hence neither output by
   itself regenerates the original minimum rectangle.

Thus common-quantile actual realization does not consume the cap-ray fixed
point.  The exact unresolved scalar boundary is

```text
exists i, y.2_i = r_i({i}),                          (Tight)
```

or, in the strict branch, the literal paid-row/inert wall with the
late-release leg lying outside the cap-prefix relation.

## 2. Law-matched finite-clock actualizers

Because `(y,lambda)` belongs to the joint semantic/law carrier, choose actual
profiles `rho_n` with

```text
Sem(rho_n) -> y,
Law(rho_n) -> lambda.                               (2.1)
```

Apply the checked profilewise common-quantile compression diagonally.  It
gives independent profiles `sigma_n`, each marginal supported on finitely
many dates plus `Never`, such that

```text
Sem(sigma_n) -> y,
Law(sigma_n) -> lambda.                             (2.2)
```

The compression preserves every marginal Never atom exactly relative to its
input profile, and its common bad-cell coupling makes every fixed terminal
outcome coordinate converge.  In particular

```text
q_n := Law(sigma_n)(Never) -> q>0.                  (2.3)
```

This is stronger than source-free finite-clock density: the actualizers
remain attached to the supplied joint law `lambda`.

If `point` is attained, one may instead take a constant realizing source and
finite-clock approximations of it.  The conclusions below do not distinguish
attainment from nonattainment.

## 3. Strict slack makes the actual cap ports literally inert

Put

```text
kappa = min_i (y.2_i-r_i({i})) >= 0.                (3.1)
```

Nonnegativity follows because all Continue is exact against `y.2`.

### Theorem 3.1 (robust actualizer inertness)

If `kappa>0`, there is an open neighborhood `N` of `y.2` and `c>0` such that
for every tail `V in N` and every product root `root`,

```text
c*Absorption(root) <= RootNashDefect(V,root).        (3.2)
```

Consequently, for every sufficiently large `n`, every exact cap root against
`Sem(sigma_n).2` is all Continue.  Every paid cap lift selected at the actual
source `sigma_n` is a literal `InertStall`: all its prefix roots are all
Continue, its terminal semantic pair and law are fixed at every finite
prefix, and its total absorption and cap displacement are zero.

### Proof

Apply
`exists_open_linearAbsorptionDefect_of_compact_strictAllContinue` to the
singleton compact set `{y.2}`, with any positive `delta<=kappa`.  Its two
hypotheses are exactly the strict singleton inequalities and uniqueness of
the all-Continue exact root.  This gives (3.2).

By (2.2), the cap vectors of `sigma_n` eventually lie in `N`.  An exact root
has total root Nash defect zero, so (3.2) and `c>0` force zero absorption.
For a finite independent product root, zero absorption forces every marginal
to Continue surely.  Since
`quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap` fixes the
semantic pair, the identical argument repeats at every cap-prefix stage.
The all-Continue law prefix is also literally the same law.  Hence every
compatible cap lift is inert. `QED`

### Corollary 3.2 (not terminal approximants)

Let

```text
E=D(y)-D_*>0.
```

Eventually

```text
D(Sem(sigma_n)) >= D_*+E/2.                         (3.3)
```

If `sigma_n` were `epsilon_n`-terminal Nash with `epsilon_n->0`, the checked
unrestricted-debt bound would give

```text
D(Sem(sigma_n)) <= 4*epsilon_n -> 0,
```

contradicting `D_*>0` (indeed already contradicting (3.3)).  Adding any
finite number of the selected all-Continue cap roots changes neither side.

Thus the strict branch is a robust actual inert plateau above the global
minimum, not an attainment or terminal-approximation mechanism.

## 4. Exact late release from the same actualizers

Choose the fixed owner `a` supplied by
`QuittingTerminalExploitabilityWitness.exists_terminalGap_le_soloReward`, so

```text
s_a:=r_a({a}) >= Gamma.                              (4.1)
```

Let `K_n` exceed the finite support of every finite clock atom in `sigma_n`.
Change only player `a`: preserve its hazards below `K_n`, Quit surely at
`K_n`, and Continue afterwards.  Call the resulting literal profile `tau_n`.
Exactly the old joint-Never event is moved to singleton `{a}`.  Therefore

```text
g_n := U_a(tau_n)-U_a(sigma_n) = s_a*q_n,
d_a(tau_n)-d_a(sigma_n) = -g_n.                     (4.2)
```

Eventually

```text
g_n >= Gamma*q/2.                                   (4.3)
```

For the other three coordinates put

```text
T_n=sum_(b!=a) [d_b(tau_n)-d_b(sigma_n)].           (4.4)
```

The exact total-debt identity is

```text
D(tau_n)-D(sigma_n) = -g_n+T_n.                    (4.5)
```

### Theorem 4.1 (off-minimum late-release fork)

After subselection, at least one of the following holds.

1. **Fixed actual descent:**

   ```text
   D(tau_n) <= D(sigma_n)-Gamma*q/4                 (4.6)
   ```

   for every sufficiently large selected `n`.

2. **Fixed opposite-face transfer:** there is one fixed `b!=a` such that

   ```text
   d_b(tau_n)-d_b(sigma_n) > Gamma*q/12             (4.7)
   ```

   for every sufficiently large selected `n`.  Applying the sharp
   finite-support decoder gives either

   ```text
   prescribed `{a}` atom > Gamma*q/24,              (4.8)
   ```

   or a same-deviation atom on one of
   `{a}`, `{b}`, `{a,b}` of magnitude

   ```text
   > Gamma*q/48.                                    (4.9)
   ```

### Proof

At each sufficiently late index, select arm 1 when

```text
D(tau_n)-D(sigma_n) <= -g_n/2.
```

Then (4.3) gives (4.6).  Otherwise (4.5) gives

```text
T_n > g_n/2 >= Gamma*q/4.
```

One of the three opponents receives more than one third of this sum.  Finite
subselection fixes it as `b`, proving (4.7).  The exact finite-support
dispatch of
`CODEX_MINER__FIN4_LATE_RELEASE_RECTANGLE_THREE_LABEL_BOUNDARY` gives half
of the recipient increase in its prescribed arm and one quarter in its
response arm, which are (4.8)--(4.9). `QED`

The alternatives are inclusive before the displayed convention; the finite
subsequence choice is common to sources, targets, recipient, response time,
and terminal label.

### Corollary 4.2 (the excess cannot hide a larger Never gain)

Let `E=D(y)-D_*` and put

```text
H=s_a*q-E.
```

If `H>0`, the transfer arm is compulsory after weakening constants: there is
a fixed `b!=a` with

```text
d_b(tau_n)-d_b(sigma_n) >= H/6                     (4.10)
```

eventually, and hence either a prescribed `{a}` atom at least `H/12`, or a
same-deviation atom on `{a}`, `{b}`, or `{a,b}` strictly larger than `H/24`.

Indeed, global minimality gives `D(tau_n)>=D_*`.  Together with (4.5),

```text
T_n >= g_n-[D(sigma_n)-D_*].                        (4.11)
```

The right side tends to `s_a*q-E=H`, so it is eventually at least `H/2`.
One of three recipients gets at least `H/6`, and the sharp decoder loses the
same factors two and four as before.

Thus the scalar survivor is not arbitrary off-minimum debt.  It must satisfy

```text
E >= s_a*q >= Gamma*q                               (4.12)
```

unless the source-matched three-label transfer already occurs.  Both `E`
and `q` scale by the same factor on the cap ray before subtracting the fixed
floor `D_*`; this is exactly why (4.12) becomes strongest near a hypothetical
return to the global minimum.

## 5. Why neither output closes the fixed point

The descent in (4.6) is a real one-shot descent at an actual source.  It is
not the cap-port descent and it has a fixed size.  But `tau_n` has player `a`
Quit surely at a finite date, so

```text
Law(tau_n)(Never)=0.                                 (5.1)
```

It therefore leaves the positive-Never cap ray and loses the normalized
Never passport used to select `(y,lambda)`.  There is, however, a cleaner
way to preserve the passport: release only a fixed fraction of player `a`'s
Never law.

### Proposition 5.1 (exact renewable half-release fork)

Let `upsilon_n` replace player `a` in `sigma_n` by the equal stopping-law
mixture of its source law and its late-capped law in `tau_n`.  This is one
literal behavioral strategy.  Exactly half of the old joint-Never event is
moved to singleton `{a}`, so

```text
Law(upsilon_n)(Never)=q_n/2 -> q/2,                 (5.2)
U_a(upsilon_n)-U_a(sigma_n)=s_a*q_n/2,
d_a(upsilon_n)-d_a(sigma_n)=-s_a*q_n/2.             (5.3)
```

Applying the proof of Theorem 4.1 with this partial target gives, after
subselection, either

```text
D(upsilon_n) <= D(sigma_n)-Gamma*q/8,               (5.4)
```

or a fixed recipient `b!=a` with debt increase greater than
`Gamma*q/24`, followed by a prescribed `{a}` atom greater than
`Gamma*q/48` or a same-deviation atom on `{a}`, `{b}`, `{a,b}` greater than
`Gamma*q/96`.

The exact identities (5.2)--(5.3) prove this fork directly.  In particular,
if the full target `tau_n` is in Theorem 4.1's descent arm, the checked
coordinatewise inequality
`quittingTerminalSemanticDebt_stoppingLawMixture_le` also gives the shorter
restoration proof

```text
D(upsilon_n) <= [D(sigma_n)+D(tau_n)]/2
             <= D(sigma_n)-Gamma*q/8.
```

No reward-Lipschitz loss or `M>0` hypothesis is needed.

Thus the descent arm of (5.4) is a genuine regenerated **positive-Never
actual-source family** with a fixed one-step debt drop and an exact retained
Never floor `q/2`.  It can be law-compactified and the same construction can
be invoked again as a numerical late-release fork.  The cap-ray
proportionality, unique-root/strict-slack basin, original maximum-support
rectangle, and its early terminal label are not asserted to survive.

This still is not a well-founded descent.  On repeated half releases the
certified Never floors can be

```text
q, q/2, q/4, ...,
```

and the guaranteed debt drops have the same geometric scale.  Their total
lower bound is finite, so a positive excess can pay the entire infinite
sequence.  More generally, releasing a fraction `h` preserves
`(1-h)q` and pays only an order-`h*q` drop or transfer.  Summing this exact
account cannot extract more than the original singleton-weighted Never
budget `s_a*q`; Corollary 4.2 is the sharp one-shot case in which that budget
already exceeds the excess.  No checked consumer accepts the remaining
geometric real descent as a finite rank or a nonvanishing cumulative-charge
floor.

In the transfer arm, the sharp atom remains source-matched to the actual
off-minimum profile `sigma_n`, but minimum-reference transfer is unavailable:
the excess `E>0` has already been spent in (4.5).  No maximum-support
contradiction follows, and the late-release row is a unilateral complete-law
replacement rather than an exact Nash--Bellman root.

In particular, reversing the rectangle leg is not a cap-prefix repair.
Every exact cap prefix scales the whole debt vector by one common survival
factor.  A support-entering late-release corner cannot be the exact cap
prefix of its minimum predecessor, and a reverse corner can be an exact cap
prefix only if its entire debt vector is a common scalar multiple of the
tail debt vector.  The reviewed rectangle supplies no such proportionality.

## 6. Tight boundary and nonattainment audit

If `kappa=0`, at least one player satisfies the literal equality (Tight).
Uniqueness of all Continue at the exact point remains valid, but the strict
linear-defect neighborhood theorem no longer applies.  Small absorbing exact
roots at nearby cap vectors are not excluded.  This is a genuine boundary,
not a missing epsilon in Theorem 3.1.

The positive joint law in (1.1) does not imply that `y` is behaviorally
attained.  Write `p_{i,n}` for player `i`'s marginal Never probability in
`sigma_n`.  Independence gives `q_n=product_i p_{i,n}` and hence
`p_{i,n}>=q_n`; every marginal is therefore eventually at least `q/2`.
After selecting a compact marginal-law subsequence, each limiting clock has
positive Never mass and lies in the all-nonproper compact-law arm.  The
checked opponent-tight/two-proper realization theorem deliberately does not
consume that arm.  Common-quantile compression produces better actual
approximants; it does not identify one profile whose unrestricted cap is
exactly `y.2`.

If `y` happens to be attained and `kappa>0`, Theorem 3.1 simply gives one
literal actual off-minimum inert source carrying the terminal-gap paid row.
That object is still compatible with the maintained inert obstruction.

## 7. Source and novelty audit

Checked declarations/files inspected:

- `exists_open_linearAbsorptionDefect_of_compact_strictAllContinue` in
  `UniformEquilibrium/Quitting/Root/StrictAllContinueBasinLinearAbsorptionDefect.lean`;
- `isZeroQuittingRootNash_allContinue_iff_singleton_le` and
  `quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `quittingTerminalSemanticDebt_stoppingLawMixture_le` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`;
- `quittingQuantileClockCompressedProfile` and
  `hasEscapeAwareQuantileClockCompressionAtRewardBound` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`, together with
  the outcome coupling in `Research/Quitting/EscapeAwareQuantileClockCollision.lean`;
- `QuittingTerminalExploitabilityWitness.exists_terminalGap_le_soloReward`;
- the exact finite late-cap identities and sharp decoder recorded and
  reviewed in
  `CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY` and
  `CODEX_MINER__FIN4_LATE_RELEASE_RECTANGLE_THREE_LABEL_BOUNDARY`; and
- `quittingTerminalSemanticPair_eq_of_opponentTight_lawLimit` and the
  two-proper/nonattainment boundary in
  `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`.

The strict actualizer conclusion is not the checked minimum-fiber inert
theorem: its center is the newly selected **off-minimum** cap-ray point.  The
late-release fork also differs from the minimum-source transfer theorem by
retaining the excess term exactly instead of discarding it.

Closest no-go results inspected:

- `CODEX_RAMSEY__RETAINED_RECTANGLE_PLATEAU_CAP_COMPATIBILITY_BARRIER` and
  `CODEX_RAMSEY__FIN4_DOUBLE_INERT_LAW_BRIDGE_PLATEAU_SEPARATION` show local
  compatibility of marked laws with a unique all-Continue root, but their
  regressions have `D_*=0`;
- `CODEX_EULER__POSITIVE_MINIMUM_FINITE_SPLICE_INERT_BOUNDARY` regenerates
  inert sources near the minimum but does not treat an off-minimum
  positive-Never unique-root point; and
- Proposition 6AL of
  `CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR` needs an
  observer-deleted endpoint reach tending to zero **in addition to** the two
  near-killed source labels required by 6AJ--6AK.  The sure finite late cap
  can supply the extra endpoint clock if the graft cutoff is taken after the
  release.  It cannot supply the base hypothesis: positive joint Never gives
  a positive product of all source marginal Never masses, so neither of the
  two fixed source labels is near-killed at a cutoff beyond the finite
  support.  Thus the infinite graft is still unavailable here, but the
  missing field is source-side two-label killing, not the endpoint clock.

No inspected declaration consumes (Tight), the strict actual inert source,
or the off-ray descent/transfer fork into a uniform payoff.

## 8. Requested review and next exact question

Please check:

1. application of the strict-basin linear-defect theorem to the singleton
   compact set `{y.2}`;
2. iteration from uniqueness of the exact root to literal inertness of every
   cap prefix at the actualizers;
3. constants and strict/non-strict choices in (4.6)--(4.9);
4. the all-nonproper nonattainment wording; and
5. the claim that the late cap can supply 6AL's endpoint clock but not
   6AJ--6AK's two-near-killed source hypothesis.

The next conjecture-facing question is now precise: does the Fin4 hard
residual eliminate the singleton-tight unique-root boundary, or can the
strict off-minimum inert actualizers' fixed late-release descent be returned
to a positive-Never passport with a nonvanishing renewal floor?  Without one
of those implications, the cap-ray branch remains unconsumed.
