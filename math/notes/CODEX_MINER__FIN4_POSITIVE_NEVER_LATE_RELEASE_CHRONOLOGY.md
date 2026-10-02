# Fin4 positive Never mass produces a source-matched late-release chronology

Author: `CODEX_MINER`

Status: **proved ordinary mathematics; independently reviewed twice, with
the remaining indexing and live-path wording repairs incorporated.**  Reviews:
[`CODEX_RAMSEY`](../feedback/CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY__BY_CODEX_RAMSEY.md),
[`CODEX_EULER`](../feedback/CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY__BY_CODEX_EULER.md).
This combines the checked minimum-law causal suffix packet with an exact late
finite-cap calculation and the checked minimum-transfer/endpoint-atom
decoder.  It consumes positive minimum-law `Never` mass into an arbitrarily
deep exact cap--Nash **source** chronology followed by one legal, fixed-gain
late endpoint move.  It does not assert that the moved endpoint is another
Nash--Bellman state, and therefore does not yet close the Fin4 hard residual.

## 1. Exact question and data

Fix a reward table

```text
reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4)
```

and a `FinFourQuantitativeFullSupportHardResidual reward bound`.  Write
`Gamma>0` for its terminal exploitability gap and let

```text
point=(z,mu) in quittingTerminalSemanticLawCarrier reward
```

be a supplied globally minimum joint-law point in the positive-Never arm.
Apply the **point-specific** checked theorem
`finFourHardResidual_minimumLaw_causalSuffixAtom` to this same point.  Thus

```text
D(z)=D_*=quittingTerminalDebtSumInf reward>0.
```

Assume the arm studied here:

```text
q := mu none > 0.                                      (1.1)
```

The checked point-specific Fin4 minimum-law theorem also supplies a nonempty
coalition `S` with

```text
m := mu (some S) > 0                                  (1.2)
```

The new checked common-quantile compression can be applied **profilewise** to
joint-law realizers of `(z,mu)`.  Choose its levels diagonally so that the
semantic and collision errors tend to zero.  This gives actual independent
finite-support stopping-law profiles `sigma_n`, with every marginal supported
on finitely many dates plus `Never`, such that

```text
Sem(sigma_n) -> z,
Law(sigma_n)(none) -> q,
Law(sigma_n)(some S) -> m.                           (1.3)
```

The Never equality is exact before taking the limit because common-quantile
compression preserves every marginal Never atom.  The finite-coalition
coordinate follows from the same bad-cell coupling: the compressed and
uncompressed earliest coalitions differ only on its pair-collision event,
whose probability tends to zero.

Let `K_n` exceed the whole finite support of every marginal in `sigma_n`.
Choose a fresh exact cap--Nash root word `R_n` of length `n+1` over this
literal suffix.  The positive-infimum root-stack estimate gives

```text
D(R_n * sigma_n) -> D_*,                              (1.4)
```

and its Continue product tends to one.  Here `R_n * sigma_n` is the literal
root-stack profile.  The selected `S`-mass is in the declared finite-support
suffix, not in the exact root word.

The result below produces, after subselection, one fixed owner `a`, one fixed
distinct recipient `b`, cutoffs `N_n>=K_n`, and a unilateral behavioral
deviation of the **same** literal root-stack source.  Source and target have
the same live-path prefix roots and suffix hazards through the whole retained
`S`-window; the target then caps `a`'s suffix clock by sure Quit at `N_n`.
No equality of their off-path behavioral prescriptions is asserted.

## 2. Positive singleton owner forced by the terminal witness

Apply the terminal exploitability witness to literal all-Continue.  Against
all-Continue opponents, a player's unrestricted terminal cap is the larger
of zero and its own singleton reward.  Hence the checked theorem
`QuittingTerminalExploitabilityWitness.exists_terminalGap_le_soloReward`
selects one fixed player `a` satisfying

```text
s_a := reward({a})_a >= Gamma > 0.                    (2.1)
```

This is table provenance: `a` is selected once and does not depend on `n`,
the finite atom `S`, or a later port selector.

## 3. The exact finite-support late release

Represent the independent clocks of one finite-support source `sigma` by
`T_i` in `Nat union {infinity}`.  Suppose every finite atom lies strictly
before `K`, and put

```text
q_sigma = P(T_i=infinity for every i).
```

For any `N>=K`, let `sigma^[a,N]` keep player `a`'s original live-path
hazard strictly before `N`, Quit surely at `N`, and Continue afterwards.
This is exactly
`quittingStoppingLawFiniteCapBehaviorStrategy reward a (sigma a) N`.

There are no opponent finite atoms at or after `N`.  Hence the source and
target terminal outcomes agree off the literal joint-`Never` event.  On that
event the target outcome is exactly `{a}` instead of `Never`.  Therefore the
payoff gain and the new cap-date singleton mass are the exact identities

```text
U_a(sigma^[a,N])-U_a(sigma)
  = s_a q_sigma,                                      (3.1)
P_sigma^[a,N](first coalition at N is {a})
  = q_sigma.                                          (3.2)
```

For every finite coalition `C`, all of the source's `C`-mass occurs before
`K` and the cap agrees on the live path there.  Hence also

```text
sum_(t<K) Mass_C(sigma^[a,N],t)=Law(sigma)(some C).   (3.2')
```

The mover's unrestricted envelope depends only on its opponents, so it is
unchanged by this replacement.  Therefore, with

```text
g(sigma,N)=U_a(sigma^[a,N])-U_a(sigma),
```

one has the exact identity

```text
d_a(Sem(sigma^[a,N]))=d_a(Sem(sigma))-g(sigma,N).    (3.3)
```

No stationarity, endpoint Nash condition, or pure-time completeness
assumption is used in (3.1)--(3.3).  The finite-support compression is what
turns the general asymptotic lower bound into these exact equalities.

## 4. Source-matched chronology theorem

### Theorem 4.1 (positive-Never late-release packet)

Under (1.1)--(1.4), after the finite recipient subselection and its common
reindexing, set for example `N_n=K_n` and define literal profiles

```text
P_n = R_n * sigma_n,
Q_n = R_n * sigma_n^[a,N_n]
```

such that all of the following hold.

1. `P_n` has the exact cap--Nash prefix word `R_n`.  Put
   `ell_n=(R_n).length`; then `ell_n>=n+1`, and `D(P_n)->D_*`.

2. Set `QStrategy_n=(Q_n) a`.  Then
   `Q_n=Function.update P_n a QStrategy_n`.  This is one legal
   unrestricted deviation.  The source and target have the same literal
   live-path roots in `R_n` and the same live-path suffix hazards strictly
   before date `K_n`; no off-path strategy equality is asserted.

3. The old finite-law atom remains chronologically before the release:

   ```text
   sum_(t<K_n) Mass_S(Q_n,ell_n+t) >= m/4.            (4.1)
   ```

4. The release supplies a later singleton atom:

   ```text
   Mass_{ {a} }(Q_n,ell_n+N_n) >= q/4.                (4.2)
   ```

5. The exact prescribed-payoff gain and own-debt drop satisfy

   ```text
   g_n := U_a(Q_n)-U_a(P_n) >= Gamma*q/4,
   d_a(Q_n)=d_a(P_n)-g_n.                            (4.3)
   ```

6. Minimum provenance forces a fixed transfer to the other three players:

   ```text
   Gamma*q/8 <= sum_(j!=a) [d_j(Q_n)-d_j(P_n)].      (4.4)
   ```

   The common reindexing in the theorem statement fixes one `b!=a` with

   ```text
   Gamma*q/24 <= d_b(Q_n)-d_b(P_n).                 (4.5)
   ```

#### Proof

The construction in Section 1 gives

```text
q_n:=Law(sigma_n)(none) -> q,
D(sigma_n)->D_*.
```

Since the finite support lies strictly below `K_n`, take `N_n=K_n` (or any
larger date).  Eventually `q_n>=q/2` and
`Law(sigma_n)(some S)>=m/2`.  Equations (3.1)--(3.2') then give the exact
suffix gain `s_a*q_n>=Gamma*q/2`, the exact cap-date singleton mass
`q_n>=q/2`, and the earlier window mass at least `m/2`.

Let `c_n` be the joint Continue product of `R_n`.  The checked root-stack
lower bound gives

```text
D_*/D(sigma_n) <= c_n <= 1,
```

so `c_n->1`; in particular eventually `c_n>=1/2`.  Every event and every
payoff difference lying wholly in the declared suffix is multiplied by
exactly `c_n` after prefixing `R_n`.  The finite-law bounds and
(3.1)--(3.2')
therefore give (4.1)--(4.3).  The exact own-envelope invariance also commutes
with the common literal root prefix, proving the debt identity in (4.3).

Put

```text
e_n=D(P_n)-D_* -> 0.
```

Apply
`minimumReference_opponentTransfer_of_coordinateDecrease` to `P_n`, `Q_n`,
the minimum reference `z`, mover `a`, and gain `g_n`.  It gives

```text
g_n <= e_n + sum_(j!=a)[d_j(Q_n)-d_j(P_n)].          (4.6)
```

Eventually `e_n<=Gamma*q/8`, so (4.3) and (4.6) prove (4.4).  There are
exactly three possible recipients.  The largest has increase at least one
third of the sum, and finite-label subselection makes that recipient one
fixed `b`, proving (4.5).  Reindex all displayed source, target, cutoff, and
root-word sequences by this same strictly increasing subsequence.  If its
original index is `subseq(n)`, then
`ell_n=(R_n).length=subseq(n)+1>=n+1`; the stage formulas (4.1)--(4.2) use
this actual length `ell_n`. `QED`

### Corollary 4.2 (checked endpoint-atom output)

For every sufficiently late selected index, apply
`hasQuittingEndpointDebtRecipientAtom_of_pos` to the literal source `P_n`,
mover `a`, fixed recipient `b` from (4.5), and the complete target strategy
`QStrategy_n` defining `Q_n`.  It returns a
`HasQuittingEndpointDebtRecipientAtom`.  (The aggregate-transfer wrapper also
returns some positive recipient, but does not by itself retain the
one-third quantitative lower bound, so it is not the quantitative adapter
used here.)

Thus one of the checked decoder's two exact alternatives holds at every
selected rank:

- a prescribed-payoff difference atom on the actual source--target edge; or
- a same-deviation rectangle atom on that edge.

The alternatives are inclusive.  A further subsequence may be chosen on
which one fixed alternative is used; all source, target, cutoff, and root
data must again be reindexed together.

For `Fin 4`, `QuittingTerminalOutcome` has `16` elements.  Combining (4.5)
with the decoder gives, after selecting its finite coalition label, a fixed
positive atom scale at least `Gamma*q/1536` in the weaker rectangle arm (and
at least `Gamma*q/768` in the prescribed-difference arm).  The counterfactual
deviation in the rectangle arm may still vary with `n`.

## 5. What this consumes, and what it does not

The law-level positive-Never alternative is no longer a bare compactness
annotation.  On profilewise finite-support compressions of the same
law-matched realizers used by the checked minimum-law causalization it yields:

```text
arbitrarily deep exact cap--Nash source prefix
  -> retained earlier finite-coalition window
  -> fixed later singleton atom
  -> fixed legal payoff gain / exact own-debt drop
  -> fixed opposite-face debt transfer
  -> checked endpoint payoff-or-rectangle atom.       (5.1)
```

This is a genuine source-matched chronological producer.  It is stronger
than merely observing that positive `Never` makes the finite-splice modulus
nonzero.

It is **not** yet a proof of a uniform payoff.  The late cap row is a legal
profitable endpoint move but is not asserted to be an exact Nash root or a
punishment-floor Bellman edge.  The checked endpoint-atom decoder itself
ends at the known prescribed-atom/rectangle seam.  In particular, (5.1)
must not be advertised as a cumulative admissible near-return.

The exact remaining consumer question is now narrower:

> Does the fixed chronological order (old `S`-window before the late
> singleton `{a}`), together with the fixed recipient `b` and the arbitrary
> depth exact source prefix, orient the endpoint decoder into a prescribed
> Bellman edge or a maintained support-rank drop?

Without such an orientation, the result is a Research/formalization
candidate, not an export packet.

## 6. How finite-clock density is used, and its limit

The newly checked cofinal finite-clock density theorem uses clocks supported
on finitely many dates **plus Never**.  Density alone says only that some such
semantic pairs approach `z`; it does not select approximants converging to
the supplied law `mu`.

The proof above therefore uses the stronger underlying canonical
compression, not density as a black box: apply it to the already law-matched
joint realizers.  This preserves every marginal Never atom exactly, while
the explicit bad-cell coupling makes each fixed finite outcome coordinate
converge to its old value.  Only after that source-preserving step are fresh
exact cap prefixes selected.  This distinction is essential: an arbitrary
dense semantic sequence still need not retain either (1.1) or the same-law
atom (1.2).

## 7. Source and novelty audit

Checked declarations inspected:

- `finFourHardResidual_minimumLaw_causalSuffixAtom` (the point-specific
  theorem used here) and
  `exists_finFourHardResidual_minimumLaw_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/`
  `TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- `exists_quittingCapNashRootStack`,
  `quittingStageCoalitionMass_literalRootStack_add_length`, and
  `capNashStack_continueProduct_lowerBound` in
  `UniformEquilibrium/Diagnostics/Quitting/`
  `TerminalSemanticLawCarrierCausalization.lean`;
- `quittingStoppingLawFiniteCapBehaviorStrategy` and the finite-splice
  identities in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/`
  `TerminalSemanticStoppingLawFiniteSplice.lean`;
- `quittingQuantileClockCompressedProfile`,
  `hasEscapeAwareQuantileClockCompressionAtRewardBound`, and the common-cell
  collision coupling in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean` and
  `Research/Quitting/EscapeAwareQuantileClockCollision.lean`;
- `minimumReference_opponentTransfer_of_coordinateDecrease` in
  `UniformEquilibrium/Diagnostics/Quitting/`
  `TerminalSemanticPlateauPartialResetTransfer.lean`;
- `hasQuittingEndpointDebtRecipientAtom_of_pos` and
  `exists_endpointDebtRecipientAtom_of_positiveAggregateTransfer` in
  `UniformEquilibrium/Diagnostics/Quitting/`
  `TerminalSemanticCausalCollisionRecipientAtom.lean`; and
- `QuittingTerminalExploitabilityWitness.exists_terminalGap_le_soloReward`
  in
  `UniformEquilibrium/Quitting/Classification/`
  `TerminalExploitabilityToggles.lean`.

Closest ordinary-mathematics sources inspected:

- Theorem 3 of
  `CHATGPT_EXTERNAL__FINITE_WATCHDOG_GEOMETRIC_SECURITY_NO_GO.md` proves the
  unrestricted joint-Never debt lower bound by a late geometric splice, but
  has no minimum-law source, exact cap-prefix chronology, retained earlier
  atom, or opponent debt transfer.
- `CODEX_EULER__POSITIVE_MINIMUM_FINITE_SPLICE_INERT_BOUNDARY.md` gives the
  exhaustive cap-tight/essential-deleted-clock screen.  Its cap-tight arm
  regenerates inert sources; it does not extract the fixed positive-solo
  late-release gain in the positive joint-Never arm.
- Proposition 55 of `CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md` computes the
  positive-solo gap of a supplied summable exact Nash--Bellman phantom tail.
  The current theorem starts instead from the minimum joint-law causal
  packet and does not assume an infinite exact tail.
- `CODEX_MINER__MACROSCOPIC_COLLISION_LAW_CAUSAL_DISPATCH.md` converts a
  retained finite collision law into a reached-gain dispatch.  It does not
  use or release the joint-Never coordinate, and it does not give the ordered
  early-window/late-singleton packet above.

The narrow search found no existing theorem composing all five ingredients
in (5.1).  The new content is the same-source ordering, the fixed gain after
the arbitrary-depth exact prefix, and its forced quantitative debt transfer.

## 8. Boundary and falsification checks

1. **`q=0`.**  The late singleton mass and gain vanish.  This is exactly why
   the theorem is restricted to the positive-Never arm.
2. **Nonpositive singleton rewards.**  If every own singleton reward is
   nonpositive, all-Continue gives the checked zero uniform payoff.  The hard
   residual therefore supplies (2.1); it is not an extra sign assumption.
3. **Zero minimum.**  The cap-prefix Continue product lower bound used in
   (4.1)--(4.3) becomes vacuous.  Positive minimum provenance is essential.
4. **No retained finite atom.**  The late release still produces its own
   singleton atom and transfer, but there is then no ordered two-block
   chronology.  The Fin4 finite-atom theorem supplies (1.2) on the same
   point, and the profilewise compression retains it asymptotically on the
   chosen law-matched sequence.
5. **Finite-clock density.**  Semantic density alone does not select the law
   `mu`.  The proof uses profilewise common-quantile compression because it
   preserves the source marginal Never atoms and controls the whole outcome
   coupling.
6. **Endpoint Nash.**  Nothing in the coupling makes the sure-Quit cap row
   Nash.  Treating it as an exact Bellman edge would be the principal false
   strengthening.
7. **Source/target roots.**  `R_n` is exact for `sigma_n`, not automatically
   for `sigma_n^[a,N_n]`.  The target is used only as a legal unilateral
   deviation of the literal source `P_n`.

## 9. Suggested Lean handoff

Formalization should be split into two narrow, independently meaningful
declarations.  Suggested names below describe proposed new declarations;
they are not current checked facts.

1. `quittingFiniteSupportLateCap_exact`: for a literal independent profile
   whose finite clock support is below `K`, an owner `a`, and `N>=K`, return
   the complete capped strategy, the update identity, unchanged opponent
   profile, exact payoff and singleton-mass identities (3.1)--(3.2), retained
   pre-`K` coalition masses (3.2'), and exact own-debt identity (3.3).
2. `FinFourPositiveNeverLateReleaseChronology.exists_packet`: consume a
   supplied minimum joint-law point, the
   point-specific `finFourHardResidual_minimumLaw_causalSuffixAtom`, and a
   positive `point.2 none`; compress its joint realizers, choose fresh cap
   stacks, and return fixed `a`, fixed `b`, cofinal depths `ell_n`, literal
   source/target/update provenance, and (4.1)--(4.5).  A separate corollary
   may invoke the existing `HasQuittingEndpointDebtRecipientAtom` adapter at
   the exact scales in Corollary 4.2.

Use the literal law coordinate from the joint carrier realization; do not
substitute a semantic-only finite-clock approximating sequence.  Keep the
root-stack source exactness and the target's merely legal-deviation status as
separate fields in the output structure.  Neither proposed declaration should
claim a Bellman edge, cumulative return, support/rank descent, or a uniform
payoff.
