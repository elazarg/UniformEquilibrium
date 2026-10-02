# Review of the soft-cycle tropical LCP and two-Never escape

Reviewer: `CODEX_SNELL`

Frozen note reviewed:
`notes/CODEX_SPINOZA__SOFT_CYCLE_TROPICAL_LCP_AND_TWO_NEVER_ESCAPE.md`

SHA-256:

```text
a48d2ce92abadca6246228933722fe944effd304571337ca2d5137660b70b79d
```

## Verdict

**PASS with one source/terminology correction.**  The first-order law,
common-clearance complementarity, unrestricted pure-time cap limit,
period-one singleton-arm elimination, and two fixed positive Never debtors
are mathematically sound.  The note should not let the phrase “full normal
core” silently mean “every player is punishment-normal.”  These are distinct
definitions in the repository.  The needed implication is the separately
checked theorem
`all_punishmentNormal_of_normalCore_eq_univ` in
`Diagnostics/Quitting/Collision/SingletonPacket/NormalCorePunishmentNormal.lean`.
Adding that declaration to the inspected sources and citing it in Theorem
4.1 resolves the issue; no mathematical hypothesis needs to change.

## Independent check of the first-order limit

Write `h_n=sum_(t,i) x_(n,t,i)`.  Uniformly over a varying number of phases,
the total probability of two selected Quit coordinates in one traversal is
at most a constant times `h_n^2`; the same estimate controls the error in
each pre-singleton survival factor.  Hence one-period absorption is
`h_n+O(h_n^2)` and the normalized first-coalition law tends to the singleton
lottery `lambda`.  Exact Bellman return identifies its payoff with the phase
zero value, giving

```text
v=sum_k lambda_k r({k}).
```

The cyclic value oscillation is `O(M h_n)`.  Therefore, uniformly in phase,

```text
C_(n,t,i)-Q_(n,t,i) -> v_i-r_i({i})=(A lambda)_i=:m_i.
```

Because every `x_(n,t,i)<=h_n->0`, the exact log-odds equation makes these
margins positive eventually.  If `m_k>=m_l+delta`, comparing the odds at any
two phases gives

```text
x_(n,t,k)/x_(n,u,l)
  <=2 exp(-delta/(2 theta_n)).
```

After summing phases the extra factor is `H_n`.  The displayed assumption is
enough because `theta_n log H_n <= H_n epsilon_n/log 2 -> 0`, while
`theta_n->0`.  Thus a positive limiting owner mass can occur only at a
minimizer of `m`.  This proves the common level `kappa>=0`.  On the eventual
Continue-better side the exact binary endpoint-regret summand is `x d`, so
division by `h_n` gives `E_n/h_n->kappa` with the asserted orientation.

Scaling `z=lambda/kappa` when `kappa>0` gives exactly
`-1+Az>=0` and complementary slackness.  Conversely `kappa=0` is exactly the
homogeneous simplex relation.  The matrix convention in the note agrees
with `normalizedSoloMatrix_eq_soloReward_sub`.

## Independent check of unrestricted caps

For fixed `i` with `lambda_i<1`, delete its hazards.  Opponent absorption per
period is

```text
b_(n,i)=h_n(1-lambda_i)+o(h_n),
```

and its conditional singleton-owner law tends to
`lambda_k/(1-lambda_i)`.  A pure Quit time `q H_n+t` decomposes exactly into:
absorption in an earlier complete opponent period; survival through those
periods and absorption in the last partial period; or survival to the chosen
Quit.  The partial-period and simultaneous-tie contributions are `O(h_n)`
uniformly in `q,t`.  The complete-period geometric sum introduces no
`q`-fold error: it is an exact convex weight on the one-period conditional
value.  Hence every finite pure-time payoff lies within `o(1)`, uniformly in
the chosen time, of the interval with endpoints `N_i` and `s_i`.

Time zero tends to `s_i`, while literal Never tends to `N_i`.  The checked
pure-time extremality theorem therefore upgrades the bound to arbitrary
behavioral deviations, including escaping clocks and Never.  The affine
identity

```text
N_i-v_i=lambda_i(v_i-s_i)/(1-lambda_i)
       =lambda_i*kappa/(1-lambda_i)
```

then proves the claimed cap and debt limits.  For `lambda_i=0`, `N_i=v_i`
and `s_i<=v_i`, so the zero-debt conclusion is also correctly separated from
the singular `lambda_i=1` case.

## Counterexample-facing positivity of the clearance

There are two clean checked routes to `kappa>0`.

First, `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` supplies
nonhomogeneity on the normal principal matrix, while
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
identifies that core with all four players.  Thus the full normalized matrix
cannot have the homogeneous simplex solution produced when `kappa=0`.

Alternatively, apply
`hasAmbientReturnedBlockRelativeErrorGap_of_fourPlayer_counterexample`
directly to these returned blocks.  Their Bellman error is zero, their total
hazard is `h_n`, and `E_n/h_n->kappa`; the checked positive relative gap
forces `kappa` to be strictly positive.  This route avoids any informal
identification of the principal subtype with the ambient matrix.

A singleton support would give
`kappa=(A lambda)_i=A_ii=0`.  Positive `kappa` therefore forces at least two
support labels.  Every such label has mass strictly between zero and one and
the preceding formula gives a strictly positive limiting Never gain.  After
the one finite-label subsequence already taken, choose any two positive-mass
owners and half the smaller of their two limiting gains; this gives the fixed
players and uniform eventual constant `gamma_0` claimed in (23).

## Period-one singleton arm and compiler audit

Fixing `H=1` is legitimate in the unconditional soft producer.  The positive
terminal exploitability gap selects one debtor `i` whose opponent absorption
tends to zero, so every `x_(n,j)->0` for `j!=i`.  Pass to
`x_(n,i)->p`.  If `p>0`, the stationary terminal law tends to `delta_{\{i\}}`
and the Bellman value tends to the complete singleton payoff vector
`r(\{i\})`.

The soft binary regret tends to zero jointly with the root and tail.  The
closedness statement needed here is exactly
`isεQuittingRootEndpointNash_of_tendsto` in
`Quitting/Bellman/Finite/EndpointNashClosed.lean`; it yields exact endpoint
Nash for the limiting solo root.  This remains valid at the boundary `p=1`:
the solo-cycle compiler assumes only a strictly positive owner hazard, not a
proper one.

For the remaining punishment inequality, use

```text
normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
  + all_punishmentNormal_of_normalCore_eq_univ.
```

The latter concludes
`quittingPunishmentValue reward i <= r_i(\{i\})`.  All hypotheses of
`isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR` are
then literal: positive hazard `p`, exact endpoint Nash against the singleton
payoff vector, and owner punishment individual rationality.  Its conclusion
contradicts no-UE, so `p=0`.  The resulting total hazard vanishes, and the
previous positivity/support argument gives the stated positive common level,
nonsingleton support, and two fixed Never debtors.

## Scope

The output is one source-coherent sequence with two literal deviations and
explicit cap limits.  It is not yet a chronological two-cut packet and does
not claim that the standard LCP solution by itself is a UE producer.  The
moving-period singleton regression is outside Theorem 4.1 because that
theorem deliberately fixes period one.  I found no hidden restriction on
behavioral deviations and no failure at sure Quit or Never.

## Corrected frozen-byte delta

I checked the corrected frozen note at SHA-256

```text
3b53c80a8803c182544e2e919132e7d5ce9d9264924bb7418df8b5886bbeab69.
```

**Exact-hash delta PASS.** The source list now names both
`all_punishmentNormal_of_normalCore_eq_univ` in
`NormalCorePunishmentNormal.lean` and the joint endpoint-Nash closedness
result in `EndpointNashClosed.lean`. The proof of Theorem 4.1 explicitly
distinguishes full recursive normal core from playerwise punishment
normality and applies the former-to-latter bridge before (27). I found no
change to the theorem's hypotheses, cap limits, positivity argument, support
claim, or two-Never conclusion.

## Export-candidate review

I independently checked the frozen export-format candidate
`/tmp/FIN4_PERIOD_ONE_TROPICAL_TWO_NEVER_REDUCTION.md` at SHA-256

```text
7a4fd1f67bab58b3398d6cfb54150b5c90c9feaa32b0283ab293d5ae0e9a3132.
```

**REVISE (one source-path correction; no mathematical objection).**  The
candidate faithfully specializes the reviewed theorem to period one.  In
particular, the positive-hazard endpoint limit remains valid at the boundary
`p=1`; the proof separately invokes the full-normal-core-to-punishment-normal
bridge; the sign in `E_n/h_n -> kappa` agrees with the checked endpoint-regret
orientation; the deterministic-time envelope is uniform over all finite
times and includes literal Never; positive clearance and the zero diagonal
force support size at least two; and two fixed support labels carry positive
Never debt on the same actual source sequence.  All seven Markdown links
resolve relative to the intended `exports/` location, all nine mandatory
headings occur exactly once, TeX delimiters balance, and the control-byte scan
is clean.

The sole required repair is in `Source correspondence`: the cited file

```text
UniformEquilibrium/Quitting/Terminal/BehaviorPureTimeExtremality.lean
```

does not exist.  The named checked theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` is in

```text
UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean.
```

Correcting that source path is sufficient for my exact-byte PASS.  As a
nonblocking provenance improvement, the paired-singleton boundary paragraph
could name `pairedSingletonMatrix_normalCore_eq_univ`,
`pairedSingletonMatrix_standardQ`, and
`pairedSingletonMatrix_noHomogeneous` from
`Quitting/Examples/BlockPair/FourPlayerPairedSingletonLCP.lean`, together
with `periodTwo_no_stationary_exactTerminalNash` and
`periodTwoProfile_isExactTerminalNash` from the corresponding period-two
example files; I independently confirmed those declarations, but the
paragraph's mathematics does not require alteration.

## Corrected export-candidate delta

I checked the repaired staged candidate at SHA-256

```text
6a4e7c3fb5d0e8af44b76e4d4aed8d08365a5c61c7787da808f3877a358eba02.
```

**Exact-hash delta PASS.**  The corrected path
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` occurs
exactly once and the rejected `Quitting/Terminal/` path no longer occurs.
Replacing that one corrected byte string in memory by the old string
reconstructs the previously reviewed SHA-256
`7a4fd1f67bab58b3398d6cfb54150b5c90c9feaa32b0283ab293d5ae0e9a3132`
exactly, proving there is no other byte delta.  The control scan remains
clean and the TeX delimiters remain balanced.  My mathematical PASS therefore
covers this exact corrected candidate.
