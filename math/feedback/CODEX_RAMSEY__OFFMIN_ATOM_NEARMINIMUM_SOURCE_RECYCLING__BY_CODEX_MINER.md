# Independent fixed-weight delta audit of off-minimum atom recycling

Reviewer: **CODEX_MINER**

Source:
[`CODEX_RAMSEY__OFFMIN_ATOM_NEARMINIMUM_SOURCE_RECYCLING.md`](../notes/CODEX_RAMSEY__OFFMIN_ATOM_NEARMINIMUM_SOURCE_RECYCLING.md)

Verdict: **PASS for the fixed-weight strengthening; internal only.**  A fixed
positive graft weight really does produce a nonvanishing marked-atom source
packet.  Convergence of the source excess to zero is not needed for the
near-minimum all-Continue freeze, the arbitrary-profile paid-port producer,
the global-retention half reset, or the generic endpoint-recipient atom
decoder.  It is needed by the presently available minimum-fiber rectangle,
tangent, and causal-law consumers.  Thus the fixed-weight correction removes
the scale objection but does not yet give an accepted `FIN4_BT` consumer.

## 1. Fixed-weight theorem checked

Let `epsilon_freeze>0` be the radius returned by
`exists_pos_nearMinimum_capNash_eq_allContinue_radius`, let `Gamma>0` be the
terminal gap, and let `M>0` bound the reward table.  Put

```text
delta = min(epsilon_freeze, Gamma/8).
```

Choose one fixed `lambda in (0,1)` with

```text
56*M*lambda < delta.
```

For any sufficiently near-minimum actual profile `pi`, independently graft
the four complete marginal stopping laws of the fixed atom profile `eta`
with weight `lambda`, obtaining `rho=rho(pi,eta,lambda)`.  Choose `pi` close
enough that

```text
D(pi)-D_* < delta-56*M*lambda.
```

The reviewed coupling estimate and global minimality give

```text
0 <= e:=D(rho)-D_* < delta,                         (1.1)
StageMass(rho,t,S) >= lambda^4*m.                   (1.2)
```

Hence every exact cap root at `rho` is literally all Continue.  The terminal
gap still gives a debtor `w` with `d_w(rho)>=Gamma`.  In
`exists_halfStoppingLawReset_nearMinimum_transfer_and_globalRetention`, use
the pointwise error `epsilon=e`: since every carrier candidate has total debt
at least `D_*`, its `hnear` premise is immediate.  The returned half reset
`chi` then satisfies

```text
gain >= Gamma/4,
sum_(j!=w) Delta d_j >= Gamma/4-e > Gamma/8,
StageMass(chi,t,S) >= lambda^4*m/2.                 (1.3)
```

In `Fin 4`, some recipient has debt rise greater than `Gamma/24`; finite
label selection fixes `w` and the recipient along a source sequence.  The
full-`Gamma` actual-profile paid port is also based at the same literal
source `rho`.  No step above uses `e -> 0`.

The strict inequalities can of course be weakened to the non-strict
constants printed in the source note.  The source note's `8M/6M/14M/56M`
coupling constants and the `lambda^4` latent-branch event were independently
rechecked and are unchanged.

## 2. Consumers which do not need vanishing excess

The fixed packet may be used immediately by:

1. the cap-freezing theorem, whose premise is only the open-tube inequality
   `D(rho)<=D_*+epsilon_freeze`;
2. `HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort`, which is
   arbitrary-profile and has no near-minimum premise;
3. the near-minimum global-retention half reset, whose error is a displayed
   pointwise number rather than a convergent sequence; and
4. `hasQuittingEndpointDebtRecipientAtom_of_pos`, after selecting the positive
   recipient from (1.3).  This last adapter gives the familiar inclusive
   prescribed-payoff-atom versus same-deviation-rectangle alternative.

Consequently fixed `lambda` is the correct formulation whenever the desired
output is a **nonvanishing actual source packet**.  Delaying `eta` behind an
arbitrarily long all-Continue cap word also gives a fixed marked suffix atom:
literal all-Continue prefixing preserves the semantic pair and law, while the
atom is merely shifted.  This is a genuine causal source, not an off-minimum
carrier annotation.

## 3. Where convergence is still essential

The fixed packet does not meet the hypotheses of the three proposed exact
consumers.

### 3.1 Minimum-fiber support rectangle

`quittingTerminalSemanticDebt_stoppingLawMixture_chordGap_le_nearMinimum`
bounds each coordinate chord gap by

```text
epsilon + theta*(D(endpoint)-D(source)).             (3.1)
```

The support-union theorem in
`CODEX_MINER__POSITIVE_NEVER_MAX_SUPPORT_RECTANGLE_EXCURSION` passes (3.1) to
zero on all three literal edges.  A fixed positive `e` leaves a fixed
coordinate error.  Because positive support is discontinuous at zero, that
estimate gives neither the exact affine debt formula nor the support union.
Thus maximal support cannot be invoked from the fixed tube alone.

### 3.2 Tangent and full-replacement support arguments

The tangent/response-square arguments normalize vanishing chord errors at a
scale tending to zero, and the no-new-support conclusions use actual limits
on the global minimum fiber.  A fixed `O(lambda)` source excess is not an
`o(scale)` error and may pay for a new positive coordinate.  The fixed atom
does not repair that normalization.

### 3.3 Minimum-law causalization

`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` assumes a
joint semantic/law carrier point satisfying the literal equality

```text
D(point.semantic)=quittingTerminalDebtSumInf reward.
```

The fixed graft is only known to lie in the open freeze tube.  Its cluster
need not be a minimum-law point, so its marked atom cannot be substituted for
the theorem's minimum-law atom.  The all-Continue word does not change this:
it exactly preserves the same off-minimum semantic pair.

## 4. Exact surviving seam

At fixed weight the imported atom no longer vanishes, but its coalition,
owner, and date are unrelated to the terminal-gap paid row, the half-reset
mover, and the positive debt recipient.  The independent marginal graft also
introduces the `2^4-2` cross-branch laws, so it does not retain the original
off-minimum endpoint's loss-free toggle or rectangle sign.

For a nonsingleton imported atom the reviewed macroscopic causal dispatch can
be applied at fixed scale, but it returns the already maintained tail
excursion versus reached-gain/transfer split.  A singleton imported atom is
exactly the outsider-regularization boundary recorded in
`FIN4_BT_QUESTION`: no positive prescribed sign follows without a
conditional-mass threshold.  The generic endpoint-recipient decoder likewise
stops at the prescribed-atom/rectangle seam.

There is also a sharp mismatch in the available quantitative bounds.  If the
imported nonsingleton stage mass is bounded only by

```text
alpha >= lambda^4*m,
```

then the macroscopic reached-gain lower bound is of order

```text
g0 = alpha^2*D_*/(2*4)
   >= lambda^8*m^2*D_*/8.                           (4.1)
```

The source's certified excess toll is only `e<=56*M*lambda+o(1)`.  To infer a
positive opposite-face transfer from `g0-e` using just these displayed
bounds would require

```text
448*M < lambda^7*m^2*D_*.
```

But `lambda,m<=1`, while bounded rewards give `D_*<=8*M` in `Fin 4` (each
unrestricted debt is at most the payoff-range diameter `2*M`).  Hence that
inequality cannot follow; indeed its right side is at most `8*M`.  This does
not refute a table-specific cancellation which makes the true graft excess
much smaller.  It proves that the current universal coupling plus collision
constants cannot make the fixed atom pay for its own source error.

The half-reset transfer avoids this eighth-order loss because its gain is
`Gamma/4`, independent of the imported atom.  Precisely for that reason its
mover/recipient event is not aligned with the imported atom event.  The two
mechanisms solve opposite quantitative problems and do not compose through a
currently named interface.

So fixed `lambda` should replace the source note's assertion that atom
vanishing is the decisive obstruction.  The decisive remaining obstruction
is **event/sign alignment**, not atom scale.  This strengthens the producer,
but reproduces a class of outputs which `FIN4_BT_QUESTION` explicitly says is
not yet an answer.

## 5. Sources checked

- `TerminalSemanticCapNashNearMinimum.lean`:
  `exists_pos_nearMinimum_capNash_eq_allContinue_radius`;
- `StoppingLaw/TerminalSemanticStoppingLawGlobalRetention.lean`:
  `exists_halfStoppingLawReset_nearMinimum_transfer_and_globalRetention`;
- `StoppingLaw/TerminalSemanticStoppingLawMinimumFiberAffine.lean`:
  `quittingTerminalSemanticDebt_stoppingLawMixture_chordGap_le_nearMinimum`;
- `TerminalSemanticLawCarrierCausalization.lean`:
  `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom`;
- `StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`: the
  arbitrary-profile paid-port producer; and
- the reviewed macroscopic collision and maximum-support rectangle notes.

Recommendation: incorporate the fixed-weight statement as the primary source
packet and retain the vanishing-weight version only for genuine return to the
minimum fiber.  Do not export without a new alignment consumer.

## Delta review of the fixed-weight rewrite

**PASS.**  The revised source now makes fixed `lambda` primary and treats
`lambda_n -> 0` only as one sufficient route back to the exact minimum fiber;
this matches the audit above.  The new endpoint-recipient extraction constants
are exact: a recipient contribution `Gamma/24`, followed by the half-retention
factor and the sixteen-outcome pigeonhole, gives a prescribed atom
`Gamma/768`; the additional rectangle quarter-factor gives `Gamma/1536`.
The inclusive branch/subsequence label fixing is honest.  Crucially, the note
still states that these recipient/terminal labels are not aligned with the
imported singleton or coalition label.  Thus the rewrite strengthens the
fixed-scale producer without claiming the missing signed consumer.
