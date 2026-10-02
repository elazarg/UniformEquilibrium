# Export-gate audit: paid cap-port trichotomy and inert stall

**Reviewer:** CODEX_EULER  
**Target:**
[`CHATGPT_EXTERNAL__PAID_CAP_PORT_EXACT_TRICHOTOMY_AND_INERT_STALL.md`](../notes/CHATGPT_EXTERNAL__PAID_CAP_PORT_EXACT_TRICHOTOMY_AND_INERT_STALL.md)  
**Verdict:** **MATHEMATICAL CORE PASS; EXPORT GATE REVISE.**  The three-way
case split, the displayed displacement-to-debt bounds, literal inertness, and
the cap-versus-prescribed seam are correct.  The note is not yet a
self-contained export packet, understates a stronger checked debt bound, and
does not prove a logical impossibility theorem for the complete ambient
source interface.  Do not move it to `exports/` until the repairs below are
made and the resulting packet receives a fresh whole-packet gate.

## 1. Claim audited

For a `QuittingPaidCapLiftedSource`, let `x_n` be its checked literal prefix
profiles, let

```text
u_n = U(x_n),  b_n = B(x_n),  d_n = b_n-u_n,
a_n = absorption(q_n),  c_n=1-a_n,
P_N = product_(n<N)c_n,  A=sum_n a_n,
b_n -> b_infinity,  rho=||b_infinity-b_0||_infinity.
```

The note asserts an exhaustive split into:

1. `A>0, rho=0`, giving fixed cumulative charge and cap-payoff return;
2. `rho>0`, giving a quantitative semantic-debt decrement, but no uniform
   well-founded restart rank as `rho` tends to zero; or
3. `A=0`, giving an all-Continue literal stall with the paid row preserved by
   pure-time shifting.

It further identifies the exact obstruction to treating the cap orbit as a
prescribed-payoff orbit: the continuation-option surcharge.

## 2. Source declarations checked

The audit used:

- `quittingCapLiftedPrefixProfile_debt_succ` and
  `quittingCapLiftedPrefixProfile_debt_eq_suffixReach_mul` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`;
- `QuittingPaidCapLiftedSource.minimum_mul_partialAbsorption_le_debtDrop`,
  `absorption_summable`, `nonempty_summableSemanticPort`, and
  `nonempty_summablePort` in the same file;
- the `ShiftedPaidRow` transport results in that file;
- `QuittingPunishmentFloorInfiniteOrbit.toFinitePrefix` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorInfiniteOrbit.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns`
  in
  `UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean`;
- `nonempty_summableChargeSignedTerminalPort_of_displacement` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorSummablePortLabel.lean`;
- `quittingRootLiteralDefect_add_surcharge_eq_capDefect_add_liveDebt` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`;
- `capNash_isZeroNash_at_prescribed_iff_surcharge_eq_liveDebt` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetEndpointSeam.lean`; and
- the all-Continue cap-selection regressions in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticIncidenceDebtRatioRegression.lean`.

The maintained summaries
`formalized/PAID_CAP_LIFTED_SUMMABLE_PORT.md` and
`formalized/CUMULATIVE_CHARGE_NEAR_RETURN_AND_SUMMABLE_PORT.md` already record
most of the source and consumer scope.  Any export must compare itself with
those files explicitly.

## 3. Exact debt and displacement calculation

The one-step checked identity gives

```text
D_(n+1)=c_n D_n,
D_N=P_N D_0.
```

Since every semantic pair in the prefix sequence belongs to the carrier and
`D_*` is its positive global minimum,

```text
D_* <= D_n  and  P_N >= D_*/D_0.
```

The note's survival estimate

```text
P(1+A) <= 1
```

is valid.  It implies

```text
D_0-D_infinity >= D_* A/(1+A).
```

The one-step movement bound `|b_(n+1)-b_n|_infinity<=2M a_n` gives
`rho<=2MA`.  On `rho>0` one necessarily has `M>0`, and monotonicity of
`x/(1+x)` gives exactly the stated valid bound

```text
D_0-D_infinity >= D_* rho/(2M+rho).
```

I found no sign or denominator error.

There is, however, a stronger already checked estimate which the note must
not omit in a novelty audit.  Passing
`minimum_mul_partialAbsorption_le_debtDrop` to the limit yields

```text
D_* A <= D_0-D_infinity.                              (S1)
```

Consequently, for `rho>0`,

```text
D_0-D_infinity >= D_* rho/(2M).                       (S2)
```

The weaker displayed constants remain true, but a packet titled “exact” must
state (S1)--(S2), or explain why it intentionally retains the weaker
survival-only calculation.  This strengthening still does not create a
well-founded restart rank: decrements proportional to a sequence
`rho_k -> 0` may be summable.

## 4. Exhaustiveness and the charged-return arm

Absorption masses are nonnegative and summable in the cap-lifted source, so
`A` is a finite nonnegative real.  Also `rho>=0`, and `rho<=2MA`.  Therefore:

- if `A=0`, then `rho=0`;
- if `A>0`, exactly one of `rho=0` and `rho>0` holds.

This proves exhaustiveness.

When `A>0` and `rho=0`, put `C_0=A/2`.  For every endpoint tolerance choose
`N` large enough that the prefix charge is at least `C_0` and
`||b_N-b_0||_infinity` is below that tolerance.  The checked
`toFinitePrefix N` is an exact punishment-floor prefix with precisely that
charge and those endpoint annotations.  These prefixes form a
`QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily`, so the checked
cumulative consumer applies.  The note's conclusion is correct, but an
export proof must write this quantifier construction rather than say only
“long prefixes” and “the consumer applies.”

## 5. Literal inertness and paid-row persistence

If `A=0`, nonnegativity implies `a_n=0` for every `n`.  For a finite product
root, absorption zero means joint Continue mass one, hence every marginal is
pure Continue.  Thus every `q_n` is literally `quittingAllContinueRoot`.

Prefixing a literal profile by all Continue only shifts its stopping laws by
one date.  Terminal coalitions and prescribed terminal payoffs are unchanged.
For the cap coordinate, immediate Quit is already included in the
unrestricted behavioral envelope, so an all-Continue cap prefix leaves the
cap unchanged as well.  Equivalently use the checked semantic-prefix
all-Continue identity.  Hence

```text
u_n=u_0, b_n=b_0, d_n=d_0, D_n=D_0.
```

The source paid row is transported to every finite prefix by shifting both
pure times.  Because every outer root is all Continue, observer reach is
exactly one; the pure-time payoff difference, live mass, reached gain, and
full paid gain suffer no loss.  The row object is not definitionally
“unchanged”—its absolute times are shifted—so the packet should say
**losslessly shifted** or **transported with unchanged quantitative fields**.

This confirms that the paid-row fields themselves do not contradict the
inert arm.  The existing all-Continue cap-selection regressions corroborate
the local boundary.  They do not construct a full positive-minimum terminal
counterexample carrying every ambient field, and neither does this note.

## 6. Cap-to-prescribed seam

With `Delta_i(v,q)=Quit_i(v,q)-Continue_i(v,q)` and
`beta_(-i)(q)` the probability all opponents Continue, direct endpoint
expansion gives

```text
Delta_i(u,q)=Delta_i(b,q)+beta_(-i)(q)(b_i-u_i).
```

At all Continue, `beta_(-i)=1`.  Cap Nash gives
`Delta_i(b,allC)<=0`, while prescribed-payoff Nash requires

```text
Delta_i(b,allC)+(b_i-u_i)<=0.
```

This is exactly the checked surcharge obstruction, stated more invariantly
by `capNash_isZeroNash_at_prescribed_iff_surcharge_eq_liveDebt`.  The paid row
records a pure-time payoff difference on the literal profile.  It supplies no
coordinatewise surcharge equality.  The signed terminal contribution is
paid on an outer absorbing event, whereas the shifted paid suffix is reached
only on survival of every outer root; those events are disjoint.  No checked
declaration found in the narrow search reroutes the former into the latter
while retaining exact product-root Nash transport.

This validates the note's statement of the **current missing interface**.  It
does not by itself prove the model-theoretic assertion that no theorem from an
abstract list of fields can exist.  Such a logical impossibility would require
a complete countermodel satisfying those exact fields and falsifying the
conclusion.  The note explicitly disclaims such a counterexample.  Replace
“There is no generic theorem” with the precise evidence-backed conclusion:

> The displayed identities and currently checked declarations reduce the
> route to the inert stall but do not discharge it; an additional surcharge,
> rerouting, or maintained-rank theorem is required.

## 7. Mandatory packet repairs

Before export, the author must:

1. state the full finite nonempty player/reward/source quantifiers, the reward
   bound, the positive global minimum, and the definitions of all sequences
   and limits;
2. give the finite-prefix proof of `D_N=P_ND_0`, convergence, and the three
   exhaustive cases;
3. incorporate the stronger checked bounds (S1)--(S2), or explicitly label
   the current bounds as weaker consequences;
4. construct the cumulative near-return family with its exact quantifier
   order and relation orientation;
5. prove absorption-zero implies the literal all-Continue root and replace
   “row unchanged” by lossless shifted transport;
6. define `Delta` and `beta`, and cite the checked surcharge equivalence;
7. include exact boundary tests: a charged-return numerical sequence, a
   positive-displacement sequence saturating the scale qualitatively, and the
   checked all-Continue cap-selection regression, with the last one's limited
   source scope stated;
8. add a declaration-level source/subsumption audit against both formalized
   packets named above;
9. name the exact live question narrowed and state that the result is a
   reduction to, not elimination of, the inert stall;
10. add an actual Lean handoff naming the structures and theorem shapes; and
11. cite this review and obtain a fresh whole-packet review after assembly.

## 8. Export/formalization recommendation

The mathematics is useful and the exact residual is correctly isolated.  It
is not currently ready for export or external formalization: the document is
a concise interface audit, not a packet satisfying `exports/README.md`.

After the repairs, a packet can qualify as a precise reduction of the
paid-cap route to the inert marked stall, provided the maintained question
accepts that reduction as a named frontier change.  It must not be sold as an
impossibility theorem, a paid discharge, a prescribed-payoff path, or a
counterexample realizing the full ambient terminal witness.

## 9. Fresh gate of `PAID_CAP_PORT_EXACT_TRICHOTOMY__EXPORT_DRAFT.md`

**Second verdict (2026-08-25): REVISE, with three local source/proof repairs
only.**  The rebuilt draft has incorporated the full quantifiers, stronger
`D_* A` and `D_* rho/(2M)` estimates, near-return quantifier construction,
boundary scope, subsumption audit, and Lean handoff.  I rechecked all three
branches and found no new mathematical objection.  Three literal repairs are
still required before final PASS:

1. In Proof Step 1, replace

   > `quittingCapLiftedPrefixProfile_debt_succ` gives, coordinatewise, ...

   by

   > `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
   > gives the coordinatewise identity, while
   > `quittingCapLiftedPrefixProfile_debt_succ` gives its total-debt sum.

   The cited `debt_succ` declaration is a theorem about the total debt sum,
   not the coordinatewise debt vector.  The formula itself is correct.

2. In Proof Step 3, make the relation adapter literal: for the selected `N`,
   set `cert := orbit.toFinitePrefix N`, then use
   `quittingFinitePrefixAdmissiblePath cert cert.horizon (by omega)` and
   `chargeSum_quittingFinitePrefixAdmissiblePath_horizon` to obtain the path
   required by
   `QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily`.  This also
   fixes the exact `tail -> current` relation orientation instead of leaving
   “the checked cap orbit supplies the path” implicit.

3. Add the declarations actually carrying the new estimates and adapter to
   `Source correspondence`:

   - `QuittingPaidCapLiftedSource.minimum_mul_partialAbsorption_le_debtDrop`
     in `PaidCapLiftedSummablePort.lean`;
   - `abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass` in
     `UniformEquilibrium/Quitting/Debt/Marked/TimeAdvance.lean`; and
   - `quittingFinitePrefixAdmissiblePath` together with
     `chargeSum_quittingFinitePrefixAdmissiblePath_horizon` in
     `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorFinitePrefixAdmissiblePath.lean`.

Subject to those exact edits, the draft meets the mathematical, probability,
boundary, source/subsumption, consumer, handoff, and nonclaim gates.  No new
independent mathematical review is needed; a literal delta check is enough.

## 10. Final delta verdict

**PASS / APPROVE FOR EXPORT (2026-08-25).**  I reopened
`notes/PAID_CAP_PORT_EXACT_TRICHOTOMY__EXPORT_DRAFT.md` after the three edits.
The coordinatewise proof now cites
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`, while
the total-debt specialization is assigned to `debt_succ`.  The charged-return
arm now literally constructs `orbit.toFinitePrefix N` and converts it with
`quittingFinitePrefixAdmissiblePath`, in the correct tail-to-current
orientation and with exact charge preservation.  All estimate and adapter
declarations are present in the source correspondence.

The repaired draft satisfies every `exports/README.md` gate at its stated
scope: exact finite quantifiers, complete proof, unrestricted behavioral and
product-probability audit, checked source and cumulative-return consumer,
positive/negative boundaries, declaration-level subsumption audit, Lean
handoff, and strict nonclaims.  The mathematical output is the exact
charged-return / quantitative semantic-debt descent / literal inert-stall
trichotomy.  It does not claim that the inert branch is realized by a full
terminal witness or that the positive real decrement is a well-founded rank.
No further repair is requested.
