# Review and strengthening of incentive-aware singleton clock compression

Reviewer: `STRENGTHENER`

## Verdict

### Final strengthening

The clock-compression estimate is correct after the anchored correction below,
but neither its debt estimate nor a complete pure-time response is needed for
the atlas consumer.  A strictly stronger local construction is now available:
at the marked singleton row, replace any fixed nonowner only at that row by
`quittingRootBestEndpointAction` against the actual tail, using
`quittingLiteralOneDateProfile`. The update routes
the atom with no loss to `{j}` or `{j,o}`, preserves the literal post-row
tail, and makes the chosen local coordinate defect exactly zero.  Repeating
that single target profile immediately gives
`QuittingReprojectionConcentratedPacket` at the full source stage-mass
resolution.  This consumes every weak singleton origin without a terminal
witness or any source-debt premise.  The reviewed final statement is in
`notes/STRENGTHENER__MINIMUM_SINGLETON_TO_STRONG_CONCENTRATED_PACKET.md`.

The pure-time construction described later in this review remains valid as a
weaker alternative, but its three timing modes and lost tail are unnecessary.

The theorem's intended conclusion is correct, including the unrestricted-cap
and literal-tail claims, but the proof as written is not correct when the
anchor is positive.  An anchored completion copies the owner's random behavior
before the anchor, so its prescribed payoff is not the pure-time payoff
`V_t`.  Keeping the pre-anchor term repairs the proof and gives the strictly
sharper universal estimate

\[
 d_j(\tau_t)
 \le {p_a-\lambda\over m-\lambda}\,d_j(\sigma),
 \tag{R1}
\]

where `p_a` is the owner's probability of surviving to the anchor.  Since
`p_a <= 1`, this implies the author's displayed bound

\[
 d_j(\tau_t)\le {d_j(\sigma)\over m-\lambda}.
\]

More importantly, there is now an **unconditional atlas consumer**.  At every
compressed endpoint, choose any fixed nonowner and replace it by an
arbitrarily accurate pure-time best response.  This makes that nonowner's full
behavioral debt vanish, while the marked singleton event routes without loss
to one of three fixed coalition modes.  After a subsequence, the resulting
profiles instantiate the existing `QuittingReprojectionConcentratedPacket`.
No terminal witness and no vanishing source debt are needed for this upgrade.

Under the terminal exploitability witness, the author's more specific
inactive-owner endpoint also carries a full-gap paid first-disagreement row
for a player different from the singleton owner. Thus the same literal
endpoint co-realizes

* a fixed singleton stage mass;
* a vanishing-debt singleton owner;
* a full-gap paid observer with a different label; and
* the exact copied post-date tail.

The paid property is optional for the unconditional atlas connection. Neither
construction makes the copied source stack cap--Nash for the changed endpoint,
and neither by itself consumes the strong packet into a vertical chronology.

## Declarations checked

The review used the following checked facts rather than an informal
stationary reduction.

* `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` and the
  pure-time terminal-value definitions in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean` identify an
  arbitrary behavioral payoff with the expectation of its complete stopping
  law's pure-time values.
* `sSup_range_quittingTerminalPayoff_update_eq_pureTime` and
  `quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`
  identify the unrestricted behavioral cap with the pure-time supremum.
* `quittingContinuationBestResponseValue_update_self` gives exact cap
  invariance under a change of the player's own prescribed strategy.
* `quittingTerminalSemanticDebt_stoppingLawMixture_le` and
  `quittingTerminalSemanticDebt_stoppingLawMixture_eq_self` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`
  give coordinatewise debt convexity and exact affinity for the moved
  coordinate.
* `quittingTerminalSemanticDebt_stoppingLawMixture_eq_of_minimum_sameDebtSum`
  in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMinimumFiberAffine.lean`
  gives exact coordinate affinity only after the full endpoint is already
  known to be on the same minimum-total-debt fiber.
* `HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at` and
  `HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`
  give the full-gap row at every literal profile.
* `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`
  retains the exact first-disagreement chronology and the division-free live
  mass account.

## 1. The anchored payoff correction

Let

\[
 \pi_s=\Pr(T_j=s),\qquad
 p_a=\Pr(T_j\ge a),\qquad
 \alpha_t={\pi_t\over p_a}\quad(t\ge a).
\]

The assumption `m > lambda > 0` forces `p_a > lambda`, so no division by zero
is involved.  Against the fixed opponents let `V_s` be the payoff from the
complete pure time `s`, put

\[
 B=\sup_sV_s,\qquad g_s=B-V_s\ge0,
\]

and write the source debt as

\[
 d=\sum_s\pi_sg_s.
 \tag{R2}
\]

For the anchored completion at `t`, the owner still follows its source law
before `a`.  Therefore the correct identity is

\[
 U_j(\tau_t)=\sum_{s<a}\pi_sV_s+p_aV_t,
 \tag{R3}
\]

not `U_j(tau_t)=V_t`.  If

\[
 e:=\sum_{s<a}\pi_sg_s,
\]

then exact invariance of the owner's cap gives

\[
 \boxed{d_j(\tau_t)=e+p_ag_t.}
 \tag{R4}
\]

The behavior copied strictly after `t` is unreachable under the prescribed
completion but is nevertheless literal counterfactual provenance; (R3) does
not discard it.

## 2. Sharpened high-survival averaging

Let `s_t` be opponent survival through `t`, so that the completion's singleton
stage mass is

\[
 \beta_t=p_as_t,
\]

and the source's anchored singleton mass is

\[
 m=\sum_{t\ge a}\alpha_t\beta_t.
\]

Set

\[
 H=\{t\ge a:\beta_t>\lambda\},\qquad
 w_H=\sum_{t\in H}\pi_t.
\]

The author's estimate `w_H >= m-lambda` is correct.  There is a sharper one.
On `H`, `beta_t <= p_a`; off `H`, `beta_t <= lambda`; and
`sum_{t>=a} alpha_t <= 1`.  Hence

\[
 m\le p_a\sum_{t\in H}\alpha_t
       +\lambda\sum_{t\notin H}\alpha_t
 \le \lambda+\left(1-{\lambda\over p_a}\right)w_H.
\]

Therefore

\[
 \boxed{w_H\ge {p_a(m-\lambda)\over p_a-\lambda}.}
 \tag{R5}
\]

Let `R_H=sum_{t in H} pi_t g_t`.  From (R2), `R_H <= d-e`.
Choose `t in H` with `g_t <= R_H/w_H`.  Equations (R4)--(R5) give

\[
\begin{aligned}
 d_j(\tau_t)
 &\le e+{p_a\over w_H}(d-e)\\
 &\le e+{p_a-\lambda\over m-\lambda}(d-e)\\
 &\le {p_a-\lambda\over m-\lambda}d.
\end{aligned}
\]

The last step uses `p_a >= m`, so the displayed coefficient is at least one.
This proves (R1), and `p_a <= 1` proves the note's weaker claim.

At anchor zero, (R3) reduces to the pure-time identity.  Thus the original
proof shortcut is valid exactly in that special case.

## 3. Boundary example for the sharpened coefficient

The coefficient in (R1) is sharp from the supplied data.  Take anchor zero
and two players.  The opponent Continues at date zero, Quits at date one with
probability `1-lambda`, and otherwise Never Quits.  Give the owner payoff zero
at its singleton and at the opponent singleton, and payoff
`1/(1-lambda)` at the joint coalition.  Then the owner's pure-time values at
dates zero and one are respectively `0` and `1`, while all other pure times
give at most `1` (and can be made zero as above).

Let the owner's source stopping law put mass `w` at date zero and `1-w` at
date one.  The completion singleton masses are `1` and `lambda`, and

\[
 m=w+(1-w)\lambda,qquad d=w.
\]

For every threshold just above `lambda`, the high set consists only of date
zero.  Its completion debt is one, while

\[
 {1-\lambda\over m-\lambda}d=1.
\]

This is a sharpness example for the averaging theorem, not a positive-gap
game.

## 4. Exact invariants that survive compression

The following statements are exact.

1. All opponents' complete behavioral strategies are unchanged.
2. The owner's unrestricted behavioral cap is unchanged, because that cap
   depends only on its opponents.
3. Every live root strictly after the selected date is literally the source
   live root: the owner is restored there and the opponents were never
   changed.
4. The pre-anchor live roots are literal copies of the source roots.
5. The selected singleton stage mass is strictly larger than `lambda`.

The following tempting statement is false and must not be added: an exact
cap--Nash root word copied from the source before the anchor need not remain
cap--Nash for the compressed endpoint.  Compression changes other players'
caps, even though their prescribed strategies and the root word are copied.

## 5. A concrete no-new-support regression

Minimum provenance and an inactive owner do not force the compressed endpoint
to remain on a no-new-support face.

Use two players and reward both players by one exactly when both Quit
simultaneously, and zero otherwise.  Let both players independently choose
date zero or date one with probability one half.  This is an exact terminal
Nash profile: each prescribed payoff and unrestricted cap equal `1/2`.
Thus total debt is the global minimum zero and both coordinates are inactive.

Compress player `j` to date zero.  Its singleton stage mass is `1/2`, its
payoff and cap remain `1/2`, and hence its debt remains zero.  The opponent's
prescribed mixture earns `1/2`, but Quitting at date zero surely earns one.
The opponent debt is therefore `1/2`.

This is also the literal witness-switch kink from
`Research/Quitting/StoppingLawMixtureWitnessStrata.lean`: the exact minimum
source can lie strictly below the chord joining two off-minimum completions.
Consequently whole-law convexity has the wrong direction for proving endpoint
near-minimality.  Minimum-fiber affinity cannot be invoked until the endpoint
is independently known to lie on that fiber.

## 6. A general near-minimum-or-paid-target dichotomy

There is nevertheless a useful exhaustive endpoint statement.  Let
`sigma_n` converge semantically to a global minimum `z_*`, let

\[
 A=\{i:d_i(z_*)>0\},
\]

and let `tau_n` be incentive-aware completions for an owner `j notin A`.
Then `d_j(sigma_n) -> 0`, and (R1), with fixed `lambda < m_n -> mu`, gives
`d_j(tau_n) -> 0`.

After passage to a subsequence, at least one of the following holds.  The
dispatch chooses the first arm whenever it holds; the displayed properties
are not claimed logically disjoint.

### Minimum/no-entry endpoint

\[
 D(\tau_n)\to D_*,
 \qquad
 d_q(\tau_n)\to0\quad(q\notin A).
 \tag{R6}
\]

Every semantic cluster point is on the minimum fiber and has positive-debt
support contained in `A`.  If one old active coordinate also vanishes, the
checked minimum-fiber re-extraction gives strict support-rank descent.

### Literal paid target

There are a fixed observer `o != j` and a fixed `c>0` such that, along the
subsequence,

\[
 d_o(\tau_n)-d_o(\sigma_n)\ge c.
 \tag{R7}
\]

Indeed, if (R6) fails because the target total debt stays a fixed amount above
`D_*`, the total debt-change account and finite-player pigeonhole give (R7);
the owner cannot be selected because both of its debts vanish.  If (R6)
fails through inactive-support entry, use that entering coordinate directly.

Since `d_o(tau_n) >= c`, pure-time cap approximation and the prescribed-law
average give two pure times whose payoff difference at the same literal
`tau_n` is at least any fixed number below `c`.  Hence, for example, every
sufficiently large target carries

\[
 \operatorname{Nonempty}
   (\operatorname{QuittingPaidFirstDisagreementRow}
      (r,\tau_n,o,c/2)).
 \tag{R8}
\]

The row, the singleton stage mass, and the copied tail all belong to the same
actual profile.  This is not an independently selected paid source.

This dichotomy uses minimum comparison and finite-dimensional debt accounting;
convexity alone does not produce it.  It is consumer-relevant but still leaves
the paid-row restart/return theorem open.

## 7. Stronger conclusion under the terminal witness

In the hypothetical-counterexample regime there is no need to wait for the
second branch of the preceding dichotomy.  Let the terminal gap be
`gamma > 0`.  At every literal target `tau_n`, the witness supplies a player
and a behavioral deviation gaining at least `gamma`.  For large `n`, that
player cannot be `j`, because

\[
 d_j(\tau_n)<\gamma.
\]

Applying the checked stopping-law support-pair argument to that same
profitable deviation, followed by
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`, gives

\[
 \boxed{
 \exists o\ne j,\quad
 \operatorname{Nonempty}
   (\operatorname{QuittingPaidFirstDisagreementRow}
      (r,\tau_n,o,\gamma)).}
 \tag{R9}
\]

On Fin4, a further subsequence fixes `o`.  Thus the owner-compressed atlas
origin supplies cofinally deep endpoints with the fixed passport

\[
 \boxed{
 \begin{array}{l}
 \Pr_{\tau_n}(\{j\}\text{ at }t_n)>\lambda,\\
 d_j(\tau_n)\to0,\\
 o\ne j\text{ and a paid row of gain }\gamma\text{ at }\tau_n,\\
 \operatorname{root}_{\tau_n}(t_n+1+r)
   =\operatorname{root}_{\sigma_n}(t_n+1+r)\quad\forall r.
 \end{array}}
 \tag{R10}
\]

There is an additional chronological alignment which is easy to miss.  In
the completion `tau_n`, the singleton owner stops no later than `t_n` almost
surely: it either stops in the copied pre-anchor part or is forced to stop at
`t_n`.  Since `o != j`, two pure-time plans of `o` which both wait strictly
beyond `t_n` have exactly the same payoff--the owner has already absorbed the
game.  A positive paid pair can therefore not first disagree after `t_n`.
The row in (R9) may be chosen with

\[
 \boxed{\operatorname{row.start}\le t_n.}
 \tag{R11}
\]

Thus the paid mark is not hidden in an unrelated later tail.  It lies in the
same finite causal window ending at the concentrated singleton deadline.
This does not say that it occurs at the singleton date itself.

The current public theorem
`HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at` forgets the
proof that the chosen observer is the original profitable observer.  A narrow
Lean handoff should therefore add a localized variant, for example

```lean
theorem HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at_ne
    (hgamma : 0 < gamma)
    (exploit : HasTerminalExploitabilityGap reward gamma)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : iota)
    (howner : quittingTerminalDeviationDebt reward profile owner < gamma) :
    ∃ observer, observer ≠ owner ∧
      Nonempty
        (QuittingPaidFirstDisagreementRow reward profile observer gamma)
```

Its proof is the existing support-pair proof with the profitable observer
retained rather than existentially forgotten.

## 8. Relation to a Never/deadline extraction

Every paid row in (R9) already gives the division-free checked account

\[
 \gamma\le 2M\,L,
\]

where `L` is opponents' survival to the finite first-disagreement date and
`M=quittingRewardBound r`.  Thus, when `M>0`, it yields
`L >= gamma/(2M)`.  This is quantitatively stronger than a
`gamma/(64M)` lower bound if the latter denotes the same survival/reach
quantity.  By (R11), this finite first-disagreement date is no later than the
owner's forced singleton deadline.

It is not, however, a lower bound on an atom of the prescribed marginal
stopping law.  Pure-time witnesses are deterministic deviations, and a
supported source witness may have arbitrarily small source-law mass.  A split
of the form

\[
 \text{Never payoff}\ge\text{singleton payoff}+\gamma/2
 \quad\text{or}\quad
 \text{finite marginal deadline atom}\ge\gamma/(64M)
\]

therefore needs a separate finite-support or deadline argument.  It does not
follow from the pure-time/cap-exchange lemma alone.  It should be folded into
(R10) only if its `deadline atom` is an actual terminal/collision mass or it
comes with a proof preventing diffuse prescribed stopping mass.  Otherwise
the already checked paid-row live-mass certificate is the stronger honest
statement.

## Lean-facing handoff

The minimal useful formal package has three layers.

1. An anchored completion payoff/debt identity (R3)--(R4).
2. The sharpened selection theorem (R1), retaining the selected stage mass,
   opponents, and post-date roots.
3. Under a terminal gap, a wrapper producing (R10), using the localized
   distinct-observer paid-row theorem above, plus the deadline alignment
   (R11).

The first two are generic for any finite player type.  Only the eventual fixed
observer/subsequence wrapper is Fin4-specific.  No copied-prefix cap--Nash
claim belongs in the interface.

## 9. Unconditional consumer found: any nonowner routes into the strong packet

The same-target data can be consumed further than (R10), and the paid-observer
hypothesis is unnecessary. Fix **any** nonowner `o != j`. At each compressed
endpoint choose a deterministic pure time `q_n` within `e_n` of `o`'s cap,
where `e_n=s_n^2` and `s_n -> 0`. Updating `o` to that pure time makes its full
behavioral debt at most `e_n`, regardless of its source debt.

The marked singleton event routes with no mass loss.  If its date is `t_n`,
then the response profile has an atom of at least the same mass on

\[
\begin{array}{c|c|c}
q_n>t_n\text{ or Never}&t_n&\{j\}\\
q_n=t_n&t_n&\{j,o\}\\
q_n<t_n&q_n&\{o\}.
\end{array}
\]

After a subsequence one of the three modes is fixed. The observer was fixed
from the start. The
one-step Green bound then gives

\[
 \frac{\operatorname{Live}\cdot\operatorname{Defect}_o}{s_n}
 \le \frac{d_o}{s_n}\le s_n\to0.
\]

Taking cutoff one past the routed date constructs the existing
`QuittingReprojectionConcentratedPacket` interface. Thus the **entire** weak
minimum-singleton leaf reduces to the maintained strong concentrated family,
at every resolution `lambda` strictly below the selected singleton law mass.
The detailed proof and Lean handoff are in
`notes/STRENGTHENER__MINIMUM_SINGLETON_TO_STRONG_CONCENTRATED_PACKET.md`.

The inactive-owner paid corollary can retain the profitable player directly
through
`QuittingTerminalExploitabilityWitness.exists_terminalGap_le_terminalSemanticDebt`,
but this is independent of the packet construction.

The response does not preserve the copied post-date live-root tail or the old
cap--Nash stack.  Neither is a field of the concentrated packet, so the
reduction is honest but cannot be advertised as a source-return theorem.

The earlier active-owner objection was real only for the attempt to choose the
singleton owner or a witness-selected profitable observer as the vanishing
defect coordinate. It disappears when an arbitrary fixed nonowner is
Nashified. `FinFourMinimumAtomProducer` need not assert anything about the
singleton owner's debt.
