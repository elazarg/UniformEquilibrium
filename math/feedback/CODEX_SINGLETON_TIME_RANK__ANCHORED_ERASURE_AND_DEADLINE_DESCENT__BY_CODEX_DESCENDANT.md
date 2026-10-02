# Review of anchored erasure plus deadline descent

Reviewer: `CODEX_DESCENDANT`

## Verdict

**PASS for the canonical pure-time/Never input, with one producer-scope
qualification.**

The singleton-refusal arm is executable in this lane.  At a singleton global
minimum, the owner has debt exactly `D_*`.  Against deterministic pure-time
opponents, an exact owner response can be chosen as either Never or Quit at
the next existing opponent deadline.  If its target remains on the minimum
fibre, the number of distinct finite deadlines strictly decreases.  Combined
with anchored erasure, this finite rank forces an actual off-minimum paid
response after finitely many rounds.

The result does not consume the resulting off-minimum paid port.  The claimed
extension from an arbitrary finite-clock source also depends on the separate
purification result cited in the note; this review checks the canonical
pure-time/Never theorem itself.

## 1. Exact response menu at a singleton deadline

Let the current canonical profile first absorb at date `t` in the singleton
`{b}`.  If some opponent has a finite deadline, let `u>t` be the least such
deadline and let `A` be the nonempty opponent coalition scheduled at `u`.
Against these deterministic opponents, every pure stopping time of `b` has
one of exactly three values:

```text
before u          -> r_b({b}),
at u              -> r_b(A union {b}),
after u or Never  -> r_b(A).
```

The complete behavioral strategy class gives no further value.  Along the
unique live history, a behavioral strategy is a distribution on pure stopping
times and Never, so its payoff is a convex combination of the displayed
values.  The global-minimum singleton moat and total-debt equality give

```text
d_b = D_* > 0,
d_i = 0 for i != b.
```

Thus the first value cannot attain the cap.  An exact cap-attaining response
may be selected as QuitAt `u` or Never.  This includes ties: choosing Never in
a tie is allowed and only strengthens the deadline decrease.

If all opponents play Never, the response menu is just the own singleton
reward and zero.  Positive owner debt makes Never the exact response.

## 2. The deadline rank is genuinely strict

Let `H` be the finite set of finite stopping dates used by the current
canonical profile.  At the singleton endpoint, `t` is used only by `b`.
Replacing `b` by Never removes `t`.  Replacing `b` by QuitAt `u` also removes
`t` and adds no date, because `u` was already an opponent deadline.  Hence in
both cases

```text
H(target) is a subset of H(source) minus {t}.
```

The target remains canonical pure-time/Never.  If it is again a global
minimum, anchored erasure at its new earliest coalition either exits the
minimum fibre or reaches a new singleton without introducing any deadline.
Therefore only the owner-response rounds recur, and every such round strictly
decreases the natural-valued rank `card H`.

At rank one, all opponents of the singleton owner are Never.  The exact Never
response gives the all-Never target.  That target cannot itself be a positive
global minimum: if some singleton reward is nonnegative, the checked singleton
moat fails at that coordinate; if all singleton rewards are negative, all
Never has zero debt.  Thus the construction must exit the minimum fibre.

This is a real renewable rank inside the pure-time lane.  It does not serialize
the horizontal erasure face as chronology.

## 3. Paid and source-faithful output

There are two exit modes.

1. An erasure sibling is the first off-minimum face point.  A maximum-debt
   player there has complete behavioral gain greater than `D_*/4` in Fin4,
   attained by a pure stopping time or Never.
2. A singleton owner's exact response leaves the minimum fibre.  This is a
   literal unilateral whole-strategy replacement of gain exactly `D_*` from
   an actual global-minimum profile.

Every profile is obtained from the incoming canonical source by finitely many
literal strategy replacements.  No compact point or unrelated realizer is
inserted.  The output is therefore stronger than a static refusal label, but
it is still a horizontal paid behavioral edge rather than an exact
Nash--Bellman prefix edge.  A downstream off-minimum paid-port consumer is
still required.

## 4. Relation to punishment and the terminal gap

At the singleton minimum, outsider zero debt implies the exact no-join
inequalities

```text
r_i({b,i}) <= r_i({b})  for i != b.
```

If `b` were punishment-normal, the checked instant-punishment theorem would
make the singleton reward vector a uniform-equilibrium payoff.  Consequently,
under the maintained no-uniform-payoff/terminal-gap branch, `b` is necessarily
punishment-abnormal.  This explains why an immediate punishment completion
does not consume the refusal endpoint.  The deadline argument does not need
normality: it executes the owner's actual response on the retained tail.

## 5. Exact regression boundary

The local singleton-refusal fields do not themselves contradict equilibrium.
Consider four players and set every own singleton reward to `-1`; set every
other reward coordinate to zero.  Use the canonical profile in which player
`0` Quits at date zero and, after refusal, player `1` Quits at date one.
Then

```text
U = (-1,0,0,0),
B = (0,0,0,0),
d = (1,0,0,0).
```

The owner is punishment-abnormal with punishment value zero, every outsider
has zero debt and no profitable collision, every coordinate satisfies the
formal singleton-margin inequality `B_i-r_i({i})=1`, and the retained tail
realizes the owner's exact refusal gain.  Nevertheless all Never is an exact
equilibrium, so the true global minimum debt is zero.  This shows that the
positive-global-minimum provenance and the finite deadline rank, rather than
the local singleton inequalities alone, do the work.

## 6. Lean handoff

The mathematical formalization can be split into:

```text
pureTimeSingleton_cap_eq_nextCollision_or_never
pureTimeSingleton_response_deadlineSupport_strict
pureTimeMinimum_anchorErase_or_deadlineDescent
pureTimeMinimum_exists_offMinimumPaidPort
```

The existing checked pure-time extremality interface justifies reduction of
arbitrary behavioral deviations to pure times/Never.  The remaining work is
finite deadline bookkeeping and composition with the reviewed anchored-erasure
lemma.  No punishment theorem or horizontal-cycle classification is needed
for the deadline descent itself.

