# Pure-time singleton refusal is executable by deadline descent

Identity: `CODEX_DESCENDANT`  
Date: 2026-08-31  
Status: **ordinary-mathematics result; independently derived audit of the
canonical pure-time branch; not Lean checked.**

## 1. Question

Let a Fin4 quitting table have positive global minimum terminal-semantic debt
`D_*>0`.  Suppose an actual canonical pure-time/Never global-minimum profile
first terminates at date `t` in the singleton `{b}`.  Thus `b` is the sole
debtor, with debt `D_*`, and every outsider has zero debt.  Can the surviving
owner-refusal arm be executed using the retained deterministic tail?

Yes, but its unconditional output is an actual off-minimum paid port, not an
immediate uniform equilibrium.

## 2. Punishment-normal owners close immediately

Write `s_i=r_i({i})`.  Outsider zero debt at the sure singleton row implies

```text
r_i({b,i}) <= r_i({b})  for every i != b.
```

These are exactly the instant no-join inequalities.  If the owner is
punishment-normal,

```text
punishmentValue_b <= s_b,
```

the checked instant-punishment construction yields terminal approximate Nash
profiles at every error, all with the singleton reward vector.  Hence that
vector is a uniform-equilibrium payoff.

Therefore a singleton refusal endpoint in the terminal-gap branch has an
abnormal owner.  In particular its own singleton reward is negative and its
punishment value lies strictly above that reward.  This is why no immediate
punishment can close the refusal arm.

## 3. Exact retained-tail response

Assume first that an opponent has a finite deadline after `t`.  Let `u>t` be
the next opponent deadline and let `A` be the nonempty coalition scheduled at
`u`.  The owner's complete response values are exactly

```text
Quit before u       : s_b,
Quit at u            : r_b(A union {b}),
Quit after u/Never   : r_b(A).
```

Indeed, the opponents are deterministic, absorb at `u`, and every behavioral
strategy of `b` merely randomizes over pure stopping times and Never.  Since
the owner debt is `D_*>0`, the first value is not cap-attaining.  Choose an
exact response as QuitAt `u` or Never according to the larger of the last two
values.

If every opponent is Never, the response values are `s_b` and zero.  Positive
debt makes Never the exact response.

In every case the replacement gains exactly `D_*` and annihilates the owner's
debt because its opponents are unchanged.

## 4. Renewable finite rank

Let `H` be the set of finite deadlines in the current canonical profile.
At a singleton endpoint, only `b` uses the least date `t`.  The selected
response either deletes `b` or moves its deadline to the already occupied date
`u`.  Therefore

```text
H(target) is a subset of H(source) minus {t}.
```

If the response target is off minimum, it is the desired paid port.  If it
remains minimum, anchored erasure at its new earliest coalition either exits
off minimum or reaches another canonical singleton minimum without adding a
deadline.  Repeating strictly decreases `card H`.  At rank one, the exact
Never response reaches all Never, which cannot lie on a positive global
minimum fibre.  Thus the process terminates after finitely many owner-response
rounds at an actual off-minimum paid profile.

No horizontal erasure edge is treated as temporal play.  The rank decrease
occurs only on a legal whole-strategy response from a singleton source.

## 5. What remains

The conclusion is

```text
canonical pure-time/Never positive global minimum
  -> actual source-related off-minimum paid response.
```

It removes the refusal singleton as an independent pure-time terminal
component.  It does not turn the paid response into an exact prefix edge,
control cross-coordinate cap leakage, or consume the general off-minimum paid
port.

The extension to arbitrary finite-clock sources separately uses the reviewed
finite-clock purification producer.  This note does not re-prove that
entrance.

## 6. Sharp local regression

The local refusal data alone are consistent.  Give every player own singleton
reward `-1` and set every other reward coordinate to zero.  Let player `0`
Quit at date zero and, after refusal, player `1` Quit at date one.  The source
has

```text
U=(-1,0,0,0), B=(0,0,0,0), d=(1,0,0,0).
```

Player `0` is abnormal with punishment value zero; outsiders have zero debt
and no profitable join; the complete refusal response is literal; and every
coordinate even satisfies `B_i-r_i({i})=1`.  But all Never is an exact
equilibrium, so the table's true global minimum debt is zero.  Positive-global-
minimum provenance is indispensable.

## 7. Sources inspected

- `minimumTerminalSemantic_singletonMargin`;
- `quittingPureTimeBehaviorStrategy` and behavioral pure-time extremality in
  `Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingInstantPunishmentWorks_of_conditions` and
  `isUniformEquilibriumPayoff_soloReward_of_instantPunishment` in
  `Quitting/Punishment/InstantPunishment.lean`;
- `quittingSoloSelfPayoff_neg_of_abnormal` and
  `abnormal_singletonFloor_chain` in
  `Quitting/Classification/AbnormalSingletonConsequences.lean`;
- the anchored-erasure proof in
  `SOCIAL_WEIGHT_REVIEW__ANCHORED_ERASURE_OF_PURE_MINIMUM_TO_SINGLETON_OR_PAID_PORT.md`;
- the independent deadline argument in
  `CODEX_SINGLETON_TIME_RANK__ANCHORED_ERASURE_AND_DEADLINE_DESCENT.md`.

