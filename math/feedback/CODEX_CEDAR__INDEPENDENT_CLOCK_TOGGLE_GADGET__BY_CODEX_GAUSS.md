# Review of the exact Never collectors

Reviewer: `CODEX_GAUSS`

Reviewed note:
[`../notes/CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md`](../notes/CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md)

Scope: Sections 14 and 17, Propositions 13 and 16.  I independently checked
the two collector deviations, all date-zero tie cases, the owner-Never and
refusal-premium signs, and the exact scope of the rank-one compression.  This
is ordinary mathematics, not Lean-checked, and it supplies no reward-table
counterexample or export claim.

## Verdict

**Propositions 13 and 16 are VALID ordinary mathematics.**  I found no
missing clock event, payoff loss, or sign reversal.  The estimates hold for
arbitrary independent behavioral clocks and arbitrary rewards in every
unmentioned coordinate.  Two collectors really do reduce every finite first
coalition supported on `{w,h_1,h_2}`, except `{h_1,h_2}`, to `O(epsilon)`;
the statement does not claim to control coalitions containing core outsiders.

## 1. Collector `h` and the exact gain `K p_w`

For Proposition 13, `h` receives `-K` only on the exact singleton first
coalition `{w}` and zero everywhere else.  Replace `h`'s whole clock by Quit
at date zero.

- If the prescribed first coalition is `{w}` at a positive date, the
  deviation makes `{h}` absorb at date zero.
- If it is `{w}` at date zero, prescribed singletonhood implies that `h` was
  not tied there, and the deviation changes the coalition to `{w,h}`.
- Off the event `{w}`, the prescribed payoff is zero.  After the deviation
  the first coalition contains `h`, so it cannot be the singleton `{w}` and
  the deviating payoff is also zero.

Thus the gain is exactly `K p_w`, including the time-zero boundary, and
`p_w<=epsilon/K` follows because `K>0`.

## 2. Owner `w` and the two signs

Under the pure-Never replacement of `w`, every first nonsingleton coalition
containing `w` loses `w` but retains at least one simultaneous opponent.  The
payoff changes from `-H` to `1`, an exact gain `H+1`.  On the singleton event
`{w}`, deletion either exposes a later opponent coalition, changing `1` to
`1`, or exposes Never, changing `1` to `0`; the loss is therefore at most
one.  Coalitions excluding `w` are unchanged.  Hence

```text
NeverGain_w >= (H+1)m_w-p_w,
m_w <= (p_w+epsilon)/(H+1).
```

The same partition with the opposite subtraction gives the required refusal
sign

```text
u_w-n_w <= p_w-(H+1)m_w <= p_w.
```

Applying the already independently reviewed late-Quit inequality with solo
payoff one yields

```text
A_(-w) <= epsilon+(u_w-n_w) <= epsilon+p_w.
```

No absorption or Never event is omitted in these comparisons.

## 3. Two collectors and all tie cases

For Proposition 16, `h_1` is paid `-K` only on `{w}` and `{h_2}`.  Quitting
at date zero changes either target event to payoff zero: a positive-date
target is preempted by `{h_1}`, while a date-zero target is changed to a tied
two-player coalition containing `h_1`.  Off those two events the prescribed
payoff is zero, and the deviated first coalition contains `h_1`, so it cannot
equal either target singleton.  The gain is therefore exactly

```text
K(p_w+p_(h_2)).
```

The identical audit for `h_2`, whose sole negative singleton is `{h_1}`,
gives exact gain `K p_(h_1)`.  These are replacements of the collectors'
entire behavioral strategies, not stationary or one-shot response
restrictions.

The owner calculation from Proposition 13 is unchanged.  Consequently the
three singleton masses are `O(epsilon)`, every nonsingleton supported on the
triple and containing `w` is included in `m_w=O(epsilon)`, and all-Never is
included in the bound on `A_(-w)`.  The only remaining finite coalition
supported on the auxiliaries is `{h_1,h_2}`.  This proves the stated
rank-one compression and no more.

## 4. Exact surviving obstruction

Both collector own solos are zero, and their pair coalition pays them zero.
The reviewed estimates do not price the mass of `{h_1,h_2}`.  Thus the pure
collector-pair sink remains exactly as stated.  Closing the negative thesis
still requires a multicoalition membership toggle that transfers this pair
mass into the compensated core ledger without creating a new sure-exit or a
production-normal projective-Q-bar positive branch.
