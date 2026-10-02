# Review of Section 16 in `CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY`

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS**, with one proof-writing handoff that should be made explicit before
any reuse: to feed (16.5) to
`exists_oriented_quitNow_never_gap_of_stationary_cap_debt`, rewrite the
stationary semantic envelope using
`quittingTerminalSemanticPair_stationary_envelope_eq_cap`.  The equality is a
checked declaration and supplies exactly the missing displayed line; it does
not change the theorem.

The constrained Nash construction, the hazard and atom constants, the two
zero-debt coordinates, and the paid-row localization all have the stated
probability and unrestricted-behavior meanings.

## Constrained two-player row

With `s` surely quitting and `o` surely continuing, absorption occurs at date
zero.  The free `c,t` game is therefore the literal finite binary game with
terminal payoffs from the four coalitions obtained by toggling `c,t` around
`{s}`.  A mixed Nash `(x,y)` exists, and its private independent marginals
give the displayed four-player product root.  No public randomization or
continuation value is hidden in this selection.

For `c`, Quit-minus-Continue at `y=0` is

```text
r_{c,s}(c)-r_s(c) <= -gamma,
```

while at `y=1` it is

```text
r_{c,s,t}(c)-r_{s,t}(c) <= 2M.
```

Affineness in `y` is exact.  If `x>0`, Quit is in `c`'s support, so the
endpoint difference is nonnegative and

```text
y >= gamma/(gamma+2M).
```

If `x=0`, `c` is surely Continue and `t`'s endpoint difference is exactly
`r_{s,t}(t)-r_s(t)>=gamma`; hence `t`'s unique best reply is Quit and `y=1`.
The source inequality also gives `gamma<=2M`; therefore the denominator is
positive and `0<alpha<=1`.  The constant `2M` is the sharp generic bound on a
difference of two reward entries and no extra factor is missing.

## Atom calculation

Since `s` quits surely at time zero, the repeated stationary profile has no
later live stage.  On the event that `t` quits, the only terminal coalitions
are

```text
{s,t}       with mass (1-x)y,
{c,s,t}     with mass xy.
```

Their sum is `y>=alpha`; hence one literal terminal-law atom has mass at least
`alpha/2`.  This is a source atom of the newly selected stationary profile,
not an atom transported from the original rooted-two profile.

## Unrestricted caps and floors

Any behavioral deviation of `c` or `t` chooses only a date-zero Boolean
marginal before the surely quitting action of `s` absorbs the game.  Histories,
Never, and later randomization are unreachable.  The constrained Nash
inequalities therefore control every unrestricted behavioral deviation, not
only stationary deviations, and give

```text
B_c=U_c,  B_t=U_t.
```

The checked inequality
`quittingPunishmentValue_le_stationaryUnilateralCap`, together with the exact
stationary-envelope identity, gives `P_c<=U_c` and `P_t<=U_t`.

Applying `witness.terminalExploitability` to the literal stationary profile
selects a deviation gain at least `gamma`.  The two cap equalities exclude
`c,t`, so a selected debtor `w` lies in `{s,o}` and satisfies
`B_w-U_w>=gamma`.  Semantic debts are nonnegative, hence the whole positive
debt support is a nonempty subset of `{s,o}` and has cardinality at most two.

For the final decoder, insert the checked rewrite

```text
B_w
 = quittingStationaryUnilateralCap reward q w
```

from `quittingTerminalSemanticPair_stationary_envelope_eq_cap`.  Then
`exists_oriented_quitNow_never_gap_of_stationary_cap_debt` gives one of the
two oriented immediate-Quit/Never differences, and
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` gives the
claimed literal paid row after assigning the lower endpoint as source and the
higher endpoint as receiving witness.  The observer is the same `w` and is
distinct from both solved labels.

## Source and scope

Corollary 15.3 supplies the signs with `c` the collider, `s` the spectator,
and `t` the third-label joiner; Finite-four distinctness leaves a unique
fourth label `o`.  Finset order makes `{c,s}` and `{s,c}` identical, so there
is no orientation mismatch in (16.1).

The result reselects a new stationary source from same-table signs.  It does
not reach that source from the original profile, produce an exact
Nash--Bellman edge, make `s,o` floor-safe, return a payoff, or compile a
uniform equilibrium.  The atom and paid row are exact data of the new source,
which is precisely the stated narrow noncompiler scope.
