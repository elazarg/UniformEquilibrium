# Review of Proposition 66

Reviewer: `CODEX_EULER`

Claim reviewed: Proposition 66 in
[`CODEX_CEDAR__PAID_ROW_REENTRY.md`](../notes/CODEX_CEDAR__PAID_ROW_REENTRY.md).

Verdict: **VALID ordinary mathematics, with one terminology repair required.**
The proof gives a finite unilateral strategy-update path through actual
behavioral profiles.  It does not give a path reached by conditioning nominal
play, so “reached path” should be replaced by “unilateral strategy-update
path” wherever chronological reach could be inferred.

## Pure-time update

For

```text
epsilon=min(eta,gamma/4)>0,
```

the terminal-gap predicate supplies at each current profile a player `m_t`
with debt at least `gamma`.  The named pure-time extremality theorem identifies
the unrestricted deviation cap with the supremum over deterministic finite
Quit times and Never.  Since these payoffs are nonempty and bounded, the
standard `sSup` approximation gives one pure time with payoff at least
`B_(m_t)-epsilon`.

Updating only `m_t` leaves its opponent profile unchanged, hence leaves its
cap exactly unchanged.  Therefore

```text
U_(m_t)(sigma^(t+1))-U_(m_t)(sigma^t)
  >= d_(m_t)(sigma^t)-epsilon >= 3*gamma/4,

d_(m_t)(sigma^(t+1))
  = B_(m_t)(sigma^t)-U_(m_t)(sigma^(t+1)) <= epsilon.
```

The new debt is also nonnegative by the definition of the cap.  The constants
and the inclusion `epsilon<=min(eta,gamma/4)` are exact.  No simultaneous
root-Nash statement is used.

## Finite payoff recurrence

All prescribed payoff vectors lie in `[-M,M]^n`.  With

```text
K=ceil(2*M/eta),
```

one has `K>=1` and `2M/K<=eta`, including the case `eta>2M`.  Partitioning
each coordinate interval into `K` half-open/right-closed cells gives `K^n`
boxes of `l_infinity` diameter at most `eta`.  Constructing exactly `K^n`
updates produces `K^n+1` payoff vectors, so two indices `r<s` share a box.
Their prescribed payoff vectors are `eta`-close, and every update in the
nonempty segment retains the bounds above.

This recurrence concerns only `U`.  It gives no closeness of unrestricted
caps, semantic pairs, debts, roots, stopping-law ports, or continuation
profiles.

## Scope and terminology

Each `sigma^t` is a genuine behavioral profile, and each arrow is a literal
change of one complete strategy to a deterministic Quit time/Never.  But
`sigma^(t+1)` is not obtained from `sigma^t` by an all-Continue history or any
other play event.  In the project's chronology vocabulary this is therefore
not a “reached” path.  The mathematical statement remains correct after the
terminology repair:

> for every tolerance there is a nonempty finite unilateral pure-time
> strategy-update subpath with close endpoint prescribed payoffs, fixed gain
> at every update, and small debt for each updater after its update.

No edge is an exact Nash--Bellman edge; no punishment-floor admissibility,
absorption charge, source matching, or common continuation tail is supplied.
Thus the proposition solves an absolute prescribed-payoff recurrence problem
for best-response dynamics only.  It does not Nashify or chronologically
implement the returned loop.

## Addendum: exact deterministic payoff return

The strengthened version added after this review is **VALID**.  Start from
all-Never.  Inductively, every player's current strategy is then one
deterministic finite Quit time or Never, because each update replaces one
strategy by another member of that class.  A profile of deterministic quit
times has one deterministic first-quitter coalition, or Never.  Its prescribed
payoff vector therefore belongs to the finite set

```text
{0} union {r(S) : S nonempty},
```

of cardinality at most `2^n`.  Among the `2^n+1` profiles obtained from
`2^n` updates, two indices `r<s` consequently have **exactly equal** prescribed
payoff vectors.  The intervening path is nonempty, has length at most `2^n`,
and every update retains the previously checked `3*gamma/4` gain and
`min(eta,gamma/4)` updater-debt bound.

This removes the payoff-box partition and strengthens `eta`-closeness to
exact equality of `U`.  It does not alter the terminology or scope verdict:
the arrows remain unilateral deterministic strategy updates, not histories
reached by play, exact Bellman edges, or charged floor-admissible roots.
