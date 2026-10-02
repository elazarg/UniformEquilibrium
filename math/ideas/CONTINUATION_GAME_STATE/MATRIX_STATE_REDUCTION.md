# What the Literal Matrix-State Idea Reduces To

## Prescribed continuation table

For a continuation payoff vector `u`, define an augmented one-stage table on
all quitting coalitions, including the empty coalition:

```text
G_u(S) = r(S)   when S is nonempty,
G_u(empty) = u.
```

If the current product root is `x` and the tail prescribed payoff is `u+`,
then the current prescribed payoff is exactly

```text
u = E_x[G_(u+)(current quitting coalition)].                      (1.1)
```

Thus a profile is a path through matrices whose nonempty rows are fixed once
and for all and whose empty row is the next continuation vector.

This is the usual Bellman spine.  No other row may change without changing the
original quitting game.

## Unilateral continuation tables

The unrestricted cap requires one extra empty-row value per player.  Against
the current opponents, player `i` compares:

```text
Quit now:      reward of T union {i};
Continue now: reward of T if opponents T != empty quit,
              and B_i(tail) if every opponent Continues.
```

Together with the prescribed empty row `u(tail)`, this is exactly the
finite-dimensional state `(U,B)` and its transition
`quittingTerminalSemanticPrefix`.

Consequently:

```text
reward matrix + variable all-Continue row       = U-state;
reward matrix + prescribed and cap empty rows   = (U,B)-state.
```

The user's matrix-state proposal in its literal finite-dimensional form is
therefore already developed.

## Why the response graph is a real enlargement

The matrix state retains only the maximum of the player's continuation
stopping problem.  It forgets which finite or escaping deadline produces each
submaximal or maximal value.  The completed response graph adds exactly this
missing row-indexed menu while leaving all terminal reward rows fixed.

Its prefix formula is not a new game rule.  It is a refinement of the same
all-Continue-row Bellman transition.

## Fence

Allowing the nonempty rows of the state matrix to change can certainly encode
more information, but then a path of such matrices is not play of the original
quitting game.  Any argument using those edges needs an explicit compiler that
reproduces every changed row using the fixed terminal reward table.  Without
that compiler, the construction is a meta-game rather than a strategy
profile.

