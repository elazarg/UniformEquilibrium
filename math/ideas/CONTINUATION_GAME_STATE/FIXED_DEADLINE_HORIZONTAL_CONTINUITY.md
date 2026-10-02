# A Proper Limiting Replacement Law Gives a Continuous Horizontal Map

The stopping-law vector does more than compute horizontal replacement at an
actual profile.  A convergent family of replacement laws with a **proper
limit** gives a continuous horizontal map on a small decorated compact
carrier.  A fixed finite deadline is the simplest special case.  Positive
limiting Never mass requires the relational/bubble machinery.

## Theorem (ordinary mathematics)

Fix a player `p` and a finite date `T`.  Let `lambda^n` be vectors of compact
stopping laws converging coordinatewise to `lambda`.  Let `b_p^n` be the
unrestricted cap of player `p` at the corresponding source profiles, and
assume

```text
b_p^n -> b_p.
```

Replace player `p` in every source by deterministic `QuitAt T`; call the
resulting profile `tau^n`.  Then, after evaluating the limiting law vector in
the same way,

```text
terminalLaw(tau^n) -> terminalLaw(tau),
U(tau^n)           -> U(tau),
B(tau^n)           -> B(tau),
```

where the limiting `p`-cap is declared to be `b_p`.

Equivalently, fixed-`T` replacement extends to a continuous map on the joint
carrier

```text
(source stopping-law vector, source p-cap).
```

## Proof

Player `p` stops no later than `T`, so every prescribed target outcome is
decided by the finite clock cylinder through date `T`.  All events in that
cylinder are clopen coordinates of the compact stopping laws.  Hence the
terminal law and prescribed payoff are continuous.

Changing `p`'s own prescribed strategy does not change `p`'s best-response
problem against the fixed opponents.  Therefore

```text
B_p(tau^n) = B_p(source^n) = b_p^n.
```

Now fix `j != p`.  Against `tau^n_-j`, player `p` is an opponent who quits at
date `T`.  Every pure response of `j` after date `T`, including Never, has the
same outcome as Continuing through `T`: absorption has already occurred.
Thus `j`'s full behavioral cap is the maximum of finitely many quantities:

```text
QuitAt 0, QuitAt 1, ..., QuitAt T,
Continue through T.
```

Each is an expectation over a finite clopen clock cylinder and is continuous
in `lambda^n`.  Their finite maximum is continuous.  Pure-time extremality
then identifies this finite maximum with the unrestricted behavioral cap.

## Consequence

For a sequence of pure-time reset endpoints there is an exact split:

```text
the selected deadlines have a bounded subsequence
    -> freeze one finite deadline and obtain continuous full-semantic
       horizontal transport;

the selected deadlines escape to infinity
    -> the compact response-graph infinity fibre or a correlated
       replacement relation is genuinely necessary.
```

This does not bound the selected dates.  The checked bounded self-reset theorem
guarantees that each reset chain eventually selects some finite date, but
those dates may diverge along a source sequence.  Hence this theorem consumes
only the bounded-date branch and does not solve the escape branch.

## Possible declarations

```text
quittingTerminalSemanticPair_update_fixedPureTime_tendsto

quittingContinuationBestResponseValue_update_other_fixedPureTime_tendsto
```

No Lean implementation is claimed here.

## Extension to every proper limiting replacement law

Let `theta_n -> theta` be replacement stopping laws for `p`, with

```text
theta({infinity}) = 0.
```

The same conclusion holds when source `n` is modified by `theta_n`.  Given an
error, choose `T` with

```text
theta({dates greater than T})
```

small.  Since every finite set of dates is clopen, weak convergence gives the
same eventual tail bound for `theta_n`.  On the complementary event, player
`p` stops by `T`, so the preceding finite-cylinder argument applies.  On the
tail event, changing any terminal payoff costs at most twice the reward bound.
The same estimate is uniform over another player's complete behavioral
deviation, because `p` remains a uniformly tight opponent.  Taking a supremum
preserves this uniform bound.

Approximation by finite truncations of `theta_n` therefore proves
continuity for the prescribed payoff, terminal law, and every non-`p` cap.
The `p`-cap is again copied exactly from the source.

Properness of the **limit** is the sharp qualitative boundary for a universal
continuity statement.  If `theta` has Never mass `q > 0`, the unresolved
all-opponents-late event survives with weight proportional to `q`, and
relative-time bubbles may remain.

For an exact example, use four players `j,p,k,h`.  Player `j` is prescribed
Never and is the payoff observer.  Replace `p` by the fixed law

```text
(1-q) QuitAt 0 + q Never.
```

In source sequence one, let `(T_k,T_h)=(n,n+1)`; in source sequence two, let
`(T_k,T_h)=(n+1,n)`.  Both source law vectors have the same weak limit, with
`k,h` Never.  On the event `p` quits at zero the two targets agree.  On the
event `p` is Never, their terminal coalitions are respectively `{k}` and
`{h}`.  Choosing

```text
r_j({k})=1,   r_j({h})=0
```

and all irrelevant rewards zero leaves a target payoff discrepancy exactly
`q`.  Hence no universal continuity theorem extends across positive Never
mass.

A quantitative refinement should bound the semantic ambiguity by a constant
times `q`; the example shows linear dependence is unavoidable.

There is also a three-player moving-law example with `q=1`: the replacement
`QuitAt (3m)` lies between source clocks `2m` and `4m`.  It is recorded in
`HORIZONTAL_REPLACEMENT_NO_GO.md`.
