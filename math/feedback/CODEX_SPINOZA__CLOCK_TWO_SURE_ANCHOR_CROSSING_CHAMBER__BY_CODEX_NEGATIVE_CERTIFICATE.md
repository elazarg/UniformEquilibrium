# Independent falsification review: clock-two sure-anchor crossing chamber

**Reviewer:** CODEX_NEGATIVE_CERTIFICATE  
**Reviewed note:**
[`notes/CODEX_SPINOZA__CLOCK_TWO_SURE_ANCHOR_CROSSING_CHAMBER.md`](../notes/CODEX_SPINOZA__CLOCK_TWO_SURE_ANCHOR_CROSSING_CHAMBER.md)  
**Reviewed SHA-256:**
`a389c183a83943fefed3f06fd5d4645246f7ef5adf491e7848042b3095f88ce5`  
**Verdict:** **PASS**.  I found no algebraic, quantifier, coordinate-count,
behavioral-scope, or compiler-orientation objection.

## The theorem checked

For distinct players `(a,b,c,d)`, the packet assumes the four positive
crossing contrasts

```text
L_a = R_a({b})-R_a({a,b}),
G_a = R_a({a,b,c})-R_a({b,c}),
G_c = R_c({b,c})-R_c({b}),
L_c = R_c({a,b})-R_c({a,b,c}),
```

and three anchor/passive inequalities.  It claims that

```text
x = G_c/(G_c+L_c),   y = L_a/(L_a+G_a)
```

produces an exact clock-two terminal Nash profile: `a,c` mix at date zero
and otherwise quit surely at date one, `b` quits surely at date zero, and `d`
waits beyond date one.  The conclusion is against unrestricted behavioral
deviations and supplies the stated terminal payoff as a uniform-equilibrium
payoff.

## Active equations and outcome weights

I independently expanded the date-zero join-minus-wait differences.  They
are exactly

```text
a: -(1-y)L_a + y G_a,
c:  (1-x)G_c - x L_c.
```

The four strict positivity assumptions make the displayed `(x,y)` the unique
solution in `(0,1)^2`.  With `A=L_a+G_a` and `C=G_c+L_c`, the four outcome
probabilities for neither mixer, only `a`, only `c`, and both are

```text
(L_c G_a, G_c G_a, L_c L_a, G_c L_a)/(AC),
```

so the weights and on-path payoff formula in (2.3)--(2.4) have the correct
orientation and sum to `AC`.

## Anchor and passive deviations

I reconstructed each of the remaining deterministic deviations.

- If `b` uses Q1, the four date-zero mixer outcomes lead respectively to
  `{a,b,c}`, `{a}`, `{c}`, and `{a,c}`.  This is exactly (3.1).
- If `b` waits strictly past date one or Never, those outcomes lead to
  `{a,c}`, `{a}`, `{c}`, and `{a,c}`.  This is exactly (3.2).
- If `d` uses Q0, adjoining `d` to the four on-path coalitions gives
  `{b,d}`, `{a,b,d}`, `{b,c,d}`, and `{a,b,c,d}`.  This is exactly (3.3).

Thus (3.4) rules out precisely all payoff-distinct pure-time deviations of
`b` and `d`.  No absolute quit time is missing: when a player other than `b`
deviates, `b` still ends the game at date zero; when `b` deviates, both `a`
and `c` have stopped by date one.  The same observation validates the claim
that `d`'s prescribed law may be any law supported strictly after date one.

## Unrestricted behavioral scope and uniform consumer

I rechecked the declarations under their imports:

- `quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` and
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `../UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
  `../UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The pure-time theorem bounds every unilateral behavioral terminal payoff
above by the supremum of deterministic absolute quit times and Never.  Since
the packet exhausts and bounds those times, its use gives exact terminal Nash
for the complete behavioral strategy class.  The exact terminal-to-uniform
consumer has the stated direction and returns the profile's own terminal
payoff at initial state `none`.  No finite-controller completeness claim or
unreachable-subgame Nash condition is being imported.

## Coordinate count and E2 specialization

The 23 used reward coordinates are indeed distinct in the stated counts:

```text
players a,c: 4 each;
player b:     4 on-path plus {a},{c},{a,c} = 7;
player d:     4 on-path plus 4 date-zero-join coordinates = 8.
```

Hence exactly `60-23=37` coordinates are absent and may vary independently
and without bounds.  With all seven inequalities strict, the used-coordinate
conditions are strict polynomial inequalities after clearing the positive
denominator `AC`, so the asserted open semialgebraic cylinder is justified.

For E2 and `(a,b,c,d)=(0,1,2,3)`, exact substitution gives

```text
(L_a,G_a,G_c,L_c)=(3,8,1,1),
(x,y)=(1/2,3/11),
(w_00,w_10,w_01,w_11)=(8,8,3,3), AC=22.
```

The three actual-payoff margins recompute to `29/44`, `5/44`, and `3/11`.
These agree with the separately audited E2 pure-time table.

## Scope

This PASS supports the supplied-contrast sufficient theorem and its
37-coordinate cylinder.  It does not turn the chamber into a producer for an
arbitrary Fin4 table or show that every hard residual can be relabelled into
it.  Future negative searches must explicitly exclude all relabellings of
this sure-anchor chamber.
