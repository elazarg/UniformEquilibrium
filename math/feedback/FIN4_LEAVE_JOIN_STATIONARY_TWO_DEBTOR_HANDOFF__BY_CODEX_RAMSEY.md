# Whole-packet gate: `FIN4_LEAVE_JOIN_STATIONARY_TWO_DEBTOR_HANDOFF`

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS.**  The packet satisfies the mathematical and export-quality gates in
`exports/README.md`.  The statement is literal `Fin 4`, the constrained Nash
selection is exhaustive including equality faces, the hazard and atom
constants are exact, and the sure-`s` argument really upgrades the two
date-zero Nash conditions to unrestricted behavioral cap equalities.  The
stationary-envelope rewrite required in the theorem review is now explicit.
No repair or removal is requested.

## Statement and finite Nash selection

The four labels are pairwise distinct and hence exhaustive in `Fin 4`.  With
`s` surely Quit and `o` surely Continue, the induced `c,t` game is an ordinary
binary normal-form game.  The three displayed cases are exhaustive from

```text
Delta_c(0)<0,  Delta_t(0)>0.
```

- `Delta_c(1)<=0` makes `(x,y)=(0,1)` Nash.
- `Delta_c(1)>0` and `Delta_t(1)>=0` makes `(1,1)` Nash.
- With both endpoint signs crossed, each affine difference has a unique
  interior zero, and the two zeros give the mixed Nash point.

Weak equalities are assigned to the correct pure boundary cases, so no
genericity or unproved finite-game theorem is hidden.

## Constant and atom audit

The source signs give

```text
Delta_c(0)<=-gamma,
Delta_t(0)>=gamma.
```

The reward box gives `Delta_c(1)<=2M`.  If `x>0`, support optimality gives
`Delta_c(y)>=0` and therefore

```text
y>=gamma/(gamma+2M).
```

If `x=0`, the strict `t` sign forces `y=1`.  The `t` source inequality also
implies `gamma<=2M`; hence the denominator is positive and
`0<alpha<=1`.  No factor of two is missing.

Sure `s` makes time zero terminal.  Conditional on `t` Quit, only `c` remains
random, so the only coalitions are `{s,t}` and `{c,s,t}` with masses
`(1-x)y` and `xy`.  Their sum is `y`, proving the literal `alpha/2` atom.

## Behavioral, floor, and paid-row audit

Under any unilateral behavioral deviation by `c` or `t`, the unchanged
opponent `s` still Quits surely at date zero.  No later history is reached,
and the arbitrary behavioral deviation reduces exactly to its empty-history
Boolean marginal.  Thus the induced Nash inequalities prove the full
all-behavior equalities

```text
B_c=U_c,  B_t=U_t,
```

not merely stationary or pure-action regret bounds.
`quittingPunishmentValue_le_stationaryUnilateralCap` and
`quittingTerminalSemanticPair_stationary_envelope_eq_cap` then give both
punishment floors.

The terminal witness supplies a deviation gain at least `gamma` against the
actual stationary profile.  The two cap equalities exclude `c,t`, so the
selected debtor is in `{s,o}`.  The packet explicitly rewrites its semantic
envelope as `quittingStationaryUnilateralCap`; this makes
`exists_oriented_quitNow_never_gap_of_stationary_cap_debt` applicable with
the correct orientation.  Choosing the lower pure-time endpoint as source
and the higher one as receiving witness meets
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` exactly.

The only randomization is private independent date-zero mixing.  There is no
public signal, cross-row correlation, or bounded-controller restriction.

## Adapter, consumer, and scope

The accepted
`FIN4_PUNISHMENT_NORMAL_ATOMIC_COLLISION_HANDOFF.md` packet supplies the same
table and same terminal gap, with `c` the collider, `s` the chain spectator,
and a third label `t` satisfying the two source inequalities.  The fourth
`Fin 4` label is the required `o`; Finset order introduces no orientation
change.  Thus the adapter is actual source data, not a supplied arbitrary
certificate disconnected from the maintained residual.

The output is an actual `QuittingPaidFirstDisagreementRow`, which is the named
paid-route source type.  The packet also honestly preserves that this is a
newly selected stationary source, not a reached continuation of the original
rooted-two profile.  It does not claim a Bellman edge, return, charged block,
floor safety for `s,o`, or a uniform payoff.  These nonclaims make the strict
semantic narrowing exact.

## Boundary and source audit

The crossed affine example attains the `alpha` constant; the pure boundary
avoids division by a mixing rate; `x=1/2` attains the atom pigeonhole factor;
and loss of sure absorption correctly shows why unrestricted zero debt would
fail.  The unsolved-`o` modification is a scope test rather than an asserted
complete counterexample and is used only in that role.

The named stationary cap, envelope, punishment, and paid-row declarations
have the stated semantics.  The checked large-base stationary handoff does
not subsume this result: it uses a different source and does not preserve the
rooted-two labels or fixed atom.  Conversely this packet solves only two free
coordinates.  The novelty comparison and absence of external literature
dependence are accurate.

## Lean handoff

The proposed handoff separates the finite sign selector, root assembly,
coalition-mass calculation, sure-opponent cap equality, and existing decoder
calls.  It does not store any conclusion as an input field.  The five boundary
tests cover the main equality, probability, and agency failure modes.  This
is an appropriately narrow formalization target.
