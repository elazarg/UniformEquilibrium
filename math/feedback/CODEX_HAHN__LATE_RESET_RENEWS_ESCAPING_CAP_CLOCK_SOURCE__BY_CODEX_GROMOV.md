# Review of late-reset escaping-cap-clock renewal

Reviewer: CODEX_GROMOV

Reviewed file:
`notes/CODEX_HAHN__LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE.md`

Reviewed exact SHA-256:
`c38983e9a73e14005838181d46f51602dafc02763df71a369920e58e1da2d2bb`

## Verdict

**PASS.** The note proves a genuine source-renewal theorem for the
positive-survival side of a late reset. It does not prove renewable debt
descent or a terminal consumer, and it states both limitations correctly.

## Fixed observer and uniform floor

Summability of all marginal hazards implies that the tail products of the
barred joint-Continue probabilities tend to one. Choosing the base depth
`R` after the tail product exceeds `1/2` is legitimate. At the terminal
child `zeta^R`, the old owner has zero debt, so the game-level terminal gap
selects an outsider. Because an opponent surely Quits by the finite deadline,
the outsider's behavioral response problem reduces to a distribution over a
finite set of pure times plus Never; one such pure time realizes at least the
same gain.

Copying that one response through later roots while copying the prescribed
root marginals makes its gain scale by the literal joint-Continue product.
Thus one fixed outsider and one fixed response give

```
d_j(zeta^N) >= Gamma/2
```

at every later depth. The label is not reselected within the ray. Repeating
the late selection separately after a later source renewal still gives the
same game-level floor `Gamma/2`, so the constants do not deteriorate between
renewed rays.

## Exact cap pin and wall

At a reset, Quit0 is by definition an attained complete behavioral cap at
the literal child. Hence its cap coordinate equals the current Quit endpoint.
As the barred opponents' hazards tend to zero, that endpoint approaches the
singleton reward. Combining the `delta/4` cap pin with debt at least `delta`
gives the actual prescribed-payoff wall

```
U_j <= r_j({j}) - 3*delta/4.
```

This is a finite-source statement. It does not use compact-limit holonomy or
identify a different source payoff with the child payoff.

The fixed-cap-pin expenditure theorem applies with `gamma=delta` and gives
the stated debt drop

```
min{delta/2, delta^2/(16*M)}.
```

The added absorption split is also correct. Large opponent absorption already
gives the displayed floor. In the complementary case, the cap pin and debt
floor make Quit strictly better at the exact root, so positive Continue mass
for the named player is impossible; that player Quits surely and joint
absorption is one.

## Literal positive-survival restart

The reset child itself has exactly the data needed by the cap-transport
calculation: it is an actual profile, Quit0 attains the named owner's complete
cap, and the named debt is positive. If an exact root against its literal
prescribed payoff has positive joint survival, the named owner has positive
Continue probability. Root exactness makes Quit no better than Continue at
the prescribed tail. Replacing the continuation by the old complete cap then
makes Continue followed by Quit0 the attained complete cap of the prefix.
Its clock is the literal deadline one and its debt is multiplied exactly by
the opponents-Continue mass.

Induction therefore produces the same escaping-cap-clock construction from
the new actual source; no stationarity, tropical formula, limiting root, or
old owner label is used. Reading every finite outward word backward gives a
literal exact Nash--Bellman block, so the checked no-uniform-payoff capacity
bound again makes an infinite positive-survival selection summable and leaves
the renewed source at positive far-end reach.

## Zero-survival split

The split is exhaustive. Zero product survival means at least one sure
quitter. With two sure quitters, every unilateral behavioral deviation still
leaves another sure quitter, so the tail is screened; exact root Nash is then
already exact terminal Nash for the literal root/profile splice.

With exactly one sure quitter `k`, every other complete debt coordinate of
the actual prefix is zero, since each such player faces the sure opponent.
The terminal gap is therefore carried by `k`. A profitable deviation by `k`
must alter its current sure-Quit strategy and may expose the literal child
tail. This is an actual finite-source paid handoff. The note correctly does
not replace it by stationary repetition and does not claim that this handoff
is a terminal consumer.

## Scope

The vertical exact prefix spends a fixed amount of debt and absorption, but
the next source is a later horizontal cap child. Other debts can be
replenished across that horizontal update. Therefore neither total debt nor
owner labels provide a decreasing rank for the complete renewed transition.
The note's remaining owner-cycle/source-seam obstruction is real, and no
uniform-equilibrium conclusion is claimed.
# Exact-final export review

Candidate:
`/tmp/FIN4_LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE.md`

Exact SHA-256:
`8f061a55d704ef5b7bd6c9463e53d9fcf79703e779630b98f2260e5156b58aa6`

**PASS.** The standalone candidate faithfully reorganizes the reviewed
source theorem at SHA
`c38983e9a73e14005838181d46f51602dafc02763df71a369920e58e1da2d2bb`.
It retains the literal nested genealogy, late fixed-observer selection,
uniform debt floor, exact Quit-now cap pin, fixed debt and absorption
expenditure, positive-survival source restart, and exhaustive zero-survival
split with the same hypotheses and constants.

The candidate does not promote renewal to a debt rank or temporalize the
horizontal cap-child seam.  Its ordinary-mathematics/unchecked status and all
conjecture-facing nonclaims are explicit.  I found no strengthened conclusion
or missing scope condition introduced by the rewrite.
