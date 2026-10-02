# Review of Proposition 29.2

Reviewer: `CODEX_RAMSEY`

Claim reviewed: after the large-base dispatch chooses the paid base member
`c`, move `c` into the free set `F'={c,x,y}` and retain only `d` as the sure
singleton owner.  Under the terminal exploitability witness, the owner's
floor excess is uniformly positive on the full induced Nash set, while the
original paid source embeds as a boundary-face `{x,y}` Nash point at which
`c` has Quit-minus-Continue defect at most `-gamma`.

## Verdict

**PASS.**  The compactness gap `delta` is independent of, and is not claimed
to be quantitatively related to, the original paid margin `gamma`.  The note
states this qualification exactly.

## Audit

The finite binary game on `F'={c,x,y}` with persistent base `{d}` has a
nonempty compact mixed Nash set.  At every point `q` in this set all three
free-player endpoint inequalities are the exact induced-game Nash
conditions.  Since `I={d} union F'`, there are no outsider conditions.
Therefore

```text
ownerFloor(d,q)<=0
```

together with the induced Nash point is precisely the hypothesis of
`nonempty_quittingSingletonBaseCertificate_of_inducedNash`.  Its checked
consumer gives a uniform-equilibrium payoff against unrestricted behavioral
deviations.  The terminal witness excludes this at every `q`, so the owner
floor is strictly positive pointwise.  The floor functional is continuous;
compactness and nonemptiness of the Nash set give a genuine minimum
`delta>0`.  No unproved equilibrium selection or attainment of the punishment
value is used.

For the boundary point, the original Proposition 26.1 output is an exact
Nash point `p` of the `{x,y}` game with both `c,d` persistent.  Reinterpreting
the same product rates in the enlarged game with only `d` persistent and
setting `c` to Quit surely leaves every payoff comparison of `x,y` unchanged.
Thus `x,y` remain exact best responses on that face.  This does not assert
that the boundary point is a Nash equilibrium of the full three-free-player
game; indeed `c` has the advertised strict defect.

With `R subset {x,y}` the endpoint difference of `c` at that face is

```text
r_({c,d} union R)(c)-r_({d} union R)(c)
 =-[r_({d} union R)(c)-r_({c,d} union R)(c)]
 =-ell_c(R).
```

The pure paid certificate gives `ell_c>=gamma`; in the strict mixed branch
the cleared inequality `N_c>=gamma*D` gives
`E_p[ell_c]>=gamma` after division by `D>0`.  Hence the expected
Quit-minus-Continue endpoint difference is at most `-gamma` in both cases.
The original label and orientation are therefore retained exactly.

The two old residual coordinates are genuinely internalized: `c` is no
longer an outsider on the full induced game, and at full Nash points its
endpoint condition is automatic; the sole remaining compiler obstruction is
the strictly positive owner floor.  Conversely, the original paid source is
only a boundary-face Nash point, so no path, connectedness, or contradiction
between `delta` and `gamma` follows.  Proposition 29.2 correctly leaves that
compact capstone open.

## Source and scope

The relevant checked facts are the compact induced Nash carrier and
continuity of `quittingSingletonBaseOwnerFloorExcess` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`,
the constructor `nonempty_quittingSingletonBaseCertificate_of_inducedNash`,
and `QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` in
`SingletonBaseSemanticDispatch.lean`.  These supply the all-behavior consumer
but not the paid-boundary alignment (29.12)--(29.14), which is the new finite
reduction.

No public correlation is used: the original mixed boundary point is the
product Bernoulli equilibrium of `{x,y}`.  No conclusion is claimed about a
connector between the boundary face and the full Nash set, and no explicit
formula for `delta` is inferred.

