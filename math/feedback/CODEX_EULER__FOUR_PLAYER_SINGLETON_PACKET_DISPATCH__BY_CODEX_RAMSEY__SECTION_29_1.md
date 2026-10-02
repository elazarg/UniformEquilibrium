# Review of Proposition 29.1

Reviewer: `CODEX_RAMSEY`

Claim reviewed: the whole four-player large-persistent-base `G` chamber may
delete its already selected paid base member `c`, reselect an arbitrary exact
Nash equilibrium of the remaining binary game on `{x,y}` with singleton base
`{d}`, and reduce to the finite pure residual (29.5) or strict
matching-pennies residual (29.9).  If both new outsider/owner quantities are
nonpositive, the checked singleton-base certificate gives a uniform-
equilibrium payoff against unrestricted behavioral deviations.

## Verdict

**PASS, with the provenance qualification already stated in the note.**  The
new residual does not inherit a quantitative `gamma` margin at the reselected
profile.  It retains the original labelled `c,gamma` paid-leave certificate
as upstream data, while terminal-witness exclusion gives only strict
positivity of one newly evaluated numerator.  Proposition 29.1 says this
correctly in its final scope paragraphs and does not use the old profile after
deletion.

## Independent checks

### Deleted finite game and pure cells

With

```text
D_ij={d} union ({x} if i=1) union ({y} if j=1),
```

the differences `bar_alpha_j` and `bar_beta_i` are respectively the
Quit-minus-Continue payoff differences of `x` and `y`.  Hence (29.4) is
exactly the four pure best-response test, including every equality face.

At such a cell, `d` Quits surely and `c` is the only outsider.  Its endpoint
difference is exactly

```text
J_c^ij=r_(D_ij union {c})(c)-r_(D_ij)(c).
```

The owner's Continue-minus-Quit floor excess is

```text
chi_d-r_d(d)                         if R_ij=empty,
r_(R_ij)(d)-r_(D_ij)(d)              otherwise,
```

which is exactly `k_d^ij`.  Therefore `J_c^ij<=0` and `k_d^ij<=0` are
precisely the outsider and owner hypotheses of
`nonempty_quittingSingletonBaseCertificate_of_inducedNash`.  There are no
other outsiders in `I={c,d,x,y}`.  The checked certificate consumer covers
arbitrary behavioral deviations and Never, so the terminal witness forces
(29.5).

### No-pure classification and weights

A two-by-two binary game with no pure Nash cell has no zero endpoint
difference.  For example, if `bar_alpha_0=0`, the four cases determined by
`bar_beta_0`, `bar_alpha_1`, and `bar_beta_1` successively give a pure cell at
`00`, `01`, `10`, or `11`; the other zero cases are symmetric.  The remaining
strict signs are exactly the two matching-pennies orientations (29.6).

For both orientations,

```text
Dbar=(bar_alpha_0-bar_alpha_1)*(bar_beta_1-bar_beta_0)>0
```

and all four displayed weights are positive.  They sum to `Dbar`.  Direct
expansion of the mixed rates gives

```text
Pr(x Quits)=-bar_beta_0/(bar_beta_1-bar_beta_0),
Pr(y Quits)= bar_alpha_0/(bar_alpha_0-bar_alpha_1),

Pr(i,j)=Wbar_ij/Dbar.
```

Thus the construction uses independent Bernoulli actions, not correlation.
The normalized outsider difference is `Jbar_c/Dbar`; the normalized owner
floor excess is `Kbar_d/Dbar`, including the punishment value only in the
joint-Continue cell.  Nonpositivity of both numerators again instantiates the
same checked singleton-base certificate, so the terminal witness and
`Dbar>0` give (29.9).

### Quantifiers and source label

Nash's theorem supplies at least one deleted-game Nash equilibrium.  If a
pure one exists, choosing any such cell is legitimate; terminal-witness
exclusion forces the residual at that chosen cell.  If none exists, the
fully mixed equilibrium is unique.  The construction therefore covers the
complete deleted Nash set without a continuity or selection assumption.

The paid label `c` was selected before deletion from the accepted large-base
finite-Nash dispatch.  Reselecting `x,y` does not change that label or erase
the upstream paid-leave inequality.  It can change every free-player rate,
so no old-profile reprojection, old paid value at the new cell, or transferred
`gamma` lower bound is inferred.  This is exactly the price recorded in the
note.

## Source and boundary audit

The relevant checked handoff is
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` and the definition
`quittingSingletonBaseOwnerFloorExcess` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`,
followed by `QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` in
`SingletonBaseSemanticDispatch.lean`.  Those declarations provide the
unrestricted-deviation consumer, but not the deletion/reselection or the
cleared finite formulas above.  Proposition 29.1 is therefore not a
restatement of the checked adapter.

Equality endpoint differences belong to the pure branch, as required.  The
strict branch has positive denominator and weights in both sign
orientations.  The result is a finite chamber-wide reduction only: it does
not consume the positive residual in (29.5) or (29.9), and it does not claim
that any pure cell extracted from a positive mixed average is itself Nash.

