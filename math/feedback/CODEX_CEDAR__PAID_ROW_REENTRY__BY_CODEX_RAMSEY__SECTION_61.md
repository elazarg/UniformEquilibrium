# Review of Section 61

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS.**  The successor-shift orientation, norm identity, terminal-gap input,
and cap-tail specialization are correct.  The conclusion excludes only the
cap-seeded absolute-level shortcut described in the note.

For a fixed product root `q`, changing the successor prescribed payoff from
`U` to `V` changes the current prescribed payoff by

```text
Succ(V,q)-Succ(U,q)=C(q)*(V-U),
```

because only the all-Continue event reaches the tail.  The sign in (61.2) is
therefore correct.  Since `C(q)>=0`, absolute homogeneity of the sup norm gives
the equality in (61.5), not merely an inequality.

The reviewed Section 51 marginal ceiling gives
`1-q_i>=gamma/(4M)` for every player at every exact boxed floor root.  Taking
the finite product gives exactly

```text
C(q)>=kappa=(gamma/(4M))^n>0.
```

The positive terminal gap excludes `M=0`; its conservative bound
`gamma<=4M` makes the displayed base a probability-scale number.  No hidden
attainment or compactness is used here.

For an actual behavioral profile, every cap coordinate is bounded by the
terminal reward box and lies above the punishment floor, so `V=B` is a legal
boxed floor tail.  The terminal gap supplies a coordinate with
`B_j-U_j>=gamma`, hence `||B-U||_infinity>=gamma`.  Applying (61.5) gives the
claimed fixed seam `kappa*gamma`.  Conversely, an edge payoff within `eta` of
the literal prefix payoff must have `||V-U||<=eta/kappa`; (61.7) follows
directly.

The semantic-port wording is also appropriately narrow.  If the Section 50
root is exact at an actual continuation payoff `U`, prefixing the actual
continuation by that root literally realizes `Succ(U,q)` as a behavioral
profile payoff.  This does not make the profile's semantic cap equal to `U`
and does not turn later reached updates into exact edges.  The proposition
rules out replacing `U` by its cap `B` while keeping the same current payoff
level.  It does not exclude an exact root already at a floor-safe `U`, a
different root, or a multi-edge payoff return.

## Addendum: floor-deficit corollary

**PASS.**  If
`floorDef(U)=max_i (P_i-U_i)_+`, every floor-admissible `V` satisfies
`V_i>=P_i`; at a maximizing deficit coordinate this gives
`|V_i-U_i|>=floorDef(U)`.  Hence `||V-U||_infinity>=floorDef(U)`, and (61.5)
immediately yields seam at least `kappa*floorDef(U)`.  This correctly shows
that low debt in one selected coordinate does not by itself make the whole
prescribed vector floor-admissible.
