# Review of Propositions 20.1--20.2

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS.**  The incident-square sign split and the three-cube complement
geometry are exact.  The note correctly treats a stable `{b,i}` corner as
only a two-coordinate face equilibrium until the other two players pass their
membership tests.

## Proposition 20.1

The square has

```text
S=T union {b},  U=T triangle {i},  V=U union {b}=S triangle {i}.
```

The edge `S->T` makes absent `b` optimal at the `T` corner, and `T->U` makes
player `i`'s membership at `U` strictly optimal against reversal.

- If `r_V(b)<=r_U(b)`, absent `b` is also optimal at `U`; hence both varying
  coordinates are stable there.
- If `r_V(b)>r_U(b)`, present `b` is optimal at `V`.  An outgoing selected
  edge `S->V` makes `i` stable at `V`, while an incoming selected edge
  `V->S` closes the four strict arrows `S->T->U->V->S`.

These cases exhaust the weak/strict `b` sign and both selected-edge
orientations.  The incoming/rejoin square is anchored at the already reachable
cycle vertex `S` and enters Section 10.

At either stable corner, a failure of the full sure-exit test cannot be caused
by `b` or `i`, so a remaining label supplies the strict toggle.  If the corner
is empty, it must be `U`; stability says `r_b(b)<=0`, while `T->U` says
`r_i(i)<0`.  Failure of all-Never therefore again supplies a player in
`I\{b,i}`.  Thus the Never boundary has no hidden agency exception.

The output is only a static third-label toggle unless the four-cycle or pure
terminal test succeeds, exactly as stated.

## Proposition 20.2

An eight-cycle in the three-cube is Hamiltonian, so every nonincident cube
edge is a chord between cycle vertices and no off-cycle source exists.

For a six-cycle, let `x,y` be the omitted vertices.  If their Hamming distance
were two, their two common neighbors would each lose two of their three cube
neighbors and have degree one in the retained induced graph.  They could not
belong to a cycle using all six retained vertices.  Thus the omitted distance
is one or three.  In the adjacent case each omitted vertex has one omitted
neighbor; in the antipodal case all three of its neighbors are retained.
From an on-cycle vertex a nonincident cube edge therefore lands either at an
omitted vertex or at a retained vertex which is not a selected-cycle neighbor.

No Bellman or chronology conclusion is inferred from this finite geometry.
