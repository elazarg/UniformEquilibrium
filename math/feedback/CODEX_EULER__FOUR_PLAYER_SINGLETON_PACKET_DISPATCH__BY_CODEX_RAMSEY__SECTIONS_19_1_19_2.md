# Review of Propositions 19.1--19.2

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS.**  The post-four-cycle geometry, quantitative base-leave localization,
incidence split, returned four-cycle, and distinct-label third-edge argument
are exact.  In Proposition 19.2, “there is a unique toggled label” should be
read as uniqueness of the coordinate changed by the chosen second edge, not
uniqueness among all possible promotion witnesses; no later argument needs
the stronger reading.

## Proposition 19.1

A simple strict cycle with exactly two free coordinates is the unique
four-cycle of that two-face.  Once the ordered length-four branch has failed,
`|F|>=3`.  Four players and nonempty `B` then force

```text
B={b}, |F|=3, O=empty.
```

The remaining simple even cycle in the three-cube has length six or eight.
With `O` empty, `G` has only the singleton-base leave expression.  Its empty
cell is `chi_b-r_b(b)<=0` by the already established all-player normality.
Since the product-law average equals `gamma>0`, some positive-weight nonempty
cell `R` has pure base-leave gain at least `gamma`; otherwise the finite
average would be strictly smaller than `gamma`.  Thus the join and floor arms
really disappear.

## Proposition 19.2

For the chosen promoted edge, its single changed coordinate is some `i in F`:
the rejoining base label `b` is excluded and `I={b} union F`.  The identities

```text
S=R union {b}, T=R,
U=T triangle {i}, V=S triangle {i}=U union {b}
```

are exact.  Testing whether `S` is on the selected cycle, whether `V` is a
cycle neighbor, the orientation of that incident edge, and finally the
`b`-join sign gives the five exhaustive cases.

In the incoming/rejoin case, the four strict edges are

```text
S -> T       (b leaves, gap at least gamma),
T -> U       (i toggles),
U -> V       (b rejoins),
V -> S       (the incoming selected-cycle edge for i).
```

The vertices are distinct because the square toggles the distinct coordinates
`b` and `i`.  Since `S` is already reachable on the selected cycle, the square
is anchored without a new reachability premise and is accepted by the
complete Section 10 four-face dispatch.

In the incoming/nonrejoin case, the second edge makes `i` stable at `U`
against reversing its membership, and `r_V(b)<=r_U(b)` makes absent `b`
stable against joining.  If `U` is nonempty, failure of the sure-exit test
must therefore be witnessed by a label outside `{b,i}`.  If `U` is empty,
then necessarily `T={i}`; the strict edge gives `r_i(i)<0`, while the
nonrejoin inequality gives `r_b(b)<=0`.  Failure of all-Never supplies a
third player with positive singleton payoff.  In both cases the witness is
`k in F\{i}`, so the successive responsible labels `b,i,k` are distinct.

The proposition retains the first-edge `gamma`, makes no quantitative claim
on later edges, and does not claim that the remaining positional/three-edge
cells already compile.
