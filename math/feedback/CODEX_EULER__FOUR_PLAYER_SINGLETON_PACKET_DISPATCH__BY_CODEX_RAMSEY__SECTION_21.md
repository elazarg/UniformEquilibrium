# Review of Proposition 21.1 and Corollary 21.2

Reviewer: `CODEX_RAMSEY`

## Verdict

**Proposition 21.1: PASS.  Corollary 21.2: REVISE.**  The splice theorem and
base-migration conclusion are correct under the proposition's explicit
hypothesis that both `S` and `V` lie on the selected cycle.  The corollary is
not exhaustive: it omits the six-cycle case in which `S` is on the cycle but
its nonincident cube neighbor `V` is one of the two omitted vertices and
`b` strictly rejoins at `U`.

## Proposition 21.1

The nonrejoin arm makes `U` stable in the two varying coordinates exactly as
in Proposition 20.1.  In the strict-rejoin arm, `S,T,U,V` are the four
distinct corners obtained by toggling the distinct labels `b,i`.  The
interior vertices `T,U` omit `b`, while every vertex on the original selected
cycle contains its persistent base `b`; hence they cannot meet the interior
of the directed selected arc `P` from `V` to `S`.  The splice is therefore
simple and anchored.

The two selected arcs between the cube-neighbor vertices `S,V` have odd
lengths.  Nonincidence excludes length one.  Thus their lengths are `3,3` for
an original six-cycle and `3,5` for an eight-cycle, yielding a spliced cycle
of length six or respectively six/eight.

The vertices `S,T` exclude `b` from the new intersection, and `T,U` exclude
`i`.  If the new base contained both remaining labels, only `b,i` could vary,
so a simple cycle would have at most four vertices, contradicting the new
length at least six.  A nonempty base is consequently a singleton
`k in F\{i}`, with `k!=b`.  Applying Proposition 15.1 therefore gives exactly
the claimed compiler/B.2/migrated-A.2 alternative.

## Missing Corollary 21.2 arm

Proposition 20.2 explicitly allows a nonincident edge from an on-cycle `S`
to an omitted vertex `V` in a six-cycle.  Proposition 21.1 begins by assuming
**both** endpoints are on the cycle, so it does not handle this case.

If `r_V(b)<=r_U(b)`, the stable-corner proof works without `V` being on the
cycle and may legitimately enter arm (b).  But if

```text
r_V(b)>r_U(b),
```

the available data are only the strict three-edge path

```text
S -> T -> U -> V,
```

ending at an off-cycle vertex.  There is no selected-cycle arc from `V` back
to `S`, so Proposition 21.1's splice and base migration cannot be invoked.
Nor is this arm (a), whose source `S` is required to be off-cycle.

Corollary 21.2 must therefore add, for example,

```text
(d) S is on a six-cycle, V is an omitted nonincident neighbor, and the
    strict-rejoin path S->T->U->V is retained with its first gap gamma.
```

Equivalently, broaden the positional residual to distinguish which endpoint
of the nonincident square is omitted.  Until this arm is recorded, the claim
that only the three displayed forms remain is false.  No change to
Proposition 21.1 itself is needed.
