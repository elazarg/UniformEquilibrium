# Review of Section 11

Reviewer: `CODEX_RAMSEY`

Claim reviewed: in the fully aligned `rootedTwo_next` geometry, applying the
terminal leave-or-join toggle at the literal owner--collider pair either
forces a two-gap owner underpayment from pair to solo or produces a distinct
outsider with a gap-sized join gain.  This is then intersected with the
already aligned hard-pair crossing.

## Verdict

**PASS** in the stated finite semantic-reduction scope.  Neither alternative
is an executable compiler, and the note correctly retains that nonclaim.

## Audit

Put `P={o,c}`.  The collision certificate gives `c!=o` and

```text
r({o})(c)+gamma <= r(P)(c).
```

The checked `exists_leave_or_join_gain P` has exactly two cases.  In its
leave arm the selected member lies in the two-element set `P`, hence is `o`
or `c`.

If it is `c`, erasing it from `P` gives `{o}` and the leave inequality is

```text
r(P)(c)+gamma <= r({o})(c).
```

Adding this to the collision inequality yields `2*gamma<=0`, contradicting
the terminal witness's `gamma>0`.  Thus the selected member is `o`; erasing
it gives `{c}` and

```text
r(P)(o)+gamma <= r({c})(o).
```

The reverse preemption hypothesis is
`QuittingSoloPreempts reward gamma c o`, whose definition is exactly

```text
r({c})(o)+gamma <= r({o})(o).
```

Adding gives `(11.2)` with the full constant `2*gamma`.  The other
preemption orientation is not accidentally used.  In the join arm, the
checked toggle theorem already supplies `s notin P` and
`r(P)(s)+gamma<=r(insert s P)(s)`, exactly `(11.3)`.

For Corollary 11.2, the reviewed two-cycle alignment identifies the hard
principal with the same literal pair `P`.  `cardTwoCrossing` gives one
positive helper for each receiver row outside that pair.  Its internal
`first/second` enumeration may be swapped, but the structure is symmetric,
so relabeling them as `o,c` yields `(11.8)` exactly.  The Fin-4 incidence
observation is also correct: the complement of `P` has two labels; if the
joiner differs from each of the two helper choices, those helper choices
must coincide.  This does not assert uniqueness of either existential
helper.

## Scope

The owner arm compares terminal rewards at `P`, `{c}`, and `{o}` but does not
make the owner able to realize its solo row from a reached pair.  The join
arm is a strict obstruction to a sure pair, not a stable replacement.  The
hard-pair helpers concern singleton rows and do not orient either
nonsingleton comparison.  Thus the result is a valid same-label semantic
calculation, not a Bellman root, sure-exit set, chronology, or uniform-payoff
consumer.
