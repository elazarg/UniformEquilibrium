# Review of Propositions 18.1--18.2

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS with one scope-wording repair.**  The gap localization, all-normal
floor exclusion, and one-step promotion are correct.  Replace the last
description “finite pair/triple reward-table reduction” by “finite
nonsingleton reward-table reduction” (or explicitly “pair/triple/grand-
coalition”).  In a four-player persistent face the localized edge can be
triple-to-grand or grand-to-triple, so the current phrase is too narrow even
though none of the formulas or conclusions relies on that phrase.

## Proposition 18.1

At a minimizing Nash point, one expression in the finite maximum defining
`G` equals `gamma`.  The outsider expression is exactly

```text
sum_R mu(R) [r_(B union R union {o})(o)-r_(B union R)(o)],
```

and, for `|B|>=2`, the base expression is exactly the corresponding average
of pure base-leave gains.  For `B={b}`, expanding `V_b` makes the nonempty
cells the same pure leave gains and the empty cell

```text
chi_b-r_b(b).
```

Since the weights form a probability law, an average at least `gamma` has a
summand at least `gamma`.  This remains true on support-cell boundaries; no
interiority or positive weight for every pure cell is assumed.

The crossed support-two floor exclusion is also exact.  Positive packet mass
makes both support owners punishment-normal.  For either outsider `x`, the
crossed inequality supplies a distinct owner `h` with `r_h(x)<r_x(x)`.
If `x` were abnormal, `abnormal_singletonFloor_chain` would give
`r_x(x)<chi_x<=r_h(x)`, a contradiction.  Thus all four players are normal
and `chi_b<=r_b(b)`, excluding a positive floor deficit.

This genuinely narrows A.2: its compact uniform gap is localized to one
literal toggle transverse to the old face.  It neither assumes nor produces a
vanishing stationary-defect sequence.

## Proposition 18.2

For a join `T=S union {o}`, failure of the sure-exit inequalities at `T`
is exactly an old-member leave, the entrant `o` leaving, or a remaining
outsider joining.  The retained sign
`r_T(o)-r_S(o)>=gamma>0` excludes the entrant-leave case.

For a base leave `S=T union {b}`, the target is nonempty: if the base has at
least two members, one remains, while in the singleton-base case Proposition
18.1's pure leave cell has `R nonempty` (the empty cell is the separate floor
case).  Failure of sure exit at `T` is a member leave or outsider join, and
the retained sign `r_T(b)>r_S(b)` excludes immediate re-entry by `b`.

Under the terminal exploitability witness, the pure sure-exit alternative is
excluded by the checked all-behavior consumer.  Hence the resulting two-edge
path is legal, preserves the quantitative first-edge label `gamma`, and does
not immediately undo its responsible player.  No quantitative lower bound on
the second edge and no chronological compiler are inferred.

The only requested repair is the final coalition-size wording noted above.
