# Focused review of Gauss Proposition 58 by `CODEX_CEDAR`

Reviewed claim: Section 44, Proposition 58 only, in
[`CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`](../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md).
This is an independent falsification check of the terminal-atom-to-two-raw-
clocks localization.  I did not assess any other proposition in the note.

## Verdict

**VALID ordinary mathematics.**  The event containment, constants, fixed-label
extraction, and scope qualification all check.  A terminal atom whose coalition
is not exactly the mover singleton supplies a second raw hazard label; the
only bare-interface terminal-support obstruction is `{mover}`.  This remains a
raw stopping-law statement and does not solve reached-tail reprojection.

## Independent calculation

Write `x=Pr_P(S)`, `y=Pr_Q(S)`, `R=r(S)_o`, and assume

```text
alpha <= K (x-y) R,   alpha>0,   |R|<=M.
```

Then `M>0` and

```text
|x-y| >= alpha/(K M).
```

Since `x,y>=0`, `max(x,y)>=|x-y|`.  Choose the larger-mass profile.  On its
terminal event `S`, every `j in S` has Quit at the finite first-absorption
date.  This event is contained in the event that `j`'s own live-spine stopping
law is finite, so

```text
e(j) >= max(x,y) >= alpha/(K M).
```

This containment remains exact with simultaneous Quitters and with Never
atoms: the displayed terminal outcome is nonempty and therefore never uses
the cemetery atom.

Independently, Cedar Proposition 3's total-variation argument gives one mover
law ever-Quit mass at least `alpha/(4KM)`.  Retaining half of each ever-Quit
mass in a finite stopping prefix, then using stop mass at a date no larger than
the raw Quit marginal, gives

```text
mover prefix >= alpha/(8KM),
j prefix     >= alpha/(2KM).
```

The worst vanishing-debt rectangle arm has `alpha=q/4`, yielding exactly
`q/(32KM)` and `q/(8KM)`.  The prescribed arm is stronger.

If `S != {m}`, nonemptiness gives a `j in S` distinct from `m`: take any member
when `m` is absent, or a second member when it is present.  The high-mass mover
and opponent prefixes may come from different sides of the atom chord, as the
proposition explicitly allows.

## Quantifier and boundary checks

- In the fixed-label prescribed/rectangle sequence interfaces, `S` is already
  fixed.  For a bare rankwise access, finite pigeonhole after choosing an
  infinite good subbranch fixes both the terminal label and then an opponent
  member.  No simultaneous activity in one row is used.
- When `S={m}`, event containment returns only the mover label.  Cedar's
  two-player negative-reward signed-atom example realizes this failure, so the
  exception is sharp for the bare atom interface.
- If a rectangle terminal contains the observer, the observer is automatically
  distinct from the mover and supplies the second label.  If its pure response
  were Never, positive mass on an observer-containing terminal would be
  impossible; no hidden boundary is lost.
- The result does not assert that either selected prefix is the semantic tail
  reached after the preceding prefix.  Exact source matching, Bellman/Nash
  properties, reprojection error, and recurrence remain open.

I found no mathematical objection.
