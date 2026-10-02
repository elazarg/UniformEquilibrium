# Review of Proposition 22.1 and Corollary 22.2

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

This review supersedes the positional gap I recorded for Corollary 21.2.  The
new comparison across the fourth side of the literal `{b,i}` square closes
exactly that gap, including the omitted-neighbor case in a six-cycle.

## Claim checked

Starting from

```text
S = T union {b},   U = T triangle {i},   V = U union {b},
S -> T -> U,
```

with the first edge carrying `gamma_(B,F)>0`, Proposition 22.1 claims an
exhaustive trichotomy:

1. `U` is stable in the two coordinates `{b,i}`;
2. `V` is stable in those two coordinates; or
3. the four vertices form the strict cycle `S -> T -> U -> V -> S`.

Corollary 22.2 then removes every earlier on-cycle/off-cycle/chord condition:
the strict cycle goes to the complete Section 10 semantic dispatch, while a
two-coordinate-stable corner can be destabilized only by one of the two
remaining labels.

## Sign audit

The square comparisons are exact.

- The strict edge `T -> U` says that player `i` strictly prefers the action it
  takes at `U` to its opposite action at `T`.
- If `r_U(b) >= r_V(b)`, absent `b` weakly prefers the action at `U`.  Thus
  both coordinates are stable at `U`.
- In the strict complementary case `r_V(b) > r_U(b)`, present `b` is stable at
  `V`.  Player `i`'s opposite corner there is `S`.  Hence
  `r_V(i) >= r_S(i)` makes `V` stable.
- If the last weak inequality fails, `r_S(i)>r_V(i)`, the two missing strict
  arrows are `U -> V` and `V -> S`.  Together with the supplied arrows this is
  exactly the displayed strict four-cycle.

The equality cases are assigned correctly: equality in the `b` comparison
goes to the stable `U` arm, and equality in the `i` comparison goes to the
stable `V` arm.  There is therefore no unassigned boundary case.

## Corner and terminal semantics

“Pure Nash corner” is correctly used only for the two-coordinate membership
face with the other two coordinates fixed.  The note then separately tests
the literal coalition against all four membership deviations.  If the full
pure terminal root fails, neither `b` nor `i` can be the strict witness, so a
destabilizer lies in `I \ {b,i}`.

The empty-corner sentence is also correct.  When `U=empty`, reversing `i`
returns `T`, so `T -> U` gives `r_i({i})<0`; stability of absent `b` gives
`r_b({b})<=0`.  Thus any profitable deviation from all-Never belongs to one
of the remaining labels.

For nonempty coalitions, the usual sure-exit membership test is the full
behavioral terminal test: nominal play terminates at date zero, and a
unilateral deviation reduces to the player's membership choice (with Never
as the empty opposite of a singleton).  No stationary-only substitution is
being made here.

## Section 10 handoff and positional scope

The Section 10 dispatcher depends only on the four static reward-table signs
and the appropriate fixed-base/passive tests.  It does not require the square
to be incident to the previously selected long cycle.  Its three base-size
cases cover the square here, and its successful arms audit unrestricted
behavioral deviations; its unsuccessful arms are explicitly retained as the
named semialgebraic residuals.  Thus no reachability hypothesis is smuggled
into the handoff.

The two-edge path reaches `U`; the third strict edge `U -> V` reaches `V` in
the second stable-corner arm.  In both cases the original paid edge `S -> T`
remains part of the recorded path.  Most importantly, the direct `V` versus
`S` comparison handles the former Corollary 21.2 item (d), where `S` is on a
six-cycle but `V` is an omitted vertex.  No selected outgoing edge from `V`
is needed anymore.

Accordingly the positional case split is genuinely subsumed.  The stated
remaining limitation is accurate: a stable two-coordinate corner plus a
third-label strict toggle is finite data, not yet a chronology or a compiler.
