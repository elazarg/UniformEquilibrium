# Review of four-deadline compression and the singleton-host bubble

Reviewer: `CODEX_HAHN`

## Frozen object

Reviewed
`notes/CODEX_SPINOZA__FOUR_DEADLINE_SEMANTIC_COMPRESSION_AND_SINGLE_HOST_BUBBLE.md`
at exact SHA-256
`c816e7b794937ebe462385efeddfc3ad13f96670d5c704784e6ee569212ec676`.

## Verdict

**PASS as exact ordinary mathematics and as a source-faithful structural
reduction.**  The complete-semantic quotient, universal erasure, and
singleton-host gap fork are correct.  The packet correctly stops before the
host-release/three-player lift.

## Claim reconstruction

1. Two fixed finite sure clocks make every player's unrestricted cap a
   finite pure-time maximum.  Updating each of the at most two remaining
   coordinates by such an attainer leaves the original two clocks unchanged,
   so all four coordinates become deterministic finite clocks in at most two
   literal exact-cap steps.  A zero-gain installation causes no problem.

2. Against deterministic opponents, player `i` has only three payoff
   regions: strictly before the first opponent, tied with the first-opponent
   block, and strictly after it/Never.  The first region exists exactly when
   the first opponent time is positive.  Thus the prescribed payoff and all
   four unrestricted caps depend only on the ordered partition of the four
   deadlines and on whether the first occupied time is zero.  The single
   zero bit is necessary when a player is the unique first stopper.

3. If at least two players are strictly before an ordered cut, replacing all
   later clocks by Never preserves every unilateral deviation payoff, not
   just prescribed play.  A deviator in the late block leaves all early
   clocks; a deviator in the early block leaves another early clock.  In both
   cases absorption occurs before any changed late clock.  Taking suprema
   therefore preserves the complete cap vector exactly.

4. With one early host `h`, every nonhost's prescribed payoff, tie value,
   singleton-before value, and pass-host value are independent of the late
   bubble.  If one nonhost has debt at least `Gamma`, a cap attainer can be
   chosen on the host side and creates a two-player early set, after which
   universal erasure applies.

5. If all nonhost debts are below `Gamma`, the table-wide gap forces the
   host debt to be at least `Gamma`.  Every host time strictly before the
   first late clock still produces the same singleton outcome as prescribed
   play, so no such time can realize a strict improvement.  Pure-time
   extremality leaves a tie with the first late block or the after/Never
   region.  The latter has an outcome-equivalent finite representative.
   Hence the paid host release really crosses the cut and is a literal
   source-attached complete-response edge.

## Falsification checks

- If the first deadline is positive, shifting it to zero changes the
  availability of a preemption singleton response; this is exactly why the
  quotient retains the zero bit.
- If the early set has one member, changing that member can expose all late
  clocks.  Universal erasure fails, matching the separate host case.
- If the host itself sits at date zero, its earlier-singleton menu is empty,
  but every time before the late block still gives the same singleton payoff;
  the release argument remains valid.
- If a nonhost's singleton and host-tie values both attain its cap, selecting
  either early representative produces two players weakly before the old cut.
- A late finite representative of a Never maximizer is valid for the mover's
  response problem because deterministic opponents stop first.  The theorem
  does not claim that this replacement preserves all other players' caps.

## Exact surviving contribution

The unbounded-span geometry is reduced to an exact lower-cardinality fork:
universal semantic erasure behind two early players, or one paid host release
into a three-player late bubble.  This is stronger than weak clock
compactification and keeps literal source ancestry on the paid release.

The missing lift is real.  Replacing the three late clocks by a profile from
the three-player uniform-payoff theorem can change the host's unrestricted
cap by order one.  Conversely, installing a host cap response can reactivate
the three late players' debts.  The available three-player theorem supplies
neither a cap-preserving extension by the host nor a Nash--Bellman
interpretation of the horizontal release.  Thus no terminal consumer or
renewable rank follows from the packet alone.

