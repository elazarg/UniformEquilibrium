# Review of two-sure active-set stabilization and cut recentering

Reviewer: `CODEX_HAHN`

## Frozen object

Reviewed
`notes/CODEX_SPINOZA__TWO_SURE_CAP_ORBIT_ACTIVE_SET_AND_ESCAPING_CUT_RECENTERING.md`
at exact SHA-256
`df3d7cd3977c6c56eb37b106a813e6af0060276969b9aad5d2c0d31161574a32`.

## Verdict

**PASS as exact ordinary mathematics and as an orbit reduction, not as a
consumer.**  I found no mathematical error in the active-set stabilization,
opponent-reach floor, fixed-spectator Never conclusion, or literal suffix cap
recentring.  The two stated residuals are genuine.

## Reconstruction

1. Once a player is prescribed a deterministic finite clock, every later
   selected cap update of that player is again a deterministic finite clock.
   A selected player outside the current finite-clock set enters it.  Hence
   the active sets increase, stabilize after at most two additions in Fin4,
   and every later mover belongs to the stabilized set.  Each spectator law
   is then literally unchanged, not merely convergent.

2. For old and new mover times `T,T'`, their first disagreement is
   `r=min(T,T')`; both clocks Continue strictly before `r`.  The full gain
   factors as opponent reach `L` times the conditional suffix gain `G`.
   Bounded rewards give `|G|<=2M`, so a gain at least `Gamma` gives
   `L>=Gamma/(2M)` (with the harmless cap at one).  Any other active pure
   clock earlier than `r` would screen the replacement and force zero gain,
   proving its time is at least `r`.

3. After stabilization the active opponents' survival factors through `r`
   are all one.  Thus `L` is exactly the product of the fixed spectators'
   tail masses.  Along `r_m -> infinity`, continuity from above for each
   probability law on `Nat union {Never}` gives the product of the literal
   spectator Never masses.  No moving-law compactness is used.  A positive
   product also implies each spectator Never mass is positive; for a full
   active set the empty product is correctly identified as vacuous.

4. Suffix cap optimality is valid, not merely a gain statement.  Given any
   behavioral deviation in the conditional suffix at `r`, lift it to the
   original profile by making the mover copy its prescribed clock before
   `r`.  Because old and new mover clocks have the same pre-`r` behavior,
   the lifted improvement is `L` times the suffix improvement.  Since
   `L>0`, a strict improvement on the installed suffix clock would contradict
   its full-profile cap attainment.  The recentered installed clock therefore
   attains the unrestricted suffix cap, and its conditional gain is
   `G=(full gain)/L>=Gamma`.

5. At the recentered date zero exactly one of the unequal old/new mover
   clocks Quits and the other Continues.  The case where the old time itself
   equals the cut is covered: the source Quits at suffix date zero and the
   target Continues.  Every other active clock becomes a nonnegative finite
   suffix clock, so a distinct sure anchor remains.

## Surviving contribution and boundary

The new useful datum is the quantitative **actual** spectator-Never cylinder
in the proper-active escaping-cut arm, together with a literal date-zero
suffix cap edge.  It is stronger than a weak-limit Never conclusion because
the spectator laws have already stabilized exactly.

It still does not match the known finite-splice product: the Never factors
belong to unmoved spectators, while the exact cap edge changes an active
finite-clock player.  Nor does it address the full-active case, where the
Never product is empty, or the bounded-cut case, where clocks strictly after
the fixed front may escape.  Nothing in the proof turns the horizontal cap
edge into a Nash--Bellman edge or a renewable source return.

## Falsification checks

- Old mover time equal to the cut: recentering is still typed and the source
  mover Quits at date zero.
- Another active player at the cut: it remains a sure date-zero anchor; it
  does not invalidate suffix cap optimality.
- A spectator with positive finite tail but zero Never mass cannot satisfy
  the uniform tail-product floor along `r_m -> infinity`.
- Zero reach would invalidate conditional cap lifting, but the gain bound
  supplies the uniform positive reach before recentering.

