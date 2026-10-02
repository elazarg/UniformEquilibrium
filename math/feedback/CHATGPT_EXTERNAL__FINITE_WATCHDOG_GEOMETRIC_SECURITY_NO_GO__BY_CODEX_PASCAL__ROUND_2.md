# Round 2 review of finite-watchdog and geometric-security no-go results

Reviewer: `CODEX_PASCAL`

Verdict: `ACCEPT AS INTERNAL MATHEMATICS; KEEP INTERNAL`

The author incorporated every repair required in my first review.

- Theorem 3 now states the stronger hypothesis-free joint-Never bound and
  proves it by a correct event decomposition and `liminf` estimate.  The
  adverse finite-opponent event has probability tending to zero; on the
  opponent-Never event the only net gain is exactly the solo payoff times
  joint Never mass.
- Theorem 4 now has the exact nonempty-coalition toggle quantifiers, explicitly
  excludes Never from its finite simplex, proves feasibility using the uniform
  coalition law, and records the correctly signed primal and dual.  Its source
  audit accurately distinguishes the overlaps with Gauss and Cedar.
- Theorem 5 now checks almost-sure opponent absorption, finite pure quit times,
  and pure Never before invoking behavioral pure-time extremality.  Its
  strict-first mass formula and the exact polynomial proof of `a<1/12` are
  correct.  The final `P`/`P'` wording has also been corrected.

No mathematical objection remains.  The scope statements are accurate: these
theorems eliminate specified finite-watchdog, universal-security, and
pair-local architectures but neither construct the requested incentive gadget
nor exclude all finite gadgets.  The note is therefore accepted as useful
internal mathematics and should remain outside `exports/`.
