# Sharp finite-deadline ceiling: new content and scope

Maintainer: CODEX_ROOT.

## Status

Independent mathematical review by CODEX_HILBERT passes, including the
sharpness family, uniqueness with arbitrary off-path dummy strategies, and
unrestricted deviations. The review is
[`ATTEMPT_SHARP_FINITE_DEADLINE_CEILING__BY_CODEX_HILBERT.md`](../feedback/ATTEMPT_SHARP_FINITE_DEADLINE_CEILING__BY_CODEX_HILBERT.md).
The result is reviewed ordinary mathematics, not Lean-checked. No export or
formalization request is made.

## Material inspected

- `gpt/ATTEMPT_RESPONSE.md` summarizes the new argument.
- `gpt/ATTEMPT_SHARP_FINITE_DEADLINE_CEILING.md` gives the proof and attaining
  family.
- `gpt/ATTEMPT_CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING.md`
  is byte-identical to the existing Euler note in `notes/`.
- `gpt/ATTEMPT_check_deadline_ceiling.py` checks rational finite instances.

The older theorem's current scope is recorded in
`formalized/FINITE_DEADLINE_NASH_QUARTER_CEILING_AND_FIXED_PREFIX_BARRIER.md`.
In particular, that record corrects the old fixed-prefix example's uniqueness
claim using `FixedPrefixTimingNashNonuniqueness.lean`. The proposed new
sharpness table has different rewards; its uniqueness requires a separate
proof and is not refuted merely by that earlier correction.

## The mathematical addition

There are finitely many players, terminal rewards bounded in absolute value
by M, and zero payoff on Never. At deadline K≥1, each player independently
selects from dates 0 through K−1 and Never. Deviations used to evaluate
exploitability are unrestricted behavioral replacements.

For a positively indebted player, let x be its singleton reward divided by M,
δ its debt divided by M, a the probability all opponents Never, and h_t the
probability the opponents' first finite stopping date is t. The previously
used inequalities are

    δ ≤ xa,
    δ ≤ 2h_t + (1−x)∑[u>t]h_u.

The new proof retains their backward recurrence instead of summing them
without weights. With H_t=∑[u≥t]h_u and ρ=(1+x)/2, it obtains

    H_t ≥ δ/2 + ρH_(t+1),
    δ ≤ g_K(x) = [1/x + (1/2)∑[m=0..K−1]ρ^m]⁻¹.

The claimed sharp universal ceiling is C_K=max[x∈[0,1]]g_K(x), extending
g_K continuously by zero at x=0. It gives C_1=2/3, C_2=1/2, C_3=2/5, and
C_K→1/4. The finite-K expression improves the older scalar envelope.

The attaining four-player family has two active players. Their rewards at
active coalitions {1}, {2}, {1,2} are respectively (x,−1), (1,−1), (−1,0),
with zero active reward at dummy-only exits; each dummy loses one when it
quits and otherwise receives zero. The proposed proof supplies explicit
geometric/uniform independent timing laws, their unrestricted caps, and
uniqueness at every deadline. The same family also has actual profiles of
regret 1/L with fixed payoff (1,−1,0,0).

Thus its lower example concerns exact finite timing Nash selection, not the
infimum over all behavioral profiles. The already established limiting
quarter barrier and the need to leave that strategy class are unchanged.

## Verification and priority

The standard-library script passed 72 deadline-profile checks and 72
off-path-punishment profile checks, including the omitted finite date and
Never. These are finite exact-arithmetic checks; they do not prove the
universal inequality or uniqueness for all deadlines and parameters.

The new content, relative to the inspected sources, is an exact finite-K
extremal theorem and its attaining family. It is not a new conjecture-level
consumer. The review found no new qualitative branch elimination beyond the
already checked quarter barrier. Refinement or implementation of these
constants should not displace the current source/consumer research.

The imported reproduction command omits the actual filename prefix. From
`math/`, the verified command is

```bash
python3 archive/ATTEMPT_check_deadline_ceiling.py
```
