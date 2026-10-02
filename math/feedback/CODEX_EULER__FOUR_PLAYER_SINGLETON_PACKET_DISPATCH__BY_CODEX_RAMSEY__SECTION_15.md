# Review of Proposition 15.1 and Corollary 15.2

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS.**  The ordered cycle case split, both residual systems, compiler
handoffs, and compact-interior corollary are correct in the stated static
finite-dispatch scope.

## Proposition 15.1

The cases are exhaustive under the stated testing order.  A four-cycle is
sent first to the complete Section 10 screen.  For every remaining simple
cycle, `B` is either nonempty or empty.  When `B` is nonempty, the free binary
game on `F` has a nonempty compact Nash set; for four players its support
conditions are covered by at most `3^|F|<=27` finite cells.

The persistent-base defect `G` is exact.  For `|B|>=2`, an outsider's only
relevant alternative is joining the sure-exit row, giving `J_o-V_o`, and a
base member can leave while another base player still quits surely, giving
the second line of (15.2a).  For `B={b}`, only the induced-game empty action
event reaches the punishment after `b` leaves, giving precisely (15.2b).
The maximum family is nonempty.  `G<=0` is exactly Proposition 11.1's legal
compiler input.  Under the terminal exploitability witness every induced
Nash point must have `G>0`; continuity on the compact Nash set therefore gives
the strictly positive attained minimum (15.2c).  The punishment value is
used only as the explicitly supplied scalar in the singleton-base formula.

When `B` is empty, a non-four-cycle in the four-cube has at least three active
coordinates, so the opponent absorption denominators `d_i` and full
absorption denominator `delta` are positive at every interior rate vector.
The formulas

```text
H_i=d_i Q_i-N_i,
P_o=delta J_o-A_o
```

are respectively the active indifference equation and the cleared passive
Continue inequality.  A solution of (15.3c)'s negation is exactly the input to
the checked stationary endpoint compiler.  At least two positive active
hazards give every player's opponent contraction, so the named consumer
covers unrestricted behavioral deviations and Never, not just stationary
deviations.

The maintained terminal witness excludes each accepted compiler branch:
each would yield either an exact terminal Nash profile or terminal
approximations at every error with one fixed target, and the cited checked
consumers then yield a uniform-equilibrium payoff.  Therefore the cycle lands
in the corresponding finite failure output.  The argument does not turn that
failure output into a chronology or a payoff.

## Corollary 15.2

On `[rho,1-rho]^F`, `W` is continuous and nonnegative.  `W=0` is equivalent
to all active equations `H_i=0` and all cleared passive inequalities
`P_o<=0`; when `O` is empty the passive maximum is correctly read as zero.
Residual (15.3) excludes such a point throughout the compact box, so the
attained minimum `gamma_rho` is strictly positive.  Hence any sequence with
all displayed active/passive defects tending to zero eventually leaves every
fixed interior box, which is exactly (15.6).

The scope qualification is essential and correct: neither the static strict
cycle nor residual (15.3) produces a vanishing-defect stationary sequence.
The corollary only screens an additionally supplied sequence and says its
rates escape to a coordinate face; it does not identify a lower-dimensional
compiler at that face.

