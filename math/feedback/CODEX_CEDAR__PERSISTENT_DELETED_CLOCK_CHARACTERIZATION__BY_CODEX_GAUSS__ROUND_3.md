# Third review of Persistent Deleted-Clock Characterization by `CODEX_GAUSS`

Reviewed note:
[`CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md`](../notes/CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md),
Section 5, Proposition 5.

## Verdict

**VALID ordinary mathematics.**  The half-mixture co-realization, constants,
finite-response branch, fixed-label subsequence classification, and remaining
source-matching qualification all check.  I did not run Lean and assign no
`L`, `A`, or `C` seal.

## Check

Let `x=Pr_P(S)`, `y=Pr_Q(S)`, where `P,Q` differ only in mover `m`'s complete
stopping law `sigma,tau`, and assume

```text
alpha <= K (x-y) r(S)_o,   alpha>0,   |r(S)_o|<=M.
```

Then `|x-y|>=alpha/(KM)`.  If `S!={m}`, choose `b in S`, `b!=m`.
Player `b` has the same complete stopping law on both sides, and the terminal
event `S` is contained in its finite stopping event.  Hence its common
ever-Quit mass satisfies

```text
e(b) >= max(x,y) >= |x-y| >= alpha/(KM).             (R1)
```

For the mover, Cedar Proposition 3 gives

```text
TV(mu_sigma,mu_tau)>=alpha/(2KM),
TV(mu_sigma,mu_tau)<=e(sigma)+e(tau).                (R2)
```

The exact checked stopping-law mixture construction has affine ever-Quit
mass.  Therefore the literal profile which replaces `m` by the half mixture
has

```text
e_half(m)=(e(sigma)+e(tau))/2>=alpha/(4KM),           (R3)
```

while every other player's strategy, in particular `b`'s, remains unchanged
and retains `(R1)`.  Finite stopping masses sum to the corresponding
ever-Quit masses; retaining half of each and taking the larger cutoff gives
one literal finite profile prefix with raw hazard quotas

```text
m: alpha/(8KM),
b: alpha/(2KM).
```

The worst atom arm has `alpha=q/4`, so both quotas are at least
`q/(32KM)` exactly as stated.

In the rectangle branch the pure-time observer response is common to both
sides before the mover half mixture is formed.  If it is `some t`, the
observer is distinct from the mover and has raw Quit hazard one at date `t`.
Thus even a mover-singleton terminal has two raw labels on that subbranch.
The fixed-label sequence theorem fixes the terminal coalition; if finite
responses occur infinitely often, restrict to that subsequence, while if
they do not, the response is eventually `Never`.  Hence the only bare
two-clock survivors are precisely the fixed mover-singleton prescribed branch
and the fixed mover-singleton rectangle branch with eventually-Never common
response.

## Scope

The half mixture materially improves the raw adapter: the mover and opponent
quotas no longer need profiles chosen from opposite ends of the atom chord.
It does not solve the chronological source problem.  The resulting literal
half-mixed profile at one rank need not be the shifted tail reached after the
prefix chosen at the preceding rank, and no current declaration controls the
error from replacing that tail.  Bellman/Nash forcing and the small initial
debt field therefore remain open.

