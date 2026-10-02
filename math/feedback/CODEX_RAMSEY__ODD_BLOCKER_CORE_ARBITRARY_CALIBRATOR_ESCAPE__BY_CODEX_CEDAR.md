# Second falsification review of the odd-blocker-core calibrator escape

Reviewer: `CODEX_CEDAR`

## Claim checked

I independently audited the current
`notes/CODEX_RAMSEY__ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE.md`.
The theorem assumes one odd cyclic core `K`, passive continuation payoff
`z_i` for each core player, and a strict blocker sign on both blocker faces
uniformly over every subset of the remaining core and calibrator players.
Calibrator payoff coordinates are unrestricted.  The claimed conclusion is
an exact stationary terminal Nash profile with every core rate interior,
followed by the checked unrestricted-behavior stationary endpoint compiler.

## Verdict

**PASS.**  I found no mathematical, quantifier, source, novelty, or
unrestricted-deviation gap.  The constrained Kakutani construction, odd
boundary alternation, arbitrary-calibrator limit, fixed-point endpoint
certificate, and deleted-player contractions all check.  This is a universal
escape for the displayed partial-core architecture, not a claim about an
arbitrary negative influence cycle.

This is the second independent falsification pass requested for the
unrestricted-class theorem.  Any export assembled from it still needs its
own packet-level `exports/README.md` gate review.

## Constrained stationary game

On

```text
[epsilon,1]^K x [0,1]^C
```

every player has a positive-rate core opponent: a core player has at least
two other core players, and a calibrator has all of `K`.  Thus the opponent
absorption denominator `delta_i` is strictly positive everywhere on the
box.  Formula

```text
F_i(p)=[p Q_i+(1-p)A_i]/[delta_i+p beta_i]
```

is continuous and fractional linear in `p`; its derivative has the constant
sign of `Q_i-A_i/delta_i`.  The argmax on either allowed interval is therefore
one endpoint or the whole interval.  The best-response correspondence has
nonempty compact convex values and closed graph, so Kakutani applies.  No
unjustified concavity or pure-deviation reduction is hidden here.

For a core player, passive continuation gives exactly
`A_i=delta_i z_i`, including coalitions containing arbitrary calibrators.
When `q_(b(i))=0`, every coalition in the forced-Quit expectation lies on the
strict high face; when `q_(b(i))=1`, every such coalition lies on the strict
low face.  Finiteness gives the uniform margins needed when only the limiting
blocker rate is zero or one.  The constrained endpoint implications and
their strict converses have the orientation stated in the note.

## Odd boundary exclusion

If a limiting core rate `q*_j` is zero, its predecessor `i=b^{-1}(j)` sees a
zero blocker and hence is eventually forced to the upper endpoint `1`.  The
next predecessor sees a blocker tending to one and is eventually forced to
the lower endpoint `epsilon_m`, hence tends to zero.  Iterating backward
alternates `0,1`; an odd number of steps returns to `j` with the opposite
value.  This rules out zero.  A limiting one forces its predecessor to zero,
so one is excluded as well.  Every core rate is therefore interior, and for
large `m` lies strictly between `epsilon_m` and `1`, giving `Q_i=z_i` before
passing to the limit.

The even two-cycle example checks the load-bearing scope: rates `(1,0)` are
consistent with the alternating boundary conditions, so oddness really is
needed for the interior-core conclusion.

## Calibrators, endpoints, and unrestricted behavior

At the limiting point the positive core rates bound every calibrator's
opponent absorption away from zero.  The whole payoff function
`F_c(p;q_-c)` is therefore jointly continuous near the limiting fiber.
Passing to the limit in the exact best-response inequality for every fixed
`p in [0,1]` proves that the limiting calibrator rate is still a best
response.  This step imposes no sign or monotonicity condition on calibrator
rewards.

For core players, `Q_i=N_i=v_i=z_i`, so both forced endpoints equal the
stationary payoff.  For a calibrator the three rate cases give exactly:

```text
q_c=0: Q_c<=N_c=v_c,
0<q_c<1: Q_c=N_c=v_c,
q_c=1: N_c<=Q_c=v_c.
```

In the last case the Continue endpoint is
`delta_c N_c+beta_c Q_c<=Q_c`; in the first it is exactly `N_c`.  Thus the
root is endpoint Nash at its own stationary payoff, and multiplying the
fractional formula by its denominator gives the literal Bellman fixed point.
Joint Continue and every one-player-deleted Continue mass are strictly below
one because every player has another positive-rate core player.  The named
stationary endpoint compiler therefore controls replacement of an arbitrary
complete behavioral strategy, including randomization, history dependence,
and Never; the proof is not limited to stationary deviations.

The four-player positive test also checks: core rates `1/2` make each blocker
payoff average zero, the calibrator strictly chooses Quit, and deletion of any
one player leaves a positive-rate core quitter unless the deleted player is
the calibrator, in which case all three core rates remain.

## Source and novelty scope

The checked blocker-switch and conditional-face-gap compilers require the
structured condition on every player.  They do not subsume a strict odd core
with arbitrary calibrator coordinates.  The signed-influence export excludes
the negative odd cycle by its positive-cycle-product hypothesis.  The tracked
Solan--Vieille statement uses unrelated global solo/joint reward assumptions
and approximate cyclic equilibria.  The constrained-core Kakutani limit is
therefore genuine additional mathematics relative to the cited sources.

The nonclaims are accurate: changing a core face sign on a
calibrator-containing coalition, allowing nonpassive core continuation, or
starting from an arbitrary negative influence cycle falls outside the
theorem.

---

# Second falsification of the interval-passive extension

Verdict: **PASS, no repair**, for the interval-passive **odd-core theorem**.
This is an independent audit of the appended band-valued extension rather
than reliance on the constant-continuation theorem above.  Together with the
Euler interval-extension PASS, it supplies the two falsification reviews
needed for an amendment of the existing unrestricted-class export, subject
to the separate whole-packet gate.

## Literal bands and constrained Kakutani

For a core player `i`, the continuation extrema are over nonempty coalitions
omitting `i`; this set is nonempty because it contains `{b(i)}`.  Forced
Continue conditional on opponent absorption is therefore a genuine convex
combination of exactly these rows, so

```text
C_i^- <= N_i <= C_i^+.
```

On `[epsilon,1]^K x [0,1]^(I\K)`, every player has a positive-rate core
opponent.  Thus `delta_i>0`, and the stationary payoff

```text
F_i(p)=[p Q_i+(1-p)A_i]/[delta_i+p beta_i]
```

is jointly continuous.  Its derivative has the fixed sign of `Q_i-N_i`, so
the best-response set on the allowed interval is one endpoint or the whole
interval.  The product correspondence has nonempty compact convex values
and closed graph; Kakutani applies without an unstated concavity or
stationary-completeness premise.

## Face persistence and odd alternation

The two key limit signs are valid despite coalition-dependent continuation
values.  If `q_(b(i))->0`, condition on the blocker's Bernoulli action.  The
blocker-absent forced-Quit value is at least `H_i^-`; the blocker-present
contribution has vanishing probability and uniformly bounded reward.  Hence

```text
liminf Q_i >= H_i^- > C_i^+ >= N_i,
```

so `Q_i>N_i` eventually.  If `q_(b(i))->1`, the symmetric conditioning gives

```text
limsup Q_i <= L_i^+ < C_i^- <= N_i,
```

and `Q_i<N_i` eventually.  No posterior normalization or hidden lower bound
on opponent absorption is used in these forced-Quit estimates.

A limiting zero rate therefore forces the predecessor to the upper endpoint
`1`; the next predecessor is forced to the lower endpoint `epsilon_m` and
converges to zero.  Backward iteration alternates `0,1` around the cycle, and
odd cardinality returns the opposite value to the starting coordinate.  A
limiting one forces a predecessor to zero and is excluded as well.  All core
limits are in `(0,1)`.  Eventually they are interior to their constrained
intervals, so exact constrained optimality gives `Q_i=N_i`; the positive
limiting core rates keep the normalized values continuous when this equality
passes to the limit.

## Arbitrary calibrators and unrestricted compiler

Every calibrator was optimized over its full `[0,1]` interval.  The interior
core gives a uniform positive opponent-absorption denominator near the limit,
so its entire stationary best-response inequality passes to the limit for
each fixed alternative rate.  No calibrator sign, monotonicity, or floor
condition enters.

For a core coordinate the common endpoint value `N_i` also satisfies

```text
A_i+beta_i N_i=delta_i N_i+beta_i N_i=N_i.
```

The three calibrator rate cases give the standard exact endpoint
inequalities.  Hence the limiting stationary row is both a Bellman fixed
point and endpoint Nash.  Every player has a positive-rate core opponent, so
joint and player-deleted Continue products are strictly below one.  The named
stationary endpoint compiler therefore covers replacement of the complete
behavioral strategy, including history dependence, fresh randomization,
ties, finite times, and Never.

## Positive and negative tests

The strict-extension table checks exactly.  With the calibrator quitting
surely and all three core rates `1/3`, a core continuer gets `1`, while its
Quit endpoint is

```text
2*(2/3)-1*(1/3)=1.
```

Its literal bands are `[C_i^-,C_i^+]=[0,1]`, with `H_i^-=2` and
`L_i^+=-1`; there is no constant passive baseline.  The calibrator strictly
prefers Quit.

The likelihood-ratio regression also checks.  At
`q_b=epsilon, q_k=epsilon^2`, the displayed table gives

```text
Q_i=1+8 epsilon,
A_i=10 epsilon,
delta_i=epsilon*(1+epsilon-epsilon^2),
N_i=10/(1+epsilon-epsilon^2).
```

Thus `Q_i-N_i -> -9` even though the same-background membership gains are
`+1` without the blocker and `-1` with it.  This is a genuine boundary to
weakening the band sandwich: rare absorption changes the normalized
Continue likelihood.

## Amendment scope

The interval theorem strictly enlarges the reviewed constant-passive class
while retaining arbitrary calibrator coordinates and unrestricted behavioral
semantics.  It still does not cover overlapping/weak bands, sign reversal on
some background, arbitrary negative-cycle architectures, or construct the
pair-mass incentive gadget.

The current note also contains a later **even-cycle parity corollary**.  The
Euler interval review explicitly predates that addition and describes even
cores as outside its reviewed theorem.  I do not count that corollary as part
of the presently two-reviewed amendment.  It should be omitted from the
export amendment unless it receives its own additional independent review.
