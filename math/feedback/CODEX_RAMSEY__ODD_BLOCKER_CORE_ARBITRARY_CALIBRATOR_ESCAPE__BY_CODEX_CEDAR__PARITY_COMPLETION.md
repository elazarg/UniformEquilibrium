# Independent falsification of the cyclic interval-core parity completion

Reviewer: `CODEX_CEDAR`

Verdict: **PASS, no repair**, as ordinary mathematics in the displayed
cyclic interval-sandwich class.  This review is independent of the earlier
odd-core reviews and checks the newly appended even-cardinality arm.

## Boundary alternation

Use the same constrained Nash vectors on

```text
[epsilon,1]^K x [0,1]^(I\K)
```

and take a limit.  The already literal band argument gives the two eventual
signs: a blocker tending to zero forces its predecessor to rate `1`, while a
blocker tending to one forces its predecessor to rate `epsilon` and hence to
zero.  Therefore, if any limiting core coordinate is zero or one, backward
iteration determines the whole cyclic word as

```text
0,1,0,1,... .
```

This is inconsistent for odd cardinality and consistent for even
cardinality.  When the even cardinality is at least four, the word contains
at least two distinct sure core quitters.

## Division-free best-response limit

The boundary proof correctly avoids dividing by an opponent-absorption
probability before it is known positive.  Put

```text
D_i(q)=delta_i(q)*(Q_i(q)-N_i(q))
      =delta_i(q)*Q_i(q)-A_i(q).
```

This is a finite polynomial in the product rates.  Fractional linearity gives
the constrained optimality inequality

```text
p D_i(q^epsilon) <= q_i^epsilon D_i(q^epsilon)
```

for every legal alternative `p`.  For a core player and arbitrary fixed
`p in [0,1]`, `p_epsilon=max(p,epsilon)` is legal and converges to `p`.
Calibrator alternatives need no modification.  Passing to the limit gives

```text
p D_i(q*) <= q_i^* D_i(q*)
```

for every player and every rate `p`.  The notation `q_i^* D_i` is ordinary
multiplication, as the note clarifies.

In the alternating even boundary, at least two core rates equal one.  Hence
every player has a positive-rate core opponent, including a sure core owner
after its own clock is deleted.  Thus every `delta_i(q*)` is strictly
positive, and the division-free inequality is exactly the endpoint
complementarity for the stationary root.  In the interior alternative the
same conclusion follows directly from constrained optimality.

## Exact and unrestricted semantics

Stationary complementarity together with the multiplied stationary-payoff
identity gives the exact Bellman fixed point and endpoint Nash certificate.
The two sure core hazards in the boundary alternative make joint Continue
and every player-deleted Continue product strictly below one.  The named
stationary endpoint compiler therefore controls arbitrary unilateral
behavioral replacement, including finite times, ties, history dependence,
randomization, and Never, and supplies the uniform-equilibrium payoff.

The exclusion of a size-two even core is exact.  Its alternating word has
only one sure core quitter; deleting that player can leave joint Continue
mass one for the remaining arbitrary clock, so the contraction premise used
by the all-behavior compiler is unavailable.  The corollary makes no claim
that such a table lacks some different equilibrium.

## Scope

This proves existence for one cyclic core of any size at least three under
the strict literal interval sandwich.  It does not allow weak or overlapping
bands, multiple unrelated cycles, background sign reversal, or construct an
incentive gadget.  Because this is another unrestricted strategy-class
extension, it still needs the other independent review and a packet-level
gate before entering an export amendment.

