# Review of Corollary 6BA

## Claim checked

Corollary 6BA extends the reviewed zero-Never periodicization of Proposition
6AZ to the pure-time rectangle arm when the rectangle observer is the second
retained source label and the mover's full replacement law also has zero
Never mass.

## Verdict

**PASS in the stated conditional periodic-source scope.**  The killed-tail
orientation, unrestricted cap coupling, debt constant, and preservation of
the rectangle witness all check.  The result does not produce the three
zero-Never hypotheses from the frontier and does not enter an arbitrary
supplied reached port.

## Checks

Let `observer=second`.  On the source side, deleting the observer leaves the
unchanged mover marginal `P_first`; its word survival tends to zero because
`NeverMass(P_first)=0`.  On the full-endpoint side, deleting the observer
leaves `R_first`, whose word survival tends to zero by the new hypothesis.
These are exactly the two environments needed after applying the same
observer pure-time override to the original and periodic profiles.  There is
no mistaken use of the deleted `P_second` clock.

Within each source or endpoint comparison, the original and periodic
overridden profiles agree through the first `L` rows.  They can differ only
if all opponents of the observer survive that word.  On the endpoint this
event is contained in survival of `R_first`.  Therefore, uniformly over every
behavioral deviation of the observer,

```text
|payoff_periodic(deviation)-payoff_original(deviation)|
  <= 2M Survival_Rfirst(L).
```

Taking suprema preserves the same bound, proving `(6BA.2)` for the
unrestricted cap.  The prescribed payoff has the same `2M` estimate.  Hence

```text
d_periodic-d_original
  <= |B_periodic-B_original|+|U_periodic-U_original|
  <= 4M Survival_Rfirst(L),
```

which is the claimed one-sided debt excess `(6BA.3)`.  No factor is missing.

The fixed pure-time override is identical on each original/periodic pair.
The four terminal comparisons therefore retain their mover, observer,
terminal orientation, and witness; their prefix-tail errors vanish by the
source `P_first` or endpoint `R_first` survival just identified.  Thus a
fixed smaller rectangle atom and the original small endpoint-debt estimate
survive for sufficiently large `L`.

The scope disclaimer is exact.  The ordinary packet supplies neither zero
Never mass for the two actual source labels nor for `R_first`; these remain
extra hypotheses.  Periodicization constructs a nearby self-loop source and
does not solve arbitrary entry, likelihood selection, or frontier
production.

## Source inspected

- `notes/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md`, current
  Proposition 6AZ and Corollary 6BA.

