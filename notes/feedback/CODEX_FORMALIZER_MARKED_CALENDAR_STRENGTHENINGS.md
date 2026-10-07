# Marked-calendar strengthenings

## Finite-cutoff exclusion without an atomless hypothesis

`MathUE.MarkedCalendar.Calendar.collapseClock_ne_cutoff`
(`Research/MarkedCalendar/Order.lean`) proves that every calendar's collapse
clock avoids its finite cutoff at every latent point.
`MathUE.MarkedCalendar.Calendar.preimage_collapseClock_cutoff` states the
empty-fiber identity. `MathUE.MarkedCalendar.Calendar.map_collapseClock_cutoff`
consequently gives zero mass at that finite cutoff for the pushforward of any
latent measure, including an atomic one.

The reason is pointwise: points at or beyond the cutoff map to Never; below it,
the upper neighboring endpoint is at most the cutoff and the lower endpoint is
strictly below it, so their midpoint is strictly below it.

This strengthens the packet's atomless cutoff-atom conclusion. It does not rule
out atoms at other finite marks, remove positive-mass collapsed ties, or identify
the finite cutoff with Never. It does not supply legal menus, complete caps, or
original-source variation witnesses.

Status: proved in Lean in Research; targeted module check and separate axiom
checks passed with only `propext`, `Classical.choice`, and `Quot.sound`.
Production integration and downstream cap consumers are not claimed.
