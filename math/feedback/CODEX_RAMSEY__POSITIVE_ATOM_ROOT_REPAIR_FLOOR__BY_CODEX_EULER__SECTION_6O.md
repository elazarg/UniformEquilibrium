# Focused review of Proposition 6O / the two-tier first-row estimate

Reviewer: `CODEX_EULER`

## Verdict

`(6O.2)` is **VALID** with the stated local scope.  A candidate head with
small coordinate debt cannot hide a fixed literal root defect without paying
the same amount, up to the candidate debt, in the prescribed-plus-cap seam.
This does not rule out changing the first root or tail, nor an adapter whose
first literal row has no fixed defect.

## Checked calculation

Let

```text
F=quittingTerminalSemanticPrefix reward q z,
c=(u,b),
E_i=|u_i-F.U_i|+|b_i-F.B_i|.
```

The hypothesis `debt_i(z)>=0` is exactly the hypothesis consumed by
`quittingRootCoordinateNashDefect_le_terminalSemanticDebt_prefix`, so

```text
rootDefect_i(q,z.U)<=debt_i(F).                      (1)
```

Expanding `debt=B-U` gives

```text
debt_i(F)-debt_i(c)
 =(F.B_i-b_i)-(F.U_i-u_i)
 <=|F.B_i-b_i|+|F.U_i-u_i|
 =E_i.                                              (2)
```

Therefore `debt_i(c)<=eta` and `(1)--(2)` imply

```text
rootDefect_i(q,z.U)<=eta+E_i,
```

with no missing sign assumption on `debt_i(F)` or on the candidate pair.
Consequently a tail-independent lower bound `rootDefect_i>=gamma` forces
`E_i>=gamma-eta`.

The displayed `E_i` is exactly the one-coordinate contribution obtained by
adding the absolute prescribed-coordinate seam and cap-coordinate seam.  It
therefore matches the compiler's additive `A+B` ledger at this row; there is
no hidden max-versus-sum constant.

## Scope

The lower bound is first-row and tail-specific.  It establishes a necessary
seam payment if the adapter retains the literal root `q` and a tail `z` on
which that root has defect at least `gamma`.  It does not show that every
root-changing repair has such a defect, that a fixed total seam must be paid
somewhere else, or that no nonsemantic two-tier adapter exists.  The note's
qualification is therefore exact.

## Source audit

The lower inequality is the checked declaration
`quittingRootCoordinateNashDefect_le_terminalSemanticDebt_prefix` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectCharge.lean`.
The upper half of `(6O.1)` is also correctly attributed there to
`quittingTerminalSemanticDebt_prefix_le_nashDefect_add_transport`, although
`(6O.2)` itself only needs the lower half and the elementary triangle
inequality above.
