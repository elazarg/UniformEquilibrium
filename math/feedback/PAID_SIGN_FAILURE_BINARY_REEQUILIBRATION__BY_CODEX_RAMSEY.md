# Export-gate review: Paid sign-failure binary re-equilibration

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

I independently checked the packet against every item in
[`exports/README.md`](../exports/README.md).  I found no unresolved
mathematical or scope objection.

## Exact finite classification

With `e=0` denoting the old action of `x`, the paid deletion of `c` gives
`J_0 <= -gamma`, failure of that old action after deletion gives `E_0>0`,
and its stability before deletion gives `E_1<=0`.  The `xor` convention keeps
these signs correct for both old actions of `x`.

The three cases in (4) exhaust the weak boundary faces:

- `J_1<=0` makes `(h,e)=(0,1)` a pure Nash cell;
- `J_1>0,E_1=0` makes `(1,1)` a pure Nash cell; and
- `J_1>0,E_1<0` gives the strict matching-pennies chamber
  `J_0<0<J_1`, `E_1<0<E_0`.

In the strict chamber the two indifference probabilities are exactly

```text
Pr(h=1)=E_0/(E_0-E_1),
Pr(e=1)=-J_0/(J_1-J_0).
```

Multiplying their independent product law by
`H=(E_0-E_1)(J_1-J_0)` gives precisely the four displayed `W_he`.  Every
weight is positive and their sum is `H`.  The equality faces are assigned to
the pure branches, so no boundary case is omitted or counted as a strict
mixture.

## Remaining signs and all-behavior handoff

Because every `O_he` contains `d`, `Delta_y^he` is always a terminal
Quit-minus-Continue difference.  Its expectation is `N_y/H`; hence the two
orientation-dependent signs in (9) are exactly the support condition for the
fixed pure action `j`.

For the sure owner `d`, continuing reaches `T_he` when it is nonempty and is
priced at `chi_d` when it is empty.  Quitting pays
`r_(T_he union {d})(d)`.  Therefore `k_d^he` is the cellwise
Continue-minus-Quit floor excess and `K_d/H` is its exact expectation.  The
empty punishment cell is handled explicitly, without pretending that the
punishment value is an attained terminal row.

Thus the selected `{c,x}` equilibrium, the `y` sign, and `K_d<=0` instantiate
the hypotheses of
`nonempty_quittingSingletonBaseCertificate_of_inducedNash`.  Since the player
set is exactly `{c,d,x,y}`, there is no omitted outsider test.  The named
`QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` consumer is the
checked unrestricted-behavior step; the finite calculation itself is not
misrepresented as an all-stopping-time argument.  Since `H>0` in all three
arms, the stated residual (10) is exactly the negation of the two accepted
weak tests.

## Source, novelty, and probability audit

The actual source chain is correctly identified: the pure arm of
`paidPure_or_paidMixed_of_forall_binaryNash` supplies the paid cell, and the
accepted `PURE_PAID_BASE_LEAVE_DESCENT` reduction exposes precisely a retained
free-label sign failure or owner premium after deletion.  Swapping the two
free labels once is enough to put a sign failure in the displayed `x`
coordinate.

The mixed object is an ordinary independent Bernoulli product root, not a
correlated lottery or a mixture of complete stopping laws.  Because `d` Quits
surely, deviations of the free players are date-zero action comparisons;
only `d`'s empty-cell deviation uses an accuracy-dependent punishment tail.
The packet clearly separates this finite induced-game algebra from the named
consumer covering arbitrary behavioral stopping times and Never.

The result is not a restatement of
`LargePersistentBaseDeletionAdapter.lean`: that checked adapter handles a
same-profile mixed deletion handoff, while this packet re-equilibrates a
failed pure retained action and eliminates the remaining real Nash parameter
into two pure cells or one division-free strict chamber.  This is a strict
finite narrowing of the named large-persistent-base obligation accepted by
`questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`.

## Boundary and handoff checks

The three numerical face tests correctly realize both equality boundaries and
the strict chamber.  In the strict test all four weights equal one.  The
positive compiler example has `N_y=K_d=0`.  The two negative tests separately
realize `N_y>0` for `j=0` and `K_d>0`; in the latter, `chi_d=0` follows because
all of `d`'s terminal rewards are either `-1` when it participates or `0`
otherwise, while Never guarantees zero.

The Lean handoff names the existing source and consumer declarations, exposes
the mixed weights and the two residual numerators as theorem output, includes
both equality faces and the empty punishment branch, and does not assume the
desired singleton-base certificate as an input field.

The nonclaims are accurate: the packet consumes only the pure retained-sign
failure, not the owner-premium, sure-exit, all-Continue, or mixed-deletion
residuals, and it makes no chronology or general cycle claim.
