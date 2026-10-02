# Normalized paid marks: compact relaxation and escaping-clock no-go

Author: `CODEX_RAMSEY`

Status: **proved ordinary-mathematics boundary; independent review
requested.**  A closed compact semantic relaxation of normalized marked debt
exists, but it forgets the operational paid row and does not make the
finite-cut descent total.  An explicit two-player escaping-clock regression
shows that absolute finite-delay and Snell-span marks are not closed, while a
translation/projective compactification retains exactly the inert
all-Continue fixed point.  Thus compactification alone cannot repair the
source-dependent descent or the `A=0` arm.

This is an architecture no-go from the current paid-cap fields.  The local
regression below does not have positive global minimum debt and is not a
counterexample to the quitting-game conjecture.  It shows precisely where a
proof using only compactness and the marked row must introduce additional
terminal-witness/global-minimum structure.

Primary inputs:

- [`PAID_CAP_PORT_EXACT_TRICHOTOMY_AND_INERT_STALL.md`](../exports/PAID_CAP_PORT_EXACT_TRICHOTOMY_AND_INERT_STALL.md);
- [`CHATGPT_EXTERNAL__NORMALIZED_PAID_FINITE_CUT_DESCENT.md`](CHATGPT_EXTERNAL__NORMALIZED_PAID_FINITE_CUT_DESCENT.md);
- review of that finite-cut argument:
  [`CODEX_RAMSEY`](../feedback/CHATGPT_EXTERNAL__NORMALIZED_PAID_FINITE_CUT_DESCENT__BY_CODEX_RAMSEY.md).

## 1. The strongest compact semantic relaxation

For a fixed observer `j` and `theta>0`, define

```text
K_(theta,j) = {X in quittingTerminalSemanticCarrier reward :
                 debt_j(X) >= theta*D(X)}.              (1.1)
```

The carrier is compact by
`quittingTerminalSemanticCarrier_isCompact`.  Coordinate debt and total debt
are continuous by `continuous_quittingTerminalSemanticDebt` and
`continuous_quittingTerminalSemanticDebtSum`.  Hence `(1.1)` is a closed
compact set, and `D` attains its minimum on every nonempty
`K_(theta,j)`.

The normalized finite-cut calculation preserves this relaxation.  Indeed
every cap prefix scales all debt coordinates by the same joint Continue
factor, so

```text
debt_j(X_N)/D(X_N)=debt_j(X_0)/D(X_0)                  (1.2)
```

whenever the denominator is positive.

This is the maximal easy compactification, but it is not the desired marked
class:

1. `debt_j>=theta D` does not store two pure-time witnesses, their temporal
   orientation, first disagreement, or an actual behavioral source;
2. the semantic carrier is a closure, so its minimizer need not be attained
   by one behavioral profile;
3. even at an attained point, `(1.1)` supplies no nonzero cap displacement
   `rho`, signed label mass, or absorbing cap root; and
4. in the inert arm an actual marked semantic point is fixed by all Continue,
   so attainment merely attains the obstruction.

Thus compactness of `(1.1)` can at most reduce the problem to an attained or
nonattained marked semantic minimizer.  It does not extend the finite-cut
descent to that minimizer.

## 2. An exact escaping-clock regression

Take two players `o,p`.  Define the terminal rewards by

```text
r_S(o) = 1  if S={o,p}, and 0 otherwise;
r_S(p) = -1 if p in S,  and 0 otherwise.                (2.1)
```

Let `sigma_0` be the deterministic profile in which `o` Never Quits and `p`
Quits at time zero.  Let `sigma_n` prefix `n` literal all-Continue product
rows before `sigma_0`.  Equivalently, `p` Quits surely at time `n` and `o`
Never Quits.

### Proposition 2.1 (constant semantic paid mark)

For every finite `n`,

```text
U(sigma_n)=(0,-1),
B(sigma_n)=(1,0),
debt(sigma_n)=(1,1),
D(sigma_n)=2.                                          (2.2)
```

Player `o` has a literal paid first-disagreement row

```text
source witness    = Never,
receiving witness = Quit at n,
live mass         = 1,
reached gain      = 1,
exact payoff difference Delta_n=1.                    (2.3)
```

Consequently its normalized paid density is the fixed value

```text
Delta_n/D(sigma_n)=1/2.                                (2.4)
```

**Proof.**  The prescribed terminal coalition is `{p}`, giving `(0,-1)`.
If `o` also Quits at time `n`, the coalition is `{o,p}` and `o` receives
one; every other pure stopping time gives `o` zero.  Hence `B_o=1` and
`(2.3)` holds.  Every finite Quit by `p` gives it `-1`, while Never gives
zero, so `B_p=0`.  This proves `(2.2)--(2.4)`. `QED`

### Proposition 2.2 (unique inert cap root)

Against the displayed cap `B=(1,0)`, the unique exact product Nash root is
all Continue.

**Proof.**  Player `p` receives `-1` whenever it Quits and zero whenever it
Continues, regardless of `o`'s root action, so exact complementarity makes
`p` Continue surely.  Given that, `o` receives zero from quitting alone and
the cap value one from Continue, so `o` also Continues surely. `QED`

Therefore the literal cap lift from `sigma_0` is exactly

```text
sigma_0,sigma_1,sigma_2,...,
A=0,
rho=0,                                                 (2.5)
```

and carries the unchanged normalized mark `(2.4)` with no absorption or debt
descent.

This regression is source-level rather than conjecture-level.  Its global
semantic minimum is zero at the all-Continue profile, so it does not
instantiate `QuittingPaidCapLiftedSource.minimum_pos`.  It nonetheless
realizes, with an actual reward table and behavioral profiles, every local
clock/cap/root phenomenon that a proposed compactification is meant to cure.
Positive global minimum must therefore be used operationally, not merely
listed as a compact lower bound.

## 3. Finite-delay passports are not a compact marked class

In the product topology on behavioral profiles,

```text
sigma_n -> sigma_infinity = all Continue.               (3.1)
```

Indeed every fixed time/history sees only Continue once `n` is large enough.
At `sigma_infinity`, prescribed payoffs and caps are both `(0,0)`: `o` can
only Quit alone for zero, and `p` can choose Never instead of a negative
Quit.  Hence

```text
D(sigma_infinity)=0,
every pure-time payoff difference for o is zero.        (3.2)
```

Thus the class of actual profiles carrying a paid difference at least one
contains every `sigma_n` but not its limit.  It is not closed.

No fixed finite-delay passport repairs this.  For any horizon `H`, if
`n>H`, every `o`-witness stopping by `H` Quits alone and pays zero; the unique
positive witness is at time `n`.  Hence no fixed finite set of witness times
contains the cap-lifted orbit.  Taking the union over `H` restores the orbit
but restores nonclosedness.

This is exactly the witness-time escape already present in the checked
`ShiftedPaidRow.start_eq` identity.

## 4. A closed Snell-span mark also fails

Let

```text
Span_o(sigma)=sup_t payoff_o(sigma[o<-t])
              -inf_t payoff_o(sigma[o<-t]),            (4.1)
```

with `t` ranging over finite pure times and Never.  The regression gives

```text
Span_o(sigma_n)=1,
Span_o(sigma_infinity)=0.                              (4.2)
```

The simpler regret/debt functional has the same jump:

```text
B_o(sigma_n)-U_o(sigma_n)=1,
B_o(sigma_infinity)-U_o(sigma_infinity)=0.             (4.3)
```

Therefore neither functional has the upper-semicontinuity needed to make a
positive superlevel marked class closed on behavioral profiles.  Replacing
the profile by its finite-dimensional semantic pair makes debt continuous,
but then the sequence is represented by the constant pair in `(2.2)` rather
than by the actual behavioral limit `(3.2)`.  That replacement is precisely
the loss of actual-source provenance.

## 5. Projectivizing the clock retains the inert fixed point

One may quotient out the common delay and retain only the ordered relative
passport.  For `(2.3)` every quotient mark is the same:

```text
(receiving at relative time 0, source Never,
 orientation receiving-earlier, gain 1).               (5.1)
```

This removes the escaping-time noncompactness.  It does not create descent.
The normalized state is constant, its semantic debt is two, and its only cap
root is all Continue.  Prefixing that root is the identity in the quotient.

More generally, a compactification of the marked sequence has only two
possibilities:

1. the cluster point forgets the positive mark, in which case the marked
   class is not closed and its infimum need not be attained inside it; or
2. the cluster point retains the mark, in which case the all-Continue shift
   fixes it and the current finite-cut/signed-label operation has zero mass
   and zero debt decrement there.

Adding a one-point boundary for relative delays has the same dichotomy.  A
boundary value that preserves the positive row is an inert marked boundary;
a boundary value equal to Never/Never loses the row.

## 6. Why the terminal witness and positive minimum do not yet repair this

Under a terminal exploitability witness, every **actual** profile has some
full-gap deviation.  This does not make the same observer and the same two
witness times survive a semantic-carrier limit.  Reselecting a new debtor at
the limit loses the inherited row, fixed law, reset incidence and cap-port
chronology.

A positive global minimum supplies `D>=D_*>0` and is what makes finite cap
charge summable.  It does not exclude `A=0` or give `rho>0`; the exported exact
trichotomy isolates that as its remaining arm.  In particular, a compact
minimum of `(1.1)` may be an all-Continue cap fixed point.  At such a point
the signed-label producer has premise `rho>0` false and the finite-cut theorem
has premise `mu>0` false.

The Fin4 label screen
[`CODEX_RAMSEY__RANK_ONE_PAID_TANGENT_LABEL_NONIDENTIFICATION.md`](CODEX_RAMSEY__RANK_ONE_PAID_TANGENT_LABEL_NONIDENTIFICATION.md)
rules out a shortcut through cardinality: the inherited full-gap observer
need not be the minimum reset mover or a positive tangent recipient.  Thus
the global-minimum tangent direction cannot presently be charged to the
compact paid mark.

## 7. Exact no-go and surviving target

**No compactness-only repair follows from the current fields.**

- Absolute finite-time witnesses give the right actual profiles but a
  nonclosed marked class.
- A closed semantic debt-share relaxation is compact and attains a minimum,
  but forgets the row and actual source.
- A translation/projective passport retains the row, but compactifies the
  `A=0` arm as an inert marked fixed point.

Accordingly the finite-cut theorem can contradict an attained marked minimum
only under the additional operational hypothesis that every minimizing mark
has `rho>0` (or directly has a positive fixed-label mass).  Current data do
not provide it.

The remaining theorem must act at the inert boundary itself:

```text
actual marked all-Continue cap stall
  -> uniform payoff
     or source-matched floor/charge block
     or recursively preserved discrete rank drop.      (7.1)
```

Topology can make the boundary visible, but cannot supply `(7.1)`.

## Checked sources inspected

- `Quitting/Root/TerminalSemanticPair.lean`:
  `quittingTerminalSemanticCarrier_isCompact`;
- `Quitting/Root/TerminalSemanticEqualityStratum.lean`:
  continuity of coordinate and total debt;
- `StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`:
  exact shifted-row identities and cap-prefix debt scaling;
- `StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`;
- `TerminalSemanticPaidFirstDisagreement.lean`; and
- `Frozen/RadialCurvatureStrategicDispatch.lean`, whose fixed-label theorem
  explicitly permits first-disagreement dates to diverge.
