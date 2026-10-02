# A stationary paid carrier either crosses the semantic debt moat or pays linearly for absorption

Author: `CODEX_EULER`

Independent theorem review:
[`CODEX_RAMSEY`](../feedback/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY__BY_CODEX_RAMSEY__SECTION_17.md)

Reviewed component packets:

- [`FIN4_LEAVE_JOIN_STATIONARY_TWO_DEBTOR_HANDOFF.md`](FIN4_LEAVE_JOIN_STATIONARY_TWO_DEBTOR_HANDOFF.md);
- [`STRICT_ALLCONTINUE_BASIN_LINEAR_ABSORPTION_DEFECT.md`](STRICT_ALLCONTINUE_BASIN_LINEAR_ABSORPTION_DEFECT.md); and
- [`FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md`](../formalized/FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md).

## Exact statement

Let the player type be literally `Fin 4`, let

```text
reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4)
```

be a quitting reward table, and fix `M>=0` bounding every reward coordinate.
Assume that this game has no uniform-equilibrium payoff.  Fix a terminal
exploitability witness of gap `gamma>0` and four distinct labels `c,s,t,o`
such that

```text
reward({c,s})_c+gamma <= reward({s})_c,
reward({s})_t+gamma   <= reward({s,t})_t.             (1)
```

Use the reviewed constrained two-player Nash construction with `s` forced to
Quit and `o` forced to Continue.  Let `x,y` be the selected Quit probabilities
of `c,t`, let `q` be the product row

```text
q_s=1, q_o=0, q_c=x, q_t=y,
```

and let `sigma` be the stationary profile repeating `q`.  Write its actual
terminal-semantic pair as

```text
X_sigma=(U,B)=quittingTerminalSemanticPair reward sigma,
d_i(X)=X.2_i-X.1_i,
D(X)=sum_i d_i(X).                                    (2)
```

The source retains the reviewed conclusions

```text
alpha=gamma/(gamma+2M),
y>=alpha,
max(Pr({s,t}),Pr({c,s,t}))>=alpha/2,                  (3)
B_c=U_c, B_t=U_t,
P_c<=U_c, P_t<=U_t,                                   (4)
exists w in {s,o}, B_w-U_w>=gamma,                    (5)
Nonempty (QuittingPaidFirstDisagreementRow
  reward sigma w gamma).                              (6)
```

There additionally exist:

- a carrier minimizer `X_*` with `D_*=D(X_*)>0`;
- the compact prescribed-payoff projection

  ```text
  K={X.1 : X is a carrier and D(X)=D_*};
  ```

- a bounded open set `N` containing `K`;
- constants `c_*>0`, `eta_*>0`, `C>0`, and `rho>0`, where `C` bounds the
  reward table and every payoff coordinate in `N`;

such that the following hold.

### A. Carrier debt alternative

Every actual terminal-semantic carrier `X` satisfies

```text
D(X)>=D_*+eta_*                                      (7)
```

or, for every `epsilon>=0` and every independent product root `r` which is
an `epsilon`-Nash root against the literal prescribed tail `X.1`,

```text
absorption(r)<=4*epsilon/c_*.                        (8)
```

In the second arm every exact root is all-Continue; its Bellman successor is
the same tail and its absorption charge is zero.

### B. Paid-source conversion barrier

Apply A to the actual source `X_sigma`.  A positive-charge exact
Nash--Bellman edge whose continuation tail is literally `U` can exist only if

```text
D(X_sigma)>=D_*+eta_*.                               (9)
```

If (9) fails and `U>=P`, the only exact floor-admissible edge at that tail is
the zero-charge identity edge.  If (9) fails and `U` is not above punishment,
no floor-admissible edge with that literal tail exists.  Replacing `U` by its
cap `B` or by a coordinatewise floor clip is not licensed by this conclusion.

### C. Successor-linked approximate paths

Let `V_0,...,V_L` be payoff vectors.  For every `0<=t<L`, let `r_t` be an
`epsilon_t`-Nash product root against the continuation tail `V_(t+1)`, with
`epsilon_t>=0`, and assume the exact successor identity

```text
V_t=Succ(V_(t+1),r_t).                               (10)
```

Put `E=sum_(t<L)epsilon_t`.  If

```text
dist_infinity(V_L,K)<rho/2,
E<c_*rho/(16C),                                      (11)
```

then every path node lies in `N` and

```text
sum_(t<L) absorption(r_t)<=4E/c_*,
max_(t<=L)||V_t-V_L||_infinity<=8CE/c_*<rho/2.       (12)
```

Equivalently, any such successor-linked path ending within `rho/2` of `K`
which reaches outside `N` spends aggregate root error at least
`c_*rho/(16C)`.

## Conjecture-facing change

The accepted stationary handoff turned the rooted-two owner-leave/join arm
into an actual profile with a quantitative nonsingleton atom, two fully solved
floor-safe coordinates, and a paid observer localized to the remaining two
labels.  It did not show that the prescribed tail was floor safe or that the
paid row could be Nashified at that tail.

This packet resolves that local conversion question.  A charged exact edge at
the literal paid tail is possible only after a fixed semantic-debt excursion
above the global minimum.  Below that moat, exact conversion is the
all-Continue identity, and approximate conversion pays linearly for every
unit of absorption.  Even an arbitrarily long successor-linked path ending
near the minimum fiber cannot hide a fixed nonlocal excursion under a
vanishing aggregate error budget.

The surviving obligation is exact and nonlocal: produce the off-minimum
carrier excursion (9), preserve or repay its payoff and floor seams, and then
return, or spend a nonvanishing approximate-root budget.  No such producer is
claimed here.

## Proof

### 1. The actual stationary source

The constrained binary game has an elementary Nash point.  Writing the
Quit-minus-Continue endpoint differences as affine functions
`Delta_c(y),Delta_t(x)`, (1) gives

```text
Delta_c(0)<=-gamma<0,
Delta_t(0)>= gamma>0.
```

Select `(x,y)` by the exhaustive three cases

```text
Delta_c(1)<=0                         -> (x,y)=(0,1),
Delta_c(1)>0 and Delta_t(1)>=0        -> (x,y)=(1,1),
Delta_c(1)>0 and Delta_t(1)<0         -> the two interior affine zeros.
```

Since `Delta_c(1)<=2M`, positive support of `c` implies
`y>=gamma/(gamma+2M)`; if `x=0`, strict optimality of `t` forces `y=1`.
Independence gives the two masses in (3).  The sure Quit of `s` reduces every
behavioral deviation of `c,t` to its date-zero marginal, proving (4).
Terminal exploitability therefore selects `w in {s,o}` with (5).  Rewriting
the unrestricted envelope as the stationary unilateral cap and applying the
immediate-Quit/Never decoder gives (6).

### 2. Linearize the whole minimum fiber

The checked Fin4 minimum-fiber theorem supplies `X_*`, compactness of the
carrier and minimum fiber, the positive minimum `D_*`, one uniform strict own-
singleton gap over that fiber, and uniqueness of the all-Continue exact root
at every `V in K`.

Apply the reviewed linear absorption-defect theorem to compact `K`.  After an
open bounded shrink it gives `N,c_*,C,rho` with

```text
c_* absorption(r)<=totalRootNashDefect(V,r)          (13)
```

for every `V in N`, and with the `rho`-collar of `K` contained in `N`.

Let

```text
Outside=Carrier intersect fst^(-1)(N^c).             (14)
```

It is compact and disjoint from the entire minimum fiber.  If empty, take
`eta_*=1`.  Otherwise debt attains a minimum `D_out>D_*` on `Outside`; take
`eta_*=(D_out-D_*)/2`.  Any carrier failing (7) lies in `N`.  For a Fin4
`epsilon`-root there, the checked defect bound gives

```text
totalRootNashDefect<=4epsilon.
```

Together with (13) this proves (8).  At `epsilon=0`, absorption is zero, so
every independent Boolean Quit marginal is zero and the root is all-Continue.

The literal profile pair `X_sigma` is a carrier member.  Applying the
alternative to it proves B.  Floor admissibility requires the literal tail
itself to dominate punishment, which proves the two floor subcases.  Neither
the carrier theorem nor Bellman orientation identifies `B` or a clipped
vector with `U`.

### 3. Bootstrap a successor-linked path

The terminal node is in `N` by the collar.  Induct backward.  Once
`V_(t+1),...,V_L` have been admitted, (13), the checked bound
`totalRootNashDefect(V_(t+1),r_t)<=4epsilon_t`, and the checked one-edge
movement bound give

```text
absorption(r_t)<=4epsilon_t/c_*,
||V_t-V_(t+1)||_infinity<=8C epsilon_t/c_*.
```

Summing from `t` to `L-1` gives displacement at most `8CE/c_*<rho/2`.
Together with terminal distance `<rho/2`, this admits `V_t` to the collar and
closes the induction without assuming locality of the head.  Summing the
absorption inequalities proves (12), and contraposition gives the excursion
toll.

## Probability and unrestricted-deviation audit

All row roots use independent private Boolean marginals; no public
correlation is introduced.  Root absorption is literal one-row probability.
The finite path proof sums deterministic one-row inequalities and assumes no
independence between dates.

The source semantic pair uses the unrestricted behavioral best-response
envelope.  The zero debts of `c,t` cover every behavioral deviation because
the unchanged sure quitter absorbs at date zero.  The paid row uses literal
immediate-Quit/Never behavioral replacements against the same opponents.
The moat and path conclusions are one-stage product-root Nash statements;
they are not relabeled as unrestricted behavioral equilibria.

Bellman orientation is fixed throughout: a root at row `t` is tested against
the continuation tail `V_(t+1)` and produces the current payoff `V_t`.

## Actual-data adapter and downstream consumer

The same-table stationary source is the reviewed
[`FIN4_LEAVE_JOIN_STATIONARY_TWO_DEBTOR_HANDOFF.md`](FIN4_LEAVE_JOIN_STATIONARY_TWO_DEBTOR_HANDOFF.md),
whose input is the checked rooted-two owner-leave/third-label-join arm of
`FIN4_PUNISHMENT_NORMAL_ATOMIC_COLLISION_HANDOFF.md`.

The minimum data are checked in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`
and archived in the formalized plateau-isolation packet.  The linear
approximate-root and path component is independently reviewed in the second
component packet above.

The downstream target is the exact floor-admissible payoff-near-return route
in `PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`.  This packet proves that its first
charged edge cannot be a local exactification of the accepted stationary
source below the moat.  A consumer must instead supply an off-minimum semantic
carrier, an admissible charged edge there, and later payoff repayment.

## Boundary tests

1. **Linear scale is necessary.**  In the one-player table with singleton
   payoff zero and tail one, a Quit probability `z` has
   `absorption=z=totalDefect`.  Approximate roots are not literally all-
   Continue; the linear conclusion is the correct strength.
2. **Uniqueness is load-bearing.**  In the two-player table with singleton
   payoff vectors zero, joint-Quit payoff one, and tail `(1/4,1/4)`, both
   all-Continue and the symmetric root of Quit probability `1/5` are exact.
   Strict singleton separation alone cannot support (13).
3. **Floor safety is independent.**  The stationary source theorem solves
   only `c,t`.  Changing only the fourth player's rewards can give `o` a
   positive immediate-Quit gain while leaving the constrained Nash and atom
   calculation unchanged.  The theorem therefore cannot silently call `U`
   floor safe.
4. **Incoming-tail orientation is sharp.**  A charged edge may have its head
   in `N` while its continuation tail lies outside `N`.  Neither (8) nor the
   path bootstrap excludes this isolated nonlocal incoming edge.
5. **Aggregate error is essential.**  A vanishing maximum row error with
   unbounded path length need not make `E` vanish and does not meet (11).

## Source and subsumption audit

The exact-root debt moat is principally a composition of the checked
minimum-fiber isolation and the exact case of the linear theorem.  It is not
presented as a new exact-root mechanism.  The new source-facing content is
the alignment with the accepted stationary paid carrier and, substantively,
the uniform approximate-root and successor-linked aggregate-error barrier at
that literal tail/fiber.

The checked fixed-incidence Nash-defect moats do not control absorption as it
tends to zero.  The linear component supplies that missing scale.  The open
all-Continue path-rigidity theorem covers exact roots but not approximate
successor paths.  Conversely, this packet does not strengthen the source
atom, solve the paid-return problem, or subsume the off-minimum charged-row
limit gate.

No external literature theorem is used.

## Checked Lean realization

The source handoff is checked by
`FinFourLeaveJoinStationaryTwoDebtorHandoff` and
`nonempty_finFourLeaveJoinStationaryTwoDebtorHandoff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/LeaveJoinStationaryTwoDebtorHandoff.lean`.

The minimum-fiber constants and generic path estimates are checked by
`exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff` and
`successorPath_mem_and_absorptionSum_le_of_linearDefect`.  Their carrier debt
moat is packaged by `FinFourCarrierSourceChargeDebtErrorGate`.

The literal composition is checked in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/StationaryPaidCarrierLinearDebtMoat.lean`:

- `debt_or_absorption_le_four_mul_error_div` proves the Fin4 root alternative;
- `debt_or_exactRoot_eq_allContinue` proves the exact identity-root arm;
- `FinFourStationaryPaidCarrierLinearDebtMoat` retains the actual stationary
  two-debtor source and the independently constructed minimum-fiber gate;
- `nonempty_finFourStationaryPaidCarrierLinearDebtMoat` constructs the
  composition on every hypothetical counterexample; and
- `source_debt_or_absorption_le_four_mul_error_div` and
  `source_debt_of_punishmentFloorAdmissiblePath` specialize the estimates to
  the stationary semantic pair and the exact floor relation.

The result has `M`, `L`, and actual stationary-source `A`.  Its root/path
theorems are checked obstruction consumers `C`; they do not construct the
charged path or the payoff near-return required for a uniform payoff.

## Scope and nonclaims

- No exact root, positive-charge Bellman edge, floor repair, descent, cyclic
  block, or payoff return is produced.
- The packet does not compare `D(X_sigma)` with `D_*+eta_*`; it proves the
  exhaustive alternative.
- The fixed pair/triple atom remains behavioral terminal-law mass, not exact-
  edge charge.
- Cap replacement and floor clipping change the literal tail and are not
  semantic adapters.
- The successor-path theorem requires terminal proximity and a small
  **aggregate** error budget.  It does not exclude an isolated incoming edge
  from outside `N`.
- The theorem controls total absorption, not a selected marginal, observer
  orientation, conditioned posterior, or tangent rank.
- It does not prove a uniform-equilibrium payoff or close the four-player
  conjecture.
