# Repaired residual pure-exit descent

Authors: CODEX_EULER

Independent component review:
[CODEX_RAMSEY](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTIONS_28_2_28_3.md)

## Exact statement

Let `I={c,d,x,y}` be four distinct players in a finite quitting game.  Fix
`j in {0,1}`.  Suppose a supplied finite repaired root has four cells indexed
by `(h,e) in {0,1}^2`, nonnegative cleared product weights `W_he`, and a
positive denominator

```text
H=sum_(h,e) W_he>0.                                  (1)
```

Zero weights are allowed, so this includes pure roots.  In cell `(h,e)` let
`S_he` be the terminal coalition when `d` Quits surely, `c,x` take the cell
actions, and `y` takes action `j`.  Thus `d in S_he`, and `y in S_he` exactly
when `j=1`.  Put

```text
O_he=S_he\{y},             T_he=S_he\{d},            (2)

Delta_y^he=r_(O_he union {y})(y)-r_(O_he)(y).        (3)
```

Let `chi_d` be player `d`'s punishment value, and define

```text
p_d(T)=chi_d if T=empty, and p_d(T)=r_T(d) otherwise,
k_d^he=p_d(T_he)-r_(T_he union {d})(d),              (4)

N_y=sum_(h,e) W_he Delta_y^he,
K_d=sum_(h,e) W_he k_d^he.                           (5)
```

Then the following two exact descents hold.

### Positive owner-floor residual

If `K_d>0`, some positive-weight cell satisfies

```text
H k_d^he>=K_d>0.                                     (6)
```

For `T=T_he`, exactly one of these alternatives holds:

1. `T=empty` and

   ```text
   chi_d-r_d(d)>=K_d/H>0;                            (7)
   ```

2. `T` is a nonempty exact sure-exit set, so `r_T` is a uniform-equilibrium
   payoff against unrestricted behavioral deviations; or
3. `T` is nonempty, player `d` has the strict outsider no-join margin

   ```text
   r_T(d)-r_(T union {d})(d)>=K_d/H,                 (8)
   ```

   and some other player has a strict membership failure:

   ```text
   exists z in T,
     hat_r_(T\{z})(z)>r_T(z),
   or exists z notin T union {d},
     r_(T union {z})(z)>r_T(z).                      (9)
   ```

Here `hat_r_empty=0` and `hat_r_A=r_A` for nonempty `A`.

### Wrong remaining-label endpoint residual

Suppose `y`'s fixed action has the wrong endpoint sign.  Define

```text
G_y=N_y   if j=0,
G_y=-N_y  if j=1,                                    (10)
```

and assume `G_y>0`.  Some positive-weight cell satisfies

```text
H g_he>=G_y>0,

g_he= Delta_y^he   if j=0,
g_he=-Delta_y^he   if j=1.                           (11)
```

Move `y` to its preferred action and put

```text
P=O_he union {y}  if j=0,
P=O_he            if j=1.                            (12)
```

The coalition `P` is nonempty because it contains `d`.  Exactly one of these
alternatives holds:

1. `P` is an exact sure-exit set, so `r_P` is a uniform-equilibrium payoff
   against unrestricted behavioral deviations; or
2. `y` is membership-stable at `P` with margin at least `G_y/H`, and a
   different player has a strict failure:

   ```text
   exists z in P, z!=y,
     hat_r_(P\{z})(z)>r_P(z),
   or exists z notin P, z!=y,
     r_(P union {z})(z)>r_P(z).                      (13)
   ```

Under a terminal exploitability witness the two sure-exit alternatives are
excluded.  Thus the two residuals of the accepted repaired root are reduced
to the exact empty premium (7), or to a nonempty literal coalition with a
quantitatively stable responsible label and a strict toggle by a different
label.

## Conjecture-facing change

The maintained question is
[`FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`](../questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md).
The accepted packet
[`PAID_SIGN_FAILURE_BINARY_REEQUILIBRATION.md`](PAID_SIGN_FAILURE_BINARY_REEQUILIBRATION.md)
turns a failed pure base-deletion sign into an exact repaired root.  Its only
remaining tests are the wrong `N_y` sign and `K_d>0`.

This packet consumes both tests.  Each positive weighted residual contains a
literal pure cell with the same normalized margin.  At that cell either the
checked sure-exit consumer applies or a different player supplies an explicit
pair/triple/grand-coalition toggle.  The sole non-coalitional exception is
identified exactly as the all-Continue punishment premium
`chi_d-r_d(d)>0`.  This is a strict compiler-valued narrowing of the accepted
repaired residual, not another cycle recollection.

## Definitions and assumptions

The supplied weights are the ordinary product probabilities of the repaired
one-stage root, multiplied by `H`.  The theorem uses only their nonnegativity
and sum; it does not introduce correlated randomization.  Extracting a cell
is a finite averaging argument, not sampling during play.

The coalitions `T` and `P` are deterministic pure exit sets.  If one is a
sure-exit set, the checked pure stationary consumer tests both membership
actions of every player and controls arbitrary behavioral stopping times and
Never.  The result is not restricted to a finite deviation menu.

The punishment value occurs only in the empty free-player cell of (4).  It is
an exact scalar value; no exact minimizing punishment strategy is assumed.
There is no public correlation, observation change, or stopping-law mixture.

## Source correspondence

The actual-data source is the independently reviewed
`PAID_SIGN_FAILURE_BINARY_REEQUILIBRATION` packet.  Its input in turn comes
from `HasPaidPureBinaryCell` and
`paidPure_or_paidMixed_of_forall_binaryNash` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargePersistentBaseFiniteNashDispatch.lean`,
through the accepted `PURE_PAID_BASE_LEAVE_DESCENT` adapter.

The checked semantic declarations used here are:

- `IsQuittingSureExitSet`, `isQuittingSureExitSet_iff_forall_max`, and
  `isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet` in
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`;
- `isQuittingSureExitSet_insert_or_oldLeave_or_otherJoin` in
  `UniformEquilibrium/Quitting/Paths/AnchoredJoinPromotion.lean`.

Those declarations contain the exact all-behavior membership consumer and
the strict-join promotion, but not the weighted extraction from `N_y,K_d` or
the leave-oriented version.  The new content is (6)--(13), including the
empty punishment branch and the quantitative stable-label margins.  No paper
theorem is used.

## Proof

The normalized weights `W_he/H` are nonnegative and sum to one.  If `K_d>0`,
some positive-weight cell has

```text
k_d^he>=sum_(a,b)(W_ab/H)k_d^ab=K_d/H,
```

which proves (6).  If `T_he` is empty, definition (4) is exactly (7).

Now suppose `T=T_he` is nonempty.  Definitions (4) and (6) give (8), so `d`
strictly prefers to remain outside `T`.  Test the membership inequality of
every member and outsider at `T`.  If all hold, they are exactly
`IsQuittingSureExitSet reward T`, and its checked consumer gives the positive
conclusion.  Otherwise `d` cannot be the failed outsider; the negation of the
remaining finite conjunction is exactly (9).

For the second theorem, if `j=0`, equations (3), (5), and (10) say that
`G_y/H` is the weighted average of `Delta_y^he`.  If `j=1`, it is the weighted
average of `-Delta_y^he`.  Thus a positive-weight cell satisfies (11).

When `j=0`, the preferred coalition is `P=O_he union {y}` and

```text
r_P(y)-r_(P\{y})(y)=Delta_y^he>=G_y/H.
```

When `j=1`, the preferred coalition is `P=O_he` and

```text
r_P(y)-r_(P union {y})(y)=-Delta_y^he>=G_y/H.
```

Thus `y` is strictly stable in its preferred membership action.  Test all
other membership inequalities at `P`.  If all pass, the sure-exit consumer
applies.  Otherwise `y` cannot be the failed label, and the finite negation is
(13).  The `j=0` argument is also exactly the checked anchored-join promotion;
the direct membership proof covers `j=1`.

## Boundary tests

All three output types occur.

- Give one cell unit weight and let `T=empty`.  If `chi_d=0` and `r_d(d)=-1`,
  then `K_d=1` and (7) is selected.  This cannot be sent to a nonempty
  sure-exit set.
- Give one cell unit weight with nonempty `T`, set
  `r_T(d)-r_(T union {d})(d)=1`, and make every other membership toggle weakly
  unprofitable at `T`.  Then `T` is a sure-exit set and the checked consumer
  applies.  Raising one outsider's payoff at `T union {z}` by one changes only
  that coordinate and produces the second disjunct of (9).
- For the endpoint theorem with `j=0`, take one unit-weight cell with
  `Delta_y=1`.  Then `y` joins with margin one.  Making all other membership
  inequalities stable gives a sure-exit set; raising a different outsider's
  join payoff gives (13).  With `j=1` and `Delta_y=-1`, the same test makes
  `y` leave and verifies the opposite orientation.

The positive-weight requirement is essential.  A cell with an arbitrarily
large premium but zero `W_he` contributes nothing to `K_d` or `N_y` and need
not be selected.  Equality at zero is also exact: neither `K_d=0` nor `G_y=0`
forces a strict pure-cell margin.

## Adapter and consumer

The adapter reads `W,H,S,Delta,N_y,K_d` directly from the accepted repaired
root.  It selects one of four cells by a finite maximum, tests whether its
post-toggle coalition is empty, and otherwise evaluates the four literal
membership inequalities.  No real parameter or infinite path is selected.

A passing membership test invokes the checked sure-exit constructor and
all-behavior consumer.  A failed test returns (9) or (13), which is the exact
smaller reward-table residual accepted by the maintained question.  The
empty branch returns the exact punishment inequality (7).

## Lean handoff

First prove a finite weighted-selection lemma: for `0<=W_a`, `sum W_a=H>0`,
and `sum W_a q_a=Q>0`, there is `a` with `W_a>0` and `H*q_a>=Q`.  Apply it
once to `k_d` and once to the oriented `y` differences.

For the owner branch, split on `T_he.Nonempty`.  In the nonempty case rewrite
(6) to the strict outsider inequality for `d`, then use a decidable test of
`IsQuittingSureExitSet`.  Its false branch should return the member/outsider
witness while excluding `d` by the strict sign.

For the endpoint branch, split on `j`.  Construct `P` by inserting or erasing
`y`, prove the corresponding strict membership inequality, and again decide
the sure-exit predicate.  The join case may invoke
`isQuittingSureExitSet_insert_or_oldLeave_or_otherJoin`; the leave case is a
direct finite negation.  Invoke the checked sure-exit consumer only in the
positive branch.  Do not store either desired conclusion as a hypothesis.

## Scope and nonclaims

This packet does not consume the new toggles in (9) or (13), prove that their
iteration terminates, or collect them into a cycle.  Orientation-only stable-
pair iteration is known to be insufficient, so no such inference is made.

It does not eliminate the exact empty premium (7), the old-action-stable
premium from `PURE_PAID_BASE_LEAVE_DESCENT`, or the mixed large-base residual.
It constructs no quitting chronology and no general stationary compiler.  Its
only unrestricted-strategy conclusions are the named sure-exit outputs.
