# Independent review of Proposition 6 in `CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE`

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS, with no mathematical repair.**  The compact blocker gap is strictly
positive, the constants in `(9.3)--(9.8)` are correct, and the supplied first
row extends to an arbitrary infinite exact punishment-floor orbit with the
orientation stated in `(9.5)`.  The conclusion correctly stops at either a
table-level pair premium or a one-coordinate nonlocal repayment; neither arm
is yet a payoff near-return or a strict decrease of a declared obstruction.

## Uniform blocker gap

Fix `k` and `p in [alpha,1-d]`.  At tail `r_k`, the solo owner `k` is
indifferent because both its immediate-Quit and Continue endpoints equal
`s_k`.  For outsider `i`, Continue has value

```text
R_i=r_k(i),
```

whereas Quit has value

```text
Q_i=(1-p)s_i+p r_{ki}(i).
```

Thus `G_k(p)<=0` is exactly the assertion that every outsider weakly prefers
Continue.  The positive solo root is then exact at `r_k`.  Since same-table
punishment normality gives `P_k<=s_k`, the checked solo-cycle completion
would yield a uniform-equilibrium payoff, contradicting the maintained
branch.  Hence `G_k(p)>0` pointwise.

The parameter set is a finite union of compact intervals, and `G_k` is the
maximum of finitely many affine functions.  Therefore, whenever the interval
is nonempty, its minimum `g_a` is attained and strictly positive.  In the
actual Proposition 5 arm the interval is automatically nonempty because the
selected hazard itself satisfies

```text
alpha<=p<=1-d.
```

Selecting an outsider attaining `G_k(p)` is legitimate even if it differs
from the initially named blocker: exactness of the solo row at `X.1` gives
the required endpoint inequality for every outsider.  With
`g=Q_i-R_i>=g_a`, the replacement threshold obeys

```text
T_i-Q_i=p g/(1-p)>=alpha g_a.
```

The last inequality uses only `p>=alpha` and `p<1`.

## Collision-premium/repayment algebra

Writing `b=r_{ki}(i)`, one has exactly

```text
g=(1-p)(s_i-R_i)+p(b-R_i).
```

If `b-R_i>=g/2`, the first alternative follows.  Otherwise,

```text
s_i-Q_i
  =p(s_i-b)
  =p(g-(b-R_i))/(1-p)
  >p g/[2(1-p)]
  =(T_i-Q_i)/2
  >=alpha g_a/2.
```

Thus the factor `1/2` in `(9.8)` and all subsequent constants are exact.

## Exact-orbit existence and orientation

Proposition 5 supplies a boxed floor tail `Y=V_0` and an exact root
`q=q_0` there.  Its successor

```text
V_1=Succ(V_0,q_0)
```

remains in the canonical box and above punishment by the checked forward
floor inequality.  At each later `V_t`, finite mixed-Nash existence selects
an exact product root; dependent choice therefore gives a
`QuittingPunishmentFloorInfiniteOrbit` whose prescribed values satisfy
`V_(t+1)=Succ(V_t,q_t)`.  This construction really can retain the supplied
first root rather than merely selecting an unrelated canonical orbit.

For coordinate `i`, the threshold identity gives

```text
V_1(i)=pR_i+(1-p)T_i=Q_i.
```

The checked theorem `infiniteOrbit_exists_value_limit` applies to every such
orbit under the terminal witness and gives a coordinatewise limit `L` with
`L_i>=s_i`.  Hence

```text
L_i-V_1(i)>=alpha g_a/2.
```

Convergence supplies a finite, sufficiently late `t` with

```text
V_t(i)-V_1(i)>=alpha g_a/4.
```

The Nash--Bellman edge orientation is predecessor-to-tail:
`V_(s+1) -> V_s`.  Consequently the finite path indeed runs

```text
V_t -> ... -> V_1 -> V_0,
```

and its final edge is the original solo row, of absorption at least `alpha`.

## Scope

The first arm is a strict pair-reward premium, not positive collision mass in
an exact root.  The second arm is an exact source-matched path with a fixed
increase in one coordinate before its charged final edge, not simultaneous
closeness of all endpoint coordinates.  It also does not decrease
`D-D_*`, support rank, or another declared well-founded invariant.  The note
states these limitations accurately.  Proposition 6 is therefore a valid
and useful narrowing of the zero-drop blocker gate, but it does not by itself
consume `PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN`.

