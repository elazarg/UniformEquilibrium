# Inactive radial inequality and support-turnover review

Reviewer: `CODEX_NOETHER`

Reviewed note:
[`../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`](../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md)

Scope: Section 37, Lemma 51A and Proposition 51, including the zero-ratio
new-support extension, pure-switch, and two-player boundary tests. I independently checked the conditional
first-order Quit expansion, probability-weighted endpoint orientation,
finiteness transfer through a positive clock ratio, old/new support signs,
and the sure-exit conclusion. This is ordinary mathematics, not Lean-checked.

## Verdict

**Lemma 51A and Proposition 51 are VALID ordinary mathematics as stated.**
They extend the shared-support equality to sharp one-sided inequalities on
dropped and newly active owners. At zero ratio, the new-support inequality
survives but the old-support inequality need not. The results do not control
the dropped owners of a zero-ratio reset or complete higher-player support
turnover.

## 1. Inactive radial inequality

At a singleton-tight coordinate `b_i=r_i({i})`, conditioning on forced Quit
gives

```text
Pr(exactly opponent j quits)
  =q_n (mu_n)_j/(1-p_(n,i)).
```

The forced-Quit probability of at least two opponents is `o(q_n)`: after
multiplication by `1-p_(n,i)` it is a subevent of the product root's collision
event, whose normalized mass tends to zero. Bounded rewards remove the
remainder. Therefore

```text
(QuitPayoff_(n,i)-b_i)/q_n -> P_i(mu).
```

The exact endpoint-Nash orientation is `QuitPayoff_(n,i)<=x_(n,i)`, even when
the prescribed hazard of `i` is zero. Dividing by positive `q_n` gives
`P_i(mu)<=v_i`; this confirms `(ST3)`. If `mu_i>0`, the player's Quit hazard
is eventually positive, while its Continue probability tends to one. The two
weighted endpoint conditions then bind, giving equality `(ST4)`. No raw-gap
inference from mere interiority is being used here: the root is exact Nash.

## 2. Old and new support orientations

Write `v_n=z_n+theta_n w_n`. For an old-active owner, Lemma 51A gives the
finite limit `v_i=P_i(mu)`. Since `theta_n->theta>0` and `z_n->z`, `w_i` has
a finite limit. Old activity already pins the common boundary coordinate to
the solo payoff, so the next-chart inactive inequality applies:

```text
lim w_i>=P_i(mu').
```

Substitution gives
`P_i(mu)>=z_i+theta P_i(mu')`, the orientation in `(ST8)`.

For a new-active owner, the next-chart equality gives
`w_i=P_i(mu')`. New activity pins the same common boundary coordinate, so the
old-chart inactive inequality gives `lim v_i>=P_i(mu)`. Substitution yields
`P_i(mu)<=z_i+theta P_i(mu')`, exactly `(ST9)`. Both inequalities become
equalities on support intersection.

The assumption `theta>0` is indispensable only for the old-owner step: at
`theta=0`, finite `v,z` do not bound an inactive next radial coordinate `w`,
and `theta_n w_n` may retain a nonzero limit.

For a **new-active** owner at zero ratio, however, the next-chart equality
still gives bounded `w_n->P_i(mu')`. Hence `theta_n w_n->0`, the source
identity gives `v_n->z_i`, and the old inactive inequality yields

```text
P_i(mu)<=z_i.
```

This validates the patched extension `(ST11)`. No corresponding old-support
claim is available at zero ratio.

## 3. Pure-switch calculation

For `mu=e_a`, `mu'=e_b`, `a!=b`, active pinning gives `z_a=0`. The old-owner
inequality becomes

```text
r_a({a,b})<=r_a({a}).
```

For the new owner `b`, expand

```text
P_b(e_a)=r_b({a,b})-r_b({b}),
z_b=r_b({a})-r_b({b}),
P_b(e_b)=0.
```

Then `(ST9)` is exactly `r_b({a,b})<=r_b({a})`. Thus `(ST10)` has the correct
row labels; it is not symmetric unless the reverse switch is also present.

## 4. Two-player sure-exit boundary

The switch `a->b` supplies the outsider condition for the singleton exit set
`{a}`: `r_b({a,b})<=r_b({a})`. If `r_a({a})>=0`, the member condition also
holds, so the checked sure-exit consumer gives a uniform payoff. Under a
no-uniform hypothesis one must have `r_a({a})<0`. A reverse positive-ratio
switch similarly forces `r_b({b})<0`. Then the empty set satisfies both
all-Continue conditions, and
`isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet`
(`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`) again contradicts the
hypothesis. This is a valid boundary test, not a new two-player theorem.

## Exact surviving obligation

For positive-ratio transitions, dropped owners and new owners satisfy opposite
weak inequalities. In higher dimension these do not by themselves assemble a
single sure exit set: different directed switches can assign incompatible
member and outsider rows. At zero ratio every new owner still satisfies
`(ST11)`, but dropped owners escape the radial transfer. The next useful
statement must therefore charge either complete support turnover or the
dropped side of a zero-ratio reset to a player-deleted clock, a floor account,
or a multi-owner sure-set condition. Merely selecting the same owner again at
a later nonconsecutive record does not close the immediate transition.
