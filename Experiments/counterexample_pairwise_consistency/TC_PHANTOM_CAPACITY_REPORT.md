# T x C: exact cap-tail compatibility and the global-capacity residual

Status: **Open**.  The exposed `T` equations, punishment-floor augmented
caps, zero-charge limiting cap, and even exact finite cap-tail edges coexist
on one rational four-player table.  The same table fails the universal part
of `C` because it has a different punishment-rational exact self-loop of
charge one.  Thus the pair is not interface-disconnected, but neither an
inconsistency nor a full consistency witness has been obtained.

Optimized-provenance qualification: the tail below is an exact
Nash--Bellman/dynamic-debt tail.  It is **not** proved to be a projective limit
of cutoff-wise optimized zero-boundary minimizers.  Consequently it proves
only exposed-equation compatibility.  The optimized-minimizer provenance is
listed separately in the residual system.

## 1. One rational four-player table

Let the players be

```text
I = {o,a,b,c}.
```

For every nonempty quitting coalition `S`, define

```text
r_o(S) = 1 if o is in S, and 0 otherwise,
r_a(S) = r_b(S) = 0,
r_c(S) = -3 if S={c}, and 0 otherwise.
```

The sharp reward bound is `M=3`.  The positive singleton caps are

```text
K_o=1,                 K_a=K_b=K_c=0.
```

The behavioral punishment vector is exactly

```text
chi=(1,0,0,0).                                           (1)
```

Indeed, `o` can guarantee `1` by quitting immediately, and opponents who
always Continue hold its best response to `1`.  Players `a,b` always receive
zero.  Player `c` can guarantee zero by Never, while all-Continue opponents
hold its best response to `max(0,-3)=0`.

## 2. A positive-hazard exact phantom tail

Put `eta=1/2`.  At date `t>=0`, only `a` has positive quitting probability:

```text
p_t := 1/(t+2)^2,
a_t=(0,p_t,0,0).
```

Write `s_t=1-p_t` and prescribe

```text
d_t(o)=(t+1)/(t+2),       v_t(o)=2(t+1)/(t+2),
d_t(j)=v_t(j)=0           for j != o.                     (2)
```

The elementary identity

```text
s_t=(t+1)(t+3)/(t+2)^2
```

gives the exact recursions

```text
d_t(o)=s_t d_(t+1)(o),    v_t(o)=s_t v_(t+1)(o).          (3)
```

At the displayed root, `o`'s Quit endpoint is `1`; its Continue endpoint is
`s_t v_(t+1)(o)=v_t(o)>=1`.  Player `a` is indifferent between zero and zero,
as is `b`.  Player `c`'s Quit endpoint is `-3s_t<0`, while Continue gives
zero.  Hence every row is exact one-stage Nash and (3) is the exact Bellman
law.

For `o`, the exact dynamic-debt update is

```text
max(1, v_t(o)+s_t d_(t+1)(o))-v_t(o)=d_t(o);             (4)
```

the other updates are zero.  This is the literal dynamic-debt recursion, not
only the external conservation identity.  It also proves that the diagonal
seam `a_(i,t)d_t(i)` vanishes in every coordinate: the only quitting player
has zero debt and the only indebted player surely Continues.

Joint absorption is `q(a_t)=p_t>0`, tends to zero, and is summable.  Moreover,

```text
eta <= d_t(o) < K_o,       d_t(o) -> 1,
v_t(o) -> 2.                                               (5)
```

Only `a` can absorb on the honest tail and `r({a})=0`; Never also pays zero.
Thus the actual terminal payoff of every suffix is identically zero, while
the prescribed owner value tends to `2`.

The owner's deleted-opponent clock is `p_t`.  From (3), for every finite
window `[T,T+L)`,

```text
sum p_t <= sum -log(s_t)
          = log(d_(T+L)(o)/d_T(o))
          <= log(K_o/eta)=log 2.                           (6)
```

This verifies all exposed `T` equations with positive hazards.

## 3. The same tail has exact augmented-cap edges

The augmented cap is

```text
w_t=v_t+d_t=(3(t+1)/(t+2),0,0,0).                         (7)
```

By (1), every `w_t` is punishment-rational; by `M=3`, it lies in the
canonical reward box.  It converges to

```text
w_infty=(3,0,0,0).
```

All-Continue is exact Nash at `w_infty` and is a literal zero-charge
self-loop there.

There is more than limiting carrier membership.  Because the diagonal debt
seam vanishes, the same tail root obeys

```text
w_t=F(a_t,w_(t+1)).                                       (8)
```

It is exact Nash against `w_(t+1)`: `o` receives `w_t(o)>1` by Continue,
`a,b` remain indifferent at zero, and `c` strictly Continues.  Consequently,
each finite chronological cap window, read in the outward orientation, is an
exact punishment-floor chain.  Starting at `w_(T+L)`, successively prepend
`a_(T+L-1),...,a_T`; the resulting values are
`w_(T+L-1),...,w_T`, and its charge is

```text
sum_(t=T)^(T+L-1) p_t <= log 2.                            (9)
```

Thus the tail-facing part of `C` is genuinely connected to `T`, and is
compatible with it.  A local potential on these selected outward edges is
simply `Phi(w)=w_o`, since

```text
w_(t+1)(o)-w_t(o)=3/((t+2)(t+3)) >= 1/(t+2)^2=p_t.       (10)
```

## 4. Why this is not a `C` witness

Let

```text
u=r({o})=(1,0,0,0)
```

and let `x` prescribe that `o` Quits surely while everyone else Continues.
Then `u` is in the same reward box and `u>=chi`.  At continuation `u`, every
player is indifferent between its prescribed action and the other endpoint:

* `o` receives `1` from Quit and `u_o=1` from Continue;
* `a,b` receive zero whether or not they join;
* `c` receives zero upon joining `{o}`, whereas only quitting alone would
  give `-3`.

Therefore `x` is exact one-stage Nash at `u` and

```text
F(x,u)=u,              q(x)=1.                              (11)
```

Repeating (11) produces an exact punishment-floor chain of every length `N`
with charge `N`.  The universal capacity is infinite.  The probe checks all
of (2)--(11) in exact rational arithmetic.

The same issue invalidates the existing cap-only regression as evidence for
`C`: `../../UniformEquilibrium/Quitting/Debt/Dynamic/DynamicDebtCapChargedAnchorCounterexample.lean` proves only that the
augmented cap has no charged exact predecessor, while the file also exhibits
a genuine absorbing exact terminal equilibrium.  Repeating that equilibrium
is an unbounded charged chain.  A zero-charge cap loop never certifies the
universal quantifier.

## 5. A general singleton-lock screen forced by `C`

The failure in (11) is not peculiar to this table.

**Singleton-lock lemma.**  Let `o` have positive singleton payoff
`K=r_o({o})>0`.  If

```text
r_j({o,j}) <= r_j({o})       for every j != o,               (12)
```

then the universal punishment-floor charge capacity is infinite.

To prove it, take `u=r({o})` and the pure root where only `o` Quits.  The
owner is indifferent because both its prescribed Quit and a deviation to
Continue give `u_o=K`.  Condition (12) says every outsider optimally
Continues.  Thus this is an exact fixed point of charge one.

It is punishment-rational without an extra assumption.  Opponents who always
Continue show `chi_o<=K`.  For `j!=o`, opponents can make `o` Quit immediately;
under (12), player `j`'s complete best reply then has value `r_j({o})=u_j`.
Hence `chi_j<=u_j`.  Repetition gives arbitrary charge.

Consequently every genuine `T x C` table must satisfy, for its positive-debt
owner,

```text
exists j != o,  r_j({o,j}) > r_j({o}).                       (13)
```

More generally, `C` forbids every punishment-rational nonempty quitting
coalition (`r(S)>=chi`) which is stable against all one-player joins and
leaves.  This is an exact finite screen, but it is not sufficient: the exact
root correspondence can still have a mixed positive-charge fixed point or
arbitrarily long charged nonrecurrent paths.

## 6. Exact residual system

Let

```text
K_floor={u in [-M,M]^I : u>=chi},
R(u)={x : x is exact one-stage Nash at u},
G_x(u)=F(x,u).
```

For the universal quantifier in `C`, the precise remaining certificate is a
globally bounded nonnegative function `B` on `K_floor` satisfying

```text
B(G_x(u))+q(x) <= B(u)                                    (14)
```

for every `u in K_floor` and every `x in R(u)` whose successor remains in the
box.  Such a `B` telescopes to a common charge bound.  Conversely, if the
common bound exists, the supremum of all finite future charges from `u`
defines such a `B`.  No continuity or semialgebraicity of `B` is implicit.

The full rational consistency search is therefore:

1. find one rational finite reward table and an exact positive phantom tail
   satisfying `T`;
2. keep all augmented caps in `K_floor` and retain the zero-charge limiting
   all-Continue loop;
3. eliminate every pure and mixed positive-charge fixed point, including the
   singleton lock (12);
4. certify (14) for the entire exact root correspondence, not only along the
   selected cap tail; and
5. separately, for the provenance-strengthened version, realize the tail as
   a projective limit of cutoff-wise optimized zero-boundary minimizers.

Items 1--2 and a nontrivial exact cap-tail interface are realized above.
Item 3 already fails for the displayed table, and item 4 is the unresolved
global condition.  Eliminating fixed points alone would not prove item 4.

## Validation

Run

```text
python Experiments/counterexample_pairwise_consistency/pair_t_c_capacity_probe.py
```

The probe uses only `fractions.Fraction`.  It exhausts all terminal coalitions
of the displayed four-player table, checks exact Bellman, endpoint-Nash,
dynamic-debt, cap-edge, carrier, and local-potential identities at 128 exact
rational tail dates, and checks the charge-one fixed loop.  The infinite-tail
and universal-loop conclusions use the closed formulas proved above, not a
floating-point tolerance or a bounded solver search.

The construction already has four players.  It does not establish
cardinal-minimality.  Adding zero-payoff dummy players preserves the tail and
the offending charged loop, so it cannot repair `C` by player extension.
