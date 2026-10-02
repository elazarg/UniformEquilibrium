# Third review: deadlock-core linear mixing and the standard-Q degree

Reviewer: `CODEX_NOETHER`

Target: Propositions 14--16 in Section 23 of
[`../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`](../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md).

Verdict: `VALID` as ordinary mathematics. I attempted to falsify the exact
13-player adapter, all sixteen LCP supports, the proper-map degree argument,
and the reduction from a balanced singleton cycle to the checked reduced
deadlock lasso. I found no objection. Proposition 14 still depends on the
ordinary-mathematics linear face theorem (Proposition 11), and none of this
review supplies a Lean or production adapter seal.

## Proposition 14: the revised literal table

The normal-core calculation is exact. A dummy row has twelve strictly
positive off-diagonal entries and leaves at the first normal layer. In the
ordered core `D={0,3,6,9}`, the four deadlock rows have negative witnesses in
columns `2,3,1,0`; they therefore remain at every later layer. The core is
exactly `D`, and its principal normalized singleton matrix is the positive
scale `deadlockMatrix/10000`.

The altered numerical bounds check:

- singleton continuer rewards lie in `[9997/10000,10003/10000]`;
- the distinguished off-diagonal row sums, after the nine dummy columns are
  added, are `14,9,8,7`, while a dummy row sum is `12`, so every `barw_i>1`;
- with the same conditional singleton-mass bound, the transformed error is

```text
974157031319839814136010357980773 /
16547013791573166847229003906250000 < 59/1000,
```

with exact positive slack

```text
2116782382977029850500872487977 /
16547013791573166847229003906250000;
```

- at the mixed upper-blocker corner, direct odds substitution gives exactly

```text
E_i >=
20640001498501688382948756177069 /
2368317064126414895057678222656250000 > 0.
```

Thus `A G=h+A E` has margin greater than `1/1000` on every face of
`[11/25,14/25]^13`. The inverse identity

`(I+P)^(-1)=(1/2)(I-P+...+P^12)`

is correct because `P^13=I`; its row `l1` norm is `13/2` and it sends the all-
one vector to half that vector. Proposition 11's range--orthant argument does
force `A` invertible, and its clamped Brouwer step therefore produces a zero
of the original stationary gap, not merely of a singular projection.

The global exclusion of every playerwise common-box certificate also survives
the replacement. For either actual blocker, swapping its probability with
the other blocker leaves the gap unchanged, because both singleton weights
are `10001/10000`. The small-box diagonal gap is strictly increasing as
claimed. In the large-box case the altered worst-weight calculation is

`11(9997/10000)(1/10)-10003/10000=9937/100000>0`,

so increasing a nonblocker coordinate strictly decreases `V_i` and strictly
increases `G_i`. The own coordinate is absent. These three cases exhaust every
possible coordinate assignment.

The sure-exit audit uses valid necessary conditions. For a coalition of size
at least two, an outsider can be stable only when both successors are in the
coalition, while a member cannot have both successors present. Any zero hence
forces the word `011`, and the all-one word fails; period three cannot close
on thirteen coordinates. Singleton coalitions fail by the exact joining
comparison `1001/1000>10003/10000`, and the same choice of outsider excludes
every instant-no-join owner. No missing size-two case repairs the recurrence.

## Proposition 15: standard Q by a proper complementarity map

The sign convention is correct. For

`Phi(x)=x^+-M x^-`,

a preimage `Phi(x)=q` gives `z=x^+`, `w=x^-`, and
`z=q+Mw`; on an orthant whose negative-coordinate support is `S`, the
derivative has column `M(*,j)` for `j in S` and identity column otherwise.
The checked theorem `eq_zero_of_isDeadlockHomogeneousComplementary` implies
`Phi^(-1)(0)={0}`. Positive homogeneity and compactness of the unit sphere then
give `||Phi(x)||>=eta||x||`, so the map is proper and one common large ball
works along every finite target segment.

I independently solved all sixteen support systems for
`q*=(1,1,2,1)`. The only feasible supports are exactly

```text
S={}       : w=(),              z=(1,1,2,1),
S={1,3}    : w=(1/2,1/3),       z_(0,2)=(7/2,2/3),
S={1,2,3}  : w=(3/4,1/2,1/2),  z_0=17/4.
```

All inequalities are strict. The corresponding complementary-matrix
determinants are `1,-6,8`, hence the local degree sum is `+1-1+1=1`.
The other support candidates in the note agree with exact elimination; none
gives a degenerate boundary solution. Homotopy invariance on a sufficiently
large ball carries degree one from `q*` to every `q`, and nonzero degree gives
an LCP solution. Positive rescaling and reindexing preserve this standard-Q
property by the elementary rescaling of the right-hand side.

## Proposition 16: balanced cycles really reduce to the checked lasso

The compression and orientation require care but are sound. A zero-hazard
phase has identical current and successor coarse values and may be deleted.
A maximal cyclic run of one owner composes to one singleton arc whose survival
is the product of the run survivals. After compression every hazard is
positive, every survival lies in `[0,1)`, adjacent owners differ, and opponent
divergence forces at least two owners.

A dummy cannot own a remaining phase. Relative to its own solo value, every
other owner's singleton gives exactly `1/10000`; cyclic unrolling makes its
active coarse value a convex combination with a strictly positive off-owner
weight, contradicting the active equality. Thus all owners lie in `D`.

Restricting to `D`, subtracting the solo baseline one, scaling by `10000`, and
reindexing gives nonnegative clearances `v_n` satisfying

`v_n=(1-s_n)M(*,owner_n)+s_n v_(n+1)`.

Active equality gives `v_n(owner_n)=0`; the owner coordinate of the same arc
and `s_n>0` give `v_(n+1)(owner_n)=0`. Read the phase word in reverse cyclic
order, take incoming clearance `v_(n+1)` and survival `s_n`, and the outgoing
clearance is exactly `v_n`. Since `v_n>=0`, every opponent clipping maximum in
`idealSingletonClearance` is inactive. The incoming owner clearance is zero,
so the local debt cost is also zero. Identically zero debt therefore satisfies
the complete `ReducedIdealSingletonLasso` recurrence, contradicting the
checked `ReducedIdealSingletonLasso.debt_pos`
(`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockReducedSingletonLassoBarrier.lean`).

This proves absence of the named balanced singleton certificate, not absence
of every singleton-only behavioral strategy language. The phase deletion,
cyclic compression, restriction, and reversal remain ordinary adapters rather
than named Lean declarations.

## Scope

Together the three propositions give a literal table on the nonhomogeneous
standard-Q side which is outside the audited sure-exit, instant-punishment,
playerwise common-box, and balanced-singleton producers, while the linear-
mixing stationary certificate applies. This is a strict supplied-certificate
separation and an actual-data positive class conditional on Proposition 11;
it is not a universal producer or a proof of the finite-quitting conjecture.
