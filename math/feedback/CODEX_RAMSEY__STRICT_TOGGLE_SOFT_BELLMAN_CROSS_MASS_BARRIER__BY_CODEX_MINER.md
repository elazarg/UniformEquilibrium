# Independent review of the strict-toggle soft Bellman cross-mass barrier

**Reviewer:** CODEX_MINER  
**Target:**
[`CODEX_RAMSEY__STRICT_TOGGLE_SOFT_BELLMAN_CROSS_MASS_BARRIER.md`](../notes/CODEX_RAMSEY__STRICT_TOGGLE_SOFT_BELLMAN_CROSS_MASS_BARRIER.md)  
**Verdict:** **PASS.**  The quantitative inequality, product-support
obstruction, both exact two-player completions, and the scoped architecture
conclusion are correct.  I found no conflict with the updated strict
minimum-fiber basin.

## 1. Quantitative orientation check

Orient `G` as target endpoint minus source endpoint.  On the advertised
opponent coalition `R`, `G_R>=Gamma`.  On every other coalition,
`G_A>=-2M`: for a nonempty coalition this is the difference of two bounded
terminal rewards; at the empty coalition it is the difference between the
bounded solo reward and bounded declared tail coordinate.  Therefore

```text
G >= w_R*Gamma-(1-w_R)*2M
  = (Gamma+2M)*w_R-2M.
```

If the target is Quit, the source-action mass is the mover's Continue mass;
if the target is Continue, it is the mover's Quit mass.  In both orientations
the gain from the prescribed mixture to the pure target is exactly `a*G`.
The two identities in `SuccessorCertificate.lean` give this with the correct
sign.  Endpoint `epsilon`-Nash therefore yields

```text
a*((Gamma+2M)*w_R-2M) <= epsilon.
```

For an exact genuine mixer, `a>0`, so
`w_R<=2M/(Gamma+2M)` and the off-row mass is at least
`Gamma/(Gamma+2M)`.  When both action masses are at least `theta`, deviations
to both pure endpoints give `|G|<=epsilon/theta`; hence (2.6).  Under
`epsilon<=theta*Gamma/2`, subtracting from one gives exactly the stated
`Gamma/[2(Gamma+2M)]` lower bound.  No absorption or independence factor is
missing from these calculations.

If all members of nonempty `R` remain sure quitters and all other opponents
retain their pure endpoint actions, then `w_R=1`.  Exactness forces the
source-action mass to zero, and the sure member of `R` makes joint survival
zero.  The one-coordinate consequence is therefore correct.

## 2. Product-law cross atom

Positive empty mass makes every marginal Continue probability positive.
Positive mass on `R union {i}` makes `i` and every member of `R` have positive
Quit probability.  Hence the product law gives positive mass to `{i}`:
`i` Quits while every other player Continues.  Since `R` is nonempty and does
not contain `i`, this is a fourth coalition.  Lemma 3.1 is exact.

## 3. Completion A

At the half-half root and tail `(0,0)`:

* player `1` has Quit and Continue endpoint values both zero;
* player `2` has Quit value
  `(1/2)(-1)+(1/2)(1)=0` and Continue value zero;
* both successor coordinates are zero;
* all-Continue mass is `1/4`, so absorption charge is `3/4`;
* each player's opponent Continue mass is `1/2<1`.

Thus the row is an exact endpoint-Nash fixed-point self-edge, and the checked
stationary compiler applies against unrestricted behavioral deviations.

The punishment-floor calculation also has the claimed exact witnesses.
Against pure row `{2}`, player `1`'s joined/unjoined cap is `max(0,0)=0`.
Against the empty pure row, player `2`'s cap is `max(-1,0)=0`.  Hence both
punishment values are at most the zero tail.

## 4. Completion B and same-edge data

With `r({2})=(-1,-1)`, player `1`'s pure Quit value is zero and pure Continue
value is `-p_2`.  Its Quit-minus-Continue difference is `p_2`, and deviation
from the prescribed marginal to pure Quit has regret

```text
(1-p_1)*p_2 = Prob_q({2}).
```

Therefore endpoint `epsilon`-Nash implies the exact bound in (4.7).  Positive
mass on empty, `{1}`, and `{1,2}` implies `0<p_1,p_2<1`, so the cross mass is
strictly positive and exact endpoint Nash is impossible for such a live
three-advertised-atom softening.

The tail remains floor safe: player `1`'s pure `{2}` cap is
`max(0,-1)=0`, and player `2` retains the empty-row cap zero.  At each edge
vertex `{1}` and `{1,2}`, the complete pure-set cap vector is `(0,1)` in both
completions.  Thus the two completions agree on the tail, both edge payoff
vectors, the mover/gap/orientation, the reward bound, and both edge cap
vectors.  Only the forced cross row differs.

The note correctly limits the negative claim: Completion B may have other
positive-charge exact roots.  What it excludes is an exact live product law
retaining positive mass on the advertised empty and both strict-edge
coalitions.  This is enough for the stated non-identification of an
edge-only converter.

## 5. Cycle and current-frontier scope

The checked reachable simple strict-toggle cycle has even length at least
four.  A simple hypercube cycle has at most the two cycle edges incident to
the empty vertex; every other toggle edge has nonempty common opponent set.
The three local choices in Section 5 therefore accurately state the barrier
to independently softening each edge from its strict inequality alone.

This is not subsumed by the older static chronology theorem: that theorem
handles literal pure roots, whereas Theorem 2.1 quantifies the off-row mass
forced by a live diffuse root.  It also neither duplicates nor contradicts
the current minimum-fiber results.  Inside the checked open minimum-fiber
tube, all-Continue is the unique exact root, so a positively absorbing exact
soft-toggle row is already excluded.  The linear theorem charges approximate
absorption by total Nash defect there.  Ramsey's barrier applies to attempts
outside that local basin and correctly says the strict edge alone does not
control the required cross-coalition rewards.  It produces no paid-port
provenance or inert-arm consumer.

