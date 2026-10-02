# Feedback on Quit-Time Compactification, Round 30

Reviewer: `CODEX_GAUSS`

Target: Section 58.15, Proposition 70 (diffuse radial complementarity
trajectory) of `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`.

## Verdict

**Valid ordinary mathematics with the stated principal-face/nonproducer
scope.**  I found no counterexample to the compactification, differential
orientation, complementarity, or finite-variation kernel extraction.  This
review is not a Lean check.

## Row and mesh checks

On a selected future row let `Q` be joint absorption, `h=max_i p_i`, and
`q_l` the record scale.  Each marginal obeys `p_i<=Q`, hence `h<=Q`.  The
collision probability is bounded by

```text
sum_(i<j) p_i p_j <= choose(n,2) h^2
                       <= choose(n,2) h Q.
```

Since every future `Q/q_l<=Phi_l->0`, collision divided by `Q` vanishes
uniformly on each fixed normalized-time interval.  The singleton
occupations are therefore uniformly bounded subprobabilities whose missing
mass tends uniformly to zero.  Finite-dimensional weak-star compactness gives
a simplex-valued measurable limit after the stated diagonal extraction.

The first-crossing/triangular repair from Proposition 69 is exactly enough:
for each fixed compact interval, all sufficiently late selected tails cover
it and their grid mesh is at most `Phi_l`.  No single finite tail is being
asked to carry an unbounded countable horizon.

## Active anchoring and compactness

If a limiting coordinate `i` has positive mass on some bounded interval,
weak-star convergence forces an actual row with positive unique-`i` mass on
that interval.  There `0<p_i<1` eventually.  Exact endpoint Nash makes the
two pure endpoints equal, while forced Quit differs from `r_i({i})` by at
most a constant times opponent absorption, hence by `O(Q)`.  As all selected
dates tend to infinity,

```text
b_i=r_i({i}),
(X_i-b_i)/q_l=O(Q/q_l)=O(Phi_l)
```

on active rows.  The one-edge `2M Q` motion bound transports a finite bound
from one such row to every fixed compact normalized interval.  This works
even if the first interval carrying `i`-mass is not near time zero: its
finite distance is absorbed into the compact-dependent bound.  The same
motion bound makes the affine interpolants equi-Lipschitz.

For every row, exact endpoint Nash gives current value at least forced Quit;
with `b_i=r_i({i})` this yields the lower error
`v_(l,i)>=-C Q/q_l`.  Thus `v_i>=0`.  On rows with positive `i` occupation the
preceding active estimate is uniform, so
`integral mu_(l,i)|v_(l,i)|->0`; weak-star/uniform convergence gives
`mu_i v_i=0` almost everywhere.

The canonical punishment-floor inequality passes to `b_i`, so each active
principal player satisfies `punishment_i<=b_i=solo_i`, exactly the claimed
production normality.

## Differential identity and dichotomy

Bellman recursion gives

```text
X_m=(1-Q_m)X_(m+1)+Q_m D_m,
(v_l)'=(X_(m+1)-D_m)
```

on the interval of length `Q_m/q_l`; the sign in `(N109)` is therefore
correct.  Collision delivery vanishes and singleton delivery converges weakly
to `sum_j mu_j r({j})`.  On `A`, where `b_i=r_i({i})`, this yields

```text
v_i' = b_i-sum_j mu_j r_i({j}) = -(M_A mu)_i.
```

Local absolute continuity gives variation
`integral ||M_A mu||`.  In the infinite-variation arm, lower semicontinuity
under uniform convergence supplies arbitrarily large normalized variation in
the exact blocks.  In the finite arm, integrability supplies Lebesgue points
`t_n->infinity` with `||M_A mu(t_n)||->0`; simplex compactness then gives a
limit `mu_*` with `M_A mu_*=0`.

The final qualification is essential and correct.  `mu_*` solves the kernel
equations only on the active principal rows.  Nothing here proves the ambient
outside-row inequalities needed to extend it to a full homogeneous simplex
LCP witness, and arm (a) supplies neither an unscaled payoff return nor Simon's
common near-feasible carrier.

