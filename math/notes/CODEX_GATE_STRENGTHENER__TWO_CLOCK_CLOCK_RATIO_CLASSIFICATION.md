# Exact two-clock clock-ratio classification

## Status

This note records a proved ordinary-mathematics classification.  It has not
been checked in Lean and is not an export packet.

The forward chronological result is an exact if-and-only-if theorem, including
an explicit converse and exact conditional Never probability.  Its strongest
Fin4 sign consequence is conditional on producing an executable forward
two-clock chronology.  The checked maximal exact-cap tail has the opposite
orientation and obeys a different recurrence; it does not supply that
chronology.

The elementary late-block consequences of summable maximal-root absorption
are not part of this result and are recorded separately in Section 9.

## 1. Forward chronological hypotheses

Fix distinct players `p,q`.  From some date `T` onward, suppose only `p,q`
can Quit and both strictly mix at every live root.  Write

\[
a_t=\Pr(p\text{ Quits at }t),
\qquad
b_t=\Pr(q\text{ Quits at }t),
\qquad 0<a_t,b_t<1.
\]

Let `v_t` be a bounded exact Nash--Bellman annotation in chronological order:

\[
v_t=T_{x_t}v_{t+1},
\]

where `x_t` is exact endpoint Nash against the next annotation `v_{t+1}`.
For player `p`, put

\[
s_p=r_p(\{p\}),
\quad
A_p=r_p(\{p,q\})-r_p(\{p\}),
\quad
B_p=r_p(\{q\})-r_p(\{p\}).
\tag{1}
\]

Strict mixing makes the Quit and Continue endpoints equal.  The Quit endpoint
and the Bellman equation give

\[
v_t(p)-s_p=b_tA_p,
\tag{2}
\]

\[
v_t(p)-s_p
=(1-b_t)(v_{t+1}(p)-s_p)+b_tB_p.
\tag{3}
\]

Using (2) at `t+1` in (3) yields

\[
\boxed{(1-b_t)b_{t+1}A_p=b_t(A_p-B_p).}
\tag{4}
\]

Symmetrically, with

\[
A_q=r_q(\{p,q\})-r_q(\{q\}),
\qquad
B_q=r_q(\{p\})-r_q(\{q\}),
\]

one has

\[
\boxed{(1-a_t)a_{t+1}A_q=a_t(A_q-B_q).}
\tag{5}
\]

The checked local ingredients corresponding to (2)--(3) are
`quittingRootQuitPayoff_pair_active`,
`quittingRootContinuePayoff_pair_active`, and `pairActive_indifference` in
`Research/Quitting/PairActiveSoloPhase.lean`.  The consecutive-date
substitution (4)--(5) is not claimed checked.

## 2. Sharp scalar theorem

Consider an infinite sequence `0<b_t<1` satisfying

\[
(1-b_t)b_{t+1}A=b_t(A-B).
\tag{6}
\]

### Degenerate chamber

If `A=0`, then `B=0`.  The corresponding value coordinate is pinned to the
singleton baseline, but this coordinate imposes no condition on the partner's
clock.

### Nondegenerate chamber

Assume `A` is nonzero and define

\[
\rho=\frac{A-B}{A},
\qquad
\kappa=\frac BA=1-\rho.
\tag{7}
\]

Then

\[
\boxed{b_{t+1}=\rho\frac{b_t}{1-b_t}.}
\tag{8}
\]

There is an infinite orbit entirely in `(0,1)` if and only if

\[
\boxed{0<\rho<1,
\qquad 0<\kappa<1,
\qquad 0<b_T\le\kappa.}
\tag{9}
\]

Equivalently, the sharp reward chamber is

\[
\boxed{0<\frac BA<1.}
\tag{10}
\]

Thus `A,B` have the same sign and `|B|<|A|`.

If `b_T=\kappa`, the orbit is exactly constant.  If `b_T<\kappa`, the clock
strictly decreases to zero and

\[
\boxed{
\frac1{b_{T+n}}
=\frac1\kappa
\rho^{-n}\left(\frac1{b_T}-\frac1\kappa\right).}
\tag{11}
\]

In particular,

\[
\frac{b_{T+n}}{\rho^n}
\longrightarrow
\left(\frac1{b_T}-\frac1\kappa\right)^{-1}.
\tag{12}
\]

Proof: setting `u_t=1/b_t` changes (8) to

\[
u_{t+1}=\frac{u_t-1}{\rho}.
\]

Its fixed point is `1/\kappa`.  Positivity gives `\rho>0`.  If
`\rho\ge1`, no infinite orbit remains in `u_t>1`; if `0<\rho<1` but
`b_T>\kappa`, the orbit lies on the unstable side of the fixed point and
eventually exits `(0,1)`.  The remaining initial values give (11) directly.

## 3. Converse

The classification is coordinatewise sufficient, not merely necessary.

* If `A=B=0`, set the coordinate annotation equal to the singleton baseline;
  any partner clock in `(0,1)` satisfies this player's equality.
* If `0<B/A<1`, choose any `0<b_T\le B/A`, generate `b` by (8), and set

  \[
  v_t(p)=s_p+b_tA_p.
  \]

  Then the Bellman equation and Quit/Continue equality hold exactly at every
  date.

Applying the construction in both directions gives a full two-player exact
endpoint-Nash/Bellman path.  With additional players, all spectator endpoint
inequalities remain independent hypotheses.  The converse does not construct
them.

## 4. Exact sum and survival information

In the diffuse chamber `0<b_T<\kappa`, let

\[
\theta=\frac{\rho}{1-b_T}<1.
\]

Monotonicity gives

\[
b_T\rho^n\le b_{T+n}\le b_T\theta^n
\tag{13}
\]

and therefore

\[
\boxed{
\frac{b_T}{\kappa}
\le \sum_{n\ge0}b_{T+n}
\le \frac{b_T(1-b_T)}{\kappa-b_T}.}
\tag{14}
\]

The conditional Never probability is exact.  Equation (8) gives

\[
1-b_{T+n}=\rho\frac{b_{T+n}}{b_{T+n+1}},
\]

so

\[
\prod_{n=0}^{N-1}(1-b_{T+n})
=\rho^N\frac{b_T}{b_{T+N}}
=1-\frac{b_T}{\kappa}(1-\rho^N).
\]

Hence

\[
\boxed{
\Pr(q\text{ Never Quits after }T
\mid\text{the live history reaches }T)
=1-\frac{b_T}{\kappa}.}
\tag{15}
\]

For two diffuse clocks the exact conditional all-Never mass is

\[
\boxed{
\left(1-\frac{a_T}{\kappa_q}\right)
\left(1-\frac{b_T}{\kappa_p}\right),}
\tag{16}
\]

where `\kappa_p=B_p/A_p` governs `b`, and `\kappa_q=B_q/A_q`
governs `a`.  This is strictly positive.  It becomes an unconditional mass
only after multiplication by the probability of reaching date `T`; the
theorem provides no lower bound on that earlier reach probability.

The endpoint `b_T=\kappa` is the constant-clock branch and its Never
probability is zero, as (15) correctly indicates.

## 5. Boundary examples

### Diffuse Zeno example

Take a symmetric two-player table with singleton baselines zero and

\[
A_p=A_q=-1,
\qquad B_p=B_q=-\frac12.
\]

Then `\rho=\kappa=1/2`.  For any `0<h_0<1/2`, define

\[
h_{t+1}=\frac{h_t}{2(1-h_t)},
\qquad
a_t=b_t=h_t,
\qquad
v_t(p)=v_t(q)=-h_t.
\]

This is an exact strict-interior two-player Nash--Bellman path.  Its
conditional all-Never probability is exactly

\[
\left(1-2h_0\right)^2.
\]

It falsifies any assertion that negative off-diagonal solo increments must
vanish in a diffuse two-clock tail.

### Constant endpoint

With the same reward ratios and `h_0=1/2`, the path is stationary and has
zero Never probability.

### Invalid ratio

Apart from `A=B=0`, a ratio `B/A` outside `(0,1)` admits no infinite forward
strict-interior orbit.  This is failure of existence, not merely failure of
diffuseness.

## 6. Hard-sign no-go for a forward chronology

In project notation,

\[
B_p=\operatorname{normalizedSoloMatrix}(r)_{p,q}
\]

and

\[
C_p:=A_p-B_p
=r_p(\{p,q\})-r_p(\{q\})
=\operatorname{quittingSingletonCollisionGain}(q,p).
\tag{17}
\]

The forward chamber requires

\[
0<\frac{C_p}{A_p}<1.
\]

If `B_p<0`, then necessarily `A_p<B_p<0`, hence `C_p<0`.  Therefore

\[
\boxed{
B_p<0\text{ and }C_p>0
\Longrightarrow
\text{no infinite forward strict-interior pair chronology}.}
\tag{18}
\]

A card-two hard principal supplies reciprocal negative `B` entries through
`FinFourHardCardTwoCrossing`.  A unique all-Continue limiting root with a
card-two binding face supplies reciprocal positive collision gains through
`quittingSingletonCollisionGain_pos_of_bindingFinset_card_eq_two` in
`Research/Quitting/BindingCollisionGainPositivity.lean`.  If an actual source
produced the forward chronology with those same labels, one coordinate would
already contradict (18).

No current source theorem supplies that chronology.  The sign no-go is a
consumer for a supplied object, not a producer from the hard residual.

## 7. Orientation of `QuittingForwardExactCapTail`

Despite its name, `QuittingForwardExactCapTail` in
`Research/Quitting/ForwardExactCapTailFlow.lean` is oriented by outward
prefixing:

\[
V_{n+1}=T_{x_n}V_n.
\tag{19}
\]

The new root `x_n` is exact against the older cap `V_n`.  If late roots are
supported on `{p,q}` and both coordinates strictly mix, the same calculation
now gives

\[
\boxed{(1-b_n)b_{n-1}A_p=b_n(A_p-B_p).}
\tag{20}
\]

For `A_p\ne0` and `\rho_p=(A_p-B_p)/A_p`, this is

\[
\boxed{b_n=\frac{b_{n-1}}{\rho_p+b_{n-1}}.}
\tag{21}
\]

Thus

\[
\frac1{b_n}=\rho_p\frac1{b_{n-1}}+1.
\]

If `b_n\to0`, then `\rho_p\ge1`.  If the clock is summable, as it is for an
actual forward exact-cap tail, the harmonic case is excluded and

\[
\boxed{\rho_p>1.}
\tag{22}
\]

The explicit solution is

\[
\boxed{
\frac1{b_{T+n}}
=\rho_p^n\frac1{b_T}
+\frac{\rho_p^n-1}{\rho_p-1}.}
\tag{23}
\]

In particular,

\[
\sum_{n\ge0}b_{T+n}
\le\frac{b_T\rho_p}{\rho_p-1}.
\tag{24}
\]

The hard signs are compatible with this outward recurrence only in the
sharper chamber

\[
B_p<0,
\qquad C_p=A_p-B_p>0,
\qquad A_p>0,
\qquad \rho_p=\frac{C_p}{A_p}>1.
\tag{25}
\]

The signs `B_p<0,C_p>0` alone do not force `A_p>0`; they therefore neither
construct nor contradict the outward orbit.  When (25) holds, they give its
geometric decay rather than a contradiction.

For both principal players, `\rho_p` governs `q`'s clock and `\rho_q`
governs `p`'s.  Unequal ratios make the slower clock dominate the normalized
current direction; equal ratios give a positive limiting pair direction.  In
either case the total one-stage absorption has asymptotic ratio

\[
\frac{\alpha_{n+1}}{\alpha_n}
\longrightarrow
\frac1{\min(\rho_p,\rho_q)}.
\tag{26}
\]

Equivalently, the normalized lost fraction tends to
`1-1/min(\rho_p,\rho_q)`.

### Actual-source adapter requirements

The outward formulas apply to an actual `QuittingForwardExactCapTail` after
one proves all of the following:

1. its binding face is exactly `{p,q}`;
2. all outsider current hazards are eventually zero;
3. both principal current hazards are eventually strictly positive; and
4. the corresponding roots are exact at the stored caps.

The checked theorem `eventually_currentHazard_supported_binding` supplies
item 2 from item 1.  Strict positivity of both pair coordinates is a separate
branch hypothesis.  Exactness and summability are fields/consequences of the
source object.

In the relevant current Fin4 strict-ray development, binding cardinality two
is already excluded by a separate finite-complementarity argument.  The
clock-ratio theorem is therefore not a new closure of that live branch.

Most importantly, the outward ray cannot be reversed into the executable
chronology `v_t = T_{x_t} v_{t+1}` from Section 1: reversal produces a
left-infinite word with no first root.  This is an orientation obstruction,
not an indexing convention.

## 8. Available and unavailable consumers

* **Forward constant/constant.**  If the complete supplied path is exact root
  Nash for every player and bounded, both constant positive clocks give
  opponent-survival contraction for every player.  The checked
  `infinitePath_isUniformEquilibriumPayoff_of_survival_tendsto_zero` in
  `UniformEquilibrium/Quitting/Paths/InfinitePathCompiler.lean` supplies an
  exact terminal Nash profile and a uniform-equilibrium payoff.
* **Forward diffuse/diffuse.**  Equation (16) gives a positive-survival
  phantom boundary.  The Bellman annotation need not equal the actual
  terminal semantic payoff; a boundary or transversality theorem is still
  required.
* **Forward constant/diffuse.**  One exceptional principal player can retain
  positive opponent survival.  The general infinite-path consumer does not
  apply without an additional punishment/anchoring theorem.
* **Outward ray.**  Equations (20)--(26) classify normalized boundary behavior
  only.  They produce no executable return, support descent, or terminal
  approximation.

## 9. Separate duplicate maximal-orbit tail facts

If `\alpha_n\ge0` and `\sum_n\alpha_n<\infty`, then

\[
\sup_{m>n}\sum_{k=n}^{m-1}\alpha_k
=\sum_{k\ge n}\alpha_k\longrightarrow0.
\]

If `c_k=1-\alpha_k`, then

\[
1-\prod_{k=n}^{m-1}c_k
\le\sum_{k=n}^{m-1}\alpha_k,
\]

so the supremum of the left-hand side also tends to zero.  These elementary
facts correctly show that late blocks of a summable maximal-prefix orbit
carry no fixed positive inserted-root charge.  They are already standard and
are not part of the clock-ratio classification.

They do not convert a retained suffix gain or inherited terminal atom into
new root absorption.

## 10. Proposed Lean boundary

The algebra and game adapters should remain separate.  Suitable theorem
shapes are:

```text
pairActive_chronologicalClockRatio_identity

interiorClockOrbit_degenerate_or_stationary_or_zeno
interiorClockOrbit_explicit
interiorClockOrbit_summable_bounds
interiorClockOrbit_neverProbability_eq

exists_interiorClockOrbit_iff_ratio_mem_openUnit

not_exists_pairInteriorNashBellmanPath_of_solo_neg_of_collisionGain_pos

QuittingForwardExactCapTail.pairInterior_outwardClockRatio_identity
QuittingForwardExactCapTail.pairInterior_outwardClock_explicit
QuittingForwardExactCapTail.pairInterior_outwardClock_ratio_gt_one
```

Tests must cover `A=B=0`, a constant calibrated clock, the negative-solo Zeno
example, an invalid ratio, the forward hard-sign contradiction, and the same
signs in the outward geometric chamber.

## 11. Nonclaims

This note does not prove:

* that a Fin4 minimum source produces a forward two-clock chronology;
* that the actual maximal ray can be reversed in time;
* that positive conditional Never mass is a contradiction;
* that the Bellman boundary annotation is an actual terminal payoff;
* that the mixed constant/diffuse branch is punishment-completable;
* that the outward normalized limit has a return or rank consumer; or
* the four-player uniform-equilibrium conjecture.

The result should remain a Research note until an actual source adapter feeds
one of its branches into a terminal or well-founded consumer.
