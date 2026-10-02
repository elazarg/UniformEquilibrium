# Independent strengthening review of the HARD_RESIDUE clock-ratio followup

## Verdict

The clock-ratio identities are correct.  The stated diffuse consequence is
also correct, but it is substantially weaker than the exact classification.
An infinite strictly interior two-clock Nash--Bellman path has only three
coordinatewise possibilities:

1. the relevant singleton and pair increments both vanish, leaving that
   opponent clock unconstrained by the coordinate;
2. the opponent clock is exactly constant; or
3. the opponent clock follows an explicit geometrically decaying Zeno orbit.

The calibrated reward ratio has a sharp necessary-and-sufficient range, and
the converse orbit is explicit.  In the diffuse case this gives quantitative
summability and a positive conditional all-Never floor.

There is also a strong conditional Fin4 no-go: a negative normalized solo
entry and a positive collision-joining gain cannot coexist with an infinite
forward, strictly interior two-clock Nash--Bellman chronology.  Those are
exactly the two signs carried by a card-two hard principal plus a unique
all-Continue binding pair.

Nevertheless, **FAIL for export as a conjecture-facing result.**  No current
source theorem produces that forward chronology.  The actual maximal exact-
cap ray is oriented oppositely: each new state prefixes the previous state.
Its pair clocks satisfy the reverse recurrence and the opposite parameter
range, which is fully compatible with the hard signs and gives geometric
outward decay.  Reversing the ray would create a left-infinite word with no
first root, precisely the missing chronology producer.

The constant/constant forward branch has an existing exact terminal/uniform
consumer, but the diffuse branch only reaches a positive-survival phantom
boundary.  Thus the local theorem is a sharp classification and source
no-go, not a completion of either the paid/reset or paired unique-cap question.

The later estimates (11)--(12) are elementary consequences of nonnegative
summability and should be treated separately.  They add no new game-theoretic
consumer.

## 1. Exact consecutive-clock identities

Let `p != q`.  From some date `T` onward, suppose only `p,q` can Quit and both
strictly mix at every live root.  Write

\[
a_t=\Pr(p\text{ Quits at }t),
\qquad
b_t=\Pr(q\text{ Quits at }t),
\qquad
0<a_t,b_t<1.
\]

Let `v_t` be a bounded exact Nash--Bellman annotation:

\[
v_t=T_{x_t}v_{t+1},
\]

with every `x_t` exact endpoint Nash against `v_{t+1}`.

For player `p`, define

\[
s_p=r_p(\{p\}),
\quad
A_p=r_p(\{p,q\})-r_p(\{p\}),
\quad
B_p=r_p(\{q\})-r_p(\{p\}).
\tag{1}
\]

The two pure endpoints at date `t` are equal because `p` strictly mixes.  The
Quit endpoint and Continue endpoint respectively give

\[
v_t(p)-s_p=b_tA_p,
\tag{2}
\]

\[
v_t(p)-s_p
=(1-b_t)(v_{t+1}(p)-s_p)+b_tB_p.
\tag{3}
\]

Applying (2) at `t+1` and substituting in (3) yields

\[
\boxed{
(1-b_t)b_{t+1}A_p=b_t(A_p-B_p).}
\tag{4}
\]

The symmetric identity is

\[
\boxed{
(1-a_t)a_{t+1}A_q=a_t(A_q-B_q),}
\tag{5}
\]

where

\[
A_q=r_q(\{p,q\})-r_q(\{q\}),
\qquad
B_q=r_q(\{p\})-r_q(\{q\}).
\]

These formulas need no boundary convergence, compactness, absorption
conditioning, or block estimate.

The existing Lean ingredients are already almost exact:
`quittingRootQuitPayoff_pair_active`,
`quittingRootContinuePayoff_pair_active`, and `pairActive_indifference` in
`Research/Quitting/PairActiveSoloPhase.lean`.  The new content is the
consecutive-time substitution.

## 2. Sharp scalar classification

Suppress the player subscript and consider one identity

\[
(1-b_t)b_{t+1}A=b_t(A-B)
\tag{6}
\]

for an infinite sequence `0<b_t<1`.

### Degenerate chamber

If `A=0`, equation (6) and `b_t>0` force

\[
B=0.
\tag{7}
\]

In fact (2)--(3) then give `v_t=s` and `v_{t+1}=s`, while imposing no further
condition on the opponent clock.

### Calibrated chamber

Assume `A != 0` and put

\[
\rho=\frac{A-B}{A},
\qquad
\kappa=\frac BA=1-\rho.
\tag{8}
\]

Equation (6) becomes

\[
\boxed{
b_{t+1}=\rho\frac{b_t}{1-b_t}.}
\tag{9}
\]

Positivity of two consecutive hazards gives `rho>0`.  Existence of an
infinite orbit entirely in `(0,1)` forces the sharp range

\[
\boxed{0<\rho<1,
\qquad
0<\kappa<1,
\qquad
0<b_T\le\kappa.}
\tag{10}
\]

To see necessity, set `u_t=1/b_t`.  Then

\[
u_{t+1}=\frac{u_t-1}{\rho},
\tag{11}
\]

whose fixed point is `1/kappa`.  If `rho>=1`, positive `u_t>1` cannot persist
forever.  If `0<rho<1` but `b_T>kappa`, then `u_T<1/kappa` and (11) eventually
leaves the admissible region.  Conversely, every value in (10) produces an
infinite interior orbit.

There are exactly two subcases.

* If `b_T=kappa`, then

  \[
  b_t=\kappa
  \]

  for every later date.
* If `0<b_T<kappa`, then `b_t` decreases to zero and

  \[
  \boxed{
  \frac1{b_{T+n}}
  =\frac1\kappa
   +\rho^{-n}\left(\frac1{b_T}-\frac1\kappa\right).}
  \tag{12}
  \]

Thus the diffuse orbit is not merely eventually geometrically bounded; it is
explicit, with

\[
\frac{b_{T+n}}{\rho^n}
\longrightarrow
\left(\frac1{b_T}-\frac1\kappa\right)^{-1}.
\tag{13}
\]

The reward restriction is equally sharp:

\[
\boxed{0<\frac BA<1.}
\tag{14}
\]

Hence `A,B` have the same sign and `|B|<|A|`.  More explicitly,

\[
A>0\Longrightarrow0<B<A,
\qquad
A<0\Longrightarrow A<B<0.
\tag{15}
\]

The implication in the packet

\[
B\ne0\Longrightarrow A\ne0\Longrightarrow\sum b_t<\infty
\]

is valid under `b_t->0`, but (10)--(15) are the full classification.

## 3. Exact quantitative summability and Never floor

In the diffuse subcase, put

\[
\theta=\frac{\rho}{1-b_T}<1.
\]

Since the clock decreases,

\[
\rho
\le\frac{b_{t+1}}{b_t}
\le\theta.
\]

Therefore

\[
b_T\rho^n
\le b_{T+n}
\le b_T\theta^n,
\tag{16}
\]

and

\[
\boxed{
\frac{b_T}{\kappa}
\le
\sum_{n\ge0}b_{T+n}
\le
\frac{b_T(1-b_T)}{\kappa-b_T}.}
\tag{17}
\]

The recurrence in fact gives the survival probability exactly.  From

\[
1-b_{T+n}=\rho\frac{b_{T+n}}{b_{T+n+1}},
\]

one obtains

\[
\prod_{n=0}^{N-1}(1-b_{T+n})
=\rho^N\frac{b_T}{b_{T+N}}
=1-\frac{b_T}{\kappa}(1-\rho^N).
\]

Therefore

\[
\boxed{
\prod_{n\ge0}(1-b_{T+n})=1-\frac{b_T}{\kappa}>0.}
\tag{18}
\]

The preceding upper sum bound also yields the weaker but sometimes convenient
exponential estimate.  Since

\[
-\log(1-x)\le\frac{x}{1-b_T}
\qquad(0\le x\le b_T),
\]

\[
\boxed{
\prod_{n\ge0}(1-b_{T+n})
\ge
\exp\left(-\frac{b_T}{\kappa-b_T}\right)>0.}
\tag{18a}
\]

Apply the same classification to `a_t`.  If both clocks are diffuse, with
calibration parameters `kappa_p=B_p/A_p` for `b` and
`kappa_q=B_q/A_q` for `a`, then the conditional probability that neither
player ever Quits after date `T` obeys

\[
\boxed{
\prod_{n\ge0}(1-a_{T+n})(1-b_{T+n})
=
\left(1-\frac{a_T}{\kappa_q}\right)
\left(1-\frac{b_T}{\kappa_p}\right)>0.}
\tag{19}
\]

The exponential lower bound follows as a corollary if a form without exact
calibration is easier for a downstream interface.

This is a tail-conditional statement.  To turn it into unconditional mass
behind an earlier source prefix, that prefix must have a positive reach
floor.

If joint one-stage absorption tends to zero, then both `a_t,b_t->0`, so the
constant alternatives are impossible and (19) applies whenever both
off-diagonal solo entries are nonzero.

## 4. Sharp converse and examples

The classification has a complete coordinatewise converse.

* If `A=B=0`, the value coordinate `v_t=s` satisfies strict endpoint
  indifference for any partner clock in `(0,1)`.
* If `0<B/A<1`, choose any `0<b_T<=B/A`, generate `b` by (9), and define

  \[
  v_t(p)=s_p+b_tA_p.
  \]

  Then the `p` coordinate satisfies the exact Bellman equation and exact
  Quit/Continue indifference at every date.

Choosing the corresponding data in both directions constructs a complete
two-player exact endpoint-Nash/Bellman path.  In a larger game, the spectators'
endpoint inequalities are extra hypotheses; the two-coordinate converse does
not manufacture them.

### Diffuse negative-solo example

Take a symmetric two-player table with singleton baselines zero and

\[
A_p=A_q=-1,
\qquad
B_p=B_q=-\frac12.
\]

Then `rho=1/2`, `kappa=1/2`.  For any `0<h_0<1/2`, define

\[
h_{t+1}=\frac{h_t}{2(1-h_t)},
\qquad
a_t=b_t=h_t,
\qquad
v_t(p)=v_t(q)=-h_t.
\]

This is an exact strictly interior two-player Nash--Bellman path and has the
positive Never mass from (19).  It falsifies the retracted claim that negative
off-diagonal solo entries must vanish in a diffuse two-clock tail.

At `h_0=1/2`, the same reward ratios give the constant stationary branch.

### Invalid parameter chamber

If `B/A` is not in `(0,1)`, no infinite strictly interior orbit satisfying
(6) exists, apart from the degenerate `A=B=0` chamber.  This is stronger than
failure of diffuseness.

## 5. Hard-pair sign obstruction for a forward chronology

The project uses

\[
B_p
=\operatorname{normalizedSoloMatrix}(r)_{p,q},
\]

and

\[
C_p:=A_p-B_p
=r_p(\{p,q\})-r_p(\{q\})
=\operatorname{quittingSingletonCollisionGain}(q,p).
\tag{20}
\]

The forward classification gives, whenever `A_p != 0`,

\[
0<\frac{C_p}{A_p}<1.
\tag{21}
\]

In particular,

\[
B_p<0\Longrightarrow A_p<B_p<0
\Longrightarrow C_p<0.
\tag{22}
\]

Consequently one coordinate already gives the exact no-go

\[
\boxed{
B_p<0\quad\text{and}\quad C_p>0
\Longrightarrow
\text{no infinite forward strictly interior pair Nash--Bellman path}.}
\tag{23}
\]

For a card-two nonprojective Fin4 hard principal, the checked
`FinFourHardCardTwoCrossing` structure supplies both reciprocal inequalities
`B_p<0`, `B_q<0`.  Under unique all-Continue at a cap whose binding face is
exactly `{p,q}`, the checked
`quittingSingletonCollisionGain_pos_of_bindingFinset_card_eq_two` supplies
`C_p>0`, `C_q>0`.  Therefore that static packet cannot be the boundary of an
infinite forward pair-interior Nash--Bellman chronology.

This is a correct conditional obstruction.  It does not show that the current
paid/reset or strict-ray source produces the forbidden forward chronology.

## 6. The actual maximal ray has the reverse recurrence

This directional distinction is decisive.

`QuittingForwardExactCapTail` is named “forward,” but its semantic orientation
is outward prefixing:

\[
V_{n+1}=T_{x_n}V_n.
\tag{24}
\]

The root `x_n` is exact cap Nash against the **older** cap `V_n`.  Suppose its
late roots are supported on `{p,q}` and both coordinates strictly mix.  The
same endpoint calculation now gives

\[
V_{n+1}(p)-s_p=b_nA_p,
\]

\[
V_{n+1}(p)-s_p
=(1-b_n)(V_n(p)-s_p)+b_nB_p.
\]

Using the preceding date to substitute for `V_n` yields

\[
\boxed{
(1-b_n)b_{n-1}A_p=b_n(A_p-B_p).}
\tag{25}
\]

For `A_p != 0` and `rho_p=(A_p-B_p)/A_p`,

\[
\boxed{
b_n=\frac{b_{n-1}}{\rho_p+b_{n-1}}.}
\tag{26}
\]

This is the reverse of (9).  With `u_n=1/b_n`,

\[
u_n=\rho_pu_{n-1}+1.
\tag{27}
\]

If `b_n->0`, then `rho_p>=1`.  If in addition `sum b_n<infinity`, as in an
actual `QuittingForwardExactCapTail`, then the harmonic case `rho_p=1` is
excluded and

\[
\boxed{\rho_p>1.}
\tag{28}
\]

The exact solution is

\[
\boxed{
\frac1{b_{T+n}}
=\rho_p^n\frac1{b_T}
 +\frac{\rho_p^n-1}{\rho_p-1}.}
\tag{29}
\]

Thus the outward clock decays geometrically with ratio `1/rho_p` and

\[
\sum_{n\ge0}b_{T+n}
\le\frac{b_T\rho_p}{\rho_p-1}.
\tag{30}
\]

The hard signs are now compatible rather than contradictory:

\[
B_p<0,\quad C_p=A_p-B_p>0
\Longrightarrow
A_p>0,\quad \rho_p>1
\]

whenever such a summable outward orbit exists.

This supplies the honest actual-source adapter.  From a
`QuittingForwardExactCapTail`, eventual support in `{p,q}`, eventual positivity
of both current coordinates, and cap-root exactness give (25)--(30).  The
existing theorem `eventually_currentHazard_supported_binding` supplies pair
support when the binding set is `{p,q}`; positivity of both pair coordinates
remains an additional branch hypothesis.  Summable absorption makes their
Continue probabilities eventually positive.

For both players, let `rho_p` govern `q`'s clock and `rho_q` govern `p`'s.
Then:

* if `rho_p != rho_q`, the slower-decaying clock dominates and the normalized
  current direction tends to a singleton boundary;
* if `rho_p=rho_q=rho`, the normalized pair direction converges to a positive
  constant determined by the two initial coefficients; and
* in either case the normalized renewal ratio tends to

  \[
  1-\frac1{\min(\rho_p,\rho_q)}.
  \tag{31}
  \]

These are exact source-level normalized classifications, not terminal
consumers.  The checked project already excludes binding cardinality two in
the relevant unique-cap strict-ray branch by an independent finite
complementarity argument, so this does not reopen or strengthen that closed
branch unless it replaces that proof by a desired simpler adapter.

## 7. Consumer audit

### Constant/constant forward clocks

If both coordinates are in their constant calibrated branch and the supplied
path is exact root Nash for every player with bounded values, every player has
a uniformly positive opponent absorption rate.  The one-step opponent-
survival contraction is strict.  The checked theorem
`infinitePath_isUniformEquilibriumPayoff_of_survival_tendsto_zero` in
`UniformEquilibrium/Quitting/Paths/InfinitePathCompiler.lean` therefore
compiles the path to an exact terminal Nash profile and a uniform-equilibrium
payoff.

This is a genuine consumer for that supplied branch.  It is not an arbitrary-
game producer.

### Diffuse/diffuse forward clocks

Both clocks are summable and the tail has positive Never mass.  The supplied
Bellman annotation converges to the singleton baseline vector on `p,q`.  The
phantom-boundary identity says that annotation differs from the actual
terminal payoff by

\[
\text{joint survival limit}\times\text{boundary value}.
\]

Thus exact local endpoint Nash does not by itself identify the annotation
with the actual semantic pair.  If the complete boundary vector is zero, a
separate zero-boundary Snell argument can select the actual terminal payoff;
that additional hypothesis is not supplied by the hard residual.

Positive Never mass is not a contradiction and is not itself a uniform-
equilibrium consumer.  It is the surviving Zeno/phantom arm.

### Mixed constant/diffuse clocks

All outsiders and one principal player see a dying opponent-survival clock,
but the other principal player can retain positive opponent survival.  The
general infinite-path compiler does not apply to every coordinate.  A one-
exceptional-owner punishment consumer would require additional punishment
and payoff anchoring not present in the clock-ratio interface.

### Outward clocks

Equations (25)--(31) describe the actual prefix ray, but an outward sequence

\[
V_0\to V_1\to V_2\to\cdots,
\qquad V_{n+1}=T_{x_n}V_n,
\]

is not executable in that order as play.  Reversing it requires a
left-infinite root word and provides no first stage.  Hence the actual-source
classification does not manufacture the forward chronology ruled out by
(23).

## 8. The separate tail-charge estimates (11)--(12)

Let `alpha_n>=0` and `sum alpha_n<infinity`.  Then

\[
\sup_{m>n}\sum_{k=n}^{m-1}\alpha_k
=\sum_{k\ge n}\alpha_k\longrightarrow0.
\]

For `c_k=1-alpha_k` in `[0,1]`, the finite union/product bound gives

\[
1-\prod_{k=n}^{m-1}c_k
\le\sum_{k=n}^{m-1}\alpha_k.
\]

Therefore the supremum of the left side also tends to zero.  These are sharp,
standard consequences of summability.  They correctly show that sufficiently
late maximal-ray blocks have no fixed positive inserted-root charge floor.
They do not affect the clock-ratio proof and do not turn the retained suffix
gain or suffix atom into root absorption.

## 9. Lean handoff

The generic forward-clock layer should be separated into algebra and game
adapters:

```text
pairActive_chronologicalClockRatio_identity

interiorClockOrbit_degenerate_or_stationary_or_zeno

interiorClockOrbit_explicit
interiorClockOrbit_summable_bounds
interiorClockOrbit_neverProduct_lowerBound

exists_interiorClockOrbit_iff_ratio_mem_openUnit
```

The game identity should reuse `pairActive_indifference` and the checked pair
Quit-payoff formula rather than re-expand product PMFs.

The sign consumer should be explicit:

```text
not_exists_pairInteriorNashBellmanPath_of_solo_neg_of_collisionGain_pos
```

For the actual prefix source, use separate names that expose orientation:

```text
QuittingForwardExactCapTail.pairInterior_outwardClockRatio_identity

QuittingForwardExactCapTail.pairInterior_outwardClock_explicit

QuittingForwardExactCapTail.pairInterior_outwardClock_ratio_gt_one
```

Do not use the chronological theorem by silently reversing a natural-numbered
`QuittingForwardExactCapTail`.

Exact tests should include:

* `A=B=0`, showing the clock is unconstrained;
* `A=-1, B=-1/2`, with both the diffuse and constant forward solutions;
* a ratio outside `(0,1)`, showing no infinite forward interior orbit;
* `B<0, A-B>0`, showing the forward sign contradiction; and
* the same signs in the outward recurrence with `rho>1`, showing geometric
  source-ray decay rather than contradiction.

## 10. Export gate

### PASS conditions

The chronological classification could become conjecture-facing only if a
named actual Fin4 source is proved to produce its forward exact pair-interior
path, so that (23) eliminates a live branch, or if every remaining clock
branch is sent to an existing terminal/rank consumer.

The outward classification could pass only if its singleton-boundary and
balanced-geometric outputs are consumed into a renewable finite rank,
admissible return, terminal approximants, or contradiction.  Merely
classifying their decay is not enough.

A special-case export would also be possible for a precisely defined class
whose actual source is proved to enter the constant/constant branch and then
uses the checked infinite-path consumer.  No such arbitrary-table adapter is
present here.

### Current FAIL conditions

* The current source ray has the opposite temporal orientation from the
  chronological identity.
* No source theorem produces an executable forward pair-interior path.
* Positive tail Never mass is an unconsumed phantom-boundary output.
* One constant and one diffuse clock leave an exceptional player uncompiled.
* The actual outward pair classification ends only in normalized boundary or
  ballistic data.
* Binding-cardinality two is already excluded in the relevant checked strict-
  ray branch by a different theorem.
* Estimates (11)--(12) are standard summability facts, not a new consumer.

The correct disposition is to retain the exact clock classification and the
forward-versus-outward orientation no-go as Research notes.  They should not
be exported as a solution to the current Fin4 questions.
