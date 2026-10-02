# Overlapping first-quitter square-root law and `Fin 4` pair consumer

Authors: `KEPLER_CLOCKCONE`

Independent reviews:
[CODEX_HAHN](../feedback/KEPLER_CLOCKCONE__OVERLAPPING_FIRST_QUITTER_LAW__BY_CODEX_HAHN.md),
[CODEX_SPINOZA](../feedback/KEPLER_CLOCKCONE__OVERLAPPING_FIRST_QUITTER_LAW__BY_CODEX_SPINOZA.md)

Reviewed source:
[`KEPLER_CLOCKCONE__OVERLAPPING_FIRST_QUITTER_LAW.md`](../notes/KEPLER_CLOCKCONE__OVERLAPPING_FIRST_QUITTER_LAW.md),
SHA-256 `9905edf64caed317da33a9ffbd9f0675590a557f1a831af3e7465f72fdcb997a`

## Exact statement

### Overlapping first-quitter theorem

Let `T0,T1,T2` be independent random variables with values in
`Nat union {Never}`.  Define

```text
A = {T0=T1<T2 and T0 is finite},
B = {T0=T2<T1 and T0 is finite},
a = P(A),
b = P(B).
```

Then

```text
sqrt(a)+sqrt(b)<=1.                                (OP)
```

Equivalently, with `ell=1-a-b`,

```text
ell >= 2*sqrt(a*b),
ell^2 >= 4*a*b.                                    (EOP)
```

The statement permits arbitrary countable atoms, nonstationary hazards,
failure of eventual stopping, and positive `Never` mass.  The finite clause
excludes an all-`Never` tie.  A strict comparison with another clock permits
that other clock to equal `Never`.

### Equality laws

If `a,b>0`, equality in `(OP)` holds exactly as follows, modulo an initial
string of dates at which all three hazards are zero and arbitrary null tails.

1. At the first active date, `T0` stops surely, while the hazards of `T1,T2`
   are `p,1-p` for some `0<p<1`.  Later conditional laws are arbitrary.
2. The first active hazards of `(T0,T1,T2)` are `(p,p,0)`.  Conditional on
   joint continuation, `T0=T2=s<T1` almost surely at one later finite date
   `s`.
3. The first active hazards are `(p,0,p)`.  Conditional on joint continuation,
   `T0=T1=s<T2` almost surely at one later finite date `s`.

In cases 2--3, the clock on the right of the final strict inequality may have
any law supported strictly after `s`, including `Never`.  Each case gives,
up to exchanging `a,b`,

```text
(a,b)=(p^2,(1-p)^2).
```

If `b=0`, equality means `a=1`, equivalently
`T0=T1=s<T2` almost surely for one deterministic finite `s`; the case `a=0`
is symmetric.

### Coalition and `K_4` consequences

For independent clocks on any finite player set, let `C,D` be incomparable
coalitions with nonempty intersection.  If `p_C,p_D` are the probabilities
that `C,D` are respectively the exact finite first-quitter coalition, then

```text
sqrt(p_C)+sqrt(p_D)<=1.                            (IC)
```

For four clocks, let `q_e` be the exact finite first-coalition probability of
the two-element set represented by edge `e` of `K_4`.  Combining `(IC)` for
adjacent edges with the previously known disjoint-pair law gives, for every
two distinct edges,

```text
sqrt(q_e)+sqrt(q_f)<=1,                            (K4)
```

equivalently `(1-q_e-q_f)^2>=4*q_e*q_f`.  All fifteen two-edge projections
are sharp.  These pairwise inequalities are not a characterization of the
six-coordinate law body.

## Conjecture-facing change

`MERIDIAN_BLINDSPOTS.md`, Section 4, isolated `(OP)` as the one unlocated
overlapping-clock law and left it explicitly conjectural after finite random
and coordinate-ascent tests.  The result above closes that arbitrary-clock
obligation and fills all twelve adjacent-edge projections of the `K_4`
pair-law body.  Together with the three existing complementary-edge
projections, every two-edge projection is now known sharply.

The direct conjecture-facing reduction is a negative semantic consumer.  If a
finite four-player reward table forces affine lower bounds on any two distinct
pair masses whose zero-error corner violates `(K4)`, Section "Adapter and
consumer" gives a fixed positive all-behavior terminal exploitability gap.
Thus a prospective `Fin 4` counterexample based on pair-event laws is reduced
to the explicit reward-table forcing problem there.  The theorem applies to
the complete clocks of an already executed arbitrary behavioral profile, so
it removes source ancestry and backward-to-forward chronology from that
negative consumer.

What remains open is essential: no reward table is proved here to force the
required affine lower bounds, and the complete six-coordinate star/cycle law
body is not characterized.

## Definitions and assumptions

For a marginal stopping law `mu_i`, define its inclusive survival at date `t`
by

```text
S_i(t)=P(T_i>=t),
```

where `Never>=t`.  When `S_i(t)>0`, its hazard is

```text
h_i(t)=P(T_i=t | T_i>=t).
```

When survival is zero, the later hazard may be set arbitrarily because that
tail has zero probability.  Conversely, arbitrary hazards in `[0,1]` specify
the finite atoms by survival times hazard; the limiting survival is the
`Never` mass.

For a quitting game, before absorption the public history is the unique
all-Continue history.  Each behavioral strategy therefore induces one such
complete stopping law.  Private behavioral randomizations make different
players' planned stopping times independent; no public correlating signal is
assumed.  The first finite minimum and its exact tie set determine the terminal
coalition.  A unilateral behavioral deviation replaces one player's complete
stopping law, not merely its current hazard.

For the terminal consumer, write `U_i(sigma)` for player `i`'s prescribed
terminal payoff, `B_i(sigma)` for the supremum over all complete unilateral
behavioral replacements, and

```text
E(sigma)=max_i (B_i(sigma)-U_i(sigma)).
```

The player set and reward table are finite, so all these quantities are
bounded.  The existing checked pure-time extremality theorem identifies each
behavioral supremum with the supremum over deterministic finite quit dates and
`Never`.

## Source correspondence

The exact Lean interfaces inspected were:

- `quittingBehaviorStoppingLaw`,
  `quittingHazardStoppingLaw_none_toReal`,
  `quittingHazardStoppingLaw_some_toReal`, and
  `stoppingLawSurvival_quittingBehaviorStoppingLaw` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingUniformEquilibriumPayoffConjecture` in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`; and
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.

The first two groups justify the stopping-law translation and unrestricted
deviation class.  The last declaration is the checked downstream negative
endpoint.  None states the new overlapping law.

The nearest conference sources inspected were the stopping-law portions of
`CODEX_CEDAR__STOPPING_TIME_COMPACT_GAME.md`,
`CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md`, and
`CODEX_CEDAR__TWO_PAIR_CLOCK_RIGIDITY_COMPILER.md`, plus Propositions 17--19
of `CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`.  Those sources prove the
disjoint equal-rank law.  Their local additive propagation fails for
overlapping pairs at hazards `(1/2,1/2,1/2)`.  The curved-region propagation
below is the new ingredient.  No literature theorem is invoked.

Both independent reviews reconstructed the endpoint algebra, arbitrary-clock
limit, coalition inclusions, boundary rigidity, and terminal consumer.  They
independently found the same narrow degeneracy omission in the first equality
proof.  The reviewed source separates that case, and both reviews record an
exact-hash delta `PASS` at the source hash printed above.

## Proof

### Curved-region propagation lemma

Let `x,q,r` lie in `[0,1]`, and let `alpha,beta>=0` satisfy

```text
sqrt(alpha)+sqrt(beta)<=1.
```

Set

```text
c = (1-x)(1-q)(1-r),
A = x*q*(1-r)+c*alpha,
B = x*r*(1-q)+c*beta.                              (P1)
```

Then `sqrt(A)+sqrt(B)<=1`.

Put `u=sqrt(alpha)` and `v=sqrt(beta)`.  The objective is increasing in `v`,
so it is enough to replace `v` by `1-u`.  For `0<=u<=1`, define

```text
F(u)=sqrt(x*q*(1-r)+c*u^2)
    +sqrt(x*r*(1-q)+c*(1-u)^2).                    (P2)
```

Each summand is convex: away from zero parameters, the second derivative of
`sqrt(d+c*u^2)` is `d*c/(d+c*u^2)^(3/2)>=0`; zero cases follow directly or by
continuity.  Hence

```text
F(u)<=max(F(0),F(1)).                              (P3)
```

Write `Q=1-q`, `R=1-r`, and `D=x*q+(1-x)*Q`.  Two-coordinate
Cauchy--Schwarz gives

```text
F(1)=sqrt(R*D)+sqrt(r*x*Q)
    <=sqrt((R+r)*(D+x*Q))
     =sqrt(x*q+Q)
     =sqrt(1-(1-x)*q)
    <=1.                                           (P4)
```

The symmetric calculation gives

```text
F(0)<=sqrt(1-(1-x)*r)<=1.                          (P5)
```

Equations `(P3)`--`(P5)` prove the lemma.

### Arbitrary-clock passage

First truncate `A,B` to common tie dates at most `N`.  Work backward from
future probabilities `(alpha,beta)=(0,0)` after date `N`.  At a live date,
write the current hazards of `(T0,T1,T2)` as `(x,q,r)`.  Independence gives
exactly recursion `(P1)`: the first term is the desired immediate tie and the
second is joint continuation followed by the corresponding conditional tail
event.  Conditional tail laws remain independent.  The propagation lemma
therefore proves `(OP)` for every common finite truncation.

The truncated events increase to the two finite-time events.  Continuity from
below and continuity of square root prove `(OP)` for arbitrary stopping laws,
including atoms and positive `Never` mass.  Squaring gives `(EOP)`.

### Equality necessity

The displayed same-date and staggered laws directly give
`(a,b)=(p^2,(1-p)^2)`, so the constant is sharp.

For necessity, apply the propagation lemma at the first date with a nonzero
hazard.  If `c>0`, equality first forces `u+v=1`.  If both immediate radicands
in `(P2)` vanish, then `F(u)=sqrt(c)` is constant on this boundary.  When
`x=0` but `q` or `r` is nonzero, `c=(1-q)(1-r)<1`; when `x>0`, positivity of
`c` and vanishing of both immediate terms force `q=r=0`, so `c=1-x<1`.
Both non-all-Continue degeneracies give strict loss.  The sole equality
degeneracy is `x=q=r=0`, an initial all-Continue row which may be deleted.

In every remaining `c>0` case, at least one immediate radicand is positive,
so the corresponding summand has strictly positive second derivative on
`(0,1)` and `F` is strictly convex.  Equality in `(P3)` forces `u=0` or
`u=1`.  If `u=1`, equality throughout `(P4)` forces `(1-x)q=0`; since
`c>0` gives `x<1`, one has `q=0`.  Equality in Cauchy--Schwarz then gives
`r=x`, and the future law has `(alpha,beta)=(1,0)`.  This is equality family
3.  The endpoint `u=0` symmetrically gives `r=0`, `q=x`, and family 2.

If `c=0` and both target probabilities are positive, necessarily `x=1`.
The one-date Cauchy--Schwarz equality condition is exactly `q+r=1`, giving
family 1.  Any earlier nonzero-hazard row gives a strict factor and is
impossible.

Finally, independent countable variables equal almost surely must have one
common deterministic atom.  Indeed equality almost surely gives them a common
mass vector `(m_s)`, while independence gives `sum_s m_s^2=1`, forcing one
`m_s=1`.  The event is finite, so this atom is a finite date.  This proves the
stated deterministic tail structure and the boundary cases.

### Incomparable coalitions and `K_4`

Choose `i` in `C intersect D`, `j` in `C\D`, and `k` in `D\C`.  The exact
`C` event is contained in `{Ti=Tj<Tk, finite}`; the exact `D` event is
contained in `{Ti=Tk<Tj, finite}`.  The overlapping theorem and monotonicity
of square root prove `(IC)`.  Incomparability is necessary: a single date with
`Ti` sure and `Tj` Bernoulli assigns masses `1-p,p` to nested coalitions
`{i}` and `{i,j}`, whose square roots sum to more than one.

Every pair of distinct `K_4` edges is adjacent or disjoint.  Applying `(IC)`
and the prior disjoint theorem proves `(K4)` for all fifteen pairs.

The pairwise conditions are not the full six-coordinate law.  If
`sum_e q_e=1`, the first finite coalition has size exactly two almost surely.
At the earliest date with positive absorption, a product Bernoulli row whose
only nonempty supported outcomes have size two must have exactly two hazards
equal to one and all others zero: any genuinely random coordinate creates a
supported singleton or a set of another size.  Absorption is then sure in one
deterministic pair.  Hence

```text
sum_e q_e=1 implies one q_e=1 and all other q_f=0.  (P6)
```

The vector `q_e=1/6` satisfies every pairwise condition and the simplex
condition but violates `(P6)`, proving noncharacterization.

## Boundary tests

The exact positive equality tests are:

- same date: `T0=t` surely, `P(T1=t)=p`, `P(T2=t)=1-p`, with failures later;
- staggered dates: hazards `(p,p,0)` followed on joint continuation by the
  sure event `T0=T2<T1`, or the symmetric orientation; and
- endpoints: `T0=T1<T2` almost surely, or its symmetric event.

They give `(a,b)=(p^2,(1-p)^2)` and cover positive `Never` mass by putting the
strictly later clock at `Never`.

The exact negative proof test for the naive induction is the live row
`x=q=r=1/2`: the two immediate event masses and joint-continuation mass are
all `1/8`, so their three square roots sum to `3/sqrt(8)>1`.  Repeating that
row stationarily gives `a=b=1/7`, which satisfies `(OP)`.  Thus the failed
local additive ledger does not refute the theorem; it demonstrates why the
future split retained in `(P2)` is necessary.

Before proving the theorem, the author exhaustively checked in exact integer
arithmetic:

- `94,196,375` triples of laws on `{0,1,2,Never}` with denominator `12`;
- `121,287,375` triples on `{0,1,2,3,Never}` with denominator `8`; and
- all `41^4=2,825,761` denominator-`40` local parameter quadruples on the
  future boundary.

For marginal denominator `D`, if `a=A/D^3`, `b=B/D^3`, `M=D^3`, the exact
test was `A+B<=M` and `(M-A-B)^2>=4AB`.  No violation occurred.  A positive
grid equality was

```text
p=(0,0,12,0), q=(0,0,1,11), r=(0,0,11,1),
(a,b)=(1/144,121/144).
```

These computations are falsification evidence only; the proof is the
arbitrary-clock argument above.

For fixed two marginals on a finite date set, `(a,b)` is linear in the third
marginal.  Its image is a polygon, and the increasing objective has a maximum
on a Pareto edge or vertex.  Thus that marginal may be chosen with support at
most two.  Replacing marginals successively at a global maximum yields a
maximizer with all three laws two-supported.  This explains the observed
boundary forms but is not needed for the proof.

## Adapter and consumer

### Actual behavioral-profile adapter

Given an arbitrary behavioral profile of a finite quitting game, apply
`quittingBehaviorStoppingLaw` to each player's live-spine strategy.  The unique
live public history and private randomization give independent complete clocks
in `Nat union {Never}`.  For an adjacent pair of `Fin 4` edges, project to the
three clocks consisting of their common endpoint and two exclusive endpoints;
drop the unused fourth-clock requirement.  Event inclusion and `(OP)` give
`(K4)`.  For a disjoint edge pair, use the prior disjoint-clock theorem.

This adapter starts from the actual executed profile.  It neither reconstructs
a profile from semantic data nor changes chronology.

### Quantitative terminal-gap consumer

Fix distinct edges `e,f`.  Suppose a concrete four-player reward table and a
strategic proof provide constants `alpha_e,alpha_f,L_e,L_f`, with nonnegative
slopes, such that every behavioral profile satisfies

```text
q_e(sigma)>=alpha_e-L_e*E(sigma),
q_f(sigma)>=alpha_f-L_f*E(sigma).                  (C1)
```

Define `[z]_+=max(z,0)` and

```text
Phi(delta)=sqrt([alpha_e-L_e*delta]_+)
          +sqrt([alpha_f-L_f*delta]_+),
Gamma=min {delta>=0 : Phi(delta)<=1}.              (C2)
```

When `sqrt(alpha_e)+sqrt(alpha_f)>1`, continuity makes `Gamma>0`; consistency
of `(C1)` makes the crossing set nonempty.  Nonnegativity, `(C1)`, and `(K4)`
give

```text
Phi(E(sigma))<=sqrt(q_e(sigma))+sqrt(q_f(sigma))<=1.
```

Therefore `E(sigma)>=Gamma` for every behavioral profile.  Choose a player
whose cap realizes the finite maximum over players and approximate its
behavioral supremum.  A pure finite quit time or `Never` gains at least
`Gamma/2`.  This produces `HasTerminalExploitabilityGap reward (Gamma/2)`.
The checked theorem
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
then refutes a uniform-equilibrium payoff for the concrete table.

If `(C1)` is available for all six edges, take the maximum of the fifteen
crossing values.  This is sharp given only each two forcing inequalities and
its pair-law projection: the crossing is exactly the first error level at
which the forced lower rectangle meets the square-root body.

The missing producer is precise: construct one finite reward table and two
pair labels for which deterministic pure-time deviation inequalities prove
`(C1)` with a forbidden zero-error corner.  The checked theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` removes any gap between
that pure-time calculation and unrestricted behavioral deviations.

## Lean handoff

The game-independent core should use a finite-horizon hazard theorem followed
by monotone convergence.  A suitable theorem shape is:

```text
theorem sqrt_prob_overlap_first_eq_add_sqrt_prob_overlap_second_le_one
    (T0 T1 T2 : PMF (Option Nat)) :
    sqrt (overlapFirstMass T0 T1 T2) +
      sqrt (overlapSecondMass T0 T1 T2) <= 1
```

Likely reusable definitions belong near
`MathUE/Probability/DiscreteHazardStopping.lean` or a new narrow `MathUE`
module, not in a conference or experiment lane.  The finite induction should
factor through a scalar lemma matching `(P1)`.  Prove convexity either by the
explicit second derivative on nondegenerate parameters plus zero cases, or by
a library convexity lemma.  Preserve the all-Continue constant-function case
explicitly if formalizing equality.

The quitting adapter should use
`quittingBehaviorStoppingLaw` and
`stoppingLawSurvival_quittingBehaviorStoppingLaw` from
`UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`.  The behavioral
cap bridge is
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` from
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`; the
negative endpoint is
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
from `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.

Useful exact tests are the one-date identity, the two staggered families, the
stationary half-hazard law `(a,b)=(1/7,1/7)`, and the degenerate current-row
cases `x=0` or `q=r=0`.  Run the narrow file check, the project trust scan, and
the relevant import-graph/document checks after choosing the production lane.
Do not import this packet or encode the desired inequality as a field.

## Scope and nonclaims

- This is ordinary reviewed mathematics, not a Lean-checked theorem.
- It does not prove or refute the finite-quitting uniform-equilibrium payoff
  conjecture.
- It does not produce a reward table satisfying `(C1)`.
- It does not characterize the full six-coordinate `K_4` law body; only every
  two-edge projection and the exact pair-only boundary are determined.
- It assumes independent private behavioral randomization.  Adding a public
  correlating signal changes the model and can invalidate the product-law
  premise.
- It does not assert compactness or continuity of the complete stopping-law
  payoff graph.
- It does not restrict a unilateral deviator to bounded memory or a finite
  horizon; the checked pure-time extremality theorem covers the full behavioral
  replacement class.
- The source-chronology bypass applies to this negative ex-post consumer.  It
  is not a positive producer and says nothing about constructing a chronological
  equilibrium profile from semantic source data.
