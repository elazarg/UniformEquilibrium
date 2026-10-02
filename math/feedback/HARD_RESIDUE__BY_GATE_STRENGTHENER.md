# Independent strengthening review of HARD_RESIDUE

## Verdict

**FAIL in its present form.**  The document contains three mathematically
different items.

1. The explicit unique-all-Continue local model is correct.  It is a sharp
   regression showing that a paid row and positive terminal atom do not by
   themselves contradict unique all-Continue root geometry.  Its global
   minimum is zero, so it is deliberately not an answer to the paired
   unique-cap question.
2. The renewable maximal-root calculation is essentially correct after the
   paid source is reconstructed with the opponents-only transport factor.  It
   yields an exact noncollapsing infinite-orbit alternative with sharp
   constants.  It still supplies neither a well-founded rank nor an admissible
   return, and therefore remains a strengthened version of an explicit
   nonanswer in `FIN4_PAID_RESET_REGENERATION_RANK.md`.
3. The proposed two-clock diffuse theorem is not proved from its stated
   hypotheses.  The displayed Lean target omits convergence of `value` to
   `boundary`; its “positive share infinitely far out” condition is undefined;
   and the block proof treats ordinary convergence to the boundary as an error
   small relative to a possibly vanishing remaining-absorption scale.  That
   inference is false.  A correct theorem can be obtained by conditioning the
   complete future terminal law on absorption and requiring positive
   **cross-singleton shares at active start times**.  This conditional theorem
   is given below, but no current hard-residual source is known to produce its
   hypotheses.

Thus the packet neither answers
`questions/FIN4_PAID_RESET_REGENERATION_RANK.md` nor
`questions/FIN4_DOUBLE_UNIQUE_CAP_CLOSURE.md`, and its followup does not yet
eliminate a source-produced Fin4 atlas arm.

## 1. Audit of the explicit local model

The four-player example is correct.

For players `i` in `{0,2,3}`, every coalition not containing `i` pays `2` and
every coalition containing `i` pays `0`.  Against any root of the other
players,

\[
C_i=2,
\qquad Q_i=0.
\]

Hence every exact root has players `0,2,3` Continue surely.  With those three
coordinates fixed at Continue, player `1` compares

\[
C_1=b_1=2
\quad\text{with}\quad
Q_1=r_1(\{1\})=1,
\]

so player `1` also Continues surely.  All Continue is the unique exact root at
the displayed cap.

In the actual profile, players `0` and `2` Quit together at date one.  Direct
inspection gives every cap coordinate equal to `2`.  Player `1` obtains `1`
by quitting at date zero and `2` by quitting at date one, so the claimed paid
pure-time comparison is exact and its receiving time attains the cap.  The
terminal law has unit mass at `{0,2}`.

The singleton profile `{1}` is an exact terminal Nash profile: player `1`
receives `1` rather than the zero all-Never payoff, while each outsider gets
`2` by staying out and `0` by joining.  Thus minimum debt is zero.

This proves the exact negative boundary:

\[
\boxed{
\text{cap + paid pure-time gap + positive finite atom}
\not\Longrightarrow
\text{a second exact cap root}.}
\]

It does not test the positive global minimum, terminal exploitability witness,
or the relation between the singleton source and its owner repair.  The
double-unique-cap question already lists a zero-minimum local regression as a
nonanswer, so this example should remain a boundary test rather than an export
claim.

## 2. Sharp renewable maximal-root theorem

### Correct one-step transport

Let `S` be an actual paid/reset source.  Write

\[
\Delta=D(\operatorname{Sem}(S)),
\qquad g>0
\]

for its total debt and stored paid lower bound.  Let `x` be the
maximum-absorption exact root at its cap, and set

\[
c=\Pr_x(\hbox{all players Continue}),
\qquad
\beta=\Pr_x(\hbox{all opponents of the paid observer Continue}).
\]

On the positive-absorption branch, positive global minimum gives `c>0`, and
positive absorption gives `c<1`.  Exact cap-prefix semantics gives

\[
\Delta'=c\Delta.
\tag{3}
\]

For the two delayed pure times stored by the paid source, the exact transport
identity is

\[
G'=\beta G,
\tag{4}
\]

where `G` and `G'` are their actual payoff differences before and after the
prefix.  Since `g <= G`, the descendant may be reconstructed with the stored
lower bound

\[
g'=\beta g.
\tag{5}

\]

This is stronger than the current constructor, which deliberately stores the
smaller lower bound `c*g`.  Because

\[
c\le\beta,

\]

the strengthened construction is valid, but it is not obtained by merely
adding a field to every existing inhabitant of
`MaximalOneStepPaidResetRegeneration`.  The constructor must be changed or a
new quantitative wrapper must reconstruct the descendant paid source using
the threshold `beta*g`.

Equation (4) is already checked as
`quittingPureTimeDeviationPayoff_sub_rootThenContinuation_shift_one` in
`PaidCapLiftedSummablePort.lean`.  Equation (3) follows from the checked exact
cap-prefix debt scaling used in `PaidCapMaximalOneStepRegeneration.lean`.

### Infinite-orbit alternative and exact constants

Iterate the canonical construction until unique all-Continue occurs.  If it
never occurs, obtain actual sources `S_n` and roots `x_n`.  Put

\[
\Delta_n=D(\operatorname{Sem}(S_n)),
\quad c_n=\Pr_{x_n}(\mathbf C),
\quad \beta_n=\Pr_{x_n}(\mathbf C_{-o}),
\quad a_n=1-c_n.
\]

Choose the descendant lower bound by (5).  Then for every `N`,

\[
\Delta_N=\Delta_0\prod_{n<N}c_n,
\qquad
g_N=g_0\prod_{n<N}\beta_n.
\tag{6}

\]

Let `D_*>0` be the retained global minimum and define

\[
\kappa=\frac{D_*}{\Delta_0}\in(0,1].
\]

Every `S_N` is an actual profile and retains the same minimum, so

\[
\prod_{n<N}c_n
=\frac{\Delta_N}{\Delta_0}
\ge\kappa.
\tag{7}

\]

Since `beta_n >= c_n`,

\[
\boxed{g_N\ge\kappa g_0>0.}
\tag{8}

\]

If a marked suffix event initially has mass `mu`, its literally inherited
component at depth `N` has mass

\[
\mu_N^{\rm inherited}
=\mu\prod_{n<N}c_n
\ge\kappa\mu.
\tag{9}

\]

The full terminal-law coordinate can be larger because a new prefix root may
also absorb in the same coalition; equality in (9) refers to the shifted
inherited event.

Finally, `0<c_n<=1` and `1-c_n<=-log(c_n)` give the sharp uniform budget

\[
\boxed{
\sum_{n=0}^{\infty}a_n
\le \log\frac{\Delta_0}{D_*}.}
\tag{10}

\]

In particular `a_n -> 0`.  The total actual debt drop also telescopes to
`Delta_0-lim Delta_n`, but that is still a real-valued, not well-founded,
quantity.

The resulting honest alternative is:

\[
\boxed{
\begin{array}{l}
\text{a finite iterate has all-Continue as its unique exact cap root},\\
\text{or there is an infinite literal outward-prefix orbit with (8)--(10),}\\
\text{a uniformly nonvanishing inherited atom, zero reset debt, positive}\\
\text{reset incidence, and a fresh fixed-law reset dispatch at every step.}
\end{array}}
\tag{11}

\]

This is a genuine quantitative strengthening of the one-step theorem.

### Boundary tests for (11)

* If `Delta_0=D_*`, then `kappa=1`; (7) forces every `c_n=1`.  Thus no
  positive-absorption regeneration can start directly on the minimum fibre.
* If `D_*=0`, the conclusion is false in the needed form.  For example the
  abstract scaling `c_n=1/2` permits debt, paid lower bound, and inherited mass
  all to collapse to zero.  Positive global minimum is exactly what supplies
  the noncollapse.
* If the descendant is allowed to store an arbitrarily smaller positive gain
  than the transported lower bound, (8) no longer follows.  The quantitative
  constructor, not mere existence of a paid row, is essential.
* Summability does not imply finite termination.  For example
  `c_n=1-2^{-n-2}` has positive infinite product and infinitely many strictly
  absorbing roots.

### Why (11) is not a consumer

The causal order is outward:

\[
S_{n+1}=x_n::S_n.
\]

There is no first root of the formal left-infinite word.  At fixed calendar
dates of a compactified sequence, later and later roots have absorption
tending to zero, while the paid row and marked suffix event recede to
infinity.  Their law mass can remain bounded below through (7) and still be
lost by the literal marginal behavioral limit.  Equations (8)--(10) therefore
do not give an executable forward chronology, an admissible return, or a
fixed terminal target.

This is precisely why `FIN4_PAID_RESET_REGENERATION_RANK.md` excludes
iteration indexed only by decreasing real debt.  The stronger passport makes
the remaining machine more rigid but does not satisfy any accepted output of
that question.

## 3. The diffuse two-clock proof as written has a gap

The proposed Lean statement includes a free `boundary` vector and only the
equalities

\[
boundary(p)=r_p(\{p\}),
\qquad
boundary(q)=r_q(\{q\}).

\]

It does not assume

\[
value(t)\longrightarrow boundary.
\tag{12}

\]

Without (12), `boundary` is unrelated to the exact Bellman path.  The
phantom-boundary identity
`quittingTailConditionedValue_eq_terminalValue_div`, which is needed to read
the conditioned value as a conditional terminal payoff, explicitly requires
this convergence.

Even adding (12) does not justify the displayed block proof.  If `A_s` is the
remaining eventual-absorption probability, a block absorbing a fixed fraction
of the remaining mass can have total mass of order `A_s -> 0`.  Ordinary
convergence

\[
value(s)-boundary\to0

\]

does not imply an endpoint error `o(A_s)`.  The proof divides by precisely
that vanishing block mass.  Boundary tightness alone therefore does not make
the left side of the block identity `o(A_n+B_n)`.

There are two further specification gaps.

* “Both players carry a positive conditioned singleton share infinitely far
  out” must say at which starting dates the shares are measured.  To identify
  `M_{p,q}`, the positive `q`-share must occur at dates where `p` is active;
  the symmetric conclusion needs positive `p`-share at dates where `q` is
  active.
* The prose defines diffuseness by the raw root absorption
  `1-c_t -> 0`, while the proposed Lean theorem assumes vanishing conditioned
  mesh.  The latter is stronger and does imply raw diffuseness because the
  remaining absorption denominator is at most one, but the two quantities
  must not be silently identified.

## 4. Corrected two-clock cross-share theorem

The block construction is unnecessary.  The complete future terminal law
conditioned on absorption gives a sharper proof and an explicit quantitative
bound.

Assume:

1. `roots,value,boundary` satisfy the exact Bellman recursion and exact
   endpoint-Nash conditions;
2. `value(t) -> boundary` coordinatewise;
3. every suffix has positive eventual absorption;
4. the conditioned absorption mesh

   \[
   w_t=\frac{1-c_t}{A_t}
   \]

   tends to zero, where `A_t` is remaining eventual absorption;
5. after some date only distinct players `p,q` may Quit;
6. the tight boundary equalities hold for `p,q`;
7. there are times `s_n -> infinity` and a number `eta_q>0` such that `p` is
   active at `s_n` and, conditional on eventual absorption from `s_n`, the
   terminal singleton `{q}` has probability at least `eta_q`;
8. symmetrically, there are `t_n -> infinity` and `eta_p>0` such that `q` is
   active at `t_n` and the conditional future singleton `{p}` has probability
   at least `eta_p`.

Then

\[
\boxed{
normalizedSoloMatrix(r)_{p,q}=0,
\qquad
normalizedSoloMatrix(r)_{q,p}=0.}
\tag{13}

\]

### Quantitative core

Let `Pi_s(S)` be the terminal coalition law of the root tail starting at `s`,
conditioned on eventual absorption.  Let

\[
\widehat v_s
=quittingTailConditionedValue(roots,value,boundary,s).

\]

At a sufficiently late `p`-active time `s`, the checked active-support gate
gives, for a reward bound `M`,

\[
|\widehat v_s(p)-r_p(\{p\})|\le2M w_s.
\tag{14}

\]

Eventual pair support and the phantom-boundary identity give

\[
\widehat v_s(p)-r_p(\{p\})
=
\Pi_s(\{q\})
  \bigl(r_p(\{q\})-r_p(\{p\})\bigr)
+
\Pi_s(\{p,q\})
  \bigl(r_p(\{p,q\})-r_p(\{p\})\bigr).
\tag{15}

\]

Write `alpha_u=1-c_u` for raw one-stage absorption.  On a two-clock root with
quit probabilities `a_u,b_u`,

\[
\frac{a_ub_u}{a_u+b_u-a_ub_u}
\le \alpha_u
\]

whenever the denominator is positive.  Averaging over the future absorption
dates yields

\[
\Pi_s(\{p,q\})
\le \sup_{u\ge s}\alpha_u
\le \sup_{u\ge s}w_u.
\tag{16}

\]

Combining (14)--(16), if `Pi_s({q}) >= eta_q`, gives the explicit estimate

\[
\boxed{
\eta_q
\left|normalizedSoloMatrix(r)_{p,q}\right|
\le
4M\sup_{u\ge s}w_u.}
\tag{17}

\]

The tail supremum tends to zero because `w_t -> 0`, so the first equality in
(13) follows along `s_n`.  The symmetric argument along `t_n` proves the
second.

This proof handles arbitrarily fragmented and alternating singleton mass.  It
does not require solo windows or fixed-length blocks.  Its essential input is
the alignment of cross-singleton share with an active start of the spectator
whose row is being identified.

### Relation to a card-two hard principal

For a two-element nonprojective principal in the checked Fin4 hard residual,
both off-diagonal normalized solo entries are strictly negative.  This is the
content of the card-two analysis in
`FullSupportHardPrincipalDispatch.lean`.  Therefore such a pair cannot support
an exact diffuse tail satisfying all eight hypotheses above.

This is a valid conditional exclusion.  It is not yet an actual-data adapter:
the hard-residual packet does not currently produce one exact infinite
Nash--Bellman tail with eventual support equal to the chosen principal,
boundary convergence, and the two aligned cross-share sequences.

## 5. Boundary tests for the corrected diffuse theorem

### Cross-share is essential

If only `p` ever absorbs, the tail payoff never evaluates the row
`r_p({q})`.  That reward coordinate may be changed arbitrarily without
altering the chronology.  No conclusion about
`normalizedSoloMatrix(r)_{p,q}` is possible.  A positive `q` singleton share
at `p`-active starts is therefore indispensable.

### Pair support is essential

With a third persistent singleton, equation (15) contains another first-order
term.  The Bellman account then gives a linear relation among several solo
matrix entries, not the vanishing of either displayed entry separately.

### Diffuseness is essential

If collision has a nonvanishing conditional share, the pair reward term in
(15) can cancel a nonzero solo entry.  One cannot discard it.

### Conditioned concentration is not unconditional charge

Failure of `w_t -> 0` does not by itself produce a fixed unconditional stage
mass.  For example, raw absorption of order `2^{-t}` can have remaining
absorption of the same order, leaving `w_t` bounded away from zero while every
unconditional late-stage mass tends to zero.  An additional source reach
floor is required before invoking an unconditional positive-charge consumer.

### Vanishing share is not automatically debt-support descent

A player's conditional terminal singleton share is a chronological occupation
quantity.  Positive-debt support is defined by unrestricted caps minus
prescribed payoff.  No general implication sends a vanishing occupation share
to disappearance from debt support.  The asserted “second branch is a support
drop” needs a separate theorem and cannot be used as a consumer here.

### Failure of tightness is not automatically a refusal certificate

A nonzero boundary displacement supplies neither its profitable sign nor a
divergent survival-weighted selected clock.  Both are needed to apply the
global refusal ledger.  The fourth branch in the document likewise remains a
producer obligation.

## 6. Lean handoff

### Quantitative maximal orbit

Do not add `descendant_gain_eq = beta * source.gain` to the existing structure
without changing its constructor: current code chooses `c * source.gain`.
Use a new wrapper or constructor, for example:

```text
QuantitativeMaximalOneStepPaidResetRegeneration
  extends MaximalOneStepPaidResetRegeneration
  descendant_gain_eq :
    descendant.gain =
      quittingRootOpponentContinueMass maximalRoot source.observer * source.gain
  descendant_debt_eq : descendant.initialDebt =
    quittingStationaryContinueMass maximalRoot * source.initialDebt
```

Then define an orbit retaining the canonical root, shifted pure-time witnesses,
reset labels, and optionally one marked inherited event.  The main declarations
should be:

```text
quantitativeMaximalOneStepPaidResetRegeneration_or_uniqueAllContinue

nonempty_quantitativeMaximalPaidResetOrbit_or_eventual_uniqueAllContinue

QuantitativeMaximalPaidResetOrbit.gain_ge_minimumRatio_mul

QuantitativeMaximalPaidResetOrbit.inheritedMass_ge_minimumRatio_mul

QuantitativeMaximalPaidResetOrbit.summable_absorption
```

The last theorem should expose the sharp bound
`sum absorption <= log (initialDebt / minimumDebt)`.

### Corrected two-clock theorem

Reuse:

* `quittingRootSequenceSingletonMass` and
  `quittingRootSequenceCollisionMass` from
  `NormalizedFiniteWindowOccupation.lean`;
* `quittingTailConditionedValue_eq_terminalValue_div` and the active-support
  gate from `PhantomBoundaryConditioning.lean`; and
* `normalizedSoloMatrix_eq_soloReward_sub` from
  `PreemptionGateDictionary.lean`.

The new interface should define conditional future singleton and collision
shares by dividing the corresponding tail masses by
`quittingTailEventualAbsorption roots start`.  Suggested theorem shapes are:

```text
twoClock_conditionedCollisionShare_le_tailSup_mesh

conditionedCrossSingletonShare_mul_abs_normalizedSoloMatrix_le

normalizedSoloMatrix_pair_eq_zero_of_twoClockDiffuse_crossShares
```

The last statement must include `value -> boundary` and two separately
quantified active-start/cross-share sequences.  A phrase such as “positive
share infinitely far out” is not a formal hypothesis.

An eventual-support adapter should first shift the root sequence past its
cutoff so that only `{p,q}` occur; this avoids repeatedly carrying finite
prefix exceptions.

## 7. Adapter and consumer audit

### Available adapters

* The maximal one-step theorem supplies every datum needed to construct the
  quantitative successor except the stronger stored gain choice, which is a
  local reconstruction.
* A card-two nonprojective hard principal supplies two strictly negative
  normalized solo entries.

### Missing adapters

* No current theorem turns an arbitrary paid/reset source into a forward
  realization of the left-infinite maximal orbit.
* No current hard-residual theorem produces the exact two-clock tail required
  by the corrected diffuse theorem.
* No theorem turns vanishing conditioned singleton share into debt-support
  descent, non-diffuse conditioned mesh into unconditional charge, or failed
  boundary tightness into a refusal chronology.

### Missing consumers

* The infinite noncollapsing maximal orbit has no positive admissible-return
  compiler and no well-founded rank.
* The eventual unique-all-Continue node remains exactly the open paired-cap
  obstruction.
* The corrected two-clock theorem excludes only a supplied tail architecture;
  it does not produce terminal approximants or a uniform payoff.

## 8. Export gate

### PASS conditions

The maximal-orbit part can pass the named paid/reset question only after its
infinite branch is compiled into a positive admissible near-return, a genuine
finite rank, terminal approximants, or a contradiction.  Quantitative
noncollapse alone does not meet that question's renewal requirement.

The diffuse part can pass as a conjecture-facing reduction only after:

1. the theorem is restated with boundary convergence and aligned cross-share
   sequences and proved using conditioned future laws;
2. an actual source adapter derives those hypotheses from a named hard
   residual branch; and
3. every complementary branch is either consumed or retained as an explicitly
   smaller named obligation with a proved transition.

The local regression could pass only as a response to a question explicitly
accepting a zero-minimum falsifier of the local implication.  The current
paired-cap question expressly does not.

### Current FAIL conditions

* The first two maximal-reset conclusions end in the existing unconsumed
  infinite-orbit or unique-cap nodes.
* The proposed diffuse theorem omits a necessary boundary-convergence
  hypothesis and uses an invalid relative-error step.
* Its singleton-share hypothesis is not quantified at the active start times
  needed by the proof.
* The claimed support-drop, positive-charge, and refusal consumers are not
  derived.
* No arbitrary-game or hard-residual adapter produces the corrected
  two-clock tail.

The correct disposition is: retain the explicit local model as a no-go,
formalize the quantitative maximal orbit if useful, and rewrite the diffuse
claim around conditioned cross-shares before considering any export.
