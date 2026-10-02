# Finite observable closure for residual transport

Author: CODEX_LARCH_ROUND2_OBSERVATION. Internal code-pattern investigation,
2026-09-07. Ordinary-mathematical sketch; no Lean changes or compilation.
The core criterion and adapter passed
[independent review](../feedback/CODEX_LARCH_ROUND2_OBSERVATION__FINITE_OBSERVABLE_CLOSURE_FOR_RESIDUAL_TRANSPORT__BY_CODEX_LARCH.md).

## Verdict: a reusable linear-observability theory

A bounded candidate survives: **the smallest operator-invariant space of
observables and its induced quotient of state distributions**. It has a
finite construction and an exact criterion for when adaptive controls leave
its evolution unchanged. Full-state invisibility, preservation of selected
residual means, and failure of a nonclosed witness list become distinct
specializations of one mathematical object.

For a generated observable space W, define μ∼ν when μ·w=ν·w for every
w∈W. Invariance makes baseline evolution well-defined on these equivalence
classes. An action induces the same evolution precisely when its transition
row difference annihilates W. This is a linear quotient of distributions,
not necessarily a Markov quotient of the physical state set: no event-law
preservation, public observation, or strategic information is added.

This is narrower than a universal strategic-state theory. Its input is a
finite coefficient presentation of the calendar's transition kernels and
residuals. Its output is a finite basis of observables and finitely many
row-annihilation checks, followed by an all-calendar transport theorem.
No claim is made that arbitrary analytic Fink germs supply low-dimensional
observable spaces or the required coefficient presentation.

The independent theory content is a consolidation of standard controlled
observability and minimal linear realization. The homogeneous minimality
theorem and finite closure procedure make the object canonical; they are
more informative than a predicate requiring all desired tests to agree.
The elementary argument below is self-contained. No foundational novelty
claim or new UE existence class is made. The game-specific residual account
below is an illustration of reuse, not the purpose of developing a UE proof.

## 1. Pattern, provenance, and existing overlap

The exact source boundary is `PlayerOwnedCalendarResidualAccount`
(`UniformEquilibrium/VanishingDiscount/Analytic/PlayerOwned/CommonPotentialPayoffBoundary.lean`).
It requires a sublinear account for the prescribed residual evaluated under
the **deviating** history law. An on-path residual estimate is insufficient.

`finiteAveragePayoff_scheduledPlayerOwned_le_of_invisible`
(`UniformEquilibrium/VanishingDiscount/Analytic/PlayerOwned/InvisiblePlayerOwnedDeviationBoundary.lean`)
already closes the stronger special case where every allowed deviation has
the exact prescribed full-state transition kernel. There is no missing
all-history argument in that file to rediscover.

At the newer quitting boundary,
`exists_terminalSemantic_commonWitness_noncompositionality`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCommonWitnessNoncompositionality.lean`)
exhibits equal current semantic pairs and equal witnesses whose values differ
after the same continuation splice. In its owner's Continue branch the two
transfer functions are

    c ↦ c,              c ↦ 1−s+sc.

They agree at c=1 and disagree at c=2. Retaining a current test does not
retain its future propagated tests. This suggests closure of a small
observable family under propagation, rather than retaining one witness or
retaining every possible response graph.

The two older files entered this repository in the August 14 migration
commit `61e9373`; this is not their original mathematical invention date.
The quitting regression entered on August 23 in `74832bc`. A bounded import
closure check found neither side reaches the other. Their closest common
project dependencies were basic probability modules, at distances 6+4 for
the account file and 5+4 for the invisibility file. Thus this is a real
cross-neighborhood comparison, though history alone does not prove novelty.

Nearby material already covers:

- full-state kernel invisibility, as above;
- supplied strong lumpability in `IsStronglyLumpable`
  (`MathUE/Probability/QuotientShadowLift.lean`);
- moving endpoint superharmonicity as a target-transport producer in
  `IsMovingPlayerOwnedEndpointSuperharmonic`
  (`UniformEquilibrium/VanishingDiscount/Analytic/Accounting/FiniteBiasPlayerOwnedTargetTransportBoundary.lean`);
- endpoint harmonic corrections and their moving-baseline residual, in
  `HarmonicInvisibleQuotientCorrection.movingBaselineResidualAt`
  (`UniformEquilibrium/VanishingDiscount/Analytic/Accounting/ProcessedHarmonicQuotientAccount.lean`);
- the fact that invariance of an endpoint-harmonic subspace is vacuous,
  recorded in `setOf_algebraInvariant_le_eq_setOf_le`
  (`UniformEquilibrium/VanishingDiscount/Bellman/EndpointHarmonicTriviality.lean`).

The last point matters: the proposal below is not a new filtration of a
fixed harmonic space. Its vectors can be nonharmonic residuals, and its
closure includes every relevant positive-parameter baseline operator.

The previous [finite dated-law cap-fiber sketch](CODEX_LARCH_DUAL__COMPETING_RISKS_CAP_FIBERS.md)
reconstructs latent quitting hazards from a supplied finite law; it supplies
neither this residual account nor an invariant observable space for general
stochastic-game calendars. Searches for Krylov closure, observable subspaces,
lumpability, and residual transport found the overlaps above but no exact
finite criterion stated below. This remains a bounded absence claim.

## 2. Finite controlled-observable transport lemma

Let S be a finite state set with N elements. For each time t let P_t be a
prescribed stochastic matrix. For a fixed deviator i, let Q_{i,t,s,a} be
the next-state distribution when the current state is s and i chooses pure
action a against the prescribed opponents. The deviator may mix and choose
actions using the entire public history. Let f_{i,t}:S→ℝ be the prescribed
residual observable at time t.

Suppose a linear subspace W_i⊆ℝ^S satisfies

    1∈W_i,       f_{i,t}∈W_i,       P_t W_i⊆W_i,
    (Q_{i,t,s,a}−P_t(s,·))·w = 0
                  for every t,s,a and w∈W_i.             (1)

Then, from every initial state, at every date t and for every adaptive
behavioral deviation,

    E_deviation f_{i,t}(X_t) = E_prescribed f_{i,t}(X_t).   (2)

Consequently the two cumulative residual expectations are exactly equal at
every finite horizon. No equality of full state or history laws is required.

Proof: inductively establish equality of expectations of every w∈W_i at
time t. Conditional on any deviating history ending at s, the next expected
value of w is P_t w(s), because each pure action agrees on w and mixing
preserves that equality. Since P_t w∈W_i, the induction hypothesis applies.
The initial laws agree; take w=f_{i,t} after the induction. This explicitly
keeps calendar dependence in both P_t and f_{i,t}.

A time-dependent version needs spaces W_{i,t} with
f_{i,t}∈W_{i,t}, P_tW_{i,t+1}⊆W_{i,t}, and row agreement on W_{i,t+1}.
The common-space form is preferable when it admits the finite construction
below; a backward space defined using all future tests would merely restate
the desired preservation unless its finite structure is independently given.

## 3. A finite source, not infinitely many unprocessed tests

Here is a concrete input class. Suppose a scalar parameter θ ranges over an
interval where all displayed probabilities are valid. Supply polynomial
coefficient presentations

    P(θ) = sum_{k=0}^d θ^k A_k,
    f_i(θ) = sum_{k=0}^e θ^k v_{i,k},
    Q_{i,θ,s,a}−P(θ)(s,·) = sum_{k=0}^h θ^k d_{i,s,a,k}.

The A_k are N×N matrices, the v_{i,k} are state functions, and the
d_{i,s,a,k} are rows. The coefficient matrices themselves need not be
stochastic. Any prescribed sequence θ_t in the valid interval is allowed,
including the nonperiodic epoch sequence used by the source interface.

Starting with W_i^0=span{1,v_{i,0},…,v_{i,e}}, repeatedly set

    W_i^(m+1) = W_i^m + sum_k A_k W_i^m.

Once the dimension stops increasing, the space is stable; this happens
after at most N strict rank increases. Compute one basis of the resulting
W_i and check the finitely many scalar equalities

    d_{i,s,a,k}·w_j = 0                                (3)

for all pure actions, source states, coefficient rows, and basis vectors.
Then (1) holds for **every** θ_t sequence. Thus finite linear algebra
produces the whole-calendar residual transport property.

Finite-phase families work by using their finitely many matrices and
residuals in the same construction. Rational families work after multiplying
by supplied common denominators that are nonzero on the valid interval;
the resulting numerator-coefficient closure is sufficient, possibly larger
than a minimal space. Arbitrary analytic families are not automatically
polynomial or rational, so this is a restricted actual-data source.

For a single time-homogeneous matrix P and one observable f, the minimal
space is span{1,f,Pf,…,P^(N−1)f}. Its row-annihilation condition is both
necessary and sufficient for preserving all future f expectations under
every control from every initial state. Necessity follows by making one
pure deviation first and then following the baseline: every difference
row must annihilate P^k f. Finite-dimensional stabilization removes the
infinite list. The multi-parameter coefficient construction above is a
robust sufficient condition, not a claimed minimal test for one fixed
calendar.

## 4. Exact positive and negative tests

**Weaker than whole-state invisibility and partition lumpability.** Let
S={−1,0,1}, f(s)=s, and let every prescribed row P put probability 1/2
on −1 and 1. An alternative action sends the state to 0 surely. Both row
types have expectation zero against f, so W=span{1,f} is invariant and
every adaptive mixture satisfies (1). Their state distributions can be
disjoint. Since f takes three distinct values, a deterministic state
quotient retaining f must distinguish all three states; equality of the
quotient transition laws would therefore demand the full kernel equality
that fails here. Linear observable transport is a weaker condition.

For an actual stochastic-game realization, give one player these transition
actions, add a dummy player, and use stage payoff f(s) independent of the
action. Baseline and every deviation have expected payoff zero after the
initial date. The normalized discounted value is (1−β)f(s), and every
action satisfies its Bellman equality. With B=0 and target 0, the prescribed
residual is exactly f. Its cumulative expectation is f(initial), bounded
by one, even though the full state laws differ. This is an exact finite
input test of the residual-account adapter. The game is elementary and
already solvable by other methods; it is not a new UE class.

**One-step test agreement is insufficient.** Let S={a,b,c}, f=(0,0,1),
and let P send a to a, b to c, and c to c. At a allow a deviation that
sends the state to b. The deviation row agrees with P(a,·) on f, but not
on Pf=(0,1,1). After that one deviation followed by prescribed play, the
two-date residual is 1 instead of 0. This is the finite controlled-chain
version of the continuation-splice obstruction: a presently invisible
change becomes visible after one propagation.

**Degenerate rank is not automatically present.** If the generated W_i
equals ℝ^S, condition (3) reduces to full-state kernel invisibility. The
theory is useful only when its computed observable rank is smaller, or when
the required row differences happen to annihilate it. No rank deficiency
is inferred from finite state space, equilibrium, or analyticity.

## 5. Adapter into the named partial result

The source residual is literally

    f_{i,t}(s) = g_{i,t}(s) + P_t B_i(s) − B_i(s) − u_i,

where g is prescribed stage reward. It depends on calendar time and current
state, as defined by `playerOwnedCalendarPrescribedBellmanResidual`
(`UniformEquilibrium/VanishingDiscount/Analytic/PlayerOwned/CalendarBellmanResidual.lean`).

Suppose the prescribed calendar already has an on-path payoff upper account

    sum_{t<T} E_prescribed g_{i,t}(X_t) − T u_i ≤ a_i(T),

with a_i(T)/T→0. Telescoping B under prescribed play bounds the cumulative
prescribed residual by a_i(T)+2||B_i||∞. Under (1), equation (2) gives
exactly the same bound for every behavioral deviation. Hence one may set

    residual.budget_i(T) = a_i(T)+2||B_i||∞

in `PlayerOwnedCalendarResidualAccount` or its entry-specific version.
The existing common-potential theorem then gives its simultaneous eventual
deviation caps. Two-sided on-path delivery remains separately required for
UE, as it was in the original source boundary.

This is a finite observable condition sufficient to bridge an existing
on-path estimate to the missing deviated-law account. It does not infer
on-path delivery, the charged-occupation potential, or (3) from arbitrary
game data. It is also not a method for inferring complete response caps
from quitting terminal-law observations: those lose precisely the future
propagation information highlighted by the new regression.

## 6. Theory-discovery assessment

The useful development would be a small generic linear-observability core:
generated invariant output spaces, quotient distributions, finite closure
and minimality, and adaptive row-agreement transport. Its three code-facing
instances are full-state invisibility, calendar residual transport, and the
diagnosis of a witness list that is not closed under future propagation.
None requires a new equilibrium producer to justify the mathematical
consolidation.

The expected gain is one precise shared object and smaller assumptions in
appropriate existing proofs. The main risk is over-abstraction: a full-rank
generated space gives no reduction, while endpoint-harmonic constants can
make invariance vacuous. These should be exposed by the rank of the finite
construction, rather than treated as evidence for a stronger theory. No
further UE proof-search or source-production task is proposed here.

No shared index, export, or Lean source was edited. Independent review checked
the exact finite-source criterion and adapter with no unresolved objection.
The [positive realization extension](CODEX_LARCH_ROUND2_OBSERVATION__POSITIVE_REALIZATIONS_AND_OBSERVABLE_ALGEBRAS.md)
separates its linear quotient from stochastic covers, deterministic event
quotients, and independent strategy factorization.
