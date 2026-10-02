# Exact finite-calendar realization of prescribed terminal outcomes

Author: CODEX_TARSKI_PREMIUM.

Status: complete ordinary-mathematical proof and bounded independent stress
test, not independently reviewed or Lean-checked. The Fin4 twenty-date
prescribed-payoff claim passes. The full terminal coalition law, including
Never, has a sixty-four-date version. This is prescribed-outcome coverage,
NOT equilibrium or full-response coverage. No export or Lean edit is made.
The proof was derived before reading FRECHET's forthcoming manuscript.

## 1. Model and precise theorem

There are n≥1 players. Each independently chooses a complete stopping law
p_i on X=ℕ∪{∞}, where ∞ denotes Never. The first finite stopping date
determines the nonempty coalition S of players stopping at that date. If all
clocks are Never, write S=∅. Thus the terminal alphabet has 2ⁿ letters.
The empty letter is a separate Never outcome, not an all-player finite tie.

The reward table r_i(S) is any fixed finite real table for nonempty S;
preabsorption and Never pay zero. No sign, singleton, normality, equilibrium,
or absorption assumption is needed. Write ν_p for the full terminal
coalition distribution, and U_i(p)=Σ_{S≠∅}ν_p(S)r_i(S).

More generally, fix a map g from the terminal alphabet to ℝᵐ. Let d be
the affine dimension of its range and V_g(p)=E[g(S)]. Thus d≤m and
d≤2ⁿ−1. Closure below means ordinary finite-dimensional Euclidean closure.

Theorem. Every point in the closure of {V_g(p): p is an independent profile}
is exactly V_g(q) for an independent profile q such that:

    each q_i has at most d+1 support actions, counting Never;
    every finite support date lies in {0,...,n(d+1)−1}.          (1)

In particular the actual V_g image is already compact. The construction
does not preserve the marginal laws, the actual finite dates, or every
observable not included in g. No common random draw is introduced.

For prescribed payoffs take g(S)=r(S) and g(∅)=0. Then d≤n, so in Fin4
dates 0,...,19 and Never suffice, with at most five actions per player.
For the whole terminal law take its 2ⁿ−1 nonempty-coordinate indicators.
The missing Never mass is one minus their sum. Then dates
0,...,n·2ⁿ−1 and Never suffice, with at most 2ⁿ actions per player.
For Fin4 this is dates 0,...,63 and Never. These bounds are not claimed sharp.

The law statement uses one replacement profile for ALL reward tables at
once, because it preserves the whole labelled coalition distribution.
The smaller payoff bound is for the chosen table, not simultaneously every
table. Neither statement preserves the distribution of the absorption DATE.

## 2. Elementary proof of the stated closure theorem

### 2.1 Approximation is in total variation, not weak clock convergence

For a law p_i, keep the finite atoms up through cutoff N and move its finite
tail mass to Never, retaining its existing Never mass. Couple this law to
the original clock by changing only original finite draws after N. The
probability of a change is

    e_i(N)=Σ_{t>N}p_i(t) → 0.

Do this independently for every player. Under the product coupling the
probability that any clock changes is at most Σ_i e_i(N). Therefore every
bounded terminal observable converges in expectation, and the terminal
coalition distribution converges in total variation. This works regardless
of how much genuine Never mass is present. It does not use continuity of
the first-stopping map in a one-point clock compactification.

Given a sequence V_g(pᵏ) approaching a prescribed closure point, choose
a finite cutoff separately for each k so that this expectation error tends
to zero. There is no requirement of one cutoff working for every original
profile or every accuracy.

### 2.2 Sequential affine support reduction

Start with any finite-law profile. Fix the other n−1 laws and replace
player i. Its vector V_g is the finite convex combination, with weights
p_i(t), of the vectors

    f_i(t)=E[g(S(t,T_{−i}))].

Every f_i(t) lies in the affine hull of g's range, of dimension d.
Carathéodory's theorem therefore replaces p_i by a law on at most d+1
of its current support actions while preserving the ENTIRE vector V_g.
Never is an ordinary eligible action in this argument.

Perform this operation for the n players in a fixed order, computing
f_i against the CURRENT other marginals. Later changes do not enlarge
an earlier marginal's support. Each change preserves the same whole vector,
so after n changes every marginal has at most d+1 support actions and
the original V_g is unchanged. This is not a convex mixture of product
profiles: there is one product profile after each single-coordinate change.

### 2.3 One common order compression retains all ties

Let D be the union of the finite support dates of these n sparse laws.
Its size k is at most n(d+1). Enumerate D increasingly and send its jth
element to j−1, while fixing Never. Apply this SAME map to every marginal.
It preserves every comparison and equality between realized finite clocks,
as well as their comparisons with Never. Hence it preserves the first
finite quitting coalition pointwise on the product support, including every
simultaneous tie and the all-Never case. Independence is preserved because
each coordinate is transformed deterministically and separately.

This order map is not asserted to transform the set of every possible
unilateral response faithfully; an omitted date can matter to a response.

### 2.4 Compactness is now on one fixed finite calendar

Put K=n(d+1). All compressed profiles lie in the fixed product of n
probability simplices on {0,...,K−1,∞}. That space is compact, and
the expected terminal vector is polynomial, hence continuous, in its
finitely many atom probabilities. The subset on which every marginal has
support size at most d+1 is also compact: it is a finite union of closed
products of simplex faces.

Apply this compactness to the approximating compressed profiles from 2.1.
A subsequential product-profile limit retains the support bound and has
exactly the requested limiting vector. It is an actual stopping-law profile,
not a formal clock-at-infinity artifact. The reverse inclusion into the
original image is immediate. This proves the theorem and compactness. QED.

Every displayed law is executable as an ordinary independent behavioral
strategy: at live date t use hazard p_i(t)/Pr(T_i≥t) when the denominator
is positive, and zero otherwise. The unique unabsorbed history carries no
additional random public signal. Product clock sampling and these live
hazards give the same coalition distribution; no observation of opponents'
future private stopping times is used.

## 3. Classical strengthening: exact sparse replacement before truncation

The finite-law approximation in 2.1 is convenient but unnecessary for
compressing ONE actual profile. A bounded countable random vector has its
mean in the ordinary convex hull of its positive-mass range, not merely
the closed convex hull. To see this, its mean is in the closed convex hull
by finite truncation. If it is on a relative boundary, a supporting affine
functional is nonnegative on the range and has expectation zero; it must
vanish at every positive-mass point. Restrict to that smaller affine space.
After finitely many dimension drops the mean is in the relative interior,
which is contained in the ordinary convex hull. Carathéodory then applies.

Consequently each sequential replacement in 2.2 can be made directly for
arbitrary original laws, using at most d+1 of that player's original
positive-mass actions. Common order compression gives the same bound (1).
Compactness of the fixed sparse product simplex then gives the closure
statement without a separate approximation sequence of finite laws.

This is established finite-observable cubature mathematics. Bayer and
Teichmann, [The proof of Tchakaloff's Theorem](https://people.math.ethz.ch/~jteichma/tchakaloff120405.pdf),
Corollary 2 and Remark 2, give positive finite representations of integrable
measurable vector moments; adjoining the constant function one preserves
probability normalization. Applied to (1,f_i), this supplies at most d+1
actions after choosing affine coordinates. The quitting-game adapter here
is the sequential independent replacement followed by common date ordering,
not a new cubature principle or a claim of worldwide priority.

## 4. Exact tests and the strategic boundary

One player causes no difficulty: finite Quit probability α and Never
probability 1−α are realized at date zero and Never, regardless of the
original finite stopping tail. A sure common finite tie remains that same
labelled coalition under order compression. All-Never remains all-Never.
These tests also explain why time-labelled terminal distributions are NOT
covered: a genuinely infinite-support absorption-date law cannot be retained
on any fixed finite calendar.

Here is a two-player cap counterexample, embedded in Fin4 by two inert
Never players if desired. Set

    r_0({1})=1, and every other reward coordinate equal to zero.

The pure profiles p=(0,1) and q=(0,∞) both induce exactly the terminal
coalition {0}; their prescribed payoff vectors are both zero. Against p,
player 0 can Never and earn 1 from player 1's later singleton, so its full
response cap is 1. Against q, every replacement earns zero, so its cap is
0. Thus full terminal law equality does not determine even the scalar cap,
and reversing the profiles gives a payoff/law-preserving change increasing
the cap. The q profile is exact terminal Nash and p is not.

Even common order compression alone can discard profitable timing options.
Take r_1({1})=1 and all other rewards zero. The pure profile (2,3) has
outcome {0}; player 1 can quit earlier and earn 1. Compress the occupied
dates to obtain (0,1), still with outcome {0}. Player 1 can now only tie
player 0 at zero or lose the race, both worth zero. Its cap drops from 1 to
0. Preserving order among OCCUPIED dates does not preserve all empty gaps.

No claimed theorem transports full caps, Nash inequalities, a semantic debt
minimum, pure-time response functions, counterfactual outcome laws after
replacement, chosen suffixes, or finite-horizon/discounted payoffs. The
compactness of the prescribed outcome image does not make the full terminal
payoff map jointly continuous on arbitrary compactified clock laws.

There is a stronger EXISTING boundary, not merely failure of a particular
compression. The independently reviewed [STALL fixture](../gpt/STALL.md),
SHA256 `0a8149762836946c208a07f4190e9c32340a05c52474b236fa4cbb4ad532bedb`,
has an exact geometric terminal Nash profile with payoff (1,3,3,1), whereas
every exact Nash law on EVERY finite deadline menu has full debt
21/2−7√2>0. See Sections 3–5 of
[its independent review](../feedback/STALL__BY_CODEX_FRECHET_CYCLE.md).
Any finite-calendar full terminal Nash profile would belong to one such
finite menu and be Nash there, contradicting that positive full debt.
Therefore this infinite exact equilibrium's complete zero-debt semantic
pair has NO finite-calendar realization at any deadline. Its terminal law
is nevertheless the simple point mass at coalition {0}, so prescribed-law
realization itself is trivial. This corollary uses the existing reviewed
fixture; its complete uniqueness proof was not independently re-audited here.

## 5. Actual finite-dimensional source, and its exact remaining limitation

Let C_r={U(p): p is an actual independent profile}. The theorem proves
unconditionally that C_r is compact and is already the image of the
Fin4 twenty-date product simplex. Thus every continuous objective H on
C_r, in particular any polynomial in prescribed payoffs, has a minimizer
U(p*) with an actual bounded-calendar realizing profile p*.

This is a genuine source improvement for an attack minimizing a hypothetical
universal polynomial over the ACTUAL prescribed-payoff carrier: actual
realization is no longer an extra premise. It is not an arbitrary convex
combination of terminal payoff vectors, and it does not enlarge the carrier
to the reward convex hull. Every literal independent root prefix q over
p* remains an actual profile, with payoff F(q,U(p*)). Consequently

    H(F(q,U(p*))) ≥ H(U(p*)) for every product root q.          (2)

Suppose a universal robust-edge polynomial has, in particular, the exact
Nash-root inequality H(v)−H(F(q,v))≥a(q), where a(q) is absorption.
At the minimizer (2) then forces every exact Nash root against U(p*)
to have a(q)=0. Equivalently every such root is all-Continue. This is an
exact consequence, not a contradiction: all-Continue can be the only
exact Nash root. An actual minimizing profile need not have Nash roots
against its own actual suffix payoffs. The missing strategic assertion is
one positive admissible absorption edge from this actual minimizing source,
or some different use of the universal hypothesis that defeats the stall.
The support theorem alone does not supply it.

Nor does it realize an entire point (U,B) of the terminal-semantic carrier,
or (U,B,ν) of the joint law carrier, because B is the unrestricted response
cap vector. The law theorem realizes (U,ν) after projecting away B, with
no bound on the cap of the realizing profile. It does not prove attainment
of the original total-debt infimum.

There is also an exact algebraic consequence. With K=n·2ⁿ, put x_i,t for
the finite calendar masses and x_i,∞ for Never. Then for every nonempty S,

    ν(S)=Σ_{t=0}^{K−1} [∏_{i∈S}x_i,t]
                         [∏_{j∉S}(x_j,∞+Σ_{u>t}x_j,u)],
    ν(∅)=∏_i x_i,∞.                                        (3)

These degree-n polynomials on a fixed product simplex parametrize the
ENTIRE actual terminal-law set. That set is compact semialgebraic, not
merely a semialgebraic outer approximation. Rational/algebraic law
membership and prescribed-payoff constraints therefore admit finite real
quantifier-elimination tests in principle. This is no efficiency claim,
general checker implementation, cap-preserving reduction, or decision
procedure for equilibrium existence or the uniform-equilibrium conjecture.

## 6. Narrow source audit and proposed stopping point

The relevant route was selected through docs/TOOLKIT.md and the actual
carrier discussion in docs/FRONTIER.md. Declarations inspected directly:

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
- `quittingTerminalPayoff_update_stoppingLawMixture_observer_eq`,
  `quittingBehaviorStoppingLaw_finiteStoppingLawMixture`, and
  `quittingTerminalPayoff_update_finiteStoppingLawMixture_eq_expect` in
  `UniformEquilibrium/Quitting/Paths/FiniteStoppingLawMixture.lean`;
- `quittingFirstStoppingOutcome` and
  `quittingIndependentTerminalOutcomeLaw` in
  `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`;
- `quittingTerminalSemanticLawCarrier` and
  `exists_terminalSemanticLawCarrier_lift` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
- `quittingTerminalSemanticDebtSafeHull_exists_small_witness` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticDebtSafeHull.lean`;
- `exists_twoSupported_canonicalOverlap_compression_on_dates` in
  `MathUE/Probability/FiniteOverlapSparseCompression.lean`; and
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`.

The debt-safe-hull theorem compresses a convex witness of semantic pairs;
it does not realize those mixtures independently. The overlap theorem
preserves one event and improves another on a supplied finite date menu;
it does not state fixed-calendar full-law coverage. The counterfactual law
definitions do not themselves identify every source-level semantic bridge;
the independent clock argument above provides the ordinary mathematics.
The polynomial characterization carries its explicit normality and positive
singleton hypotheses; no such hypotheses are needed for realization itself.
No Lean build or current integration certification was performed.

A narrow conference search found the overlap optimization discussion in
KEPLER_CLOCKCONE__OVERLAPPING_FIRST_QUITTER_LAW.md, not this whole-vector
fixed-calendar statement. The old contact-barycenter test was consulted only
to distinguish actual payoff minimization from convex-envelope minimization.
The independent forthcoming FRECHET note was not read. The primary
literature search located the exact cubature antecedent in Section 3; no
exhaustive literature-priority conclusion is claimed.

Next requested check: independently verify the whole-law fixed-calendar
bound and whether the universal-polynomial argument has an additional
positive-edge assertion at its now ACTUAL minimizing source. This note
stops before proposing a new conditional consumer or claiming that assertion.
