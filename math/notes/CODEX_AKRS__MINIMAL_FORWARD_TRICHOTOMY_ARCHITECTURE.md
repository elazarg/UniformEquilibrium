# AGKRS forward trichotomy: minimal honest architecture

## Status

This is a mathematical dependency audit of
`formalized/AGKRS_FORWARD_TRICHOTOMY_BY_REFUSAL_COMPACTIFICATION.md`.  The
note itself makes no new Lean-checked claim; the packet's formalization record
now points to the checked realization of this architecture.

The main verdict is:

> The direct proof really needs an absorption-clock compactness argument and
> a suffix-uniform decoder.  It does not need the full general theory of
> abstract absorption paths proposed by the paper.

There is therefore no honest short proof obtained merely by deleting the
large analytic middle.  There is, however, a substantially smaller
theorem-specific interface to formalize.  A second possible simplification of
the decoder is recorded below; its finite estimates are given, but the route
has not had independent review and is not a replacement theorem yet.

## Question audited

For a finite quitting game with an arbitrary payoff at Never, assume that a
behavioral terminal epsilon-equilibrium exists for every positive epsilon.
Prove the fixed AGKRS forward alternative:

1. stationary approximate equilibria at every sufficiently small error; or
2. sure-first-stage-Quit approximate equilibria with an arbitrary behavioral
   punishment at the quitter's min-max; or
3. completely absorbing root sequences which are sequentially approximately
   perfect against their literal continuation payoffs.

Only this forward implication is under discussion.  Neither the printed
reverse implication nor the false printed error-exponent conversion is part
of the target.

## Project relevance

This theorem is not a missing producer for the finite-quitting uniform-payoff
conjecture.  Its premise already says that terminal approximate equilibria
against arbitrary behavioral replacements exist at every positive error.
The checked terminal-selection equivalence
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
already turns that premise into a uniform-equilibrium payoff.

Completing AGKRS Theorem 3.4 is therefore valuable as an honest literature
result and as a structural classification of games already known to have
approximate equilibria.  It does not establish approximate-equilibrium
existence for a new game.  Of its machinery, the global refusal ledger and a
source-faithful absorption-clock compactification may be reusable on the open
producer frontier; the final S.1/S.2/S.3 classification itself is not a direct
conjecture-closing consumer.

The published proof of this statement is not a proof that can simply be
transcribed.  Its invocation of Simon's old classification acquires a fourth,
stationarily-generated branch after Simon's correction.  An honest
formalization must either formalize that corrected classification and consume
the fourth branch, or prove the three-way statement by another argument.  The
export takes the second route.

## Sources inspected

- AGKRS, *Absorption paths and equilibria in quitting games*, the pinned
  source `literature/AKRS.tex`, especially Theorem 3.4 and the absorption-path
  compactness and discretization of Section 4;
- `Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean`, especially
  `theorem3_4`, `theorem3_4_of_correctedDependencies`, and the paper-facing
  accounts of Propositions 4.6, 4.9 and 4.12;
- `UniformEquilibrium/Quitting/AbsorptionPath/ContinuousPath.lean`;
- `UniformEquilibrium/Quitting/Classification/Existence/AGKRSTheorem34Dependencies.lean`;
- `UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRootSequence.lean`;
- the current worktree file
  `UniformEquilibrium/Quitting/Classification/Existence/GlobalRefusalLedger.lean`;
  and
- `UniformEquilibrium/Quitting/AbsorptionPath/LogarithmicProductLaw.lean` and
  `LogarithmicBlockDiscretization.lean` for the optional decoder
  simplification below.

## What is mathematically unavoidable in the direct proof

“Unavoidable” here means that the exported proof uses this information and
that deleting it leaves a known countermechanism.  It does not claim a
logical uniqueness theorem saying that no entirely different proof could
exist.

### 1. An escape-clock compactification

Calendar-time product compactness is insufficient.  Stationary hazards going
to zero converge coordinatewise to Never while retaining an absorbing
terminal law.  The proof must retain, in some equivalent form:

- the limiting finite-coalition measure in cumulative-absorption time;
- the remaining conditional reward moment at every nonterminal clock;
- a product-row witness at every limiting atom; and
- the fact that nonatomic collision mass vanishes, so diffuse mass is
  singleton-valued.

One may encode this by AGKRS cadlag paths, by finitely many weakly convergent
measures on the compact interval, or by a Helly selection of cumulative
distribution functions.  Changing the encoding does not remove the
compactness problem.

The matching-source-atom statement is essential.  At a nonterminal limiting
jump, it is what turns global Nash error into reached suffix error and proves
the exact support inequalities of SP.1.  At a terminal jump it is what
produces the genuine source row used in S.2.

### 2. A global refusal or equivalent Snell ledger

Pointwise Quit inequalities do not prove the supported indifference condition
on a diffuse clock.  Individual source dates may have vanishing reach or
vanishing Quit probability, and the relevant mass may be spread over
infinitely many dates.

The necessary bridge is a single legal behavioral deviation which refuses
Quit on all dates carrying a fixed positive gap.  In finite form it gives

    delta * sum(selected source-reach * prescribed Quit mass)
      <= global Nash error.

Finite exhaustion then controls the entire selected clock.  This is exactly
the content now present in the worktree declarations
`delta_mul_finiteRefusalCharge_le_of_nash` and
`delta_mul_tsum_selectedRefusalCharge_le_of_nash` in
`GlobalRefusalLedger.lean`.

This lemma, or an equivalent optional-sampling/Snell argument, is the genuinely
new nonlocal ingredient.  A collection of one-date deviations does not
substitute for it.

### 3. Terminal-jump separation and the S.2 coupling

Sequential path perfection deliberately imposes no SP.1 condition after a
jump which consumes every remaining mass.  Such a jump cannot be sent through
the S.3 decoder.

The proof must therefore separate it.  Finiteness of the player set turns
zero joint Continue mass into one sure quitter.  A matching source row, a
min-max punishment, and a coupling uniform over every replacement by another
player then produce literal S.2.  The coupling and the selected quitter's
min-max inequality are real mathematical steps; the terminal case cannot be
hidden in a continuity convention.

### 4. A support-preserving, suffix-uniform S.3 decoder

In the no-terminal-jump case the limit object must be returned to one actual
independent root sequence.  Two properties are indispensable:

- a coordinate receives positive Quit probability only when the source cell
  contains positive singleton mass for that coordinate; and
- the continuation-payoff error is uniform over every suffix, including
  suffixes arbitrarily near absorption clock one.

The first is needed because positive probability activates the lower support
inequality in epsilon-perfection.  Mere metric proximity of coalition laws is
not enough.  The second cannot follow from bare weak convergence, whose
conditional denominators degenerate near clock one.  It needs a weighted
law/Bellman telescope.

These four items are the irreducible mathematical core of the exported route.

## Necessary but small layers

The following steps are also required, but they are not reasons to build a
large new theory.

- Coordinatewise subtraction of the Never payoff and restoration of the
  original table branches.
- The positive-solo nonabsorption estimate and a late absorbing completion.
  Equivalently one could retain a Never atom and prove that its limit is zero;
  this changes packaging, not mathematics.
- Continuity of bounded reward moments at the finitely selected continuity
  points and quantitative conditioning below a fixed clock less than one.
- The final finite-disjunction selection showing that one branch works for
  all small errors.

## Machinery not required for Theorem 3.4

An honest theorem-specific implementation need not prove any of the
following general statements.

- Density of behavioral profiles in **every** abstract absorption path.
  Only the selected zero-perfect/no-terminal limit needs a decoder.
- Sequential compactness of every pre-existing bundled path.  Only paths
  induced by the selected completed equilibrium sequence need a cluster.
- General closure of arbitrary sequentially epsilon-perfect paths.  The
  source profiles here are ordinary global equilibria, and the refusal
  argument is a specialized closure theorem.
- A general profile/path equivalence or uniqueness theorem.
- The characterization of all connected components of the complement of the
  clock and jump sets as a public API.
- A general binary composition law, marked-obstacle graph, deleted-law
  compactification, or holonomy carrier.
- The reverse direction of AGKRS Theorem 4.13.
- Solan--Vieille's conversion from sequential perfection to approximate Nash.
  S.3 itself is the endpoint of Theorem 3.4.

These may be valuable reusable infrastructure, but they are proof-engineering
choices rather than dependencies of this forward theorem.

There is also no advantage in replacing the direct proof by a formalization
of the printed citation chain.  That route must formalize the substantial
corrected Simon theorem and then separately consume its stationarily-generated
fourth branch.  Current project records show that this is at least as large
and has an additional unresolved interface.

## A smaller suggested theorem interface

Instead of first completing the whole AGKRS path library, introduce a single
theorem-specific limit record, for example `AGKRSLimitChronology`, containing
only:

1. finitely many coalition measures on the absorption clock;
2. their bounded tail reward quotients;
3. source-product witnesses for nonterminal atoms;
4. zero nonatomic mass on nonsingleton coalitions; and
5. the refusal support statement for singleton mass.

The producer should accept the actual completed equilibrium sequence and
return this record or a terminal jump.  A second theorem should decode a
no-terminal record into S.3.  This factorization exposes the two genuinely
hard lemmas without requiring the general path API to be finished first.

The refusal support field can be stated in an interval/measure form rather
than through lower right derivatives:

> On every compact continuous-clock interval on which the continuation value
> of player i exceeds its solo reward by delta > 0, the limiting singleton-i
> measure is zero.

This is exactly what the global refusal ledger proves.  It is also exactly
what the decoder needs: if a cell contains positive singleton-i mass, that
cell meets the zero-gap support after allowing the cell's payoff-transport
error.  Thus a full reusable derivative theory is optional for Theorem 3.4.

## Candidate simplification of the small-cell product decoder

This subsection is ordinary mathematics not independently reviewed and not
Lean-checked.  It is a possible reduction in implementation size, not part of
the audited export.

Let a small cell have correlated conditional law `y`, total absorption `p`,
singleton masses `s_i`, total singleton mass `s=sum_i s_i`, and collision mass
`c=p-s`.  Copy every jump of conditional absorption at least `1/k`.  The
remaining product jumps have conditional absorption below `1/k`; their
collision bound and the singleton nature of the nonatomic part give

    c <= C_d * p / k,

where one may take `C_d=d^2/2` from `q_i <= rho`,
`sum_i q_i <= d*rho`, and the checked quadratic collision estimate.

Define an actual product root directly by

    q_i = 1 - exp(-s_i).

This is `logarithmicProductRoot` with integrated hazards `A_i=s_i`.  It has
three immediate advantages:

- `q_i>0` iff `s_i>0`, so support is preserved exactly;
- every `q_i<1`; and
- no scalar equation or product-law selection theorem is needed.

Let `y'` be its complete Boolean coalition law.  Its Continue mass is
`exp(-s)`.  The checked logarithmic singleton and collision bounds give

    sum_i |y'({i})-s_i| <= s*(1-exp(-s)) <= s^2,

    y'(coalitions of size at least 2) <= s^2/2,

and

    |(1-exp(-s))-p| <= c+s^2/2.

Therefore the complete one-cell L1 error satisfies

    ||y'-y||_1 <= 2*c+2*s^2
                <= 2*(C_d+1)*p/k.

For all sufficiently large `k`, also

    1-exp(-s) >= exp(-1)*s >= exp(-1)*p/2.

Thus the source cell absorption is bounded by a fixed multiple of the new
cell absorption.  A standard sequential-kernel coupling, weighted by the new
survival probabilities, then gives from every suffix

    total law distance <= constant(d)/k,

because the sum of `survival * new-cell-absorption` is one.  The new sequence
is completely absorbing since its cell hazards dominate the source cell
hazards by a fixed factor.  Bounded reward moments inherit the same uniform
error.

If this telescope is formalized, it replaces the paper's exact
same-absorption product resolver and its exact-survival comparison by the
already available logarithmic product root plus one generic sequential-kernel
total-variation lemma.  What remains to check before adopting the route is:

1. the chosen path partition supplies the displayed aggregate collision bound
   for every small cell;
2. the suffix coupling is stated for the actual countable root sequence and
   proves the bound uniformly from every starting cell; and
3. the interval-form refusal support statement supplies the lower Quit support
   inequality for every active cell coordinate.

The local estimates above are exact, but these three adapters have not been
independently audited.  Until then the published support-preserving decoder
remains the conservative implementation route.

## Recommended formalization order

1. Finish and audit the finite/countable global refusal ledger.
2. State the minimal equilibrium-sequence-to-limit-chronology record before
   building any more general topology.
3. Prove the terminal-jump S.2 consumer directly from that record.
4. Decide, by a small isolated prototype, between the published
   same-absorption decoder and the logarithmic approximate-survival decoder.
5. Prove the suffix-uniform decoder and only then expose the final fixed-branch
   capstone.

The stopping criterion for abstraction should be strict: if a proposed path
lemma is not used by the source-to-limit theorem, the terminal-jump consumer,
or the no-terminal S.3 decoder, it is not needed for an honest proof of the
forward trichotomy.
