# Adversarial experiment proposals

These are proposed finite or exact-computation attacks on the current
uniform-equilibrium program. They are not theorem claims and they are not yet
members of the registered Base suite. Every proposal has an explicit
promotion boundary. In particular, failure of a bounded controller grammar,
bounded path grammar, stationary class, or public strategy class is never
called a refutation of unrestricted uniform-equilibrium existence.

## P01 — hybrid absorption path-or-barrier CEGIS

**Hypothesis under attack.** After the stationary and first-stage-absorption
exceptions are removed, a rational four-player quitting table should admit a
proper nonterminal sequentially 0-perfect absorption path, or a corrected
augmented path whose terminal jumps carry credible continuation witnesses.
The printed path definition is not currently interchangeable with either
object: its discrete optimality clause omits sure terminal jumps.

**Finite/exact protocol.** For a supplied rational terminal table:

1. eliminate the two simple branches by exact real-algebraic tests, retaining
   symbolic certificates and a quantified small-error interval;
2. enumerate finite jump supports and piecewise-rational singleton-flow cells,
   classifying every candidate terminal jump separately;
3. impose promise keeping, nonterminal jump Nash inequalities, flow
   complementarity, nonnegative rates, and terminal mass as exact polynomial
   constraints; in a separate augmented run, attach explicit off-path
   continuation witnesses to terminal jumps and test Nash in `G_r(y)`;
4. when a candidate fails, extract the violated row and refine the grammar;
5. in parallel, synthesize a finite semialgebraic barrier cover whose cells are
   closed under every admissible flow and jump but exclude the terminal
   boundary. Check every sign and tangency claim by rational arithmetic or an
   independently checkable real-algebraic certificate.

**Reporting rule.** Report three columns, never one merged verdict:

1. the literal printed `SP_source` convention;
2. proper paths, in which every jump remains nonterminal and First/Never are
   disjoint branches; and
3. augmented terminal paths with a supplied credible continuation `y`.

The diagnostic all-jumps test with terminal continuation fixed to zero is not
a repair and may reject genuine first-stage equilibria.

**What falsifies the idea.** A barrier proves nonexistence only if its cover is
global for the repaired hybrid path definition, including arbitrary jump sets,
measurable singleton flows, accumulation behavior, and all boundary support
changes. Failure of every path up to a chosen number of pieces merely
falsifies that bounded grammar. A barrier for proper paths becomes a
game-theoretic obstruction only after the separate simple branches and the
corrected path/equilibrium bridge are proved.

**What it does not establish.** A bounded search failure does not rule out an
infinite-cycle path, an irregular measurable flow, a terminal approximate
equilibrium, or a uniform equilibrium. Conversely, finding a path does not by
itself give a quantitative finite-horizon uniform modulus.

**Promotion criterion.** Promote only an exact repaired path with a proved
conversion to terminal approximate equilibria, or a global repaired-path
barrier theorem plus the simple-branch and terminal-equilibrium bridge.
Question 101 states the mathematical discriminant; Review 07 records why the
printed equivalence cannot be imported.

## P02 — local retargeting versus global irreversible-SCC coherence

**Hypothesis under attack.** If every recurrent region of a finite stochastic
game has a nonempty sustainable local target correspondence, then targets can
be selected coherently across irreversible moves and assembled into one
global ordinary profile.

**Finite/exact protocol.** Enumerate small rational games whose action-support
graph has a short condensation DAG. For every maximal recurrent region,
enumerate fixed public architectures and compute their exact semialgebraic
target/cap sets. For each irreversible exit, record the full continuation
target vector, the owner who can trigger or suppress the exit, and the
punisher-side unilateral value. Solve the resulting global target-selection
and handoff constraints exactly. Preserve all alternative exits rather than
choosing one locally before the global solve.

**What falsifies the idea.** An exact instance with nonempty local sustainable
sets but an empty global consistency system falsifies the naive local-gluing
principle. A stronger semantic falsifier would additionally show that every
history-dependent ordinary strategy induces one of the enumerated
inconsistent SCC handoffs.

**What it does not establish.** Empty consistency for a fixed public-node
bound, deterministic update skeleton, or public strategy class does not rule
out larger public controllers, hidden randomized memory, clocked-private play,
or unrestricted equilibrium existence.

**Promotion criterion.** Promote either a general SCC dynamic-programming
selection theorem, or a concrete game together with a strategy-class-
independent reduction from every ordinary profile to the inconsistent local
handoff system.

## P03 — occupation/escape-flux aliasing

**Hypothesis under attack.** A normalized occupation vector, augmented by one
leading escape-flux layer, contains enough asymptotic information to determine
target delivery and unilateral credibility through a metastable transition.

**Finite/exact protocol.** Construct pairs of rational or algebraic policy
germs with the same limiting occupation measure. Match, successively, their
leading exit rates and first `k` normalized escape-flux jets while varying the
post-exit recurrent payoff or owner. Compute exact Abel and long Cesaro
payoffs, hitting probabilities, architecture-specific unilateral values, and
gain--bias residuals. Begin with two recurrent SCCs joined by rare directed
edges so every asymptotic coefficient is symbolic.

**What falsifies the idea.** For a proposed finite flux signature, two germs
with identical signature but different sustainable target/cap verdicts
falsify completeness of that signature. If no finite `k` separates a
parameterized family, the family is evidence for an intrinsically multiscale
or inverse-limit interface.

**What it does not establish.** Aliasing of an occupation signature does not
show that the game lacks an equilibrium; it only kills a proposed finite data
reduction. Numerical near-equality does not count as aliasing.

**Promotion criterion.** Promote an exact symbolic alias family for every
fixed jet depth, or a proved finite-order separation theorem with explicit
hypotheses and reconstruction bounds.

## P04 — continuous selector and monodromy stress test

**Hypothesis under attack.** Local sustainable target branches over analytic
game data admit a globally continuous branch selector compatible with
rebasing and target transport.

**Finite/exact protocol.** Build low-dimensional rational polynomial families
whose local target/certificate solutions form a finite covering over a loop in
parameter space. Continue every nonsingular solution branch exactly using
resultants or certified interval algebra, compute the monodromy permutation,
and test whether the payoff target (rather than merely an auxiliary witness)
returns to itself. Repeat after quotienting by obvious player/action
symmetries and after allowing target retargeting at declared singular cells.

**What falsifies the idea.** Nontrivial monodromy with no symmetry-compatible
fixed target branch falsifies a global continuous-selector theorem in the
stated class. A branch exchange only in auxiliary certificates does not.

**What it does not establish.** Continuous-selector failure does not obstruct
measurable, discontinuous, history-dependent, or accuracy-indexed selection,
and therefore does not refute uniform-equilibrium existence.

**Promotion criterion.** Promote a fully specified polynomial family with a
proved covering/monodromy computation and a theorem connecting that
monodromy to the exact selector interface being rejected.

## P05 — zero-debt loops versus escape-flux discrepancy

**Hypothesis under attack.** Pumpable zero-target-debt loops, together with a
finite escape-flux label, suffice either to construct a sustainable controller
or to prove routing resistance when a finite controller revisits a state.

**Finite/exact protocol.** Enumerate short legal loops in small absorbing games
and compute exactly: accumulated target debt, endpoint continuation state,
owner-tagged action counts, escape probabilities, and deviation gain. Search
for pairs with identical zero debt and endpoint but incompatible owner/escape
flux. Product each pair with bounded deterministic controllers, enumerate
reachable cycles, and test the exact gain--bias inequalities before and after
pumping.

**What falsifies the idea.** A pair indistinguishable by the proposed debt/flux
label but with opposite deviation-cap verdicts falsifies that label as a
sufficient routing invariant. A universal positive result would require a
proof that every repeated controller configuration exposes one of the
enumerated pumpable witnesses.

**What it does not establish.** A bounded-controller discrepancy is not the
universal finite-public resistance theorem for the Big Match and says nothing
by itself about private-clocked or unrestricted strategies.

**Promotion criterion.** Promote either a generic concatenation/pumping lemma
with owner-tagged escape flux, or an exact counterexample showing why every
finite-dimensional version of the proposed label loses strategic data.

## P06 — irreversible punisher-cycle audit

**Hypothesis under attack.** A deviator-capping response can always be chosen
so that every punisher is dynamically willing to carry it through an
irreversible recurrent transition.

**Finite/exact protocol.** Enumerate rational games with two or three recurrent
SCCs and a public deviation flag. For each proposed response, solve the
deviator's cap and every responder's continuation MDP simultaneously. Require
the response to be closed under unilateral changes by each responder, and
record whether suppressing the punishing exit preserves that responder's
floor. Search first for cycles in which each edge caps one player but strictly
harms the next responder.

**What falsifies the idea.** A complete finite response set in which every
deviator-capping response has a positive recurrent Bellman surplus for some
responder falsifies the local punisher-existence claim for that game and
target. To affect root existence, all alternative targets and response modes
must also be eliminated.

**What it does not establish.** Failure of one punishment profile, one target,
or one public architecture is not failure of ordinary equilibrium existence.

**Promotion criterion.** Promote a target-independent cycle theorem or a
fully exhaustive target/response elimination proof; otherwise retain the
instance as a credibility regression only.

## P07 — late-horizon incompatibility search

**Hypothesis under attack.** Accuracy-indexed profiles can always be chosen so
that one profile controls every sufficiently late horizon. The counterpattern
would be a fixed positive exploitability gap recurring arbitrarily late for
every profile.

**Finite/exact protocol.** For small rational games and bounded controller
classes, solve exact finite-horizon best-response polynomials on increasing
horizons. Search for residue classes or metastable windows with disjoint
approximate-equilibrium requirements. Attempt to extract a symbolic pumping
argument proving

\[
\exists\delta>0\;\forall\sigma\;\forall H\;\exists N\ge H\;
\exists i,\tau_i:\quad
\gamma_{i,N}(\tau_i,\sigma_{-i})
\ge \gamma_{i,N}(\sigma)+\delta.
\]

**What falsifies the idea.** The displayed statement, proved over all behavior
profiles, is a target-free nonexistence certificate. A repeating pattern found
only for stationary or bounded-memory profiles merely falsifies that class.

**What it does not establish.** Alternation of finite-horizon Nash payoffs, or
failure of one profile at one subsequence, is insufficient; the quantifiers
must cover every profile and arbitrarily late horizons with one common gap.

**Promotion criterion.** Promote only a symbolic all-behavior proof of the
displayed quantifiers, or a theorem reducing all behavior profiles to a
finite exact obstruction. The already formalized semantic certificate can
then consume it.

## P08 — target-optimized selected-fiber separation

**Hypothesis under attack.** If a compact correlated packet correspondence has
nonempty sustainable targets and each context separately admits a
product-realizable local observation on every target fiber, then target
optimization should leave at least one packet that is product-realizable at
all contexts simultaneously.

**Finite/exact protocol.** Enumerate two- and three-context rational packet
systems with two binary players per context. Represent each local product
image by its exact rank-one polynomial equations and the global correlated
packet set by rational affine balance, delivery, floor, and unilateral-slack
constraints. Eliminate the target variables only after imposing simultaneous
product feasibility. Require the search to certify both:

1. for every feasible target and every context separately, some correlated
   packet on that target fiber is product-realizable at that context; and
2. no target admits one packet product-realizable at all contexts.

Minimize contexts, actions, retained observation coordinates, and global
constraints. Use quantifier elimination or exact Positivstellensatz
certificates, not floating-point infeasibility.

**What falsifies the idea.** An exact instance satisfying both displayed
conditions falsifies the local selected-fiber gluing principle even after
target optimization. If every enumerated instance admits a simultaneous
selector, that is only evidence until a structural theorem explains the bound.

**What it does not establish.** Empty product feasibility for one target, one
fixed packet, or one bounded architecture does not rule out retargeting in the
same game, a larger architecture, or unrestricted equilibrium existence. Even
exhaustion of the packet correspondence refutes only the claim that this
correspondence is a complete strategy representation unless every behavior
profile has independently been reduced to it.

**Promotion criterion.** Promote either the lexicographically minimal exact
separator with independently checkable positive and negative certificates, or
a theorem giving a simultaneous selector under an explicit compatibility
condition strictly weaker than full local product/correlated image equality.

## P09 — Puiseux elimination-order and rebasing stress test

**Hypothesis under attack.** Leading-order metastable reduction can eliminate
equally fast classes in any order, discard higher terms after each step, and
still preserve prescribed rewards, owner-labelled unilateral residual signs,
and stopped-history rebasing.

**Finite/exact protocol.** Enumerate two- to five-state stochastic matrices
with monomial or binomial Puiseux transition entries and symbolic reward
vectors. For every admissible fast-class elimination order:

1. compute the exact Schur complement over the Puiseux germ field;
2. compute the version truncated after the currently smallest visible order;
3. transport every owner-labelled unilateral affine row;
4. apply a basis of affine continuation rebases both before and after
   elimination; and
5. compare reduced operators, reward values, first nonzero residual signs, and
   rebase maps symbolically.

Search separately for arbitrary-depth cancellation families showing that no
fixed jet depth is sufficient.

**What falsifies the idea.** Different residual signs or noncommuting rebase
maps for two legal truncated schedules falsify the leading-order-only rule.
A discrepancy in coordinates that disappears under an explicit positive-unit
equivalence and preserves every value and residual is not a falsifier.

**What it does not establish.** Failure of premature truncation does not
falsify exact Schur confluence or the existence of an adaptive-precision
Puiseux certificate. A counterexample for one selected policy family does not
show that all equilibrium branches fail.

**Promotion criterion.** Promote an exact minimal symbolic counterexample with
the discarded coefficient identified, or a proved adaptive-jet algorithm with
a termination measure, schedule-independent normal form, owner-row
preservation, and rebase functoriality.

## P10 — adversarial online circulation scheduler

**Hypothesis under attack.** A rational zero-charge circulation with an
offline periodic bounded-discrepancy walk can be realized by one finite-state
causal scheduler that preserves the required public conditional law against
adaptive mode selection and still has uniformly bounded realized discrepancy.

**Finite/exact protocol.** Start with the one-vertex two-loop fair circulation,
then enumerate small directed multigraphs, public observation maps, rational
mode rows, integer charges, and private scheduler memories of size at most
\(K\). Solve the universal-history constraints for:

1. exact or tolerance-\(\delta\) conditional public-output laws;
2. path consistency;
3. bounded, square-root, and supplied sublinear maximal discrepancy;
4. reachability of every used memory state; and
5. every adaptive public mode selector.

For the fair two-loop case, verify the martingale variance identity and the
linear lower bound on cumulative conditional-law distortion under bounded
discrepancy. In partially observed cases, search for charge directions
controllable inside observation fibers without changing the public law.

**What falsifies the idea.** The fair-loop lower bound falsifies simultaneous
exact public conditional fairness and bounded public discrepancy. For a
claimed hidden-fiber positive class, an exact adversarial mode sequence forcing
linear discrepancy or conditional-law distortion falsifies that class.

**What it does not establish.** Failure at memory bound \(K\) does not exclude
larger or unbounded private memory. Failure of bounded discrepancy does not
exclude the optimal square-root martingale rate, which is already sublinear.
Failure for one circulation or target does not imply target-free equilibrium
nonexistence.

**Promotion criterion.** Promote a sharp theorem separating publicly
measurable martingale directions from secretly controllable fiber directions,
with matching rates and a finite-state synthesis criterion, or a minimal exact
counterexample to the proposed separation.

## P11 — predictive-compression lower-bound census

**Hypothesis under attack.** Uniform contraction of a finite hidden-state
continuation implies that a small accuracy-dependent public predictor
preserves prescribed payoffs and unilateral best-response values, and that
the required predictor size is substantially below the full belief-simplex
covering number.

**Finite/exact protocol.** Enumerate rational hidden-state controlled kernels
with a certified common contraction margin and bounded Lipschitz rewards.
For each state bound \(K\):

1. synthesize the best \(K\)-cell public quantizer and compressed transition
   rule;
2. solve the exact finite-horizon unilateral values in the original and
   compressed models;
3. maximize the normalized gap over initial beliefs, horizons, and adaptive
   unilateral controls; and
4. compare one fixed payoff, every payoff in a finite separating family, the
   unilateral value, and the full public continuation law as four distinct
   tasks.

Search for families realizing the belief-simplex covering exponent and for
one-state contractive examples with unavoidable linear total error
\(\Theta(\delta N)\) at fixed grid radius.

**What falsifies the idea.** An order-one value gap under a uniformly
contractive controlled kernel and arbitrarily fine quantization falsifies the
proposed two-sided transfer theorem or its metric hypothesis. A covering lower
bound for full-law approximation does not falsify small compression for one
payoff coordinate.

**What it does not establish.** Failure at one fixed memory bound or fixed grid
does not rule out a finer accuracy-indexed predictor. A lower bound inside the
finite hidden-state contractive class does not refute unrestricted equilibrium
existence, and a failure for one target is not a target-free obstruction.

**Promotion criterion.** Promote a symbolic family with matching upper and
lower state-count bounds for a named strategic task, or a corrected
contraction/simulation theorem whose constants and adaptive-control quantifiers
are validated on the census.

## P12 — adapted-kernel Kakutani dichotomy on the play measure

**Hypothesis under attack.** The E63 product dichotomy survives the passage
from independent per-stage deviation rates to **history-dependent** ones: for
two behaviour profiles inducing play measures via `Kernel.trajMeasure`, with
stagewise conditional Hellinger discrepancies \(\delta_t(h)\) adapted to the
history, \(\sum_t \delta_t^2 < \infty\) along play still forces absolute
continuity, and \(\sum_t \delta_t^2 = \infty\) forces mutual singularity.

**Why now, and what it unblocks.** E63 closed layer 2 for independent rates,
completing the Q38 impossibility chain (E51 → E61 → E60 → E62 → E63) for
mixture deviations over a positive base. The chain's conclusion — unbounded
incentive debt with every anytime detector missing at every level — therefore
holds only against deviators who cannot condition their rate on the history.
A strategic deviator can. The adapted version is the honest form of the
impossibility, and E61 already names its missing ingredient: the sequential
chain rule for the stagewise discrepancies.

**Finite/exact protocol.** The E63 proof shape is the asset to preserve:
exact finite-horizon `withDensity` identities for hybrid measures, one uniform
Cauchy–Schwarz TV–Hellinger cylinder bound, cylinder density, tail vanishing —
no filtrations, no L² martingale convergence, no 0–1 law, second direction by
symmetry. Attempt the same skeleton with conditional Hellinger affinities
per history prefix; the hybrid-measure identities should survive with
kernel-indexed densities. If they do not, the failure point identifies exactly
what history dependence costs.

**What falsifies the idea.** A pair of adapted profiles with
\(\sum \delta_t^2 < \infty\) a.s. whose play measures are mutually singular
kills the adapted dichotomy and confines Q38's impossibility to the
independent-rate class permanently — itself a publishable fence.

**What it does not establish.** The dichotomy alone does not re-run the E62
composition; the debt divergence \(\sum \delta_t = \infty\) with
\(\sum \delta_t^2 < \infty\) must be re-exhibited by an adapted profile, since
the harmonic family is independent by construction.

**Promotion criterion.** Promote when the adapted dichotomy is Lean-verified
against `Kernel.trajMeasure` with standard axioms only, and one adapted
harmonic-type family witnesses the composed impossibility end to end.

## P13 — certificate-guided weight search

**Hypothesis under attack.** The interesting quitting weights — occupants of
the cycle-existence hole, isolated-negative weights without repairs, and
above all a weight whose `F_ε` orbits have bounded total variation — are
findable by automated search *now*, because the wave's results turn every
boundary into a cheap exact certificate, where prior search code was general
and certificate-free.

**Finite/exact protocol.** Rational arithmetic throughout for decisions;
floats only for exploration. Search the affine gauge quotient (normalize
`d_i ∈ {−1,0,+1}`, unit scale; the invariant data is `B_ij = r_i({j}) − d_i`).
Escalating exact filters: (1) zero-solo — note the predicate is `≤ 0`, so
zero-diagonal tables belong to it; (2) period-one **complementary-row**
existence via the affine no-join LP per coordinate, followed by (2b) the
**admissibility stage** — the LP certifies a complementary row exists, which
is strictly weaker than the compiler's requirement; the isolated coordinate's
solo-weight sign / deleted survival must be checked separately, and the
two-player counterexample is precisely a weight where (2) passes and (2b)
fails; (3) singleton-LCP feasibility via
support-pattern enumeration; (4) fixed-period exact-cycle existence for small
periods via certified root-finding (the repo's dyadic-interval/Krawczyk
island is the intended certifier); (5) **lock-certificate search** — the
label-lock shape (a phase-value floor, a value pin, strict neighbour
inequalities) is a finite certificate for the all-periods no-cycle statement;
each certified hit occupies the hole. On filtered survivors: an
`F_ε`-orbit-variation profiler (bounded-variation candidates escalate toward
the orbit-side counterexample criterion; growth and handoff statistics feed
the lock/unlock dichotomy), and a punishment-floor refutation sweep (weights
where every stationary/cyclic/instant candidate payoff violates someone's
floor are mandatory relaxed-compiler test cases).

**Validation gate.** No sweep is trusted until every checker reproduces the
known suite: the FTV table admissible at `p = 1/2`; `G_ε` failing no-join at
every rate and every coordinate; the Q154 weight admitting relaxed cycles at
absorption `7/8` with no exact cycle; the two-branch counterexample landing in
the isolated-negative branch; the hostile table's punishment level at `−500`.
A checker that cannot fire on known positives is not evidence.

**What falsifies the idea.** If the gauge-reduced space at `n = 3` with small
rational entries contains no weight passing filters (1)–(4) beyond the known
family, tailored search adds nothing over analysis and the effort moves to
the compiler. A bounded-variation profile that dissolves under exact
recomputation falsifies the profiler's escalation rule, not the idea.

**What it does not establish.** Numerical bounded variation is never a
counterexample — only an escalation trigger toward the exact orbit-side
criterion. Lock certificates certify no-cycle, not nonexistence of
equilibria; occupants of the hole still have uniform payoffs unless the
orbit-side criterion also fires.

**Promotion criterion.** Promote a certified new hole occupant, a certified
bounded-variation candidate surviving exact recomputation, or the floor-refuted
test-case suite adopted by the relaxed-compiler row.

**Slice-two findings (2026-08-05).** Gate 27/27 before any sweep number. The
survivor taxonomy is the tool's first lesson: all eight random survivors at
denominator 2 have backward-distance bound **0** — exact-but-inadmissible
rows, the two-player-counterexample shape — while `G_ε` through the identical
pipeline correctly reports bound **1**. So genuine hole occupants are not
found by random small-denominator sampling (coverage ~1.8e-12); the next
sweeps must be **directed**: lock-certificate guided, LCP-guided, and the
queued **circulation-certificate mode** (the `L = 1` linear check per
support, then small-`L`) — plus the Q160-thread family's `(x, ε)` square as
the standing target. A real structural fact surfaced by a bug: a period-one
row with exactly one coordinate pinned pure decouples — `c_{−k} = 0` kills
every other player's value dependence, leaving independent univariate linear
equations with generic small-denominator exact roots. This shape is invisible
to the solo LP and to the certifier's corner analysis; only grid search sees
it. Worth a small Lean lemma (the pinned-pure decoupling), and it means
"exact period-one rows are generic" in a precise sense — admissibility, not
existence, is the discriminating filter at period one.

**Integration with the numerical-analysis intake (2026-08-05).** Filter (4)
— fixed-period exact-cycle decision — must **consume**
`Experiments/certsearch/krawczyk_cycle_certifier.py` (in flight from
the numerical-analysis source note §2), not rebuild it; slice two waits for it.
Two search modes join the design from the backward-error lens: **backward
distance** — for surviving weights, estimate the distance to the nearest
period-`L` exact-cycle stratum for small `L` (the per-player own-set shift of
§1 gives the cheap upper bound; the certifier refutes below); a weight at
uniformly positive distance from every low-period stratum is the
lens-theoretic form of a Q159 trap candidate, and the `d(ε,δ)`-conditioning
conjecture predicts its relaxed periods diverge. And **conditioning maps** —
log the interior-margin condition number along found relaxed cycles; the
backward condition number, the lock margin, and the weighted-gain weakness at
extreme hazards are one phenomenon in three lenses, so ill-conditioned rows
are where locks live and where certified arithmetic must be tightest.
