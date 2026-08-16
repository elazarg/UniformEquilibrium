# Experiment results

All results below are finite-model or interface results.  None is promoted to
the active proof tree, and none is counted as closure of a general analytic
atlas leaf.

Each result is reproduced by `python Experiments/Base/run_all.py`; its tracked
source, assumptions, and limitations are part of the durable record. Generated
logs and raw runs are not retained as evidence.

## E01 — jointly controlled finite-group lottery

Passed.  Finite-group addition produces a uniform signal against either one
controller's unilateral change, and uniform group signals encode rational
lotteries exactly.  A raw-action transition counterexample shows that the
continuation must factor through the protected signal.

## E02 — inhomogeneous hazard scheduler

Passed.  For a power schedule `alpha_t = t^-a`, useful order `k` can recur while
harmful order `m` is summable exactly when `m > k` permits
`1/m < a <= 1/k`.  Nonvanishing irreversible leaks remain fatal.

## E03 — path-complete Livsic account

Passed.  Exact rational cycle checking recovers the potential/cycle
alternative.  A lifted `(mode,state)` potential exists in an example with no
state-only potential, and bounded `O(sqrt(T))` reset debt is `o(T)`.

## E04 — Curry–Howard atlas analyzer

Passed against the current atlas.  It found fourteen constructors, one semantic
terminal, and thirteen nonsemantic forms.  Every current nonsemantic
reconstruction type is conclusion-bearing; this is a progress-obligation map,
not thirteen concrete eliminators.

## E05 — arc orientation

Passed.  A rational analytic coordination family has pure and fully mixed
equilibrium arcs with different limiting supports.  Arc selection is therefore
a real variable.  The toy orientation determinant is not a stochastic-game
equilibrium-index theorem.

## E06 — owner monodromy

Passed.  A mixed-owner cycle has zero aggregate holonomy but typed holonomy
`(1,-1)`, producing nontrivial deck translation in finite covers.  This
formalizes custody failure but does not equate it with strategic harmfulness.

## E07 — Kelly debt boundary

Passed.  The optimal iid Bernoulli likelihood bankroll has expected log growth
`KL(1/2+p || 1/2) = 2p^2 + O(p^4)`.  It cannot pay debt linear in `p`; quadratic
debt is the critical scale.

## E08 — causal states and synchronization

Passed.  A three-hidden-state chain produces indefinitely many beliefs already
distinguished by one-step prediction.  The subset construction also recovers
the Cerny `(n-1)^2` shortest synchronization lengths through seven states.

## E10 — exact small-game census

Passed.  All 6,561 two-player `2x2` games with payoffs in `{-1,0,1}` were
classified exactly.  Removing response degeneracies leaves only the expected
unique-pure, unique-mixed, and two-pure-plus-mixed patterns.  This is a census
pipeline dry run, not an atlas census.

## E11 — continuous-time resolvent

Passed.  For `P_lambda = I + lambda A`, the reduced Abel value converges exactly
to `(I-A)^-1 g`, the rate-one exponentially killed continuous-time resolvent.
The calculation transfers occupation values, not strategic credibility.

## E12 — collateral account

Passed.  Exhaustive finite paths verify that minimum escrow is maximum prefix
drawdown.  For increments of a bounded pathwise potential it is bounded sharply
by the potential oscillation.  Expected-drift certificates need an additional
probabilistic-solvency interface.

## E14 — approximate predictive compression

Passed.  A contractive two-state predictor was quantized to 33 memory states
and retained a horizon-independent error bound over 257 initial beliefs and 500
steps.  Conditioning on a rare observation amplified a tiny belief error by
nearly one thousand, proving that transition mixing alone is insufficient.

## E15 — random-phase sigma-delta lottery

Passed.  One uniform phase realized a 400-step rational rate stream with exact
one-time marginals and pathwise prefix discrepancy below one.  Once the phase
is public, however, future pulses are perfectly predictable; causal refresh is
the unresolved strategic requirement.

## E16 — Abel boundary layer and retargeting

Passed.  A one-live-state Markov reward model has Abel endpoint `23/36`, while
every fixed positive-hazard policy has Cesaro target `5/4`.  Horizon-dependent
hazards preserve the boundary layer but are not a uniform policy.

## E17 — multiscale filter bank

Passed.  A logarithmically slow scale handles every fixed finite collection of
polynomial access orders and inverse-power monitoring bills.  It does not
amplify an `exp(-1/lambda^2)` event with the same epochs, fencing the required
rate-class assumption.

## E18 — transition algebra

Passed.  Exact rational closure distinguishes a scalar identity algebra, a
four-dimensional cyclic algebra, a four-dimensional nilpotent/transient
algebra, and a generic full `3x3` matrix algebra.  Their commutant dimensions
are respectively 9, 4, 4, and 1.  Actual endpoint-operator extraction and a
general Jacobson-radical computation remain open.

## E19 — player representations

Passed.  Reynolds averaging gives the common-welfare projection, while the
stabilizer of a distinguished deviator splits player space into deviator,
opponent-average, and opponent-standard channels.  Pure transfer obstructions
can be invisible in the trivial representation without thereby being proved
harmless.

## E20 — cyclic Fourier Abel/Cesaro modes

Passed.  For a slow cyclic kernel `P_lambda=(1-c lambda)I+c lambda C`, every
nontrivial character has a nonzero Abel boundary-layer limit but vanishes in
the Cesaro limit of each fixed positive-speed policy.  This is a modewise
retargeting calculation, not a general-game diagonalization.

## E22 — stationary Hodge currents

Passed.  Exact rational linear algebra decomposes a stationary edge field into
an orthogonal gradient and a divergence-free cycle current.  A biased
three-cycle carries net current `1/9` and entropy production `log(2)/3`.
Owner-valued currents can cancel in aggregate while remaining nonzero in each
owner channel, so scalar circulation loses strategically relevant custody.

## E23 — adiabatic Markov tracking

Passed.  In a moving two-state chain, a target varying on the logarithmic time
scale is tracked when the spectral gap closes as `t^-0.4`: the error falls to
about `1.6e-5` by time one million.  At the critical `t^-1` gap, the error
stays near `0.127`.  Adiabatic tracking is therefore a genuine positive regime,
but it requires a quantitative separation between target drift and mixing.

## E24 — metastable Schur confluence

Passed.  Exact rational Schur-complement elimination of two fast transient
states gives the same effective generator and effective reward whether they
are eliminated jointly, first-to-second, or second-to-first.  The calculation
isolates an order-independent local coarse-graining primitive; nonlinear
strategic selection and credibility are not included.

## E25 — thermal equilibrium selection

Passed.  Scalar logit fixed-point computations in the Big Match and Sorin's
absorbing game show that the ratio of temperature to discount selects different
stationary branches.  Very cold regularization recovers the discounted targets,
whereas warmer `tau=sqrt(lambda)` scaling selects radically different limits.
Thermal smoothing is consequently an arc selector, not a universal cure for
the Abel/Cesaro target gap.

## E26 — entropy production versus linear debt

Passed.  Near detailed balance in a biased cycle, stationary current and a
current-sensitive payoff loss are first order in the bias, while entropy
production and one-step relative entropy are second order.  The tilted pressure
has the expected quadratic germ `log cosh(theta)`.  Entropy production is a
useful monitor, but by itself cannot finance a generic linear credibility debt.

## E27 — common reversible Dirichlet geometry

Passed.  Two distinct rational kernels with a common uniform invariant law
satisfy exact Dirichlet identities and common Poincare bounds, exhaustively
checked on 625 integer-valued functions.  Their shared coercive geometry gives
uniform `L2` contraction under arbitrary switching.  This is a robust positive
subclass, although general controlled kernels need not share an invariant law
or reversibility.

## E28 — finite-controller cycle verifier

Passed.  Exact cycle enumeration finds a reachable positive-mean deviation
cycle in the unsafe product.  In the safe product, the maximum simple-path
potential satisfies every edge inequality and bounds all accumulated gain.
This gives a short checker for a fixed deterministic controller while leaving
the controller producer outside the theorem.

## E29 — exact-rate memory blow-up

Passed.  All 1,259 reduced rates with denominator at most 64 have minimum
deterministic recurrent cycle length exactly equal to their denominator.  The
balanced construction attains prefix discrepancy below one.  Along rates
`1/2^k`, explicit phase memory is exponential in the binary input length even
though the target rate has a tiny description.

## E30 — contextual selector synthesis contains SAT

Passed.  For every subset of the eight signed three-variable clauses, the
assignments satisfying the formula are exactly the selectors making all clause
cycles nonpositive.  A true literal contributes `-3` and a false literal `+1`.
Thus verification is linear in the displayed cycles, while unrestricted
contextual selector synthesis contains a 3-SAT core.  This is not asserted as
a hardness classification of the full conjecture.

## E31 — commit/reveal timing

Passed.  Simultaneous XOR has zero bias against either one deviator, whereas a
public sequential last mover achieves bias `1/2`.  Ideal commitments recover
the simultaneous guarantee only with enforced or simultaneous opening;
sequential opening with selective abort again permits bias `1/2`.  Binding,
hiding, and guaranteed opening are separate resources.

## E32 — threshold secret sharing

Passed.  Exact enumeration over `GF(5)` verifies perfect one-share privacy for
a 2-of-3 Shamir scheme and reconstruction from every pair.  Once all shares are
public, each transcript determines the secret.  Private observation is the
resource producing the secret phase; the algebra alone does not provide it.

## E33 — live entropy budget

Passed.  A deterministic 24-stage stream generated by a hidden three-bit seed
has exactly three total bits of conditional entropy.  Revealing the seed makes
the total zero, while one fresh honest simultaneous XOR contribution supplies
24 bits over 24 stages.  Deterministic expansion can redistribute seed entropy
but cannot amplify it information-theoretically.
