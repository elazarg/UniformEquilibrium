# Independent review of Items 5--6: gluing minors and weighted defect

Reviewer: `CODEX_MINER`  
Review tag requested by the intake: `HOOKE_GLUING_POTENTIAL`  
Date: 2026-08-26

Source reviewed: Items 5 and 6 of `../idea_derivations.zip`, against
[`CHATGPT_EXTERNAL__CONCRETE_NONLOCALITY_DERIVATIONS_INTAKE.md`](../notes/CHATGPT_EXTERNAL__CONCRETE_NONLOCALITY_DERIVATIONS_INTAKE.md).

## Separate verdicts

- **Item 5, product-root gluing minors: PASS as ordinary mathematics.**  The
  boundary support condition is essential and is stated; with it, all zero
  patterns, reconstruction, and uniqueness at every reached row are correct.
  The constants `1/4`, `1/2`, and `1/(2H)` are correct under the explicitly
  intended half-`L1` convention.  The finite chronology induction is exact.
  Two wording qualifications are needed for a formal statement: define the
  subprobability TV convention in (5.3), and say that roots after zero reach
  are deliberately nonunique.
- **Item 6, weighted cycle and defect: core mathematics PASS, statement/source
  audit REVISE.**  The SCC order, both signed potential increments, the
  `1/(2w_i)` constants, and the unrestricted behavioral consumer are correct.
  The empty-player global maximum `max_i E_i(w)` is not defined as printed;
  assume a nonempty player type or adjoin zero to the maximum.  Also say that
  all graph edges are off-diagonal, count `E_C` as undirected in the
  spanning-tree paragraph, and retract the claim that the abstract
  cycle/gauge recognition theorem is absent: checked generic versions already
  exist.  The actual-coefficient wrapper and robust weighted-curl estimate
  remain useful.

Neither item by itself carries payoff/cap/source annotations through the
gluing theorem or contracts the maintained hard residual.  I recommend no
export from this archive review.

## I. Item 5: exact product-law characterization

### I.1 Strictly positive case

For a positive law `p`, the zero minor based at `S \ {j}` gives

\[
 \frac{p(S\cup\{i\})}{p(S)}
 =\frac{p((S\setminus\{j\})\cup\{i\})}{p(S\setminus\{j\})}.
\]

Deleting the elements of `S` therefore makes the odds of adding `i`
independent of the background.  Hence

\[
 p(S)=p(\varnothing)\prod_{i\in S}r_i,
 \qquad r_i=\frac{p(\{i\})}{p(\varnothing)}.
\]

Normalization gives the displayed Bernoulli parameters
`x_i=r_i/(1+r_i)`.  Conversely, direct cancellation proves every minor is
zero.  This proof includes the one-free-coordinate and zero-free-coordinate
cases: their minor families are vacuous, as they should be.

### I.2 Boundary support and every zero pattern

For a product law, put

\[
 L=\{i:x_i=1\},\qquad U=\{i:x_i>0\}.
\]

A coalition has positive mass exactly when `L subset S subset U`.  Conversely,
if the positive support is exactly `[L,U]`, translating by `L` gives a
strictly positive law on the free cube `2^(U\L)`.  The positive theorem
applies to the minors whose bases and two toggled coordinates remain in that
free cube; forced coordinates are then set to one on `L` and zero outside
`U`.  This covers:

- `L=U`, including every deterministic coalition;
- all-zero and all-one Bernoulli vectors;
- one-dimensional faces, where any positive two-point law is Bernoulli; and
- the empty player type, where the unique law is mass one at `empty`.

The face hypothesis cannot be dropped.  On three players, the law assigning
mass `1/2` to `empty`, mass `1/2` to the grand coalition, and zero elsewhere
has **every** adjacent Boolean-square minor equal to zero, but its support is
not a Boolean face and it is not a product law.  Thus the archive correctly
keeps support and minors as separate requirements.

The reconstructed root is unique, including on the boundary, because

\[
 x_i=\sum_{S\ni i}p(S)
\]

is the `i`-th marginal of the supplied law.  In the face proof this is also
visible from the forced coordinates and the free odds ratios.

### I.3 Quantitative constants and convention

For `a,b,c,d in [0,1]`,

\[
 |ab-cd|\le |a-c|+|b-d|.
\]

Applying this once to each product in the minor gives exactly (4.1).  Hence
four coordinate errors bound the minor, proving the `L-infinity` constant
`1/4`.  With

\[
 d_{TV}(p,q)=\frac12\sum_S|p(S)-q(S)|,
\]

the same four errors are at most `2 d_TV`, proving (4.3) with constant `1/2`.
This convention agrees with the checked finite-PMF interface in
`MathUE/ProbabilityMassFunction/TotalVariation.lean`.

For equal-mass subprobabilities `m` and `Hq`, every coordinate is at most
`H`, so the scaled calculation is

\[
 |\mathcal M(m)|\le
 H\sum_{R\in\{S,Si,Sj,Sij\}}|m(R)-Hq(R)|
 \le 2H d_{TV}(m,Hq).
\]

Thus (5.3), `d_TV >= |Delta|/(2H)`, is correct for `H>0`.  Since the checked
`pmfTV` definition applies to probability laws rather than raw
subprobabilities, the archive should explicitly define the left side here as
half-`L1` on two fluxes of the same total mass.  At `H=0`, homogeneity (5.2)
is still literal but the divided estimate is intentionally absent.

The numerical example has minor `0.4^2-0.1^2=0.15` and therefore yields the
stated TV floor `0.075`.

### I.4 Unnormalized flux and finite chronology

The homogeneity identity

\[
 \mathcal M(Hp)=H^2\mathcal M(p)
\]

is exact.  In Theorem 6.1, nonnegativity and
`sum_S m_t(S)=H_t` make `m_t/H_t` a probability law whenever `H_t>0`.
The face/minor theorem then gives a unique hazard vector at that reached row.
The identity

\[
 H_{t+1}=m_t(\varnothing)
\]

is precisely the one-step all-Continue survival recursion.  Induction from
`H_0=1` proves every stage flux in (6.4).

If `H_t=0`, nonnegativity and the total-mass equation force every `m_t(S)=0`,
and conservation forces `H_(t+1)=0`.  Any root can therefore be installed at
that unreachable row.  Existence remains exact, but uniqueness holds only at
positive-reach rows; this should be stated rather than silently treating an
unreachable root as identified by zero flux.

The current Lean correspondence is exact:

- `Math.PMFProduct.coalitionMass` and `sum_coalitionMass` are in
  `MathUE/PMFProduct/CoalitionMass.lean`;
- `rootOfHazard` realizes every `[0,1]` hazard vector as a literal `PMF Bool`
  root in `UniformEquilibrium/Quitting/Bellman/Finite/HazardRowBridge.lean`;
- `quittingRootSequenceProfile` turns the reconstructed rows into one
  history-independent behavioral chronology in
  `UniformEquilibrium/Quitting/Root/SequencePayoff.lean`.

This reconstructs only the supplied finite probability prefix.  It neither
chooses the continuation after the prefix nor glues payoff, Nash, cap, floor,
or source labels; the archive's boundary section correctly makes that
nonclaim.  A narrow search found no existing Boolean-face/minor
characterization or finite-flux reconstruction declaration in the current
tree.

## II. Item 6: positive symmetrizability cycle test

### II.1 Exact algebra, support, and uniqueness

All coefficient and influence-graph statements must be read for **distinct**
players.  The diagonal coefficient never occurs in

\[
 g_i(S)=a_i+\sum_{j\in S}M_{ij},\qquad i\notin S,
\]

and the checked `QuittingAffineInfluenceEdge` is explicitly off-diagonal.

Positive symmetry implies reciprocal support with the same sign.  On a
reciprocal edge,

\[
 \frac{w_j}{w_i}=\rho_{ij}:=\frac{M_{ij}}{M_{ji}}>0.
\]

Products telescope around closed walks.  Conversely, unit product on cycles
makes the path product from a chosen root independent of path and constructs
the weights.  Connectivity of the reciprocal support graph follows because
the argument is taking place inside an SCC after reciprocal support has been
imposed.  Comparing two weight systems along paths proves uniqueness up to
one positive scalar on each SCC, including a singleton SCC.

The spanning-tree reduction is also correct, provided `E_C` denotes the
number of **undirected reciprocal pairs**.  It leaves
`|E_C|-|C|+1` fundamental equations; a complete four-vertex reciprocal graph
has `6-4+1=3`.  If directed arcs were counted, the printed number would be
wrong, so the convention should be made explicit.

The rational matrix (3.1) is correct: `w=(1,2,3)` makes the three weighted
pair coefficients respectively `2`, `6`, and `3`, and its cycle ratio is one.

### II.2 Novelty qualification

The quitting-specific coefficient recognition wrapper is not currently a
named declaration.  The underlying cycle/gauge theorem, however, is already
checked abstractly.  In particular:

- `Maths.MaxAffineTransport.cycleProduct_eq_one_iff_exists_slopeGauge_of_stronglyConnected`
  in `MathUE/DirectedTransport/MaxAffine/Slopes.lean` gives unit
  multiplicative holonomy iff a positive gauge exists; and
- `hasTrivialCycleLabels_iff_hasSCCUnitPotentials` and
  `existsUnique_normalizedUnitPotential_of_trivialCycleLabels` in
  `MathUE/DirectedTransport/NormalForms.lean` and
  `MathUE/DirectedTransport/PotentialRigidity.lean` give the componentwise
  potential and normalized uniqueness forms.

Thus Section 2 is a correct, useful adapter from reciprocal coefficients to
the checked componentwise weighted-potential hypothesis, but not a fresh
abstract multiplicative cycle theorem.  The intake/source wording should be
repaired accordingly.

## III. Item 6: robust weighted defect

### III.1 SCC orientation and cross-component terms

The archive uses the same correct orientation as the checked source: an edge
`j -> i` means `j` influences the membership gain of `i`.  A source-to-sink
topological order therefore has these properties:

- earlier selected players contribute exactly to
  `theta_i=a_i+sum_(j in S_<C) M_ij`;
- current-component interactions enter the quadratic block potential; and
- a later player cannot have nonzero `M_ij` for current `i`, because that
  would be a backward condensation edge.

After a component is selected, later choices cannot change its membership
gains.  One-way cross-component coefficients are consequently handled
exactly, not charged to the curl budget.

### III.2 Signed increment audit and constants

For

\[
 e_{ij}=w_iM_{ij}-w_jM_{ji},\qquad
 \psi_{\{i,j\}}=\frac{w_iM_{ij}+w_jM_{ji}}2,
\]

one has both `e_ji=-e_ij` and

\[
 \psi_{\{i,j\}}=w_iM_{ij}-\frac12e_{ij}.
\]

If `i` is outside the maximizing block `T`, its insertion increment is

\[
 w_i g_i(S)-\frac12\sum_{j\in T}e_{ij}\le0.
\]

Therefore

\[
 g_i(S)\le\frac1{2w_i}\sum_{j\in T}e_{ij}
 \le \frac1{2w_i}\sum_{j\in C(i),j\ne i}|e_{ij}|=E_i(w).
\]

If `i` is in `T`, maximality against deletion makes the insertion increment
from `T\{i}` nonnegative:

\[
 w_i g_i(S\setminus\{i\})
 -\frac12\sum_{j\in T\setminus\{i\}}e_{ij}\ge0.
\]

Hence

\[
 -g_i(S\setminus\{i\})
 \le-\frac1{2w_i}\sum_{j\in T\setminus\{i\}}e_{ij}
 \le E_i(w).
\]

These are exactly the outsider-join and member-delete regrets.  The signs and
the factor `1/2` in (4.2) are correct; no extra SCC-cardinality factor is
missing.  The perturbation in Section 6 likewise has only
`e_13=epsilon`, `e_31=-epsilon`, giving
`E_1=|epsilon|/2`, `E_3=|epsilon|/6`, and `E_2=0`.

### III.3 Empty and singleton boundaries

For a one-player game, the unique SCC has no pair defect, so `E_i=0`.  The
block potential compares `0` with `w_i a_i`: it selects the singleton when
`a_i>=0` and the empty set when `a_i<=0` (either at equality).  This is the
exact singleton/All-Continue sure-exit dichotomy.

For a nonempty player type, the constructed exit coalition itself may be
empty.  The playerwise outsider bounds then say every solo quitting gain is
at most `E_i`, which is exactly the approximate all-Continue condition.  No
absorption assumption is needed.

For an **empty player type**, Theorem 4.1's playerwise inequalities are
vacuous and the empty pure profile is exact, but the printed real number

\[
 E(w)=\max_i E_i(w)
\]

does not exist under the ordinary maximum notation.  Repair this either by
assuming `[Nonempty I]` for (4.3)--(5.4), or, preferably, defining

\[
 E(w)=\max(\{0\}\cup\{E_i(w):i\in I\}),
\]

which is zero at the empty boundary and unchanged otherwise because every
`E_i` is nonnegative.

### III.4 Unrestricted behavioral deviations and consequences

The appropriate checked consumer is the full epsilon characterization
`isεAsymptoticNash_pureSetRoot_iff` in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.  Its reverse direction
bounds an arbitrary unilateral behavioral deviation by the two terminal
membership toggles.  Thus the constructed pure stationary profile really has
terminal exploitability at most `E(w)`; this is not a stationary-deviation
inference.  At zero error,
`isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet` and
`isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet` give the exact
and uniform conclusions.

The finite-repetition proof of Corollary 5.2 is valid: if `E(w^n)->0`, one of
the finitely many selected coalitions repeats, and its fixed toggle gains are
nonpositive in the limit.  Corollary 5.3 also has the correct direction: a
full unrestricted terminal gap `gamma` applies to the constructed pure
profile, while that profile's exploitability is at most `E(w)`, so
`E(w)>=gamma` and some row has absolute weighted defect at least
`2 gamma w_i`.

The exact zero-defect producer is already checked in
`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`
and was independently reviewed in
[`CHATGPT_EXTERNAL__COMPONENTWISE_WEIGHTED_POTENTIAL_QUITTING__BY_CODEX_MINER.md`](CHATGPT_EXTERNAL__COMPONENTWISE_WEIGHTED_POTENTIAL_QUITTING__BY_CODEX_MINER.md)
and
[`CHATGPT_EXTERNAL__COMPONENTWISE_WEIGHTED_POTENTIAL_QUITTING__BY_CODEX_EULER.md`](CHATGPT_EXTERNAL__COMPONENTWISE_WEIGHTED_POTENTIAL_QUITTING__BY_CODEX_EULER.md).
Item 6's genuinely additional content is therefore the raw-coefficient cycle
adapter and, especially, the nonzero robust defect estimate.  It remains a
special-class diagnostic/producer and does not by itself consume the general
quitting hard residual.

## Required repairs before either item is transcribed as a packet

1. In Item 5, define subprobability `d_TV` in (5.3) as half-`L1` on the two
   equal-mass fluxes, and state reached-root uniqueness versus arbitrary roots
   after `H_t=0`.
2. In Item 6, restrict all influence edges and coefficient equations to
   distinct players.
3. Define the empty-index maximum in (4.3), or add a nonempty-player
   hypothesis to the global exploitability and infimum statements.
4. Say `E_C` counts undirected reciprocal pairs in the spanning-tree test.
5. Replace the abstract novelty claim for Theorem 2.1 by the exact generic
   Lean correspondence above.  Preserve novelty only for the coefficient
   wrapper and robust weighted-curl bound.
6. Keep the probability-gluing theorem separate from payoff/source gluing,
   and keep the robust potential theorem separate from any claim that the
   universal hard residual is affine or approximately symmetrizable.

With those local repairs, both mathematical derivations are sound at their
stated internal scope.  No export recommendation is made here.
