# Nonlocality Technique Catalogue

This is an enumeration of reusable lenses, not a list of claims about quitting
games. The identifiers are intended to remain stable enough to cite from an
owned research note.

The recurring obstruction has several forms: dependence on arbitrarily late
stopping times, compact semantic limits not realized by one behavioral
profile, and locally compatible witnesses that do not coexist on one literal
source or reached history. Mathematics and physics usually respond by
enlarging the state, identifying the defect of compactness, or replacing the
desired construction by a global invariant or dual certificate.

## I. Make the evolution local in a larger state

### NL-01 — Markovianization by state augmentation

Adjoin enough memory to make the next transition depend only on the current
augmented state. Possible coordinates include a complete stopping law, its
posterior survival state, a cap witness, a paid row, a curvature square, and a
literal continuation suffix.

Physics analogue: enlarge phase space or introduce auxiliary degrees of
freedom so an effective memory equation becomes local.

Main danger: recording the entire original strategy makes the reformulation
tautological. A useful augmentation must have a closed transition rule and a
consumer that uses only its packaged coordinates.

### NL-02 — Localization by extension

Represent a nonlocal problem as the boundary trace of a local problem with an
extra variable. The extra coordinate may represent age, remaining stopping
time, a selector, or a scale parameter.

Physics analogue: bulk/boundary formulations and auxiliary dimensions.

Main danger: the extended local object may have no realizable projection back
to an actual behavioral profile.

### NL-03 — Hidden-variable and auxiliary-field linearization

Introduce selectors or latent variables under which a nonlinear envelope or
mixture becomes affine, then retain the posterior state required to recover
the original semantics.

Physics analogue: Hubbard--Stratonovich variables and latent-field
representations.

Main danger: fresh rowwise randomization is not the same as a whole-strategy
mixture. The hidden variable must respect the game's actual information and
randomization structure.

### NL-04 — Projective and inverse-limit construction

Build compatible finite-horizon or finite-prefix objects and pass to a global
object through an inverse-limit theorem. Compatibility, rather than separate
existence at every horizon, is the decisive hypothesis.

Physics analogue: consistent finite-volume states and thermodynamic limits.

Main danger: profitable deviations can escape beyond every fixed horizon, so
ordinary diagonal compactness without a uniform tail condition is inadequate.

## II. Understand failure of compactness

### NL-05 — Tightness and uniform integrability

Prove that stopping mass, payoff mass, or witness mass cannot escape to late
times. Tightness turns weak convergence of laws into convergence of the
quantities used by the cap.

Physics analogue: infrared control and removal of a large-volume cutoff.

Main danger: tightness of the prescribed terminal law need not control the
best-response witness law.

### NL-06 — Defect measures and boundary variables

When convergence loses information, package the loss as an explicit positive
measure or boundary coordinate: mass at `Never`, a cap jump, a disappearing
atom, or an unobserved continuation port.

Physics analogue: radiation fields, soft modes, boundary charges, and anomaly
terms.

Main danger: naming a defect is useful only if it obeys a transport identity or
has a consumer.

### NL-07 — Concentration--compactness

Classify every noncompact sequence into compactness, concentration, splitting,
or escape. In the present temporal setting the relevant profiles may separate
into bounded stopping clocks, late clocks, and a `Never` component.

Physics analogue: bubble or scattering-channel decomposition.

Main danger: several scales may interact through simultaneous quitting, so a
profile decomposition needs a theorem controlling cross-scale payoff terms.

### NL-08 — Relaxation and recovery sequences

First work in a compact relaxed carrier of semantic or measure-valued objects.
Then characterize which relaxed points are realized exactly and which admit
actual recovery sequences preserving the required cap and provenance data.

Physics analogue: effective descriptions whose states must be lifted back to
microscopic configurations.

Main danger: a recovery sequence for prescribed payoffs may fail to recover
the unrestricted best-response envelope.

### NL-09 — Compensated compactness

Combine two weakly convergent quantities using an additional conservation or
orthogonality identity to obtain strong convergence of their product or
pairing.

Physics analogue: conservation laws suppressing otherwise uncontrolled
oscillations.

Potential target: couple terminal-law convergence with an exact debt, flux, or
Bellman identity so cap-relevant pairings converge despite clock diffusion.

## III. Transport global information through chronology

### NL-10 — Cocycles, transfer operators, and holonomy

Find a quantity with an exact composition law under prefixing. Debt scaling,
shifted witness differences, and curvature transport are examples of the
desired algebraic form.

Physics analogue: transfer matrices, Wilson lines, and transported charges.

Main danger: a multiplicative cocycle may decay to zero. A useful passport
needs normalization, renewal, or a quantized alternative preventing indefinite
loss.

### NL-11 — Gluing and descent

Treat local witnesses as charts and ask for explicit compatibility data that
make them restrictions of one global profile or one reached chronology.

Physics analogue: patching gauge fields and checking transition-function
consistency.

Potential target: formalize source provenance as a genuine descent datum,
rather than as equality of player labels or terminal laws.

Main danger: pairwise compatibility need not imply global compatibility.

### NL-12 — Renewal, regeneration, and inducing

Find an actually reached state at which the construction restarts with the
same quantitative passport. Work on return blocks rather than individual
dates.

Physics analogue: Poincare sections and repeated scattering cells.

Main danger: a semantic port may not be an actual reached profile, and a raw
quantity may shrink at every restart.

### NL-13 — Martingales, optional stopping, and flux accounts

Turn an ex ante gain into a sum or conditional gain on reached histories.
Preserve live mass explicitly rather than dividing by a possibly vanishing
reach probability.

Physics analogue: conserved probability currents and flux through a surface.

Main danger: optional-stopping hypotheses and uniform integrability cannot be
assumed when stopping times escape.

### NL-14 — Occupation measures and flow conservation

Encode a chronology by the mass assigned to states, actions, terminal labels,
and transitions. Exact Bellman equations become linear flow constraints;
source matching becomes conservation at entrances and exits.

Physics analogue: currents on a network and path-integral occupation weights.

Main danger: a feasible relaxed flow need not decompose into admissible product
behavioral paths with the required provenance.

## IV. Replace construction by a global certificate

### NL-15 — Convex duality and separation

If a desired chronology does not exist, separate the feasible set from its
target and interpret the dual functional as a new invariant, contradiction,
or counterexample certificate.

Physics analogue: Legendre duality and effective actions.

Potential target: a dual of source-matched exact-flow feasibility rather than
another primal packet constructor.

Main danger: the relevant feasible set may be nonconvex because product
behavior and unilateral deviations are coupled.

### NL-16 — Minimax and saddle-point enlargement

Exchange construction of one profile with control of a worst deviation after
proving the hypotheses of an appropriate minimax theorem. Mixed laws or
occupation measures may convexify one side.

Physics analogue: variational principles and adversarial effective energies.

Main danger: supremum, limits, conditioning, and behavioral strategy selection
do not commute automatically.

### NL-17 — Monotonicity, Lyapunov functions, and entropy production

Find a quantity that strictly decreases under every unresolved transition or
has a rigid equality case. Finite support rank is preferable to unquantized
real descent when it can be regenerated.

Physics analogue: free energy, entropy production, and c-theorems.

Main danger: real-valued descent can be Zeno, and support rank is not monotone
if new debtor coordinates can appear.

### NL-18 — Topological degree, index, and parity

Use a global invariant to force a fixed point, cycle, or branch crossing even
when no continuous selector exists.

Physics analogue: index theorems, winding numbers, and anomaly matching.

Main danger: topological existence of a root does not give literal source
provenance or unrestricted behavioral optimality.

## V. Separate and recombine scales

### NL-19 — Renormalization and block dynamics

Replace many small transitions by an effective block, retaining only variables
whose influence survives at the next scale. Cumulative charge is an example:
many small absorbing edges can form one uniformly proper block.

Physics analogue: renormalization-group blocking.

Main danger: the effective block may lose labels, source anchors, or exact
product structure.

### NL-20 — Spectral, generating-function, and Tauberian methods

Encode a stopping law by a generating function or transform. Late-time escape
then becomes behavior near a distinguished frequency or boundary point.

Physics analogue: propagators and zero-frequency infrared modes.

Potential target: quantify when cap witnesses can move to infinity while
prescribed payoffs and debt remain stable.

Main danger: the cap is a supremum over stopping plans, not a linear transform,
so a spectral representation still needs an optimization theorem.

### NL-21 — Multiscale profile decomposition

Extract clocks at separated temporal scales and compute the limiting game
between those scales. A finite hierarchy may replace one unavailable compact
limit.

Physics analogue: hard, soft, and collinear mode separation.

Main danger: there is no prior bound on the number of relevant scales.

### NL-22 — Decoupling and finite-influence estimates

Prove that sufficiently late changes have a quantitatively small effect under
explicit reach, hazard, or reward hypotheses.

Physics analogue: clustering and finite-propagation bounds.

Main danger: unconditional finite-horizon control is false; any valid estimate
must expose the tail parameter that pays for decoupling.

## VI. Regularize carefully

### NL-23 — Cutoff, discount, and vanishing-regularization limits

Solve a finite-horizon, discounted, perturbed, or strictly proper game and
remove the regulator using estimates uniform in the regulator.

Physics analogue: lattice, mass, volume, and frequency cutoffs.

Main danger: every finite truncation can be stable against its visible quit
times while a profitable witness sits immediately beyond the horizon. A
nonuniform limiting argument proves nothing about the original cap.

### NL-24 — Generic perturbation and transversality

Break ties or degenerate intersections, prove a statement for generic tables,
and control what survives when the perturbation vanishes.

Physics analogue: symmetry-breaking fields and generic regularization.

Main danger: the uniform-equilibrium target and unrestricted cap must remain
stable as the perturbation disappears; generic uniqueness alone is not a
consumer.
