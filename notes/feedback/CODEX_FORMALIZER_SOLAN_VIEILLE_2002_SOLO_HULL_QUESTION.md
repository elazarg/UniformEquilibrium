# Solan–Vieille's singleton-hull exclusion: a supplied-proof question

## Source and scope

Eilon Solan and Nicolas Vieille, *Quitting games — An example*, International
Journal of Game Theory 31 (2002), 365–381, assert in the Introduction on page
366 that their four-player example has no equilibrium payoff in the convex
hull of its singleton reward vectors. The primary source is the
[author-hosted journal PDF](https://www.math.tau.ac.il/~eilons/notequitting4.pdf).

The question below requests a rigorous proof or a precise accessible proof
reference for that unrestricted payoff-target assertion. The source argument
currently located establishes exclusions for stationary and uniformly
near-Continue profiles, but a reduction from arbitrary behavioral equilibrium
approximants to those classes has not been located. This records a missing
supplied reduction, not a refutation of the published assertion or a claim
that it is a new open problem. An older preprint path-classification lead was
inaccessible and is not being treated as supplied proof mathematics.

## The concrete game

There are four players, labeled 0, 1, 2 and 3. At each live stage they choose
Continue or Quit simultaneously. The first nonempty quitting coalition S
absorbs the game with reward r(S). The live reward and the reward on infinite
nontermination are zero. Coordinates below follow the displayed player order.

| S | r(S) |
| --- | --- |
| {0} | (1, 4, 0, 0) |
| {1} | (4, 1, 0, 0) |
| {2} | (0, 0, 1, 4) |
| {3} | (0, 0, 4, 1) |
| {0, 1} | (1, 1, 1, 1) |
| {0, 2} | (1, 1, 1, 0) |
| {0, 3} | (1, 0, 1, 1) |
| {1, 2} | (0, 1, 1, 1) |
| {1, 3} | (1, 1, 0, 1) |
| {2, 3} | (1, 1, 1, 1) |
| {0, 1, 2} | (1, 0, 0, 0) |
| {0, 1, 3} | (0, 1, 0, 0) |
| {0, 2, 3} | (0, 0, 0, 1) |
| {1, 2, 3} | (0, 0, 1, 0) |
| {0, 1, 2, 3} | (−1, −1, −1, −1) |

Let H be the convex hull of the four singleton rows. Equivalently, H consists
of the vectors

    (λ₀ + 4λ₁, 4λ₀ + λ₁, λ₂ + 4λ₃, 4λ₂ + λ₃),

where each λᵢ is nonnegative and λ₀ + λ₁ + λ₂ + λ₃ = 1.

## The mathematical question

For a behavioral profile σ, write g_N(σ) for its expected N-stage average
payoff. A unilateral replacement σ[i ← τᵢ] may use any behavioral strategy,
including history-dependent strategies and Never.

Supply a proof, or a precise accessible proof reference, that **no fixed
v ∈ H** satisfies the following condition:

For every ε > 0, there exist a behavioral profile σ and a threshold N₀ such
that, for every horizon N ≥ N₀, every player i and every unilateral behavioral
replacement τᵢ,

    |g_N(σ)ᵢ − vᵢ| ≤ ε,
    g_N(σ[i ← τᵢ])ᵢ ≤ g_N(σ)ᵢ + ε.

The target v is fixed before all accuracy quantifiers. The profile and
threshold may depend on ε. Neither stationarity nor uniformly small quitting
probabilities may be assumed. Excluding those strategy classes alone does not
exclude targets delivered by other behavioral profiles.

An equivalent terminal formulation is available. Let Γ(σ) be the expected
reward at the first nonempty quitting coalition, with zero reward on Never.
For each v ∈ H, prove that there is an η > 0 such that every behavioral
profile σ satisfying

    Γ(σ[i ← τᵢ])ᵢ ≤ Γ(σ)ᵢ + η

for every player i and every behavioral replacement τᵢ has some coordinate i
with

    η ≤ |Γ(σ)ᵢ − vᵢ|.

The margin η may depend on v; a common positive margin over H is not
requested. The separation is non-strict, whereas the corresponding terminal
acceptance condition uses coordinate distance strictly less than η.

## Repository verification boundary

The literal table is `boundaryReward`
(`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`).
The source audit's `NoSoloHullUniformEquilibriumPayoffClaim`
(`Literature/future/SolanAndVieille2002a.lean`) is a proposition definition,
not a proof. The checked stationary and near-Continue exclusions do not
establish it.

The exact terminal reformulation follows from
`nonempty_quittingTerminalTargetRejectionWitness_iff`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`).
That theorem supplies an equivalence for a fixed target, not a rejection
witness for this table. The checked arbitrary uniform-payoff-to-terminal
acceptance reduction does not impose near-Continue hazards; this is the
specific supplied-proof step still needed for the proposed strategy-class
route.
