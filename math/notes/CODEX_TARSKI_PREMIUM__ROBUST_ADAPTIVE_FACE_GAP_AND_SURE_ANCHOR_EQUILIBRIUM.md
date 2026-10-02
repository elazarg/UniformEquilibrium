# Robust adaptive-face obstruction with a nearby sure-anchor equilibrium

Author: CODEX_TARSKI_PREMIUM.

Ordinary mathematics. This is a short composition, not a new root-finding
mechanism or a separately proposed existence class. The source all-face
proof remains unchanged in
[the adaptive-face note](CODEX_TARSKI_PREMIUM__ADAPTIVE_FACE_PRESERVING_EXTENSION_OBSTRUCTION.md).

Let r* be that note's full table, Never zero:

    r*_0(S)=1 if 0∈S, and 2·1_{2∈S} otherwise;
    r*_1(S)=(2·1_{0∈S}−1)·1_{1∈S};
    r*_2(S)=(2·1_{1∈S}−1)·1_{2∈S};
    r*_3(S)=1_{3∈S}.

Its actual singleton vector is (1,−1,−1,1). Write c>0 for the proved
constant satisfying E_(r*)(μ)+E_(r*^(−d))(μ_−d)≥c for every actual
independent behavioral profile and every omitted player. All caps here
are against unrestricted behavioral deviations.

## 1. Whole-strategy reward robustness

Put δ=max_(S,i)|r_i(S)−r*_i(S)|, and keep Never zero. For EVERY actual
profile and EVERY unilateral replacement, the terminal payoff changes by
at most δ: the same outcome law is evaluated against two reward tables
at uniform distance δ. Taking suprema gives |B_i^r−B_i^(r*)|≤δ, so

    |E_r(μ)−E_(r*)(μ)|≤2δ.

The same bound applies to every literal three-player restriction. Hence

    E_r(μ)+E_(r^(−d))(μ_−d)≥c−4δ.                   (1)

In particular δ<c/8 retains the common all-face floor c/2. No compactness,
equilibrium selection, or restriction of the deviation class is used.

## 2. A simultaneous nearby mixed root

Let A={0,1,2} and q∈[1/4,3/4]^3. For each i∈A define Q_i(r,q) and
C_i(r,q) as its expected reward when 3 surely quits at date zero, the
other two active players independently quit with their q_j, and i
respectively Quits or Continues. Both are finite multilinear expectations
over coalitions containing 3. Set Δ_i=Q_i−C_i.

At r*, the three gaps are (1−2q_2,2q_0−1,2q_1−1). Thus the permuted
field F=(Δ_1,Δ_2,−Δ_0) is exactly (2q_0−1,2q_1−1,2q_2−1).
Each Q_i and C_i changes by at most δ, so each field coordinate changes
by at most 2δ uniformly on the entire box. At δ<1/8 its lower and upper
faces retain strict opposite signs, since the original face values are
−1/2 and 1/2. Rectangular Poincare–Miranda gives one INTERIOR q with all
three gaps zero, simultaneously. No independent scalar choices are made.

Prescribe player 3 Quit0 surely and every active i Quit0 with probability
q_i and Never otherwise. For an active deviation the anchor still quits
at zero; its complete response problem is exactly Q_i versus C_i. The
vanishing gaps therefore give zero full debt to all three active players.

## 3. The anchor's complete Continue cap

Put C=∏_(i∈A)(1−q_i)≤27/64. Let w(S) be the active product probability
of the date-zero quitting set S⊆A. Player 3's prescribed payoff is

    Q_3=Σ_(S⊆A) w(S) r_3(S∪{3})≥1−δ.

Its pure Never payoff and every pure strictly positive finite-time payoff
are, respectively,

    W_3=Σ_(∅≠S⊆A)w(S)r_3(S),
    L_3=W_3+C r_3({3}).

These formulas are exact: if no active player quits at zero, all three
have chosen Never. Therefore W_3≤δ and L_3≤C+δ≤27/64+δ. For δ<1/8,
both are strictly less than Q_3≥1−δ. Every behavioral replacement is a
mixture of Quit0, later finite times, and Never, so B_3=Q_3. This checks
the deleted-anchor path rather than presuming it absorbs immediately.

The profile is exact terminal Nash. It supplies a uniform-equilibrium
payoff as well: active deviations absorb at zero, and an anchor deviation
conditional on Continuing at zero has finite-average upper payoff at most
C+δ (up to the vanishing initial-stage convention), strictly below Q_3.
The prescribed profile absorbs at zero and its averages tend to its one
fixed terminal payoff vector. Mixing an immediate anchor Quit with any
such Continue plan cannot improve it at sufficiently long horizons.

## 4. Combined neighborhood and source scope

Choose ρ=min(c/8,1/8)>0. Every raw table r with ||r−r*||∞<ρ, with Never
still zero, has both the uniform all-face floor c/2 in (1) AND an actual
exact terminal/uniform equilibrium of the displayed sure3/mixed-active
form. This is a full open neighborhood in the 60 terminal reward
coordinates, not just a normalized subspace.

The reward estimate is already checked as
`abs_quittingTerminalExploitability_sub_le_of_reward_close` in
`Research/Quitting/TerminalExploitabilityRewardRobustness.lean`; the
global-infimum variant is not needed. The generic face-sign mechanism
already appears in `QuittingRationalStationaryFaceBox.exists_faceNumeratorZero`
in `UniformEquilibrium/Quitting/Classification/Existence/RationalStationaryFaceBox.lean`
and its centered certificate wrapper. Here the finite field and all full
caps are verified directly; no supplied stationary certificate is assumed.

The new combined statement is robustness of the adaptive unchanged-child
architecture obstruction INSIDE a neighborhood of explicitly solved
games. It is neither a positive-global-gap table nor a canonical
single-pivot result. Final packet assembly may replace the older deleted-3
suffix argument by the independently checked adjacent-deadline mass move;
the source notes themselves stay unchanged.

The EXISTENCE CLASS is already covered more broadly by
`exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorMembership` and
`exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorPoint` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingleAnchorArbitraryCompletionEscape.lean`.
At the center, player 3 is the literal membership coordinate. Nearby,
every anchor-containing reward is at least 1−δ, while anchor-excluding
rewards are at most δ; for δ<1/2 every complementary induced Nash point
passes `QuittingSingleAnchorInducedDominance`. Those declarations produce
a stationary profile with the active randomization repeated on deleted-
anchor paths. The one-date-then-Never profile proved here is different on
those paths; Section 3 separately checks its complete cap. No new UE
existence class is claimed.
